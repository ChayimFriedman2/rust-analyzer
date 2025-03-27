//! Provides validators for names of declarations.
//!
//! This includes the following items:
//!
//! - variable bindings (e.g. `let x = foo();`)
//! - struct fields (e.g. `struct Foo { field: u8 }`)
//! - enum variants (e.g. `enum Foo { Variant { field: u8 } }`)
//! - function/method arguments (e.g. `fn foo(arg: u8)`)
//! - constants (e.g. `const FOO: u8 = 10;`)
//! - static items (e.g. `static FOO: u8 = 10;`)
//! - match arm bindings (e.g. `foo @ Some(_)`)
//! - modules (e.g. `mod foo { ... }` or `mod foo;`)
// FIXME: This does not handle generic parameters.

mod case_conv;

use std::fmt;

use hir_def::{
    AdtId, ConstId, DefWithBodyId, EnumId, EnumVariantId, FieldId, FunctionId, HasModule,
    ItemContainerId, Lookup, ModuleDefId, ModuleId, StaticId, StructId, TraitAliasId, TraitId,
    TypeAliasId, UnionId, VariantId,
    data::{
        ConstData, FunctionData, StaticData, TraitAliasData, TraitData, TypeAliasData,
        adt::{EnumData, EnumVariants, StructData, VariantData},
    },
    db::DefDatabase,
    expr_store::Body,
    hir::{Pat, PatId},
    nameres::DefMap,
    src::{HasChildSource, HasSource},
};
use hir_expand::{InFile, name::Name};
use intern::{Symbol, sym};
use rustc_hash::FxHashSet;
use syntax::{
    AstNode, AstPtr,
    ast::{self, HasName},
};

use crate::db::HirDatabase;

use self::case_conv::{to_camel_case, to_lower_snake_case, to_upper_snake_case};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseType {
    /// `some_var`
    LowerSnakeCase,
    /// `SOME_CONST`
    UpperSnakeCase,
    /// `SomeStruct`
    UpperCamelCase,
}

impl fmt::Display for CaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = match self {
            CaseType::LowerSnakeCase => "snake_case",
            CaseType::UpperSnakeCase => "UPPER_SNAKE_CASE",
            CaseType::UpperCamelCase => "UpperCamelCase",
        };

        repr.fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentType {
    Constant,
    Enum,
    Field,
    Function,
    Module,
    Parameter,
    StaticVariable,
    Structure,
    Trait,
    TypeAlias,
    Variable,
    Variant,
}

impl fmt::Display for IdentType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = match self {
            IdentType::Constant => "Constant",
            IdentType::Enum => "Enum",
            IdentType::Field => "Field",
            IdentType::Function => "Function",
            IdentType::Module => "Module",
            IdentType::Parameter => "Parameter",
            IdentType::StaticVariable => "Static variable",
            IdentType::Structure => "Structure",
            IdentType::Trait => "Trait",
            IdentType::TypeAlias => "Type alias",
            IdentType::Variable => "Variable",
            IdentType::Variant => "Variant",
        };

        repr.fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncorrectCaseSource {
    ModuleName { module: ModuleId },
    ItemName { item: ModuleDefId },
    Field { field: FieldId },
    Binding { owner: DefWithBodyId, pat: PatId },
}

impl IncorrectCaseSource {
    fn resolve_item_name<N, S, L>(db: &dyn HirDatabase, id: L) -> Option<InFile<AstPtr<ast::Name>>>
    where
        N: AstNode + HasName + fmt::Debug,
        S: HasSource<Value = N>,
        L: Lookup<Data = S, Database = dyn DefDatabase> + HasModule + Copy,
    {
        let loc = id.lookup(db.upcast());
        let source = loc.source(db.upcast());
        Some(source.with_value(AstPtr::new(&source.value.name()?)))
    }

    /// The original diagnostic computation is inside a query, so it cannot refer to the AST to stay incremental.
    /// This method is supposed to be called from IDE layer to resolve the name.
    pub fn resolve(&self, db: &dyn HirDatabase) -> Option<InFile<AstPtr<ast::Name>>> {
        match self {
            IncorrectCaseSource::ModuleName { module } => {
                let def_map = module.def_map(db.upcast());
                let module_data = &def_map[module.local_id];
                let module_src = module_data.declaration_source(db.upcast())?;
                let name_ast = module_src.value.name()?;
                Some(module_src.with_value(AstPtr::new(&name_ast)))
            }
            IncorrectCaseSource::ItemName { item } => match *item {
                ModuleDefId::FunctionId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::AdtId(AdtId::EnumId(it)) => Self::resolve_item_name(db, it),
                ModuleDefId::AdtId(AdtId::StructId(it)) => Self::resolve_item_name(db, it),
                ModuleDefId::AdtId(AdtId::UnionId(it)) => Self::resolve_item_name(db, it),
                ModuleDefId::EnumVariantId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::ConstId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::StaticId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::TraitId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::TraitAliasId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::TypeAliasId(it) => Self::resolve_item_name(db, it),
                ModuleDefId::BuiltinType(_)
                | ModuleDefId::MacroId(_)
                | ModuleDefId::ModuleId(_) => unreachable!("not an item"),
            },
            IncorrectCaseSource::Field { field } => {
                let src = field.parent.child_source(db.upcast());
                let name = src.value[field.local_id].as_ref().right()?.name()?;
                Some(src.with_value(AstPtr::new(&name)))
            }
            &IncorrectCaseSource::Binding { owner, pat } => {
                let (_, source_map) = db.body_with_source_map(owner);
                let source_ptr = source_map.pat_syntax(pat).ok()?;
                let ptr = source_ptr.value.cast::<ast::IdentPat>()?;
                let root = source_ptr.file_syntax(db.upcast());
                let ident_pat = ptr.to_node(&root);
                Some(source_ptr.with_value(AstPtr::new(&ident_pat.name()?)))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncorrectCase {
    pub source: IncorrectCaseSource,
    pub expected_case: CaseType,
    pub ident_type: IdentType,
    pub ident: Symbol,
    /// Remember to escape this if it's a keyword in the file's edition!
    pub suggested_text: String,
}

pub struct IncorrectCaseValidator<'a> {
    db: &'a dyn HirDatabase,
    sink: Vec<IncorrectCase>,
}

#[derive(Debug)]
struct Replacement {
    current_name: Name,
    suggested_text: String,
    expected_case: CaseType,
}

impl<'a> IncorrectCaseValidator<'a> {
    pub fn new(db: &'a dyn HirDatabase) -> IncorrectCaseValidator<'a> {
        IncorrectCaseValidator { db, sink: Vec::new() }
    }

    pub fn validate_module(&mut self, module_id: ModuleId, def_map: &DefMap) {
        // Check the module name.
        let Some(module_name) = module_id.name_with_def_map(def_map) else { return };
        let Some(module_name_replacement) =
            to_lower_snake_case(module_name.as_str()).map(|new_name| Replacement {
                current_name: module_name,
                suggested_text: new_name,
                expected_case: CaseType::LowerSnakeCase,
            })
        else {
            return;
        };
        self.sink.push(IncorrectCase {
            source: IncorrectCaseSource::ModuleName { module: module_id },
            expected_case: module_name_replacement.expected_case,
            ident_type: IdentType::Module,
            ident: module_name_replacement.current_name.symbol().clone(),
            suggested_text: module_name_replacement.suggested_text,
        });
    }

    pub fn validate_trait(&mut self, trait_id: TraitId, data: &TraitData) {
        // Check the trait name.
        self.create_incorrect_case_diagnostic_for_item_name(
            trait_id.into(),
            &data.name,
            CaseType::UpperCamelCase,
            IdentType::Trait,
        );
    }

    pub fn validate_trait_alias(&mut self, trait_alias_id: TraitAliasId, data: &TraitAliasData) {
        // Check the trait name.
        self.create_incorrect_case_diagnostic_for_item_name(
            trait_alias_id.into(),
            &data.name,
            CaseType::UpperCamelCase,
            IdentType::Trait,
        );
    }

    pub fn validate_func(&mut self, func: FunctionId, data: &FunctionData) {
        let container = func.lookup(self.db.upcast()).container;
        if matches!(container, ItemContainerId::ExternBlockId(_)) {
            cov_mark::hit!(extern_func_incorrect_case_ignored);
            return;
        }

        // Check the function name.
        // Skipped if function is an associated item of a trait implementation.
        if !self.is_trait_impl_container(container) {
            // Don't run the lint on extern "[not Rust]" fn items with the
            // #[no_mangle] attribute.
            if data.is_no_mangle() && data.abi.as_ref().is_some_and(|abi| *abi != sym::Rust) {
                cov_mark::hit!(extern_func_no_mangle_ignored);
            } else {
                self.create_incorrect_case_diagnostic_for_item_name(
                    func.into(),
                    &data.name,
                    CaseType::LowerSnakeCase,
                    IdentType::Function,
                );
            }
        } else {
            cov_mark::hit!(trait_impl_assoc_func_name_incorrect_case_ignored);
        }
    }

    /// Check incorrect names for patterns inside a body.
    /// This includes function parameters except for trait implementation associated functions.
    pub fn validate_body(&mut self, def: DefWithBodyId, body: &Body) {
        let mut exclude_shorthand_pats = FxHashSet::default();
        // Need to collect eagerly so that `exclude_shorthand_pats` will be filled. Not a problem because the list
        // is usually empty.
        let pats_replacements = body
            .pats
            .iter()
            .filter_map(|(pat_id, pat)| match pat {
                Pat::Bind { id, .. } => {
                    let bind_name = &body.bindings[*id].name;
                    let suggested_text = to_lower_snake_case(bind_name.as_str())?;
                    let replacement = Replacement {
                        current_name: bind_name.clone(),
                        suggested_text,
                        expected_case: CaseType::LowerSnakeCase,
                    };
                    // FIXME: This is not entirely accurate, e.g. it will report `fn foo(Foo(x): Foo)` as not a parameter.
                    let is_param = body.params.contains(&pat_id);
                    let ident_type =
                        if is_param { IdentType::Parameter } else { IdentType::Variable };
                    Some((pat_id, replacement, ident_type))
                }
                Pat::Record { args, .. } => {
                    exclude_shorthand_pats
                        .extend(args.iter().filter(|arg| arg.is_shorthand).map(|arg| arg.pat));
                    None
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        for (pat, replacement, ident_type) in pats_replacements {
            if exclude_shorthand_pats.contains(&pat) {
                continue;
            }
            self.sink.push(IncorrectCase {
                source: IncorrectCaseSource::Binding { owner: def, pat },
                expected_case: replacement.expected_case,
                ident_type,
                ident: replacement.current_name.symbol().clone(),
                suggested_text: replacement.suggested_text,
            });
        }
    }

    pub fn validate_struct(
        &mut self,
        struct_id: StructId,
        struct_data: &StructData,
        variant_data: &VariantData,
    ) {
        // Check the structure name.
        self.create_incorrect_case_diagnostic_for_item_name(
            struct_id.into(),
            &struct_data.name,
            CaseType::UpperCamelCase,
            IdentType::Structure,
        );

        // Check the field names.
        self.validate_fields(struct_id.into(), variant_data);
    }

    pub fn validate_union(
        &mut self,
        union_id: UnionId,
        union_data: &StructData,
        variant_data: &VariantData,
    ) {
        // Check the union name.
        self.create_incorrect_case_diagnostic_for_item_name(
            union_id.into(),
            &union_data.name,
            CaseType::UpperCamelCase,
            IdentType::Structure,
        );

        // Check the field names.
        self.validate_fields(union_id.into(), variant_data);
    }

    /// Check incorrect names for struct fields.
    fn validate_fields(&mut self, variant_id: VariantId, data: &VariantData) {
        let VariantData::Record { fields, .. } = data else {
            return;
        };
        let fields_replacements = fields.iter().filter_map(|(field_idx, field)| {
            Some((
                field_idx,
                to_lower_snake_case(field.name.as_str()).map(|new_name| Replacement {
                    current_name: field.name.clone(),
                    suggested_text: new_name,
                    expected_case: CaseType::LowerSnakeCase,
                })?,
            ))
        });

        for (field_idx, replacement) in fields_replacements {
            self.sink.push(IncorrectCase {
                source: IncorrectCaseSource::Field {
                    field: FieldId { parent: variant_id, local_id: field_idx },
                },
                expected_case: replacement.expected_case,
                ident_type: IdentType::Field,
                ident: replacement.current_name.symbol().clone(),
                suggested_text: replacement.suggested_text,
            });
        }
    }

    pub fn validate_enum(
        &mut self,
        enum_id: EnumId,
        enum_data: &EnumData,
        variants_data: &EnumVariants,
    ) {
        // Check the enum name.
        self.create_incorrect_case_diagnostic_for_item_name(
            enum_id.into(),
            &enum_data.name,
            CaseType::UpperCamelCase,
            IdentType::Enum,
        );

        // Check the variant names.
        self.validate_enum_variants(variants_data)
    }

    pub fn validate_enum_variant(&mut self, variant_id: EnumVariantId, data: &VariantData) {
        self.validate_fields(variant_id.into(), data);
    }

    /// Check incorrect names for enum variants.
    fn validate_enum_variants(&mut self, data: &EnumVariants) {
        let enum_variants_replacements = data.variants.iter().filter_map(|(variant_id, name)| {
            Some((
                *variant_id,
                to_camel_case(name.as_str()).map(|new_name| Replacement {
                    current_name: name.clone(),
                    suggested_text: new_name,
                    expected_case: CaseType::UpperCamelCase,
                })?,
            ))
        });
        for (variant_id, replacement) in enum_variants_replacements {
            self.sink.push(IncorrectCase {
                source: IncorrectCaseSource::ItemName { item: variant_id.into() },
                expected_case: replacement.expected_case,
                ident_type: IdentType::Variant,
                ident: replacement.current_name.symbol().clone(),
                suggested_text: replacement.suggested_text,
            });
        }
    }

    pub fn validate_const(&mut self, const_id: ConstId, data: &ConstData) {
        let container = const_id.lookup(self.db.upcast()).container;
        if self.is_trait_impl_container(container) {
            cov_mark::hit!(trait_impl_assoc_const_incorrect_case_ignored);
            return;
        }

        let Some(name) = &data.name else {
            return;
        };
        self.create_incorrect_case_diagnostic_for_item_name(
            const_id.into(),
            name,
            CaseType::UpperSnakeCase,
            IdentType::Constant,
        );
    }

    pub fn validate_static(&mut self, static_id: StaticId, data: &StaticData) {
        if data.is_extern {
            cov_mark::hit!(extern_static_incorrect_case_ignored);
            return;
        }

        self.create_incorrect_case_diagnostic_for_item_name(
            static_id.into(),
            &data.name,
            CaseType::UpperSnakeCase,
            IdentType::StaticVariable,
        );
    }

    pub fn validate_type_alias(&mut self, type_alias_id: TypeAliasId, data: &TypeAliasData) {
        let container = type_alias_id.lookup(self.db.upcast()).container;
        if self.is_trait_impl_container(container) {
            cov_mark::hit!(trait_impl_assoc_type_incorrect_case_ignored);
            return;
        }

        // Check the type alias name.
        self.create_incorrect_case_diagnostic_for_item_name(
            type_alias_id.into(),
            &data.name,
            CaseType::UpperCamelCase,
            IdentType::TypeAlias,
        );
    }

    fn create_incorrect_case_diagnostic_for_item_name(
        &mut self,
        item_id: ModuleDefId,
        name: &Name,
        expected_case: CaseType,
        ident_type: IdentType,
    ) {
        let to_expected_case_type = match expected_case {
            CaseType::LowerSnakeCase => to_lower_snake_case,
            CaseType::UpperSnakeCase => to_upper_snake_case,
            CaseType::UpperCamelCase => to_camel_case,
        };
        let Some(replacement) = to_expected_case_type(name.as_str()).map(|new_name| Replacement {
            current_name: name.clone(),
            suggested_text: new_name,
            expected_case,
        }) else {
            return;
        };

        self.sink.push(IncorrectCase {
            source: IncorrectCaseSource::ItemName { item: item_id },
            expected_case: replacement.expected_case,
            ident_type,
            ident: replacement.current_name.symbol().clone(),
            suggested_text: replacement.suggested_text,
        });
    }

    fn is_trait_impl_container(&self, container_id: ItemContainerId) -> bool {
        if let ItemContainerId::ImplId(impl_id) = container_id {
            if self.db.impl_data(impl_id).target_trait.is_some() {
                return true;
            }
        }
        false
    }

    pub fn finish(self) -> Vec<IncorrectCase> {
        self.sink
    }
}
