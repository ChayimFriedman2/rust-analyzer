//! This module contains the queries that define diagnostics, for incrementality.
//!
//! Compare [`crate::diagnostics`] which wraps the diagnostics in a non-incrementalizable
//! layer for IDE consumption (for example, it refer to syntax trees).
// FIXME: We currently have one query that computes the diagnostics for all item's children
// and for the item. Is it worth splitting it to two queries? Memory usage will be doubled,
// but incrementality will be better served.

use std::mem::discriminant;

use base_db::{Crate, impl_intern_key, salsa};
use hir_def::{
    AdtId, AssocItemId, AttrDefId, BlockId, ConstId, ConstParamId, DefWithBodyId, EnumId,
    FunctionId, GenericDefId, GenericParamId, HasModule, ImplId, LifetimeParamId, MacroId,
    ModuleDefId, ModuleId, StaticId, StructId, TraitAliasId, TraitId, TypeAliasId,
    TypeOrConstParamId, TypeParamId, UnionId, VariantId,
    data::{ImplData, TraitFlags},
    expr_store::Body,
    generics::TypeOrConstParamData,
    hir::{BindingAnnotation, BindingId, ExprOrPatId},
    lang_item::LangItem,
    nameres::{DefMap, assoc::ImplItems, diagnostics::DefDiagnosticKind},
};
use hir_expand::{ExpandResult, name::Name};
use hir_ty::{
    InferenceDiagnostic, InferenceResult, TraitRefExt, Ty, TyLoweringDiagnostic, TypeMismatch,
    check_orphan_rules,
    db::HirDatabase,
    diagnostics::{IncorrectCase, IncorrectCaseValidator, MissingUnsafeResult},
    mir::{self, BorrowckResult, MirSpan},
};
use intern::{Symbol, sym};
use span::MacroCallId;
use stdx::{impl_from, never};
use syntax::SyntaxError;
use thin_vec::ThinVec;
use triomphe::{Arc, ThinArc};

// FIXME: We probably need to use the interned in all places.
// Alternatively, don't intern it and instead have a `module_diagnostics()` query taking
// `Crate, Option<BlockId>, LocalModuleId`, but that won't be beneficial until
// https://github.com/salsa-rs/salsa/issues/599 is implemented.
impl_intern_key!(InternedModuleId, ModuleId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, salsa::Supertype)]
pub(crate) enum DiagnosticsOwner {
    Crate(Crate),
    BlockId(BlockId),
    ModuleId(InternedModuleId),
    FunctionId(FunctionId),
    AdtId(AdtId),
    ConstId(ConstId),
    StaticId(StaticId),
    TraitId(TraitId),
    TraitAliasId(TraitAliasId),
    TypeAliasId(TypeAliasId),
    MacroId(MacroId),
    ImplId(ImplId),
}
impl_from!(
    Crate,
    BlockId,
    FunctionId,
    AdtId,
    ConstId,
    StaticId,
    TraitId,
    TraitAliasId,
    TypeAliasId,
    MacroId,
    ImplId
    for DiagnosticsOwner
);
impl From<InternedModuleId> for DiagnosticsOwner {
    #[inline]
    fn from(module: InternedModuleId) -> Self {
        DiagnosticsOwner::ModuleId(module)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TypesMapOwner {
    Generics(GenericDefId),
    Fields(VariantId),
    TypeAliasType(TypeAliasId),
    Impl(ImplId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AnyDiagnostic {
    DefDiagnostic {
        krate: Crate,
        diag: DefDiagnosticKind,
    },
    MacroError {
        macro_call_id: MacroCallId,
        errors: Arc<ExpandResult<Arc<[SyntaxError]>>>,
    },
    TyLoweringDiagnostic {
        owner: TypesMapOwner,
        diags: ThinArc<(), TyLoweringDiagnostic>,
    },
    /// Body lowering diagnostics need to refer the AST directly, and we cannot afford ourselves
    /// that here. So instead, we only mark the bodies that have diagnostics and let IDE fetch
    /// the errors, on the hope that only a small number of bodies will have errors at a point
    /// in time.
    BodyLoweringDiagnostics {
        body: DefWithBodyId,
    },
    InferenceDiagnostics {
        owner: DefWithBodyId,
        diags: Box<[InferenceDiagnostic]>,
    },
    TypeMismatch {
        owner: DefWithBodyId,
        node: ExprOrPatId,
        mismatch: TypeMismatch,
    },
    BodyValidationDiagnostics {
        owner: DefWithBodyId,
        diags: Box<[BodyValidationDiagnostic]>,
    },
    BorrowckDiagnostic {
        owner: DefWithBodyId,
        diag: BorrowckDiagnostic,
    },
    IncoherentImpl {
        impl_: ImplId,
    },
    IncorrectCase(IncorrectCase),
    TraitImplOrphan {
        impl_: ImplId,
    },
    TraitImplIncorrectSafety {
        impl_: ImplId,
        should_be_safe: bool,
    },
    TraitImplRedundantAssocItems {
        impl_: ImplId,
        trait_: TraitId,
        assoc_item: (Name, AssocItemId),
    },
    TraitImplMissingAssocItems {
        impl_: ImplId,
        trait_: TraitId,
        missing: Box<[(Name, AssocItemId)]>,
    },
}

type Diagnostics = ThinVec<AnyDiagnostic>;

#[salsa::tracked(return_ref)]
pub(crate) fn diagnostics_for(db: &dyn HirDatabase, owner: DiagnosticsOwner) -> Diagnostics {
    match owner {
        DiagnosticsOwner::Crate(it) => crate_diagnostics(db, it),
        DiagnosticsOwner::BlockId(it) => block_diagnostics(db, it),
        DiagnosticsOwner::ModuleId(it) => module_diagnostics(db, it),
        DiagnosticsOwner::FunctionId(it) => function_diagnostics(db, it),
        DiagnosticsOwner::AdtId(AdtId::StructId(it)) => struct_diagnostics(db, it),
        DiagnosticsOwner::AdtId(AdtId::EnumId(it)) => enum_diagnostics(db, it),
        DiagnosticsOwner::AdtId(AdtId::UnionId(it)) => union_diagnostics(db, it),
        DiagnosticsOwner::ConstId(it) => const_diagnostics(db, it),
        DiagnosticsOwner::StaticId(it) => static_diagnostics(db, it),
        DiagnosticsOwner::TraitId(it) => trait_diagnostics(db, it),
        DiagnosticsOwner::TraitAliasId(it) => trait_alias_diagnostics(db, it),
        DiagnosticsOwner::TypeAliasId(it) => type_alias_diagnostics(db, it),
        DiagnosticsOwner::MacroId(it) => macro_diagnostics(db, it),
        DiagnosticsOwner::ImplId(it) => impl_diagnostics(db, it),
    }
}

fn crate_diagnostics(db: &dyn HirDatabase, krate: Crate) -> Diagnostics {
    let _guard = tracing::info_span!("crate_diagnostics", crate=%crate_name(db, krate)).entered();
    let def_map = db.crate_def_map(krate);
    let incoherent_impls = incoherent_crate_inherent_impls(db, krate);
    return crate_or_block_diagnostics(db, &def_map, &incoherent_impls);

    fn crate_name(db: &dyn HirDatabase, krate: Crate) -> Symbol {
        krate
            .extra_data(db)
            .display_name
            .as_ref()
            .map(|it| it.crate_name().symbol().clone())
            .unwrap_or(sym::consts::missing)
    }
}

fn block_diagnostics(db: &dyn HirDatabase, block: BlockId) -> Diagnostics {
    let _guard = tracing::debug_span!("block_diagnostics").entered();
    let def_map = db.block_def_map(block);
    let incoherent_impls = incoherent_block_inherent_impls(db, block);
    crate_or_block_diagnostics(db, &def_map, &incoherent_impls)
}

// These are firewall queries: we don't want diagnostics to depend on all impls in a crate/block.
#[salsa::tracked(return_ref)]
fn incoherent_crate_inherent_impls(db: &dyn HirDatabase, krate: Crate) -> ThinVec<ImplId> {
    db.inherent_impls_in_crate(krate).invalid_impls().iter().copied().collect()
}

#[salsa::tracked(return_ref)]
fn incoherent_block_inherent_impls(db: &dyn HirDatabase, block: BlockId) -> ThinVec<ImplId> {
    match db.inherent_impls_in_block(block) {
        Some(it) => it.invalid_impls().iter().copied().collect(),
        None => ThinVec::new(),
    }
}

fn crate_or_block_diagnostics(
    db: &dyn HirDatabase,
    def_map: &DefMap,
    incoherent_impls: &[ImplId],
) -> Diagnostics {
    let mut diagnostics = Vec::new();

    diagnostics.extend(def_map.diagnostics().iter().map(|diag| AnyDiagnostic::DefDiagnostic {
        krate: def_map.krate(),
        diag: diag.kind.clone(),
    }));

    // It's worth talking a bit about how we nest modules. We have two options: we could let any module
    // compute the diagnostics for its children modules, or (what we do) we can compute them all at once
    // in the def map.
    // The advantage of the first approach is that it produces a hierarchy, and assuming code changes tend
    // to have local effects on its children and parent modules and less on sibling modules (a reasonable
    // but maybe-incorrect assumption), it will lead to better incrementality.
    // However, it also has one serious disadvantage for us: computing the diagnostics for all children modules,
    // especially when the module is high on the hierarchy, is pretty expensive. We don't want to do that
    // on every keystroke - only on save, where we check everything. If we include the children modules'
    // diagnostics, we have no way to compute *just* this module's diagnostics.
    let modules =
        def_map.modules().map(|(module, _)| InternedModuleId::new(db, def_map.module_id(module)));
    diagnostics.extend(modules.flat_map(|module| diagnostics_for(db, module.into())).cloned());

    diagnostics.extend(
        incoherent_impls.iter().copied().map(|impl_| AnyDiagnostic::IncoherentImpl { impl_ }),
    );

    Diagnostics::from_iter(diagnostics)
}

fn module_diagnostics(db: &dyn HirDatabase, module: InternedModuleId) -> Diagnostics {
    let module = module.loc(db);
    let def_map = module.def_map(db.upcast());
    let _guard =
        tracing::debug_span!("module_diagnostics", module=%module_name(&def_map, module)).entered();
    let mut diagnostics = Vec::new();
    let scope = &def_map[module.local_id].scope;

    diagnostics.extend(scope.all_macro_calls().filter_map(|macro_call_id| {
        Some(AnyDiagnostic::MacroError {
            macro_call_id,
            errors: db.parse_macro_expansion_error(macro_call_id)?,
        })
    }));

    diagnostics.extend(
        scope
            .declarations()
            .filter_map(|declaration| match declaration {
                // Module diagnostics are calculated as part of the crate/block diagnostics - see `crate_or_block_diagnostics()`.
                ModuleDefId::ModuleId(_) => None,
                ModuleDefId::FunctionId(it) => Some(it.into()),
                ModuleDefId::AdtId(it) => Some(it.into()),
                ModuleDefId::ConstId(it) => Some(it.into()),
                ModuleDefId::StaticId(it) => Some(it.into()),
                ModuleDefId::TraitId(it) => Some(it.into()),
                ModuleDefId::TraitAliasId(it) => Some(it.into()),
                ModuleDefId::TypeAliasId(it) => Some(it.into()),
                ModuleDefId::MacroId(it) => Some(it.into()),
                ModuleDefId::EnumVariantId(_) | ModuleDefId::BuiltinType(_) => None,
            })
            .chain(scope.unnamed_consts().map(Into::into))
            .chain(scope.legacy_macros().flat_map(|(_, macros)| macros).copied().map(Into::into))
            .chain(scope.impls().map(Into::into))
            .flat_map(|declaration| diagnostics_for(db, declaration))
            .cloned(),
    );

    return Diagnostics::from_iter(diagnostics);

    fn module_name(def_map: &DefMap, module: ModuleId) -> Symbol {
        def_map[module.local_id]
            .parent
            .and_then(|parent| {
                def_map[parent].children.iter().find_map(|(name, module_id)| {
                    if *module_id == module.local_id { Some(name.symbol().clone()) } else { None }
                })
            })
            .unwrap_or_else(|| sym::consts::crate_)
    }
}

fn function_diagnostics(db: &dyn HirDatabase, function: FunctionId) -> Diagnostics {
    let data = db.function_data(function);
    let _guard =
        tracing::debug_span!("function_diagnostics", function = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    generics_diagnostics(db, function.into(), &mut diagnostics);
    body_diagnostics(db, function.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_func(function, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn struct_diagnostics(db: &dyn HirDatabase, strukt: StructId) -> Diagnostics {
    let data = db.struct_data(strukt);
    let _guard = tracing::debug_span!("struct_diagnostics", struct = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    let (variants_data, variants_diagnostics) = db.variant_data_with_diagnostics(strukt.into());
    let krate = strukt.loc(db).container.krate();
    diagnostics.extend(
        variants_diagnostics
            .iter()
            .map(|diag| AnyDiagnostic::DefDiagnostic { krate, diag: diag.kind.clone() }),
    );
    generics_diagnostics(db, strukt.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_struct(strukt, &data, &variants_data)
    });
    if let Some(diags) = db.field_types_with_diagnostics(strukt.into()).1 {
        diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
            owner: TypesMapOwner::Fields(strukt.into()),
            diags,
        });
    }

    Diagnostics::from_iter(diagnostics)
}

fn union_diagnostics(db: &dyn HirDatabase, union: UnionId) -> Diagnostics {
    let data = db.union_data(union);
    let _guard = tracing::debug_span!("union_diagnostics", union = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    let (variants_data, variants_diagnostics) = db.variant_data_with_diagnostics(union.into());
    let krate = union.loc(db).container.krate();
    diagnostics.extend(
        variants_diagnostics
            .iter()
            .map(|diag| AnyDiagnostic::DefDiagnostic { krate, diag: diag.kind.clone() }),
    );
    generics_diagnostics(db, union.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_union(union, &data, &variants_data)
    });
    if let Some(diags) = db.field_types_with_diagnostics(union.into()).1 {
        diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
            owner: TypesMapOwner::Fields(union.into()),
            diags,
        });
    }

    Diagnostics::from_iter(diagnostics)
}

fn enum_diagnostics(db: &dyn HirDatabase, enum_: EnumId) -> Diagnostics {
    let data = db.enum_data(enum_);
    let _guard = tracing::debug_span!("enum_diagnostics", enum = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    let variants = db.enum_variants(enum_);
    let krate = enum_.loc(db).container.krate();
    generics_diagnostics(db, enum_.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_enum(enum_, &data, &variants)
    });

    for &(variant, _) in variants.variants.iter() {
        let (variant_data, variant_diagnostics) = db.variant_data_with_diagnostics(variant.into());
        diagnostics.extend(
            variant_diagnostics
                .iter()
                .map(|diag| AnyDiagnostic::DefDiagnostic { krate, diag: diag.kind.clone() }),
        );
        if let Some(diags) = db.field_types_with_diagnostics(variant.into()).1 {
            diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
                owner: TypesMapOwner::Fields(variant.into()),
                diags,
            });
        }
        incorrect_case(db, &mut diagnostics, |incorrect_case| {
            incorrect_case.validate_enum_variant(variant, &variant_data)
        });
        body_diagnostics(db, variant.into(), &mut diagnostics);
    }

    Diagnostics::from_iter(diagnostics)
}

fn trait_diagnostics(db: &dyn HirDatabase, trait_: TraitId) -> Diagnostics {
    let data = db.trait_data(trait_);
    let _guard = tracing::debug_span!("trait_diagnostics", trait = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    generics_diagnostics(db, trait_.into(), &mut diagnostics);
    let krate = trait_.loc(db).container.krate();
    let (items, items_diagnostics) = db.trait_items_with_diagnostics(trait_);
    diagnostics.extend(
        items_diagnostics
            .iter()
            .map(|diag| AnyDiagnostic::DefDiagnostic { krate, diag: diag.kind.clone() }),
    );
    if let Some(macro_calls) = &items.macro_calls {
        diagnostics.extend(macro_calls.iter().filter_map(|&(_, macro_call)| {
            Some(AnyDiagnostic::MacroError {
                macro_call_id: macro_call,
                errors: db.parse_macro_expansion_error(macro_call)?,
            })
        }));
    }
    for &(_, item) in &items.items {
        let item = match item {
            AssocItemId::FunctionId(it) => it.into(),
            AssocItemId::ConstId(it) => it.into(),
            AssocItemId::TypeAliasId(it) => it.into(),
        };
        diagnostics.extend(diagnostics_for(db, item).iter().cloned());
    }
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_trait(trait_, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn trait_alias_diagnostics(db: &dyn HirDatabase, trait_alias: TraitAliasId) -> Diagnostics {
    let data = db.trait_alias_data(trait_alias);
    let _guard = tracing::debug_span!("trait_alias_diagnostics", trait_alias = %data.name.symbol())
        .entered();
    let mut diagnostics = Vec::new();

    generics_diagnostics(db, trait_alias.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_trait_alias(trait_alias, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn type_alias_diagnostics(db: &dyn HirDatabase, type_alias: TypeAliasId) -> Diagnostics {
    let data = db.type_alias_data(type_alias);
    let _guard =
        tracing::debug_span!("type_alias_diagnostics", type_alias = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    generics_diagnostics(db, type_alias.into(), &mut diagnostics);
    if let Some(diags) = db.type_for_type_alias_with_diagnostics(type_alias).1 {
        diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
            owner: TypesMapOwner::TypeAliasType(type_alias),
            diags,
        });
    }
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_type_alias(type_alias, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn const_diagnostics(db: &dyn HirDatabase, konst: ConstId) -> Diagnostics {
    let data = db.const_data(konst);
    let _guard = tracing::debug_span!("const_diagnostics", const = ?data.name.as_ref().map(|it| it.symbol())).entered();
    let mut diagnostics = Vec::new();

    body_diagnostics(db, konst.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_const(konst, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn static_diagnostics(db: &dyn HirDatabase, statik: StaticId) -> Diagnostics {
    let data = db.static_data(statik);
    let _guard = tracing::debug_span!("static_diagnostics", static = %data.name.symbol()).entered();
    let mut diagnostics = Vec::new();

    body_diagnostics(db, statik.into(), &mut diagnostics);
    incorrect_case(db, &mut diagnostics, |incorrect_case| {
        incorrect_case.validate_static(statik, &data)
    });

    Diagnostics::from_iter(diagnostics)
}

fn macro_diagnostics(db: &dyn HirDatabase, makro: MacroId) -> Diagnostics {
    let _guard = tracing::debug_span!("macro_diagnostics").entered();
    let mut diagnostics = Vec::new();

    let def = db.macro_def(makro);
    if let hir_expand::db::TokenExpander::DeclarativeMacro(expander) = db.macro_expander(def) {
        if let Some(e) = expander.mac.err() {
            if let Some(ast) = def.ast_id().left() {
                let krate = makro.krate(db.upcast());
                diagnostics.push(AnyDiagnostic::DefDiagnostic {
                    krate,
                    diag: DefDiagnosticKind::MacroDefError { ast, message: e.to_string() },
                });
            } else {
                never!("declarative expander for non decl-macro: {:?}", e);
            }
        }
    }

    Diagnostics::from_iter(diagnostics)
}

fn impl_diagnostics(db: &dyn HirDatabase, impl_: ImplId) -> Diagnostics {
    let _guard = tracing::debug_span!("impl_diagnostics").entered();
    let mut diagnostics = Vec::new();
    let krate = impl_.krate(db.upcast());

    let data = db.impl_data(impl_);
    let (items, items_diagnostics) = db.impl_items_with_diagnostics(impl_);
    diagnostics.extend(
        items_diagnostics
            .iter()
            .map(|diag| AnyDiagnostic::DefDiagnostic { krate, diag: diag.kind.clone() }),
    );
    if let Some(macro_calls) = &items.macro_calls {
        diagnostics.extend(macro_calls.iter().filter_map(|&(_, macro_call)| {
            Some(AnyDiagnostic::MacroError {
                macro_call_id: macro_call,
                errors: db.parse_macro_expansion_error(macro_call)?,
            })
        }));
    }
    for &(_, item) in &items.items {
        let item = match item {
            AssocItemId::FunctionId(it) => it.into(),
            AssocItemId::ConstId(it) => it.into(),
            AssocItemId::TypeAliasId(it) => it.into(),
        };
        diagnostics.extend(diagnostics_for(db, item).iter().cloned());
    }

    generics_diagnostics(db, impl_.into(), &mut diagnostics);
    let impl_trait = db.impl_trait_with_diagnostics(impl_);
    if let Some(diags) = impl_trait.as_ref().and_then(|it| it.1.as_ref()) {
        diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
            owner: TypesMapOwner::Impl(impl_),
            diags: diags.clone(),
        });
    }
    let impl_trait = impl_trait.map(|(impl_trait, _)| impl_trait.skip_binders().hir_trait_id());
    check_impl_safety(db, impl_, &data, impl_trait, krate, &mut diagnostics);
    check_impl_versus_trait_items(db, impl_, &data, impl_trait, &items, &mut diagnostics);
    if let Some(diags) = db.impl_self_ty_with_diagnostics(impl_).1 {
        diagnostics
            .push(AnyDiagnostic::TyLoweringDiagnostic { owner: TypesMapOwner::Impl(impl_), diags });
    }
    if !check_orphan_rules(db, impl_) {
        diagnostics.push(AnyDiagnostic::TraitImplOrphan { impl_ });
    }

    Diagnostics::from_iter(diagnostics)
}

fn check_impl_versus_trait_items(
    db: &dyn HirDatabase,
    impl_: ImplId,
    impl_data: &ImplData,
    trait_: Option<TraitId>,
    impl_items: &ImplItems,
    diagnostics: &mut Vec<AnyDiagnostic>,
) {
    let Some(trait_) = trait_ else { return };
    if impl_data.is_negative {
        // Negative impls can't have items, don't emit missing items diagnostic for them
        return;
    }

    let items = &db.trait_items(trait_.into()).items;
    let required_items = items.iter().filter(|&(_, assoc)| match *assoc {
        AssocItemId::FunctionId(it) => !db.function_data(it).has_body(),
        AssocItemId::ConstId(id) => !db.const_data(id).has_body,
        AssocItemId::TypeAliasId(it) => db.type_alias_data(it).type_ref.is_none(),
    });

    let redundant = impl_items
        .items
        .iter()
        .filter(|(name, id)| {
            !items.iter().any(|(impl_name, impl_item)| {
                discriminant(impl_item) == discriminant(id) && impl_name == name
            })
        })
        .map(|(name, item)| (name.clone(), *item));
    for (name, assoc_item) in redundant {
        diagnostics.push(AnyDiagnostic::TraitImplRedundantAssocItems {
            trait_,
            impl_,
            assoc_item: (name, assoc_item),
        })
    }

    let missing = required_items
        .filter(|(name, id)| {
            !impl_items.items.iter().any(|(impl_name, impl_item)| {
                discriminant(impl_item) == discriminant(id) && impl_name == name
            })
        })
        .map(|(name, item)| (name.clone(), *item))
        .collect::<Box<[_]>>();
    if !missing.is_empty() {
        diagnostics.push(AnyDiagnostic::TraitImplMissingAssocItems { trait_, impl_, missing })
    }
}

fn check_impl_safety(
    db: &dyn HirDatabase,
    impl_: ImplId,
    impl_data: &ImplData,
    trait_: Option<TraitId>,
    krate: Crate,
    diagnostics: &mut Vec<AnyDiagnostic>,
) {
    let drop_maybe_dangle = (|| {
        // FIXME: This can be simplified a lot by exposing hir-ty's utils.rs::Generics helper
        let trait_ = trait_?;
        let drop_trait = db.lang_item(krate, LangItem::Drop)?.as_trait()?;
        if drop_trait != trait_.into() {
            return None;
        }
        let parent = impl_.into();
        let generic_params = db.generic_params(parent);
        let lifetime_params = generic_params.iter_lt().map(|(local_id, _)| {
            GenericParamId::LifetimeParamId(LifetimeParamId { parent, local_id })
        });
        let type_params = generic_params
            .iter_type_or_consts()
            .filter(|(_, it)| it.type_param().is_some())
            .map(|(local_id, _)| {
                GenericParamId::TypeParamId(TypeParamId::from_unchecked(TypeOrConstParamId {
                    parent,
                    local_id,
                }))
            });
        let res = type_params
            .chain(lifetime_params)
            .any(|p| db.attrs(AttrDefId::GenericParamId(p)).by_key(&sym::may_dangle).exists());
        Some(res)
    })()
    .unwrap_or(false);

    let trait_is_unsafe =
        trait_.is_some_and(|t| db.trait_data(t).flags.contains(TraitFlags::IS_UNSAFE));
    let impl_is_negative = impl_data.is_negative;
    let impl_is_unsafe = impl_data.is_unsafe;

    match (impl_is_unsafe, trait_is_unsafe, impl_is_negative, drop_maybe_dangle) {
        // unsafe negative impl
        (true, _, true, _) |
        // unsafe impl for safe trait
        (true, false, _, false) => diagnostics.push(AnyDiagnostic::TraitImplIncorrectSafety { impl_, should_be_safe: true }),
        // safe impl for unsafe trait
        (false, true, false, _) |
        // safe impl of dangling drop
        (false, false, _, true) => diagnostics.push(AnyDiagnostic::TraitImplIncorrectSafety { impl_, should_be_safe: false }),
        _ => (),
    };
}

fn generics_diagnostics(
    db: &dyn HirDatabase,
    def: GenericDefId,
    diagnostics: &mut Vec<AnyDiagnostic>,
) {
    let generics = db.generic_params(def);
    if generics.is_empty() && generics.no_predicates() {
        return;
    }

    let mut handle_diags = |diags| {
        if let Some(diags) = diags {
            diagnostics.push(AnyDiagnostic::TyLoweringDiagnostic {
                owner: TypesMapOwner::Generics(def),
                diags,
            });
        }
    };

    handle_diags(db.generic_defaults_with_diagnostics(def).1);
    handle_diags(db.generic_predicates_without_parent_with_diagnostics(def).1);
    for (param_id, param) in generics.iter_type_or_consts() {
        if let TypeOrConstParamData::ConstParamData(_) = param {
            handle_diags(
                db.const_param_ty_with_diagnostics(ConstParamId::from_unchecked(
                    TypeOrConstParamId { parent: def, local_id: param_id },
                ))
                .1,
            );
        }
    }
}

fn body_diagnostics(
    db: &dyn HirDatabase,
    def: DefWithBodyId,
    diagnostics: &mut Vec<AnyDiagnostic>,
) {
    let body = db.body(def);
    let infer = db.infer(def);
    let config = db.diagnostics_config();

    diagnostics.extend(
        body.blocks_no_def_map().flat_map(|block| diagnostics_for(db, block.into())).cloned(),
    );
    diagnostics.extend(body.expansions().filter_map(|macro_call_id| {
        Some(AnyDiagnostic::MacroError {
            macro_call_id,
            errors: db.parse_macro_expansion_error(macro_call_id)?,
        })
    }));
    if body.has_diagnostics {
        diagnostics.push(AnyDiagnostic::BodyLoweringDiagnostics { body: def });
    }
    if !infer.diagnostics.is_empty() {
        diagnostics.push(AnyDiagnostic::InferenceDiagnostics {
            owner: def,
            diags: infer.diagnostics.clone().into_boxed_slice(),
        });
    }
    diagnostics.extend(infer.type_mismatches().map(|(node, mismatch)| {
        AnyDiagnostic::TypeMismatch { owner: def, node, mismatch: mismatch.clone() }
    }));
    let validation_check = body_validation_diagnostics(db, def);
    if !validation_check.is_empty() {
        diagnostics.push(AnyDiagnostic::BodyValidationDiagnostics {
            owner: def,
            diags: validation_check.iter().cloned().collect(),
        });
    }
    if config.enable_borrowck {
        if let Ok(borrowck_results) = hir_ty::mir::borrowck(db, def) {
            for borrowck_result in &*borrowck_results {
                borrowck_diagnostics(def, &body, &infer, borrowck_result, diagnostics);
            }
        }
    }
    incorrect_case(db, diagnostics, |incorrect_case| incorrect_case.validate_body(def, &body));
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BodyValidationDiagnostic {
    Validation(hir_ty::diagnostics::BodyValidationDiagnostic),
    UnsafeCheck(MissingUnsafeResult),
}

// This is a separate query because it touches a lot of queries other than the body itself (especially match check),
// and we don't want a change in them to invalidate e.g. borrowck.
#[salsa::tracked(return_ref)]
fn body_validation_diagnostics(
    db: &dyn HirDatabase,
    def: DefWithBodyId,
) -> ThinVec<BodyValidationDiagnostic> {
    let body = db.body(def);
    let infer = db.infer(def);
    let config = db.diagnostics_config();
    let validation_diagnostics = hir_ty::diagnostics::BodyValidationDiagnostic::collect(
        db,
        def,
        &body,
        &infer,
        config.style_lints,
    );

    // We also put unsafe check here, even though we probably shouldn't, it probably should be a separate query (or maybe
    // even part of inference), to save memory and because they both touch queries besides the body and we don't want
    // other body diagnostics (e.g. borrowck) to get invalidated when they are invalidated.
    let mut unsafe_check = hir_ty::diagnostics::missing_unsafe(db, def, &body, &infer);
    let unsafe_check = if !unsafe_check.is_empty() {
        unsafe_check.shrink_to_fit();
        Some(BodyValidationDiagnostic::UnsafeCheck(unsafe_check))
    } else {
        None
    };

    ThinVec::from_iter(
        validation_diagnostics
            .into_iter()
            .map(BodyValidationDiagnostic::Validation)
            .chain(unsafe_check),
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BorrowckDiagnostic {
    MovedOutOfRef { ty: Ty, span: MirSpan },
    UnusedVariable { variable: BindingId },
    NeedMut { variable: BindingId, span: MirSpan },
    UnusedMut { variable: BindingId },
}

fn borrowck_diagnostics(
    def: DefWithBodyId,
    body: &Body,
    infer: &InferenceResult,
    borrowck_result: &BorrowckResult,
    diagnostics: &mut Vec<AnyDiagnostic>,
) {
    let make_diag = |diag| AnyDiagnostic::BorrowckDiagnostic { owner: def, diag };
    let mir_body = &borrowck_result.mir_body;
    diagnostics.extend(borrowck_result.moved_out_of_ref.iter().map(|moof| {
        make_diag(BorrowckDiagnostic::MovedOutOfRef { ty: moof.ty.clone(), span: moof.span })
    }));
    let mol = &borrowck_result.mutability_of_locals;
    for (binding_id, binding_data) in body.bindings.iter() {
        if binding_data.problems.is_some() {
            // We should report specific diagnostics for these problems, not `need-mut` and `unused-mut`.
            continue;
        }
        let Some(&local) = mir_body.binding_locals.get(binding_id) else {
            continue;
        };
        let mut need_mut = &mol[local];
        if body[binding_id].name == sym::self_ && need_mut == &mir::MutabilityReason::Unused {
            need_mut = &mir::MutabilityReason::Not;
        }
        let is_mut = body[binding_id].mode == BindingAnnotation::Mutable;

        match (need_mut, is_mut) {
            (mir::MutabilityReason::Unused, _) => {
                let should_ignore = body[binding_id].name.as_str().starts_with('_');
                if !should_ignore {
                    diagnostics.push(make_diag(BorrowckDiagnostic::UnusedVariable {
                        variable: binding_id,
                    }));
                }
            }
            (mir::MutabilityReason::Mut { .. }, true) | (mir::MutabilityReason::Not, false) => (),
            (mir::MutabilityReason::Mut { spans }, false) => {
                diagnostics.extend(spans.iter().map(|&span| {
                    make_diag(BorrowckDiagnostic::NeedMut { span, variable: binding_id })
                }));
            }
            (mir::MutabilityReason::Not, true) => {
                if !infer.mutated_bindings_in_closure.contains(&binding_id) {
                    let should_ignore = body[binding_id].name.as_str().starts_with('_');
                    if !should_ignore {
                        diagnostics.push(make_diag(
                            BorrowckDiagnostic::UnusedMut { variable: binding_id }.into(),
                        ));
                    }
                }
            }
        }
    }
}

fn incorrect_case(
    db: &dyn HirDatabase,
    diagnostics: &mut Vec<AnyDiagnostic>,
    callback: impl FnOnce(&mut IncorrectCaseValidator<'_>),
) {
    let mut incorrect_case = IncorrectCaseValidator::new(db);
    callback(&mut incorrect_case);
    diagnostics.extend(incorrect_case.finish().into_iter().map(AnyDiagnostic::IncorrectCase));
}
