//! IDE translation for diagnostics.
//!
//! This module should serve as a thin translation layer between [`crate::diagnostic_queries`]'s types
//! and syntax trees. It should never do any heavy work. This is left for the queries in [`crate::diagnostic_queries`].

use cfg::CfgExpr;
use either::Either;
use hir_def::{
    AdtId, DefWithBodyId, GenericDefId, HasModule, ImplId, SyntheticSyntax,
    expr_store::{ExprOrPatPtr, ExpressionStoreDiagnostics},
    hir::ExprOrPatId,
    item_tree::{AttrOwner, FieldParent, ItemTreeFieldId},
    nameres::diagnostics::DefDiagnosticKind,
    path::{ModPath, hir_segment_to_ast_segment},
    type_ref::TypesSourceMap,
};
use hir_expand::{
    ExpandResult, HirFileId, InFile, MacroCallKind, RenderedExpandError, ValueResult,
    attrs::collect_attrs, name::Name,
};
use hir_ty::{
    CastError, InferenceDiagnostic, InferenceTyDiagnosticSource, PathLoweringDiagnostic,
    TyLoweringDiagnostic, TyLoweringDiagnosticKind,
    db::HirDatabase,
    diagnostics::{BodyValidationDiagnostic, UnsafetyReason},
    mir::MirSpan,
};
use itertools::Itertools;
use span::MacroCallId;
use stdx::never;
use syntax::{
    AstNode, AstPtr, SyntaxError, SyntaxNodePtr, T, TextRange,
    ast::{self, HasAttrs, HasGenericArgs, HasGenericParams, HasName},
    match_ast,
};
use triomphe::Arc;

use crate::{
    AssocItem, Crate, Field, Function, Local, Trait, Type,
    diagnostic_queries::{
        AnyDiagnostic as QueriesAnyDiagnostic, BorrowckDiagnostic, TypesMapOwner,
    },
};

pub use hir_def::VariantId;
pub use hir_ty::{
    GenericArgsProhibitedReason,
    diagnostics::{CaseType, IncorrectCase},
};

macro_rules! diagnostics {
    ($($diag:ident,)*) => {
        #[derive(Debug)]
        pub enum AnyDiagnostic {$(
            $diag(Box<$diag>),
        )*}

        $(
            impl From<$diag> for AnyDiagnostic {
                fn from(d: $diag) -> AnyDiagnostic {
                    AnyDiagnostic::$diag(Box::new(d))
                }
            }
        )*
    };
}
// FIXME Accept something like the following in the macro call instead
// diagnostics![
// pub struct BreakOutsideOfLoop {
//     pub expr: InFile<AstPtr<ast::Expr>>,
//     pub is_break: bool,
//     pub bad_value_break: bool,
// }, ...
// or more concisely
// BreakOutsideOfLoop {
//     expr: InFile<AstPtr<ast::Expr>>,
//     is_break: bool,
//     bad_value_break: bool,
// }, ...
// ]

diagnostics![
    AwaitOutsideOfAsync,
    BreakOutsideOfLoop,
    CastToUnsized,
    ExpectedFunction,
    InactiveCode,
    IncoherentImpl,
    IncorrectCase,
    InvalidCast,
    InvalidDeriveTarget,
    MacroDefError,
    MacroError,
    MacroExpansionParseError,
    MalformedDerive,
    MismatchedArgCount,
    MismatchedTupleStructPatArgCount,
    MissingFields,
    MissingMatchArms,
    MissingUnsafe,
    MovedOutOfRef,
    NeedMut,
    NonExhaustiveLet,
    NoSuchField,
    PrivateAssocItem,
    PrivateField,
    RemoveTrailingReturn,
    RemoveUnnecessaryElse,
    ReplaceFilterMapNextWithFindMap,
    TraitImplIncorrectSafety,
    TraitImplMissingAssocItems,
    TraitImplOrphan,
    TraitImplRedundantAssocItems,
    TypedHole,
    TypeMismatch,
    UndeclaredLabel,
    UnimplementedBuiltinMacro,
    UnreachableLabel,
    UnresolvedAssocItem,
    UnresolvedExternCrate,
    UnresolvedField,
    UnresolvedImport,
    UnresolvedMacroCall,
    UnresolvedMethodCall,
    UnresolvedModule,
    UnresolvedIdent,
    UnusedMut,
    UnusedVariable,
    GenericArgsProhibited,
    ParenthesizedGenericArgsWithoutFnTrait,
    BadRtn,
];

#[derive(Debug)]
pub struct BreakOutsideOfLoop {
    pub expr: InFile<ExprOrPatPtr>,
    pub is_break: bool,
    pub bad_value_break: bool,
}

#[derive(Debug)]
pub struct TypedHole {
    pub expr: InFile<ExprOrPatPtr>,
    pub expected: Type,
}

#[derive(Debug)]
pub struct UnresolvedModule {
    pub decl: InFile<AstPtr<ast::Module>>,
    pub candidates: Box<[String]>,
}

#[derive(Debug)]
pub struct UnresolvedExternCrate {
    pub decl: InFile<AstPtr<ast::ExternCrate>>,
}

#[derive(Debug)]
pub struct UnresolvedImport {
    pub decl: InFile<AstPtr<ast::UseTree>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UnresolvedMacroCall {
    pub macro_call: InFile<SyntaxNodePtr>,
    pub precise_location: Option<TextRange>,
    pub path: ModPath,
    pub is_bang: bool,
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UnreachableLabel {
    pub node: InFile<AstPtr<ast::Lifetime>>,
    pub name: Name,
}

#[derive(Debug)]
pub struct AwaitOutsideOfAsync {
    pub node: InFile<AstPtr<ast::AwaitExpr>>,
    pub location: String,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UndeclaredLabel {
    pub node: InFile<AstPtr<ast::Lifetime>>,
    pub name: Name,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct InactiveCode {
    pub node: InFile<SyntaxNodePtr>,
    pub cfg: CfgExpr,
    pub krate: Crate,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MacroError {
    pub node: InFile<SyntaxNodePtr>,
    pub precise_location: Option<TextRange>,
    pub message: String,
    pub error: bool,
    pub kind: &'static str,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MacroExpansionParseError {
    pub node: InFile<SyntaxNodePtr>,
    pub precise_location: Option<TextRange>,
    pub errors: Arc<[SyntaxError]>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MacroDefError {
    pub node: InFile<AstPtr<ast::Macro>>,
    pub message: String,
    pub name: Option<TextRange>,
}

#[derive(Debug)]
pub struct UnimplementedBuiltinMacro {
    pub node: InFile<SyntaxNodePtr>,
}

#[derive(Debug)]
pub struct InvalidDeriveTarget {
    pub node: InFile<SyntaxNodePtr>,
}

#[derive(Debug)]
pub struct MalformedDerive {
    pub node: InFile<SyntaxNodePtr>,
}

#[derive(Debug)]
pub struct NoSuchField {
    pub field: InFile<AstPtr<Either<ast::RecordExprField, ast::RecordPatField>>>,
    pub private: bool,
    pub variant: VariantId,
}

#[derive(Debug)]
pub struct PrivateAssocItem {
    pub expr_or_pat: InFile<ExprOrPatPtr>,
    pub item: AssocItem,
}

#[derive(Debug)]
pub struct MismatchedTupleStructPatArgCount {
    pub expr_or_pat: InFile<ExprOrPatPtr>,
    pub expected: usize,
    pub found: usize,
}

#[derive(Debug)]
pub struct ExpectedFunction {
    pub call: InFile<ExprOrPatPtr>,
    pub found: Type,
}

#[derive(Debug)]
pub struct UnresolvedField {
    pub expr: InFile<ExprOrPatPtr>,
    pub receiver: Type,
    pub name: Name,
    pub method_with_same_name_exists: bool,
}

#[derive(Debug)]
pub struct UnresolvedMethodCall {
    pub expr: InFile<ExprOrPatPtr>,
    pub receiver: Type,
    pub name: Name,
    pub field_with_same_name: Option<Type>,
    pub assoc_func_with_same_name: Option<Function>,
}

#[derive(Debug)]
pub struct UnresolvedAssocItem {
    pub expr_or_pat: InFile<ExprOrPatPtr>,
}

#[derive(Debug)]
pub struct UnresolvedIdent {
    pub node: InFile<(ExprOrPatPtr, Option<TextRange>)>,
}

#[derive(Debug)]
pub struct PrivateField {
    pub expr: InFile<ExprOrPatPtr>,
    pub field: Field,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsafeLint {
    HardError,
    UnsafeOpInUnsafeFn,
    DeprecatedSafe2024,
}

#[derive(Debug)]
pub struct MissingUnsafe {
    pub node: InFile<ExprOrPatPtr>,
    pub lint: UnsafeLint,
    pub reason: UnsafetyReason,
}

#[derive(Debug)]
pub struct MissingFields {
    pub file: HirFileId,
    pub field_list_parent: AstPtr<Either<ast::RecordExpr, ast::RecordPat>>,
    pub field_list_parent_path: Option<AstPtr<ast::Path>>,
    pub missed_fields: Vec<Name>,
}

#[derive(Debug)]
pub struct ReplaceFilterMapNextWithFindMap {
    pub file: HirFileId,
    /// This expression is the whole method chain up to and including `.filter_map(..).next()`.
    pub next_expr: AstPtr<ast::Expr>,
}

#[derive(Debug)]
pub struct MismatchedArgCount {
    pub call_expr: InFile<ExprOrPatPtr>,
    pub expected: usize,
    pub found: usize,
}

#[derive(Debug)]
pub struct MissingMatchArms {
    pub scrutinee_expr: InFile<AstPtr<ast::Expr>>,
    pub uncovered_patterns: String,
}

#[derive(Debug)]
pub struct NonExhaustiveLet {
    pub pat: InFile<AstPtr<ast::Pat>>,
    pub uncovered_patterns: String,
}

#[derive(Debug)]
pub struct TypeMismatch {
    pub expr_or_pat: InFile<ExprOrPatPtr>,
    pub expected: Type,
    pub actual: Type,
}

#[derive(Debug)]
pub struct NeedMut {
    pub local: Local,
    pub span: InFile<SyntaxNodePtr>,
}

#[derive(Debug)]
pub struct UnusedMut {
    pub local: Local,
}

#[derive(Debug)]
pub struct UnusedVariable {
    pub local: Local,
}

#[derive(Debug)]
pub struct MovedOutOfRef {
    pub ty: Type,
    pub span: InFile<SyntaxNodePtr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IncoherentImpl {
    pub impl_: InFile<AstPtr<ast::Impl>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitImplOrphan {
    pub impl_: InFile<AstPtr<ast::Impl>>,
}

// FIXME: Split this off into the corresponding 4 rustc errors
#[derive(Debug, PartialEq, Eq)]
pub struct TraitImplIncorrectSafety {
    pub impl_: InFile<AstPtr<ast::Impl>>,
    pub should_be_safe: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitImplMissingAssocItems {
    pub impl_: InFile<AstPtr<ast::Impl>>,
    pub missing: Vec<(Name, AssocItem)>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitImplRedundantAssocItems {
    pub trait_: Trait,
    pub impl_: InFile<AstPtr<ast::Impl>>,
    pub assoc_item: (Name, AssocItem),
}

#[derive(Debug)]
pub struct RemoveTrailingReturn {
    pub return_expr: InFile<AstPtr<ast::ReturnExpr>>,
}

#[derive(Debug)]
pub struct RemoveUnnecessaryElse {
    pub if_expr: InFile<AstPtr<ast::IfExpr>>,
}

#[derive(Debug)]
pub struct CastToUnsized {
    pub expr: InFile<ExprOrPatPtr>,
    pub cast_ty: Type,
}

#[derive(Debug)]
pub struct InvalidCast {
    pub expr: InFile<ExprOrPatPtr>,
    pub error: CastError,
    pub expr_ty: Type,
    pub cast_ty: Type,
}

#[derive(Debug)]
pub struct GenericArgsProhibited {
    pub args: InFile<AstPtr<Either<ast::GenericArgList, ast::ParenthesizedArgList>>>,
    pub reason: GenericArgsProhibitedReason,
}

#[derive(Debug)]
pub struct ParenthesizedGenericArgsWithoutFnTrait {
    pub args: InFile<AstPtr<ast::ParenthesizedArgList>>,
}

#[derive(Debug)]
pub struct BadRtn {
    pub rtn: InFile<AstPtr<ast::ReturnTypeSyntax>>,
}

impl AnyDiagnostic {
    pub(crate) fn body_validation_diagnostic(
        db: &dyn HirDatabase,
        diagnostic: &BodyValidationDiagnostic,
        source_map: &hir_def::expr_store::BodySourceMap,
    ) -> Option<AnyDiagnostic> {
        match diagnostic {
            BodyValidationDiagnostic::RecordMissingFields { record, variant, missed_fields } => {
                let variant_data = variant.variant_data(db.upcast());
                let missed_fields = missed_fields
                    .iter()
                    .map(|&idx| variant_data.fields()[idx].name.clone())
                    .collect();

                let record = match *record {
                    Either::Left(record_expr) => source_map.expr_syntax(record_expr).ok()?,
                    Either::Right(record_pat) => source_map.pat_syntax(record_pat).ok()?,
                };
                let file = record.file_id;
                let root = record.file_syntax(db.upcast());
                match record.value.to_node(&root) {
                    Either::Left(ast::Expr::RecordExpr(record_expr)) => {
                        if record_expr.record_expr_field_list().is_some() {
                            let field_list_parent_path =
                                record_expr.path().map(|path| AstPtr::new(&path));
                            return Some(
                                MissingFields {
                                    file,
                                    field_list_parent: AstPtr::new(&Either::Left(record_expr)),
                                    field_list_parent_path,
                                    missed_fields,
                                }
                                .into(),
                            );
                        }
                    }
                    Either::Right(ast::Pat::RecordPat(record_pat)) => {
                        if record_pat.record_pat_field_list().is_some() {
                            let field_list_parent_path =
                                record_pat.path().map(|path| AstPtr::new(&path));
                            return Some(
                                MissingFields {
                                    file,
                                    field_list_parent: AstPtr::new(&Either::Right(record_pat)),
                                    field_list_parent_path,
                                    missed_fields,
                                }
                                .into(),
                            );
                        }
                    }
                    _ => {}
                }
            }
            BodyValidationDiagnostic::ReplaceFilterMapNextWithFindMap { method_call_expr } => {
                if let Ok(next_source_ptr) = source_map.expr_syntax(*method_call_expr) {
                    return Some(
                        ReplaceFilterMapNextWithFindMap {
                            file: next_source_ptr.file_id,
                            next_expr: next_source_ptr.value.cast()?,
                        }
                        .into(),
                    );
                }
            }
            BodyValidationDiagnostic::MissingMatchArms { match_expr, uncovered_patterns } => {
                match source_map.expr_syntax(*match_expr) {
                    Ok(source_ptr) => {
                        let root = source_ptr.file_syntax(db.upcast());
                        if let Either::Left(ast::Expr::MatchExpr(match_expr)) =
                            &source_ptr.value.to_node(&root)
                        {
                            match match_expr.expr() {
                                Some(scrut_expr) if match_expr.match_arm_list().is_some() => {
                                    return Some(
                                        MissingMatchArms {
                                            scrutinee_expr: InFile::new(
                                                source_ptr.file_id,
                                                AstPtr::new(&scrut_expr),
                                            ),
                                            uncovered_patterns: uncovered_patterns.clone(),
                                        }
                                        .into(),
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                    Err(SyntheticSyntax) => (),
                }
            }
            BodyValidationDiagnostic::NonExhaustiveLet { pat, uncovered_patterns } => {
                match source_map.pat_syntax(*pat) {
                    Ok(source_ptr) => {
                        if let Some(ast_pat) = source_ptr.value.cast::<ast::Pat>() {
                            return Some(
                                NonExhaustiveLet {
                                    pat: InFile::new(source_ptr.file_id, ast_pat),
                                    uncovered_patterns: uncovered_patterns.clone(),
                                }
                                .into(),
                            );
                        }
                    }
                    Err(SyntheticSyntax) => {}
                }
            }
            BodyValidationDiagnostic::RemoveTrailingReturn { return_expr } => {
                if let Ok(source_ptr) = source_map.expr_syntax(*return_expr) {
                    // Filters out desugared return expressions (e.g. desugared try operators).
                    if let Some(ptr) = source_ptr.value.cast::<ast::ReturnExpr>() {
                        return Some(
                            RemoveTrailingReturn {
                                return_expr: InFile::new(source_ptr.file_id, ptr),
                            }
                            .into(),
                        );
                    }
                }
            }
            BodyValidationDiagnostic::RemoveUnnecessaryElse { if_expr } => {
                if let Ok(source_ptr) = source_map.expr_syntax(*if_expr) {
                    if let Some(ptr) = source_ptr.value.cast::<ast::IfExpr>() {
                        return Some(
                            RemoveUnnecessaryElse { if_expr: InFile::new(source_ptr.file_id, ptr) }
                                .into(),
                        );
                    }
                }
            }
        }
        None
    }

    pub(crate) fn inference_diagnostic(
        db: &dyn HirDatabase,
        def: DefWithBodyId,
        d: &InferenceDiagnostic,
        outer_types_source_map: &TypesSourceMap,
        source_map: &hir_def::expr_store::BodySourceMap,
    ) -> Option<AnyDiagnostic> {
        let expr_syntax = |expr| {
            source_map.expr_syntax(expr).inspect_err(|_| stdx::never!("synthetic syntax")).ok()
        };
        let pat_syntax =
            |pat| source_map.pat_syntax(pat).inspect_err(|_| stdx::never!("synthetic syntax")).ok();
        let expr_or_pat_syntax = |id| match id {
            ExprOrPatId::ExprId(expr) => expr_syntax(expr),
            ExprOrPatId::PatId(pat) => pat_syntax(pat),
        };
        Some(match d {
            &InferenceDiagnostic::NoSuchField { field: expr, private, variant } => {
                let expr_or_pat = match expr {
                    ExprOrPatId::ExprId(expr) => {
                        source_map.field_syntax(expr).map(AstPtr::wrap_left)
                    }
                    ExprOrPatId::PatId(pat) => source_map.pat_field_syntax(pat),
                };
                NoSuchField { field: expr_or_pat, private, variant }.into()
            }
            &InferenceDiagnostic::MismatchedArgCount { call_expr, expected, found } => {
                MismatchedArgCount { call_expr: expr_syntax(call_expr)?, expected, found }.into()
            }
            &InferenceDiagnostic::PrivateField { expr, field } => {
                let expr = expr_syntax(expr)?;
                let field = field.into();
                PrivateField { expr, field }.into()
            }
            &InferenceDiagnostic::PrivateAssocItem { id, item } => {
                let expr_or_pat = expr_or_pat_syntax(id)?;
                let item = item.into();
                PrivateAssocItem { expr_or_pat, item }.into()
            }
            InferenceDiagnostic::ExpectedFunction { call_expr, found } => {
                let call_expr = expr_syntax(*call_expr)?;
                ExpectedFunction { call: call_expr, found: Type::new(db, def, found.clone()) }
                    .into()
            }
            InferenceDiagnostic::UnresolvedField {
                expr,
                receiver,
                name,
                method_with_same_name_exists,
            } => {
                let expr = expr_syntax(*expr)?;
                UnresolvedField {
                    expr,
                    name: name.clone(),
                    receiver: Type::new(db, def, receiver.clone()),
                    method_with_same_name_exists: *method_with_same_name_exists,
                }
                .into()
            }
            InferenceDiagnostic::UnresolvedMethodCall {
                expr,
                receiver,
                name,
                field_with_same_name,
                assoc_func_with_same_name,
            } => {
                let expr = expr_syntax(*expr)?;
                UnresolvedMethodCall {
                    expr,
                    name: name.clone(),
                    receiver: Type::new(db, def, receiver.clone()),
                    field_with_same_name: field_with_same_name
                        .clone()
                        .map(|ty| Type::new(db, def, ty)),
                    assoc_func_with_same_name: assoc_func_with_same_name.map(Into::into),
                }
                .into()
            }
            &InferenceDiagnostic::UnresolvedAssocItem { id } => {
                let expr_or_pat = expr_or_pat_syntax(id)?;
                UnresolvedAssocItem { expr_or_pat }.into()
            }
            &InferenceDiagnostic::UnresolvedIdent { id } => {
                let node = match id {
                    ExprOrPatId::ExprId(id) => match source_map.expr_syntax(id) {
                        Ok(syntax) => syntax.map(|it| (it, None)),
                        Err(SyntheticSyntax) => source_map
                            .format_args_implicit_capture(id)?
                            .map(|(node, range)| (node.wrap_left(), Some(range))),
                    },
                    ExprOrPatId::PatId(id) => pat_syntax(id)?.map(|it| (it, None)),
                };
                UnresolvedIdent { node }.into()
            }
            &InferenceDiagnostic::BreakOutsideOfLoop { expr, is_break, bad_value_break } => {
                let expr = expr_syntax(expr)?;
                BreakOutsideOfLoop { expr, is_break, bad_value_break }.into()
            }
            InferenceDiagnostic::TypedHole { expr, expected } => {
                let expr = expr_syntax(*expr)?;
                TypedHole { expr, expected: Type::new(db, def, expected.clone()) }.into()
            }
            &InferenceDiagnostic::MismatchedTupleStructPatArgCount { pat, expected, found } => {
                let expr_or_pat = match pat {
                    ExprOrPatId::ExprId(expr) => expr_syntax(expr)?,
                    ExprOrPatId::PatId(pat) => {
                        let InFile { file_id, value } = pat_syntax(pat)?;

                        // cast from Either<Pat, SelfParam> -> Either<_, Pat>
                        let ptr = AstPtr::try_from_raw(value.syntax_node_ptr())?;
                        InFile { file_id, value: ptr }
                    }
                };
                MismatchedTupleStructPatArgCount { expr_or_pat, expected, found }.into()
            }
            InferenceDiagnostic::CastToUnsized { expr, cast_ty } => {
                let expr = expr_syntax(*expr)?;
                CastToUnsized { expr, cast_ty: Type::new(db, def, cast_ty.clone()) }.into()
            }
            InferenceDiagnostic::InvalidCast { expr, error, expr_ty, cast_ty } => {
                let expr = expr_syntax(*expr)?;
                let expr_ty = Type::new(db, def, expr_ty.clone());
                let cast_ty = Type::new(db, def, cast_ty.clone());
                InvalidCast { expr, error: *error, expr_ty, cast_ty }.into()
            }
            InferenceDiagnostic::TyDiagnostic { source, diag } => {
                let source_map = match source {
                    InferenceTyDiagnosticSource::Body => &source_map.types,
                    InferenceTyDiagnosticSource::Signature => outer_types_source_map,
                };
                Self::ty_diagnostic(diag, source_map, db)?
            }
            InferenceDiagnostic::PathDiagnostic { node, diag } => {
                let source = expr_or_pat_syntax(*node)?;
                let syntax = source.value.to_node(&db.parse_or_expand(source.file_id));
                let path = match_ast! {
                    match (syntax.syntax()) {
                        ast::RecordExpr(it) => it.path()?,
                        ast::RecordPat(it) => it.path()?,
                        ast::TupleStructPat(it) => it.path()?,
                        ast::PathExpr(it) => it.path()?,
                        ast::PathPat(it) => it.path()?,
                        _ => return None,
                    }
                };
                Self::path_diagnostic(diag, source.with_value(path))?
            }
        })
    }

    fn path_diagnostic(
        diag: &PathLoweringDiagnostic,
        path: InFile<ast::Path>,
    ) -> Option<AnyDiagnostic> {
        Some(match *diag {
            PathLoweringDiagnostic::GenericArgsProhibited { segment, reason } => {
                let segment = hir_segment_to_ast_segment(&path.value, segment)?;

                if let Some(rtn) = segment.return_type_syntax() {
                    // RTN errors are emitted as `GenericArgsProhibited` or `ParenthesizedGenericArgsWithoutFnTrait`.
                    return Some(BadRtn { rtn: path.with_value(AstPtr::new(&rtn)) }.into());
                }

                let args = if let Some(generics) = segment.generic_arg_list() {
                    AstPtr::new(&generics).wrap_left()
                } else {
                    AstPtr::new(&segment.parenthesized_arg_list()?).wrap_right()
                };
                let args = path.with_value(args);
                GenericArgsProhibited { args, reason }.into()
            }
            PathLoweringDiagnostic::ParenthesizedGenericArgsWithoutFnTrait { segment } => {
                let segment = hir_segment_to_ast_segment(&path.value, segment)?;

                if let Some(rtn) = segment.return_type_syntax() {
                    // RTN errors are emitted as `GenericArgsProhibited` or `ParenthesizedGenericArgsWithoutFnTrait`.
                    return Some(BadRtn { rtn: path.with_value(AstPtr::new(&rtn)) }.into());
                }

                let args = AstPtr::new(&segment.parenthesized_arg_list()?);
                let args = path.with_value(args);
                ParenthesizedGenericArgsWithoutFnTrait { args }.into()
            }
        })
    }

    pub(crate) fn ty_diagnostic(
        diag: &TyLoweringDiagnostic,
        source_map: &TypesSourceMap,
        db: &dyn HirDatabase,
    ) -> Option<AnyDiagnostic> {
        let source = match diag.source {
            Either::Left(type_ref_id) => {
                let Ok(source) = source_map.type_syntax(type_ref_id) else {
                    stdx::never!("error on synthetic type syntax");
                    return None;
                };
                source
            }
            Either::Right(source) => source,
        };
        let syntax = || source.value.to_node(&db.parse_or_expand(source.file_id));
        Some(match &diag.kind {
            TyLoweringDiagnosticKind::PathDiagnostic(diag) => {
                let ast::Type::PathType(syntax) = syntax() else { return None };
                Self::path_diagnostic(diag, source.with_value(syntax.path()?))?
            }
        })
    }
}

fn emit_def_diagnostic(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    krate: base_db::Crate,
    diag: &DefDiagnosticKind,
) {
    match diag {
        DefDiagnosticKind::UnresolvedModule { ast: declaration, candidates } => {
            let decl = declaration.to_ptr(db.upcast());
            acc.push(
                UnresolvedModule {
                    decl: InFile::new(declaration.file_id, decl),
                    candidates: candidates.clone(),
                }
                .into(),
            )
        }
        DefDiagnosticKind::UnresolvedExternCrate { ast } => {
            let item = ast.to_ptr(db.upcast());
            acc.push(UnresolvedExternCrate { decl: InFile::new(ast.file_id, item) }.into());
        }

        DefDiagnosticKind::MacroError { ast, path, err } => {
            let item = ast.to_ptr(db.upcast());
            let RenderedExpandError { message, error, kind } = err.render_to_string(db.upcast());
            let edition = krate.data(db).edition;
            acc.push(
                MacroError {
                    node: InFile::new(ast.file_id, item.syntax_node_ptr()),
                    precise_location: None,
                    message: format!("{}: {message}", path.display(db.upcast(), edition)),
                    error,
                    kind,
                }
                .into(),
            )
        }
        DefDiagnosticKind::UnresolvedImport { id, index } => {
            let file_id = id.file_id();
            let item_tree = id.item_tree(db.upcast());
            let import = &item_tree[id.value];

            let use_tree = import.use_tree_to_ast(db.upcast(), file_id, *index);
            acc.push(
                UnresolvedImport { decl: InFile::new(file_id, AstPtr::new(&use_tree)) }.into(),
            );
        }

        DefDiagnosticKind::UnconfiguredCode { tree, item, cfg } => {
            let item_tree = tree.item_tree(db.upcast());
            let ast_id_map = db.ast_id_map(tree.file_id());
            // FIXME: This parses... We could probably store relative ranges for the children things
            // here in the item tree?
            (|| {
                let process_field_list =
                    |field_list: Option<_>, idx: ItemTreeFieldId| match field_list? {
                        ast::FieldList::RecordFieldList(it) => Some(SyntaxNodePtr::new(
                            it.fields().nth(idx.into_raw().into_u32() as usize)?.syntax(),
                        )),
                        ast::FieldList::TupleFieldList(it) => Some(SyntaxNodePtr::new(
                            it.fields().nth(idx.into_raw().into_u32() as usize)?.syntax(),
                        )),
                    };
                let ptr = match *item {
                    AttrOwner::ModItem(it) => {
                        ast_id_map.get(it.ast_id(&item_tree)).syntax_node_ptr()
                    }
                    AttrOwner::TopLevel => ast_id_map.root(),
                    AttrOwner::Variant(it) => {
                        ast_id_map.get(item_tree[it].ast_id).syntax_node_ptr()
                    }
                    AttrOwner::Field(FieldParent::EnumVariant(parent), idx) => process_field_list(
                        ast_id_map
                            .get(item_tree[parent].ast_id)
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .field_list(),
                        idx,
                    )?,
                    AttrOwner::Field(FieldParent::Struct(parent), idx) => process_field_list(
                        ast_id_map
                            .get(item_tree[parent.index()].ast_id)
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .field_list(),
                        idx,
                    )?,
                    AttrOwner::Field(FieldParent::Union(parent), idx) => SyntaxNodePtr::new(
                        ast_id_map
                            .get(item_tree[parent.index()].ast_id)
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .record_field_list()?
                            .fields()
                            .nth(idx.into_raw().into_u32() as usize)?
                            .syntax(),
                    ),
                    AttrOwner::Param(parent, idx) => SyntaxNodePtr::new(
                        ast_id_map
                            .get(item_tree[parent.index()].ast_id)
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .param_list()?
                            .params()
                            .nth(idx.into_raw().into_u32() as usize)?
                            .syntax(),
                    ),
                    AttrOwner::TypeOrConstParamData(parent, idx) => SyntaxNodePtr::new(
                        ast_id_map
                            .get(parent.ast_id(&item_tree))
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .generic_param_list()?
                            .type_or_const_params()
                            .nth(idx.into_raw().into_u32() as usize)?
                            .syntax(),
                    ),
                    AttrOwner::LifetimeParamData(parent, idx) => SyntaxNodePtr::new(
                        ast_id_map
                            .get(parent.ast_id(&item_tree))
                            .to_node(&db.parse_or_expand(tree.file_id()))
                            .generic_param_list()?
                            .lifetime_params()
                            .nth(idx.into_raw().into_u32() as usize)?
                            .syntax(),
                    ),
                };
                acc.push(
                    InactiveCode {
                        node: InFile::new(tree.file_id(), ptr),
                        cfg: cfg.clone(),
                        krate: krate.into(),
                    }
                    .into(),
                );
                Some(())
            })();
        }
        DefDiagnosticKind::UnresolvedMacroCall { ast, path } => {
            let (node, precise_location) = precise_macro_call_location(ast, db);
            acc.push(
                UnresolvedMacroCall {
                    macro_call: node,
                    precise_location,
                    path: path.clone(),
                    is_bang: matches!(ast, MacroCallKind::FnLike { .. }),
                }
                .into(),
            );
        }
        DefDiagnosticKind::UnimplementedBuiltinMacro { ast } => {
            let node = ast.to_node(db.upcast());
            // Must have a name, otherwise we wouldn't emit it.
            let name = node.name().expect("unimplemented builtin macro with no name");
            acc.push(
                UnimplementedBuiltinMacro {
                    node: ast.with_value(SyntaxNodePtr::from(AstPtr::new(&name))),
                }
                .into(),
            );
        }
        DefDiagnosticKind::InvalidDeriveTarget { ast, id } => {
            let node = ast.to_node(db.upcast());
            let derive = node.attrs().nth(*id);
            match derive {
                Some(derive) => {
                    acc.push(
                        InvalidDeriveTarget {
                            node: ast.with_value(SyntaxNodePtr::from(AstPtr::new(&derive))),
                        }
                        .into(),
                    );
                }
                None => stdx::never!("derive diagnostic on item without derive attribute"),
            }
        }
        DefDiagnosticKind::MalformedDerive { ast, id } => {
            let node = ast.to_node(db.upcast());
            let derive = node.attrs().nth(*id);
            match derive {
                Some(derive) => {
                    acc.push(
                        MalformedDerive {
                            node: ast.with_value(SyntaxNodePtr::from(AstPtr::new(&derive))),
                        }
                        .into(),
                    );
                }
                None => stdx::never!("derive diagnostic on item without derive attribute"),
            }
        }
        DefDiagnosticKind::MacroDefError { ast, message } => {
            let node = ast.to_node(db.upcast());
            acc.push(
                MacroDefError {
                    node: InFile::new(ast.file_id, AstPtr::new(&node)),
                    name: node.name().map(|it| it.syntax().text_range()),
                    message: message.clone(),
                }
                .into(),
            );
        }
    }
}

fn precise_macro_call_location(
    ast: &MacroCallKind,
    db: &dyn HirDatabase,
) -> (InFile<SyntaxNodePtr>, Option<TextRange>) {
    // FIXME: maybe we actually want slightly different ranges for the different macro diagnostics
    // - e.g. the full attribute for macro errors, but only the name for name resolution
    match ast {
        MacroCallKind::FnLike { ast_id, .. } => {
            let node = ast_id.to_node(db.upcast());
            (
                ast_id.with_value(SyntaxNodePtr::from(AstPtr::new(&node))),
                node.path()
                    .and_then(|it| it.segment())
                    .and_then(|it| it.name_ref())
                    .map(|it| it.syntax().text_range()),
            )
        }
        MacroCallKind::Derive { ast_id, derive_attr_index, derive_index, .. } => {
            let node = ast_id.to_node(db.upcast());
            // Compute the precise location of the macro name's token in the derive
            // list.
            let token = (|| {
                let derive_attr = collect_attrs(&node)
                    .nth(derive_attr_index.ast_index())
                    .and_then(|x| Either::left(x.1))?;
                let token_tree = derive_attr.meta()?.token_tree()?;
                let chunk_by = token_tree
                    .syntax()
                    .children_with_tokens()
                    .filter_map(|elem| match elem {
                        syntax::NodeOrToken::Token(tok) => Some(tok),
                        _ => None,
                    })
                    .chunk_by(|t| t.kind() == T![,]);
                let (_, mut group) = chunk_by
                    .into_iter()
                    .filter(|&(comma, _)| !comma)
                    .nth(*derive_index as usize)?;
                group.find(|t| t.kind() == T![ident])
            })();
            (
                ast_id.with_value(SyntaxNodePtr::from(AstPtr::new(&node))),
                token.as_ref().map(|tok| tok.text_range()),
            )
        }
        MacroCallKind::Attr { ast_id, invoc_attr_index, .. } => {
            let node = ast_id.to_node(db.upcast());
            let attr = collect_attrs(&node)
                .nth(invoc_attr_index.ast_index())
                .and_then(|x| Either::left(x.1))
                .unwrap_or_else(|| {
                    panic!("cannot find attribute #{}", invoc_attr_index.ast_index())
                });

            (
                ast_id.with_value(SyntaxNodePtr::from(AstPtr::new(&attr))),
                Some(attr.syntax().text_range()),
            )
        }
    }
}

fn macro_call_diagnostics(
    db: &dyn HirDatabase,
    macro_call_id: MacroCallId,
    errors: &ExpandResult<Arc<[SyntaxError]>>,
    acc: &mut Vec<AnyDiagnostic>,
) {
    let ValueResult { value: parse_errors, err } = errors;
    if let Some(err) = err {
        let loc = db.lookup_intern_macro_call(macro_call_id);
        let file_id = loc.kind.file_id();
        let node =
            InFile::new(file_id, db.ast_id_map(file_id).get_erased(loc.kind.erased_ast_id()));
        let RenderedExpandError { message, error, kind } = err.render_to_string(db.upcast());
        let precise_location = if err.span().anchor.file_id == file_id {
            Some(
                err.span().range
                    + db.ast_id_map(err.span().anchor.file_id.into())
                        .get_erased(err.span().anchor.ast_id)
                        .text_range()
                        .start(),
            )
        } else {
            None
        };
        acc.push(MacroError { node, precise_location, message, error, kind }.into());
    }

    if !parse_errors.is_empty() {
        let loc = db.lookup_intern_macro_call(macro_call_id);
        let (node, precise_location) = precise_macro_call_location(&loc.kind, db);
        acc.push(
            MacroExpansionParseError { node, precise_location, errors: parse_errors.clone() }
                .into(),
        )
    }
}

fn handle_ty_lowering_diagnostics(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: &TypesMapOwner,
    diags: &[TyLoweringDiagnostic],
) {
    let item_tree_source_maps;
    let generics_source_map;
    let source_map = match *owner {
        TypesMapOwner::Generics(id) => match db.generic_params_with_source_map(id).1 {
            Some(it) => {
                generics_source_map = it;
                &generics_source_map
            }
            None => match id {
                GenericDefId::FunctionId(id) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.function(tree_id.value).generics()
                }
                GenericDefId::ImplId(id) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.impl_(tree_id.value).generics()
                }
                GenericDefId::TraitAliasId(id) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.trait_alias_generic(tree_id.value)
                }
                GenericDefId::TraitId(id) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.trait_generic(tree_id.value)
                }
                GenericDefId::TypeAliasId(id) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.type_alias(tree_id.value).generics()
                }
                GenericDefId::AdtId(AdtId::StructId(id)) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.strukt(tree_id.value).generics()
                }
                GenericDefId::AdtId(AdtId::UnionId(id)) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.union(tree_id.value).generics()
                }
                GenericDefId::AdtId(AdtId::EnumId(id)) => {
                    let tree_id = id.loc(db).id;
                    item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
                    item_tree_source_maps.enum_generic(tree_id.value)
                }
                GenericDefId::StaticId(_) | GenericDefId::ConstId(_) => {
                    never!("statics and consts cannot have generic diagnostics");
                    return;
                }
            },
        },
        TypesMapOwner::Fields(VariantId::StructId(id)) => {
            let tree_id = id.loc(db).id;
            item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.strukt(tree_id.value).item()
        }
        TypesMapOwner::Fields(VariantId::UnionId(id)) => {
            let tree_id = id.loc(db).id;
            item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.union(tree_id.value).item()
        }
        TypesMapOwner::Fields(VariantId::EnumVariantId(id)) => {
            let tree_id = id.loc(db).id;
            item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.variant(tree_id.value)
        }
        TypesMapOwner::TypeAliasType(id) => {
            let tree_id = id.loc(db).id;
            item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.type_alias(tree_id.value).item()
        }
        TypesMapOwner::Impl(id) => {
            let tree_id = id.loc(db).id;
            item_tree_source_maps = tree_id.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.impl_(tree_id.value).item()
        }
    };
    for diag in diags {
        if let Some(diag) = AnyDiagnostic::ty_diagnostic(diag, source_map, db) {
            acc.push(diag);
        }
    }
}

fn handle_body_lowering_diagnostics(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: DefWithBodyId,
) {
    let (_, source_map) = db.body_with_source_map(owner);
    let krate = owner.krate(db.upcast());

    for diag in source_map.diagnostics() {
        acc.push(match diag {
            ExpressionStoreDiagnostics::InactiveCode { node, cfg } => {
                InactiveCode { node: *node, cfg: cfg.clone(), krate: krate.into() }.into()
            }
            ExpressionStoreDiagnostics::MacroError { node, err } => {
                let RenderedExpandError { message, error, kind } =
                    err.render_to_string(db.upcast());

                let precise_location = if err.span().anchor.file_id == node.file_id {
                    Some(
                        err.span().range
                            + db.ast_id_map(err.span().anchor.file_id.into())
                                .get_erased(err.span().anchor.ast_id)
                                .text_range()
                                .start(),
                    )
                } else {
                    None
                };
                MacroError {
                    node: (node).map(|it| it.into()),
                    precise_location,
                    message,
                    error,
                    kind,
                }
                .into()
            }
            ExpressionStoreDiagnostics::UnresolvedMacroCall { node, path } => UnresolvedMacroCall {
                macro_call: (*node).map(|ast_ptr| ast_ptr.into()),
                precise_location: None,
                path: path.clone(),
                is_bang: true,
            }
            .into(),
            ExpressionStoreDiagnostics::AwaitOutsideOfAsync { node, location } => {
                AwaitOutsideOfAsync { node: *node, location: location.clone() }.into()
            }
            ExpressionStoreDiagnostics::UnreachableLabel { node, name } => {
                UnreachableLabel { node: *node, name: name.clone() }.into()
            }
            ExpressionStoreDiagnostics::UndeclaredLabel { node, name } => {
                UndeclaredLabel { node: *node, name: name.clone() }.into()
            }
        });
    }
}

fn handle_inference_diagnostic(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: DefWithBodyId,
    diags: &[InferenceDiagnostic],
) {
    let item_tree_source_maps;
    let outer_types_source_map = match owner {
        DefWithBodyId::FunctionId(function) => {
            let function = function.loc(db).id;
            item_tree_source_maps = function.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.function(function.value).item()
        }
        DefWithBodyId::StaticId(statik) => {
            let statik = statik.loc(db).id;
            item_tree_source_maps = statik.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.statik(statik.value)
        }
        DefWithBodyId::ConstId(konst) => {
            let konst = konst.loc(db).id;
            item_tree_source_maps = konst.item_tree_with_source_map(db.upcast()).1;
            item_tree_source_maps.konst(konst.value)
        }
        DefWithBodyId::VariantId(_) | DefWithBodyId::InTypeConstId(_) => &TypesSourceMap::EMPTY,
    };
    let (_, source_map) = db.body_with_source_map(owner);

    acc.extend(diags.iter().filter_map(|diag| {
        AnyDiagnostic::inference_diagnostic(db, owner, diag, outer_types_source_map, &source_map)
    }));
}

fn handle_type_mismatch(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: DefWithBodyId,
    node: ExprOrPatId,
    mismatch: &hir_ty::TypeMismatch,
) {
    let (_, source_map) = db.body_with_source_map(owner);
    let expr_or_pat = match node {
        ExprOrPatId::ExprId(expr) => source_map.expr_syntax(expr).map(Either::Left),
        ExprOrPatId::PatId(pat) => source_map.pat_syntax(pat).map(Either::Right),
    };
    let expr_or_pat = match expr_or_pat {
        Ok(Either::Left(expr)) => expr,
        Ok(Either::Right(InFile { file_id, value: pat })) => {
            // cast from Either<Pat, SelfParam> -> Either<_, Pat>
            let Some(ptr) = AstPtr::try_from_raw(pat.syntax_node_ptr()) else {
                return;
            };
            InFile { file_id, value: ptr }
        }
        Err(SyntheticSyntax) => return,
    };

    acc.push(
        TypeMismatch {
            expr_or_pat,
            expected: Type::new(db, owner, mismatch.expected.clone()),
            actual: Type::new(db, owner, mismatch.actual.clone()),
        }
        .into(),
    );
}

fn handle_body_validation_diagnostics(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: DefWithBodyId,
    diags: &[crate::diagnostic_queries::BodyValidationDiagnostic],
) {
    let (_, source_map) = db.body_with_source_map(owner);

    for diag in diags {
        match diag {
            crate::diagnostic_queries::BodyValidationDiagnostic::Validation(diag) => {
                acc.extend(AnyDiagnostic::body_validation_diagnostic(db, diag, &source_map))
            }
            crate::diagnostic_queries::BodyValidationDiagnostic::UnsafeCheck(diag) => {
                for &(node, reason) in &diag.unsafe_exprs {
                    match source_map.expr_or_pat_syntax(node) {
                        Ok(node) => acc.push(
                            MissingUnsafe {
                                node,
                                lint: if diag.fn_is_unsafe {
                                    UnsafeLint::UnsafeOpInUnsafeFn
                                } else {
                                    UnsafeLint::HardError
                                },
                                reason,
                            }
                            .into(),
                        ),
                        Err(SyntheticSyntax) => {
                            // FIXME: Here and elsewhere in this file, the `expr` was
                            // desugared, report or assert that this doesn't happen.
                        }
                    }
                }
                for &node in &diag.deprecated_safe_calls {
                    match source_map.expr_syntax(node) {
                        Ok(node) => acc.push(
                            MissingUnsafe {
                                node,
                                lint: UnsafeLint::DeprecatedSafe2024,
                                reason: UnsafetyReason::UnsafeFnCall,
                            }
                            .into(),
                        ),
                        Err(SyntheticSyntax) => never!("synthetic DeprecatedSafe2024"),
                    }
                }
            }
        }
    }
}

fn handle_borrowck_diagnostic(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    owner: DefWithBodyId,
    diag: &BorrowckDiagnostic,
) {
    let mir_span_to_ptr = |span| {
        let (_, source_map) = db.body_with_source_map(owner);
        match span {
            MirSpan::ExprId(id) => source_map.expr_syntax(id).ok().map(|it| it.map(Into::into)),
            MirSpan::PatId(id) => source_map.pat_syntax(id).ok().map(|it| it.map(Into::into)),
            MirSpan::BindingId(id) => source_map
                .patterns_for_binding(id)
                .iter()
                .find_map(|&pat| source_map.pat_syntax(pat).ok())
                .map(|it| it.map(Into::into)),
            MirSpan::SelfParam => source_map.self_param_syntax().map(|it| it.map(Into::into)),
            MirSpan::Unknown => None,
        }
    };

    match diag {
        BorrowckDiagnostic::MovedOutOfRef { ty, span } => {
            acc.extend(mir_span_to_ptr(*span).map(|span| {
                MovedOutOfRef {
                    ty: Type::new_for_crate(owner.krate(db.upcast()), ty.clone()),
                    span,
                }
                .into()
            }))
        }
        BorrowckDiagnostic::UnusedVariable { variable } => acc
            .push(UnusedVariable { local: Local { parent: owner, binding_id: *variable } }.into()),
        BorrowckDiagnostic::NeedMut { variable, span } => {
            acc.extend(mir_span_to_ptr(*span).map(|span| {
                NeedMut { local: Local { parent: owner, binding_id: *variable }, span }.into()
            }))
        }
        BorrowckDiagnostic::UnusedMut { variable } => {
            acc.push(UnusedMut { local: Local { parent: owner, binding_id: *variable } }.into())
        }
    }
}

fn impl_id_to_source(db: &dyn HirDatabase, impl_: ImplId) -> InFile<AstPtr<ast::Impl>> {
    let loc = impl_.loc(db);
    let tree = loc.id.item_tree(db.upcast());
    let node = &tree[loc.id.value];
    let file_id = loc.id.file_id();
    let ast_id_map = db.ast_id_map(file_id);
    InFile::new(file_id, ast_id_map.get(node.ast_id))
}

pub(crate) fn convert_from_queries(
    db: &dyn HirDatabase,
    acc: &mut Vec<AnyDiagnostic>,
    diagnostics: &[QueriesAnyDiagnostic],
) {
    for diagnostic in diagnostics {
        match diagnostic {
            QueriesAnyDiagnostic::DefDiagnostic { krate, diag } => {
                emit_def_diagnostic(db, acc, *krate, diag)
            }
            QueriesAnyDiagnostic::MacroError { macro_call_id, errors } => {
                macro_call_diagnostics(db, *macro_call_id, errors, acc)
            }
            QueriesAnyDiagnostic::TyLoweringDiagnostic { owner, diags } => {
                handle_ty_lowering_diagnostics(db, acc, owner, &diags.slice)
            }
            QueriesAnyDiagnostic::BodyLoweringDiagnostics { body } => {
                handle_body_lowering_diagnostics(db, acc, *body)
            }
            QueriesAnyDiagnostic::InferenceDiagnostics { owner, diags } => {
                handle_inference_diagnostic(db, acc, *owner, diags)
            }
            QueriesAnyDiagnostic::TypeMismatch { owner, node, mismatch } => {
                handle_type_mismatch(db, acc, *owner, *node, mismatch)
            }
            QueriesAnyDiagnostic::BodyValidationDiagnostics { owner, diags } => {
                handle_body_validation_diagnostics(db, acc, *owner, diags)
            }
            QueriesAnyDiagnostic::BorrowckDiagnostic { owner, diag } => {
                handle_borrowck_diagnostic(db, acc, *owner, diag)
            }
            QueriesAnyDiagnostic::IncoherentImpl { impl_ } => {
                acc.push(IncoherentImpl { impl_: impl_id_to_source(db, *impl_) }.into())
            }
            QueriesAnyDiagnostic::IncorrectCase(diag) => acc.push(diag.clone().into()),
            QueriesAnyDiagnostic::TraitImplOrphan { impl_ } => {
                acc.push(TraitImplOrphan { impl_: impl_id_to_source(db, *impl_) }.into())
            }
            &QueriesAnyDiagnostic::TraitImplIncorrectSafety { impl_, should_be_safe } => acc.push(
                TraitImplIncorrectSafety { impl_: impl_id_to_source(db, impl_), should_be_safe }
                    .into(),
            ),
            QueriesAnyDiagnostic::TraitImplRedundantAssocItems {
                impl_,
                trait_,
                assoc_item: (assoc_item_name, assoc_item_id),
            } => acc.push(
                TraitImplRedundantAssocItems {
                    impl_: impl_id_to_source(db, *impl_),
                    assoc_item: (assoc_item_name.clone(), AssocItem::from(*assoc_item_id)),
                    trait_: Trait::from(*trait_),
                }
                .into(),
            ),
            QueriesAnyDiagnostic::TraitImplMissingAssocItems { impl_, trait_: _, missing } => acc
                .push(
                    TraitImplMissingAssocItems {
                        impl_: impl_id_to_source(db, *impl_),
                        missing: missing
                            .iter()
                            .map(|(name, id)| (name.clone(), AssocItem::from(*id)))
                            .collect(),
                    }
                    .into(),
                ),
        }
    }
}
