//! Things related to consts in the next-trait-solver.

use std::{hash::Hash, marker::PhantomData};

use hir_def::ConstParamId;
use intern::Interned;
use macros::{TypeFoldable, TypeVisitable};
use rustc_ast_ir::visit::VisitorResult;
use rustc_type_ir::{
    BoundVar, BoundVarIndexKind, ConstVid, DebruijnIndex, FallibleTypeFolder, FlagComputation,
    Flags, InferConst, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable,
    TypeVisitable, TypeVisitableExt, TypeVisitor, WithCachedTypeInfo,
    inherent::{AsKind, PlaceholderLike, SliceLike},
    relate::{Relate, RelateRef, TypeRelation},
};

use crate::{
    MemoryMap,
    next_solver::{
        BoundVarKind, ClauseKind, DbInterner, ErrorGuaranteed, GenericArgs, ParamEnv, Placeholder,
        Ty, default_types, infer::relate::RelateResult,
    },
};

pub type ConstKind<'db> = rustc_type_ir::ConstKind<DbInterner<'db>>;
pub type UnevaluatedConst<'db> = rustc_type_ir::UnevaluatedConst<DbInterner<'db>>;

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Const<'db> {
    pub(super) interned: Interned<ConstInterned>,
    pub(super) _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(PartialEq, Eq, Hash)]
#[repr(align(4))] // Needed for GenericArg packing.
pub(super) struct ConstInterned(pub(super) WithCachedTypeInfo<ConstKind<'static>>);

intern::impl_internable!(ConstInterned);

impl std::fmt::Debug for ConstInterned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.internee.fmt(f)
    }
}

impl<'db> Const<'db> {
    #[inline]
    pub fn is_ct_infer(&self) -> bool {
        matches!(self.kind(), ConstKind::Infer(_))
    }

    #[inline]
    pub fn is_ct_error(&self) -> bool {
        matches!(self.kind(), ConstKind::Error(_))
    }

    pub fn is_ct_var(&self) -> bool {
        matches!(self.kind(), ConstKind::Infer(InferConst::Var(_)))
    }

    #[inline]
    pub fn is_trivially_wf(&self) -> bool {
        match self.kind() {
            ConstKind::Param(_) | ConstKind::Placeholder(_) | ConstKind::Bound(..) => true,
            ConstKind::Infer(_)
            | ConstKind::Unevaluated(..)
            | ConstKind::Value(_)
            | ConstKind::Error(_)
            | ConstKind::Expr(_) => false,
        }
    }

    #[inline]
    pub fn new(kind: ConstKind<'_>) -> Self {
        // SAFETY: FIXME
        let kind = unsafe { std::mem::transmute::<ConstKind<'_>, ConstKind<'static>>(kind) };
        let flags = FlagComputation::for_const_kind(&kind);
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Const { interned: Interned::new(ConstInterned(cached)), _marker: PhantomData }
    }

    #[inline]
    pub fn inner(&self) -> &WithCachedTypeInfo<ConstKind<'db>> {
        unsafe {
            std::mem::transmute::<
                &WithCachedTypeInfo<ConstKind<'static>>,
                &WithCachedTypeInfo<ConstKind<'db>>,
            >(&self.interned.0)
        }
    }

    #[inline]
    pub fn kind(&self) -> &ConstKind<'db> {
        &self.inner().internee
    }

    #[inline]
    pub fn new_error() -> Self {
        default_types().consts.error.clone()
    }

    #[inline]
    pub fn new_param(param: ParamConst) -> Self {
        Const::new(ConstKind::Param(param))
    }

    #[inline]
    pub fn new_placeholder(placeholder: PlaceholderConst) -> Self {
        Const::new(ConstKind::Placeholder(placeholder))
    }

    #[inline]
    pub fn new_bound(index: DebruijnIndex, bound: BoundConst) -> Self {
        Const::new(ConstKind::Bound(BoundVarIndexKind::Bound(index), bound))
    }

    #[inline]
    pub fn new_infer(var: InferConst) -> Self {
        Const::new(ConstKind::Infer(var))
    }

    #[inline]
    pub fn new_var(var: ConstVid) -> Self {
        Const::new(ConstKind::Infer(InferConst::Var(var)))
    }

    #[inline]
    pub fn new_anon_bound(debruijn: DebruijnIndex, var: BoundVar) -> Self {
        Const::new(ConstKind::Bound(BoundVarIndexKind::Bound(debruijn), BoundConst { var }))
    }

    #[inline]
    pub fn new_canonical_bound(var: BoundVar) -> Self {
        Const::new(ConstKind::Bound(BoundVarIndexKind::Canonical, BoundConst { var }))
    }

    #[inline]
    pub fn new_unevaluated(uv: rustc_type_ir::UnevaluatedConst<DbInterner<'db>>) -> Self {
        Const::new(ConstKind::Unevaluated(uv))
    }

    #[inline]
    pub fn new_expr(expr: ExprConst) -> Self {
        Const::new(ConstKind::Expr(expr))
    }

    #[inline]
    pub fn new_valtree(ty: Ty<'db>, memory: Box<[u8]>, memory_map: MemoryMap<'db>) -> Self {
        Const::new(ConstKind::Value(ValueConst {
            ty,
            value: Valtree::new(ConstBytes { memory, memory_map }),
        }))
    }
}

impl<'db> std::fmt::Debug for Const<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind().fmt(f)
    }
}

pub type PlaceholderConst = Placeholder<BoundConst>;

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct ParamConst {
    // FIXME: See `ParamTy`.
    pub id: ConstParamId,
    pub index: u32,
}

impl std::fmt::Debug for ParamConst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.index)
    }
}

impl ParamConst {
    pub fn find_const_ty_from_env<'a, 'db>(self, env: ParamEnv<'db>) -> Ty<'db>
    where
        'db: 'a,
    {
        let caller_bounds = env.caller_bounds();
        let mut candidates = caller_bounds.iter().filter_map(|clause| {
            // `ConstArgHasType` are never desugared to be higher ranked.
            match clause.kind_skip_binder() {
                ClauseKind::ConstArgHasType(param_ct, ty) => {
                    assert!(!(param_ct, ty).has_escaping_bound_vars());

                    match param_ct.kind() {
                        ConstKind::Param(param_ct) if param_ct.index == self.index => {
                            Some(ty.clone())
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        });

        // N.B. it may be tempting to fix ICEs by making this function return
        // `Option<Ty<'db>>` instead of `Ty<'db>`; however, this is generally
        // considered to be a bandaid solution, since it hides more important
        // underlying issues with how we construct generics and predicates of
        // items. It's advised to fix the underlying issue rather than trying
        // to modify this function.
        let ty = candidates.next().unwrap_or_else(|| {
            panic!("cannot find `{self:?}` in param-env: {env:#?}");
        });
        assert!(
            candidates.next().is_none(),
            "did not expect duplicate `ConstParamHasTy` for `{self:?}` in param-env: {env:#?}"
        );
        ty
    }
}

/// A type-level constant value.
///
/// Represents a typed, fully evaluated constant.
#[derive(Debug, Clone, Eq, PartialEq, Hash, TypeFoldable, TypeVisitable)]
pub struct ValueConst<'db> {
    pub ty: Ty<'db>,
    // FIXME: Should we ignore this for TypeVisitable, TypeFoldable?
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    pub value: Valtree<'db>,
}

impl<'db> ValueConst<'db> {
    #[inline]
    pub fn new(ty: Ty<'db>, bytes: ConstBytes<'db>) -> Self {
        let value = Valtree::new(bytes);
        ValueConst { ty, value }
    }
}

impl<'db> rustc_type_ir::inherent::ValueConst<DbInterner<'db>> for ValueConst<'db> {
    #[inline]
    fn ty(&self) -> Ty<'db> {
        self.ty.clone()
    }

    #[inline]
    fn valtree(&self) -> Valtree<'db> {
        self.value.clone()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstBytes<'db> {
    pub memory: Box<[u8]>,
    pub memory_map: MemoryMap<'db>,
}

impl Hash for ConstBytes<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.memory.hash(state)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Valtree<'db> {
    interned: Interned<ValtreeInterned<'static>>,
    _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct ValtreeInterned<'db> {
    bytes: ConstBytes<'db>,
}

intern::impl_internable!(ValtreeInterned<'static>);

impl<'db> Valtree<'db> {
    #[inline]
    pub fn new(bytes: ConstBytes<'db>) -> Self {
        let interned = ValtreeInterned { bytes };
        // SAFETY: FIXME
        let interned = unsafe {
            std::mem::transmute::<ValtreeInterned<'db>, ValtreeInterned<'static>>(interned)
        };
        Self { interned: Interned::new(interned), _marker: PhantomData }
    }

    #[inline]
    fn inner(&self) -> &ValtreeInterned<'db> {
        // SAFETY: FIXME
        unsafe {
            std::mem::transmute::<&ValtreeInterned<'static>, &ValtreeInterned<'db>>(&*self.interned)
        }
    }

    #[inline]
    pub fn bytes(&self) -> &ConstBytes<'db> {
        &self.inner().bytes
    }
}

impl std::fmt::Debug for Valtree<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner().fmt(f)
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, TypeVisitable, TypeFoldable)]
pub struct ExprConst;

impl rustc_type_ir::inherent::ParamLike for ParamConst {
    fn index(self) -> u32 {
        self.index
    }
}

impl<'db> AsKind for Const<'db> {
    type Kind = ConstKind<'db>;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        self.kind()
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Const<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        visitor.visit_const(self.clone())
    }
}

impl<'db> TypeSuperVisitable<DbInterner<'db>> for Const<'db> {
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match self.kind() {
            ConstKind::Unevaluated(uv) => uv.visit_with(visitor),
            ConstKind::Value(v) => v.visit_with(visitor),
            ConstKind::Expr(e) => e.visit_with(visitor),
            ConstKind::Error(e) => e.visit_with(visitor),

            ConstKind::Param(_)
            | ConstKind::Infer(_)
            | ConstKind::Bound(..)
            | ConstKind::Placeholder(_) => V::Result::output(),
        }
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Const<'db> {
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_const(self)
    }
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        folder.fold_const(self)
    }
}

impl<'db> TypeSuperFoldable<DbInterner<'db>> for Const<'db> {
    fn try_super_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let kind = match self.kind() {
            ConstKind::Unevaluated(uv) => ConstKind::Unevaluated(uv.clone().try_fold_with(folder)?),
            ConstKind::Value(v) => ConstKind::Value(v.clone().try_fold_with(folder)?),
            ConstKind::Expr(e) => ConstKind::Expr(e.try_fold_with(folder)?),

            ConstKind::Param(_)
            | ConstKind::Infer(_)
            | ConstKind::Bound(..)
            | ConstKind::Placeholder(_)
            | ConstKind::Error(_) => return Ok(self),
        };
        if kind != *self.kind() { Ok(Const::new(kind)) } else { Ok(self) }
    }
    fn super_fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        let kind = match self.kind() {
            ConstKind::Unevaluated(uv) => ConstKind::Unevaluated(uv.clone().fold_with(folder)),
            ConstKind::Value(v) => ConstKind::Value(v.clone().fold_with(folder)),
            ConstKind::Expr(e) => ConstKind::Expr(e.fold_with(folder)),

            ConstKind::Param(_)
            | ConstKind::Infer(_)
            | ConstKind::Bound(..)
            | ConstKind::Placeholder(_)
            | ConstKind::Error(_) => return self,
        };
        if kind != *self.kind() { Const::new(kind) } else { self }
    }
}

impl<'db> RelateRef<DbInterner<'db>> for Const<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.clone(), b.clone())
    }
}

impl<'db> Relate<DbInterner<'db>> for Const<'db> {
    type RelateResult = Const<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self
    }

    #[inline]
    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        relation.consts(a, b)
    }
}

impl<'db> Flags for Const<'db> {
    #[inline]
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.inner().flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.inner().outer_exclusive_binder
    }
}

impl<'db> rustc_type_ir::inherent::Const<DbInterner<'db>> for Const<'db> {
    fn new_infer(_interner: DbInterner<'db>, var: InferConst) -> Self {
        Const::new_infer(var)
    }

    fn new_var(_interner: DbInterner<'db>, var: ConstVid) -> Self {
        Const::new_var(var)
    }

    fn new_bound(_interner: DbInterner<'db>, debruijn: DebruijnIndex, var: BoundConst) -> Self {
        Const::new_bound(debruijn, var)
    }

    fn new_anon_bound(_interner: DbInterner<'db>, debruijn: DebruijnIndex, var: BoundVar) -> Self {
        Const::new_anon_bound(debruijn, var)
    }

    fn new_canonical_bound(_interner: DbInterner<'db>, var: BoundVar) -> Self {
        Const::new_canonical_bound(var)
    }

    fn new_placeholder(_interner: DbInterner<'db>, param: PlaceholderConst) -> Self {
        Const::new_placeholder(param)
    }

    fn new_unevaluated(
        _interner: DbInterner<'db>,
        uv: rustc_type_ir::UnevaluatedConst<DbInterner<'db>>,
    ) -> Self {
        Const::new_unevaluated(uv)
    }

    fn new_expr(_interner: DbInterner<'db>, expr: ExprConst) -> Self {
        Const::new_expr(expr)
    }

    fn new_error(_interner: DbInterner<'db>, _guar: ErrorGuaranteed) -> Self {
        Const::new_error()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundConst {
    pub var: BoundVar,
}

impl<'db> rustc_type_ir::inherent::BoundVarLike<DbInterner<'db>> for BoundConst {
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        var.expect_const()
    }
}

impl<'db> PlaceholderLike<DbInterner<'db>> for PlaceholderConst {
    type Bound = BoundConst;

    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> rustc_type_ir::BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: BoundConst) -> Self {
        Placeholder { universe: ui, bound: var }
    }
    fn new_anon(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundConst { var } }
    }
}

impl<'db> RelateRef<DbInterner<'db>> for ExprConst {
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        _relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = b;
        Ok(*a)
    }
}

impl<'db> Relate<DbInterner<'db>> for ExprConst {
    type RelateResult = Self;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self
    }

    #[inline]
    fn relate<R: TypeRelation<DbInterner<'db>>>(
        _relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self> {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = b;
        Ok(a)
    }
}

impl<'db> rustc_type_ir::inherent::ExprConst<DbInterner<'db>> for ExprConst {
    fn args(&self) -> GenericArgs<'db> {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = self;
        GenericArgs::default()
    }
}
