//! Things related to regions.

use std::{fmt, marker::PhantomData};

use hir_def::LifetimeParamId;
use intern::{Interned, InternedRef, Symbol};
use rustc_type_ir::{
    BoundVar, BoundVarIndexKind, DebruijnIndex, Flags, INNERMOST, RegionVid, TypeFlags,
    TypeFoldable, TypeVisitable,
    inherent::{AnyRegion, AsKind, PlaceholderLike, SliceLike},
    relate::{Relate, RelateRef, TypeRelation},
};

use crate::next_solver::{
    GenericArg, OutlivesPredicate, default_types,
    impl_foldable_for_interned_slice_without_borrowed, infer::relate::RelateResult,
    interned_slice_without_borrowed,
};

use super::{
    SolverDefId, interned_slice,
    interner::{BoundVarKind, DbInterner, Placeholder},
};

pub type RegionKind<'db> = rustc_type_ir::RegionKind<DbInterner<'db>>;

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Region<'db> {
    pub(super) interned: Interned<RegionInterned>,
    pub(super) _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(PartialEq, Eq, Hash)]
#[repr(align(4))] // Needed for GenericArg packing.
pub(super) struct RegionInterned(RegionKind<'static>);

intern::impl_internable!(RegionInterned);

impl std::fmt::Debug for RegionInterned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RegionRef<'a, 'db> {
    pub(super) interned: InternedRef<'a, RegionInterned>,
    pub(super) _marker: PhantomData<fn() -> &'db ()>,
}

impl<'a, 'db> RegionRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> Region<'db> {
        Region { interned: self.interned.o(), _marker: PhantomData }
    }

    #[inline]
    pub fn kind(self) -> &'a RegionKind<'db> {
        // SAFETY: FIXME
        unsafe { std::mem::transmute::<&RegionKind<'_>, &RegionKind<'db>>(&self.interned.get().0) }
    }

    #[inline]
    fn type_flags(&self) -> TypeFlags {
        let mut flags = TypeFlags::empty();

        match self.kind() {
            RegionKind::ReVar(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_INFER;
            }
            RegionKind::RePlaceholder(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_PLACEHOLDER;
            }
            RegionKind::ReEarlyParam(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_PARAM;
            }
            RegionKind::ReLateParam(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
            }
            RegionKind::ReStatic => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
            }
            RegionKind::ReBound(BoundVarIndexKind::Canonical, ..) => {
                flags |= TypeFlags::HAS_RE_BOUND;
                flags |= TypeFlags::HAS_CANONICAL_BOUND;
            }
            RegionKind::ReBound(BoundVarIndexKind::Bound(..), ..) => {
                flags |= TypeFlags::HAS_RE_BOUND;
            }
            RegionKind::ReErased => {
                flags |= TypeFlags::HAS_RE_ERASED;
            }
            RegionKind::ReError(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_ERROR;
            }
        }

        flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        match self.kind() {
            RegionKind::ReBound(BoundVarIndexKind::Bound(debruijn), _) => debruijn.shifted_in(1),
            _ => INNERMOST,
        }
    }

    #[inline]
    pub fn is_placeholder(&self) -> bool {
        matches!(self.kind(), RegionKind::RePlaceholder(..))
    }

    #[inline]
    pub fn is_static(&self) -> bool {
        matches!(self.kind(), RegionKind::ReStatic)
    }

    #[inline]
    pub fn is_erased(&self) -> bool {
        matches!(self.kind(), RegionKind::ReErased)
    }

    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self.kind(), RegionKind::ReVar(_))
    }

    #[inline]
    pub fn is_error(&self) -> bool {
        matches!(self.kind(), RegionKind::ReError(_))
    }
}

impl<'db> Region<'db> {
    #[inline]
    pub fn new(kind: RegionKind<'_>) -> Self {
        // SAFETY: FIXME
        let kind = unsafe { std::mem::transmute::<RegionKind<'_>, RegionKind<'static>>(kind) };
        Region { interned: Interned::new(RegionInterned(kind)), _marker: PhantomData }
    }

    #[inline]
    pub fn kind(&self) -> &RegionKind<'db> {
        self.r().kind()
    }

    #[inline(always)]
    pub fn r(&self) -> RegionRef<'_, 'db> {
        RegionRef { interned: self.interned.r(), _marker: PhantomData }
    }

    #[inline]
    pub fn new_early_param(early_bound_region: EarlyParamRegion) -> Self {
        Region::new(RegionKind::ReEarlyParam(early_bound_region))
    }

    #[inline]
    pub fn new_placeholder(placeholder: PlaceholderRegion) -> Self {
        Region::new(RegionKind::RePlaceholder(placeholder))
    }

    #[inline]
    pub fn new_var(v: RegionVid) -> Region<'db> {
        Region::new(RegionKind::ReVar(v))
    }

    #[inline]
    pub fn new_erased() -> Region<'db> {
        default_types().regions.erased.clone()
    }

    #[inline]
    pub fn new_bound(index: DebruijnIndex, bound: BoundRegion) -> Region<'db> {
        Region::new(RegionKind::ReBound(BoundVarIndexKind::Bound(index), bound))
    }

    #[inline]
    pub fn new_anon_bound(
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        Region::new(RegionKind::ReBound(
            BoundVarIndexKind::Bound(debruijn),
            BoundRegion { var, kind: BoundRegionKind::Anon },
        ))
    }

    #[inline]
    pub fn new_canonical_bound(var: rustc_type_ir::BoundVar) -> Self {
        Region::new(RegionKind::ReBound(
            BoundVarIndexKind::Canonical,
            BoundRegion { var, kind: BoundRegionKind::Anon },
        ))
    }

    #[inline]
    pub fn new_static() -> Self {
        default_types().regions.statik.clone()
    }

    #[inline]
    pub fn new_error() -> Self {
        default_types().regions.error.clone()
    }
}

pub type PlaceholderRegion = Placeholder<BoundRegion>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct EarlyParamRegion {
    // FIXME: See `ParamTy`.
    pub id: LifetimeParamId,
    pub index: u32,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// The parameter representation of late-bound function parameters, "some region
/// at least as big as the scope `fr.scope`".
///
/// Similar to a placeholder region as we create `LateParam` regions when entering a binder
/// except they are always in the root universe and instead of using a boundvar to distinguish
/// between others we use the `DefId` of the parameter. For this reason the `bound_region` field
/// should basically always be `BoundRegionKind::Named` as otherwise there is no way of telling
/// different parameters apart.
pub struct LateParamRegion {
    pub scope: SolverDefId,
    pub bound_region: BoundRegionKind,
}

impl std::fmt::Debug for LateParamRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ReLateParam({:?}, {:?})", self.scope, self.bound_region)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum BoundRegionKind {
    /// An anonymous region parameter for a given fn (&T)
    Anon,

    /// Named region parameters for functions (a in &'a T)
    ///
    /// The `DefId` is needed to distinguish free regions in
    /// the event of shadowing.
    Named(SolverDefId),

    /// Anonymous region for the implicit env pointer parameter
    /// to a closure
    ClosureEnv,
}

impl std::fmt::Debug for BoundRegionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            BoundRegionKind::Anon => write!(f, "BrAnon"),
            BoundRegionKind::Named(did) => {
                write!(f, "BrNamed({did:?})")
            }
            BoundRegionKind::ClosureEnv => write!(f, "BrEnv"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl rustc_type_ir::inherent::ParamLike for EarlyParamRegion {
    fn index(self) -> u32 {
        self.index
    }
}

impl std::fmt::Debug for EarlyParamRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.index)
        // write!(f, "{}/#{}", self.name, self.index)
    }
}

impl<'db> rustc_type_ir::inherent::BoundVarLike<DbInterner<'db>> for BoundRegion {
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_region())
    }
}

impl core::fmt::Debug for BoundRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            BoundRegionKind::Anon => write!(f, "{:?}", self.var),
            BoundRegionKind::ClosureEnv => write!(f, "{:?}.Env", self.var),
            BoundRegionKind::Named(def) => {
                write!(f, "{:?}.Named({:?})", self.var, def)
            }
        }
    }
}

impl BoundRegionKind {
    pub fn is_named(&self) -> bool {
        matches!(self, BoundRegionKind::Named(_))
    }

    pub fn get_name(&self) -> Option<Symbol> {
        None
    }

    pub fn get_id(&self) -> Option<SolverDefId> {
        match self {
            BoundRegionKind::Named(id) => Some(*id),
            _ => None,
        }
    }
}

impl fmt::Debug for Region<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}

impl fmt::Debug for RegionRef<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}

impl<'db> AsKind for Region<'db> {
    type Kind = RegionKind<'db>;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        self.kind()
    }
}

impl<'db> AsKind for RegionRef<'_, 'db> {
    type Kind = RegionKind<'db>;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        (*self).kind()
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Region<'db> {
    fn visit_with<V: rustc_type_ir::TypeVisitor<DbInterner<'db>>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_region(self.r())
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for RegionRef<'_, 'db> {
    fn visit_with<V: rustc_type_ir::TypeVisitor<DbInterner<'db>>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_region(*self)
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Region<'db> {
    fn try_fold_with<F: rustc_type_ir::FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_region(self)
    }
    fn fold_with<F: rustc_type_ir::TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        folder.fold_region(self)
    }
}

impl<'db> RelateRef<DbInterner<'db>> for Region<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.r(), b.r())
    }
}

impl<'db> Relate<DbInterner<'db>> for RegionRef<'_, 'db> {
    type RelateResult = Region<'db>;

    #[inline]
    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Region<'db>> {
        relation.regions(a, b)
    }

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self.o()
    }
}

impl<'db> Flags for Region<'db> {
    #[inline]
    fn flags(&self) -> TypeFlags {
        self.r().type_flags()
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.r().outer_exclusive_binder()
    }
}

impl<'db> Flags for RegionRef<'_, 'db> {
    #[inline]
    fn flags(&self) -> TypeFlags {
        self.type_flags()
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.outer_exclusive_binder()
    }
}

impl<'db> AnyRegion<DbInterner<'db>> for Region<'db> {}

impl<'db> AnyRegion<DbInterner<'db>> for RegionRef<'_, 'db> {}

impl<'db> rustc_type_ir::inherent::Region<DbInterner<'db>> for Region<'db> {
    fn new_bound(
        _interner: DbInterner<'db>,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundRegion,
    ) -> Self {
        Region::new_bound(debruijn, var)
    }

    fn new_anon_bound(
        _interner: DbInterner<'db>,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        Region::new_anon_bound(debruijn, var)
    }

    fn new_canonical_bound(_interner: DbInterner<'db>, var: rustc_type_ir::BoundVar) -> Self {
        Region::new_canonical_bound(var)
    }

    fn new_static(_interner: DbInterner<'db>) -> Self {
        Region::new_static()
    }

    fn new_placeholder(
        _interner: DbInterner<'db>,
        var: <DbInterner<'db> as rustc_type_ir::Interner>::PlaceholderRegion,
    ) -> Self {
        Region::new_placeholder(var)
    }
}

impl<'db> PlaceholderLike<DbInterner<'db>> for PlaceholderRegion {
    type Bound = BoundRegion;

    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> rustc_type_ir::BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, bound: Self::Bound) -> Self {
        Placeholder { universe: ui, bound }
    }

    fn new_anon(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundRegion { var, kind: BoundRegionKind::Anon } }
    }
}

type GenericArgOutlivesPredicate<'db> = OutlivesPredicate<'db, GenericArg<'db>>;

interned_slice!(
    RegionAssumptionsStorage,
    RegionAssumptions,
    RegionAssumptionsRef,
    GenericArgOutlivesPredicate<'db>,
    GenericArgOutlivesPredicate<'db>,
    GenericArgOutlivesPredicate<'static>,
    region_assumptions,
);
interned_slice_without_borrowed!(
    RegionAssumptions,
    RegionAssumptionsRef,
    GenericArgOutlivesPredicate<'db>,
    GenericArgOutlivesPredicate<'static>,
);
impl_foldable_for_interned_slice_without_borrowed!(RegionAssumptions, RegionAssumptionsRef);
