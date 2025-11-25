//! Things related to predicates.

use core::fmt;
use std::{iter, marker::PhantomData, ops::Deref};

use intern::{Interned, InternedRef, InternedSlice, InternedSliceRef};
use macros::{TypeFoldable, TypeVisitable};
use rustc_type_ir::{
    self as ty, EarlyBinder, FallibleTypeFolder, FlagComputation, Flags, PredicatePolarity,
    TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor,
    Upcast, UpcastFrom, WithCachedTypeInfo,
    elaborate::Elaboratable,
    error::{ExpectedFound, TypeError},
    inherent::{AsKind, AsKindRef, AsOwnedKindRef, SliceLike},
    relate::{Relate, TypeRelation},
};

use crate::next_solver::{
    AsBorrowedSlice, AsOwnedSlice, GenericArg, SameRepr, Span, TraitIdWrapper, default_types,
    impl_foldable_for_interned_slice_without_borrowed, infer::relate::RelateResult,
    interned_slice_without_borrowed,
};

use super::{Binder, BoundVarKinds, DbInterner, Region, Ty, interned_slice};

pub type BoundExistentialPredicate<'db> = Binder<'db, ExistentialPredicate<'db>>;

pub type TraitRef<'db> = ty::TraitRef<DbInterner<'db>>;
pub type AliasTerm<'db> = ty::AliasTerm<DbInterner<'db>>;
pub type ProjectionPredicate<'db> = ty::ProjectionPredicate<DbInterner<'db>>;
pub type ExistentialPredicate<'db> = ty::ExistentialPredicate<DbInterner<'db>>;
pub type ExistentialTraitRef<'db> = ty::ExistentialTraitRef<DbInterner<'db>>;
pub type ExistentialProjection<'db> = ty::ExistentialProjection<DbInterner<'db>>;
pub type TraitPredicate<'db> = ty::TraitPredicate<DbInterner<'db>>;
pub type ClauseKind<'db> = ty::ClauseKind<DbInterner<'db>>;
pub type PredicateKind<'db> = ty::PredicateKind<DbInterner<'db>>;
pub type NormalizesTo<'db> = ty::NormalizesTo<DbInterner<'db>>;
pub type CoercePredicate<'db> = ty::CoercePredicate<DbInterner<'db>>;
pub type SubtypePredicate<'db> = ty::SubtypePredicate<DbInterner<'db>>;
pub type OutlivesPredicate<'db, T> = ty::OutlivesPredicate<DbInterner<'db>, T>;
pub type RegionOutlivesPredicate<'db> = OutlivesPredicate<'db, Region<'db>>;
pub type TypeOutlivesPredicate<'db> = OutlivesPredicate<'db, Ty<'db>>;
pub type PolyTraitPredicate<'db> = Binder<'db, TraitPredicate<'db>>;
pub type PolyRegionOutlivesPredicate<'db> = Binder<'db, RegionOutlivesPredicate<'db>>;
pub type PolyTypeOutlivesPredicate<'db> = Binder<'db, TypeOutlivesPredicate<'db>>;
pub type PolySubtypePredicate<'db> = Binder<'db, SubtypePredicate<'db>>;
pub type PolyCoercePredicate<'db> = Binder<'db, CoercePredicate<'db>>;
pub type PolyProjectionPredicate<'db> = Binder<'db, ProjectionPredicate<'db>>;
pub type PolyTraitRef<'db> = Binder<'db, TraitRef<'db>>;
pub type PolyExistentialTraitRef<'db> = Binder<'db, ExistentialTraitRef<'db>>;
pub type PolyExistentialProjection<'db> = Binder<'db, ExistentialProjection<'db>>;
pub type ArgOutlivesPredicate<'db> = OutlivesPredicate<'db, GenericArg<'db>>;

interned_slice!(
    BoundExistentialPredicatesStorage,
    BoundExistentialPredicates,
    BoundExistentialPredicatesRef,
    BoundExistentialPredicate<'db>,
    BoundExistentialPredicate<'db>,
    BoundExistentialPredicate<'static>,
    bound_existential_predicates,
);
interned_slice_without_borrowed!(
    BoundExistentialPredicates,
    BoundExistentialPredicatesRef,
    BoundExistentialPredicate<'db>,
    BoundExistentialPredicate<'static>,
);
impl_foldable_for_interned_slice_without_borrowed!(
    BoundExistentialPredicates,
    BoundExistentialPredicatesRef,
);

impl<'a, 'db> rustc_type_ir::inherent::BoundExistentialPredicates<'a, DbInterner<'db>>
    for BoundExistentialPredicatesRef<'a, 'db>
where
    'db: 'a,
{
    fn principal_def_id(self) -> Option<TraitIdWrapper> {
        match self.as_slice()[0].skip_binder_ref() {
            ExistentialPredicate::Trait(tr) => Some(tr.def_id),
            _ => None,
        }
    }

    fn principal(
        self,
    ) -> Option<
        rustc_type_ir::Binder<DbInterner<'db>, rustc_type_ir::ExistentialTraitRef<DbInterner<'db>>>,
    > {
        let principal = &self.as_slice()[0];
        match principal.skip_binder_ref() {
            ExistentialPredicate::Trait(tr) => Some(principal.rebind(tr.clone())),
            _ => None,
        }
    }

    fn auto_traits(self) -> impl IntoIterator<Item = TraitIdWrapper> {
        self.as_slice().iter().filter_map(|predicate| match predicate.skip_binder_ref() {
            ExistentialPredicate::AutoTrait(did) => Some(*did),
            _ => None,
        })
    }

    fn projection_bounds(
        self,
    ) -> impl IntoIterator<Item = Binder<'db, ExistentialProjection<'db>>> {
        self.as_slice().iter().filter_map(|predicate| match predicate.skip_binder_ref() {
            ExistentialPredicate::Projection(projection) => {
                Some(predicate.rebind(projection.clone()))
            }
            _ => None,
        })
    }
}

impl<'db> Relate<DbInterner<'db>> for BoundExistentialPredicatesRef<'_, 'db> {
    type RelateResult = BoundExistentialPredicates<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self.o()
    }

    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        // Fast path for when the auto traits do not match, or if the principals
        // are from different traits and therefore the projections definitely don't
        // match up.
        if a.len() != b.len() {
            return Err(TypeError::ExistentialMismatch(ExpectedFound::new(a.o(), b.o())));
        }
        let v = iter::zip(a, b).map(|(ep_a, ep_b)| {
            match (ep_a.skip_binder_ref(), ep_b.skip_binder_ref()) {
                (ty::ExistentialPredicate::Trait(a), ty::ExistentialPredicate::Trait(b)) => {
                    Ok(ep_a.rebind(ty::ExistentialPredicate::Trait(
                        relation
                            .relate(&ep_a.rebind(a.clone()), &ep_b.rebind(b.clone()))?
                            .skip_binder(),
                    )))
                }
                (
                    ty::ExistentialPredicate::Projection(a),
                    ty::ExistentialPredicate::Projection(b),
                ) => Ok(ep_a.rebind(ty::ExistentialPredicate::Projection(
                    relation
                        .relate(&ep_a.rebind(a.clone()), &ep_b.rebind(b.clone()))?
                        .skip_binder(),
                ))),
                (
                    ty::ExistentialPredicate::AutoTrait(a),
                    ty::ExistentialPredicate::AutoTrait(b),
                ) if a == b => Ok(ep_a.rebind(ty::ExistentialPredicate::AutoTrait(*a))),
                _ => Err(TypeError::ExistentialMismatch(ExpectedFound::new(a.o(), b.o()))),
            }
        });
        let v = v.collect::<Result<_, _>>()?;
        Ok(BoundExistentialPredicates::new_from_vec(v))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Predicate<'db> {
    interned: Interned<PredicateInterned>,
    _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(PartialEq, Eq, Hash)]
struct PredicateInterned(WithCachedTypeInfo<Binder<'static, PredicateKind<'static>>>);

intern::impl_internable!(PredicateInterned);

impl std::fmt::Debug for PredicateInterned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.internee.fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct PredicateRef<'a, 'db> {
    interned: InternedRef<'a, PredicateInterned>,
    _marker: PhantomData<(fn() -> &'db (), &'a &'db ())>,
}

impl<'a, 'db> PredicateRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> Predicate<'db> {
        Predicate { interned: self.interned.o(), _marker: PhantomData }
    }

    #[inline]
    pub fn inner(self) -> &'a WithCachedTypeInfo<Binder<'db, PredicateKind<'db>>> {
        // SAFETY: FIXME
        unsafe {
            std::mem::transmute::<
                &WithCachedTypeInfo<Binder<'_, PredicateKind<'_>>>,
                &WithCachedTypeInfo<Binder<'db, PredicateKind<'db>>>,
            >(&self.interned.get().0)
        }
    }

    #[inline]
    pub fn kind(self) -> &'a Binder<'db, PredicateKind<'db>> {
        &self.inner().internee
    }

    /// Flips the polarity of a Predicate.
    ///
    /// Given `T: Trait` predicate it returns `T: !Trait` and given `T: !Trait` returns `T: Trait`.
    pub fn flip_polarity(self) -> Option<Predicate<'db>> {
        let kind = self
            .kind()
            .map_bound_ref(|kind| match kind {
                PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                    trait_ref,
                    polarity,
                })) => Some(PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                    trait_ref: trait_ref.clone(),
                    polarity: polarity.flip(),
                }))),

                _ => None,
            })
            .transpose()?;

        Some(Predicate::new(kind))
    }
}

impl<'db> Predicate<'db> {
    #[inline]
    pub fn new(kind: Binder<'db, PredicateKind<'db>>) -> Self {
        // SAFETY: FIXME
        let kind = unsafe {
            std::mem::transmute::<
                Binder<'db, PredicateKind<'db>>,
                Binder<'static, PredicateKind<'static>>,
            >(kind)
        };
        let flags = FlagComputation::for_predicate(&kind);
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Predicate { interned: Interned::new(PredicateInterned(cached)), _marker: PhantomData }
    }

    #[inline]
    pub fn inner(&self) -> &WithCachedTypeInfo<Binder<'db, PredicateKind<'db>>> {
        self.r().inner()
    }

    #[inline]
    pub fn kind(&self) -> &Binder<'db, PredicateKind<'db>> {
        self.r().kind()
    }

    #[inline(always)]
    pub fn r(&self) -> PredicateRef<'_, 'db> {
        PredicateRef { interned: self.interned.r(), _marker: PhantomData }
    }
}

impl<'db> std::fmt::Debug for Predicate<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind().fmt(f)
    }
}

impl<'db> std::fmt::Debug for PredicateRef<'_, 'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind().fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Clauses<'db> {
    interned: InternedSlice<ClausesStorage>,
    _marker: PhantomData<fn() -> &'db ()>,
}

intern::impl_slice_internable!(ClausesStorage, WithCachedTypeInfo<()>, Clause<'static>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClausesRef<'a, 'db> {
    interned: InternedSliceRef<'a, ClausesStorage>,
    _marker: PhantomData<(fn() -> &'db (), &'a &'db ())>,
}

impl<'a, 'db> ClausesRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> Clauses<'db> {
        Clauses { interned: self.interned.o(), _marker: PhantomData }
    }

    #[inline]
    pub fn as_slice(self) -> &'a [ClauseRef<'a, 'db>] {
        let clauses = self.interned.get().slice.as_borrowed_slice();
        // SAFETY: FIXME
        unsafe {
            std::mem::transmute::<&'a [ClauseRef<'a, 'static>], &'a [ClauseRef<'a, 'db>]>(clauses)
        }
    }
}

impl<'db> Clauses<'db> {
    #[inline]
    pub fn new_from_slice(slice: &[ClauseRef<'_, 'db>]) -> Self {
        let flags = FlagComputation::<DbInterner<'db>>::for_clauses(slice);
        // SAFETY: FIXME
        let slice =
            unsafe { std::mem::transmute::<&[ClauseRef<'_, 'db>], &[Clause<'static>]>(slice) };
        let cached = WithCachedTypeInfo {
            internee: (),
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Clauses {
            interned: InternedSlice::from_header_and_slice(cached, slice),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn new_from_vec(vec: Vec<Clause<'db>>) -> Self {
        let flags = FlagComputation::<DbInterner<'db>>::for_clauses(vec.as_borrowed_slice());
        // SAFETY: FIXME
        let vec = unsafe { std::mem::transmute::<Vec<Clause<'db>>, Vec<Clause<'static>>>(vec) };
        let cached = WithCachedTypeInfo {
            internee: (),
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Clauses { interned: InternedSlice::from_header_and_vec(cached, vec), _marker: PhantomData }
    }

    #[inline]
    pub fn new_from_iter(iter: impl IntoIterator<Item = Clause<'db>>) -> Self {
        let vec = iter.into_iter().collect();
        Self::new_from_vec(vec)
    }

    #[inline]
    pub fn as_slice(&self) -> &[ClauseRef<'_, 'db>] {
        self.r().as_slice()
    }

    #[inline(always)]
    pub fn r(&self) -> ClausesRef<'_, 'db> {
        ClausesRef { interned: self.interned.r(), _marker: PhantomData }
    }
}

impl<'db> std::fmt::Debug for Clauses<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<'db> std::fmt::Debug for ClausesRef<'_, 'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<'a, 'db> rustc_type_ir::inherent::Clauses<'a, DbInterner<'db>> for ClausesRef<'a, 'db> where
    'db: 'a
{
}

impl<'a, 'db> rustc_type_ir::inherent::SliceLike<'a> for ClausesRef<'a, 'db>
where
    'db: 'a,
{
    type Item = ClauseRef<'a, 'db>;

    #[inline]
    fn as_slice(self) -> &'a [Self::Item] {
        self.as_slice()
    }
}

impl<'a, 'db> IntoIterator for ClausesRef<'a, 'db>
where
    'db: 'a,
{
    type Item = ClauseRef<'a, 'db>;
    type IntoIter = std::iter::Copied<std::slice::Iter<'a, ClauseRef<'a, 'db>>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter().copied()
    }
}

impl<'db> Default for Clauses<'db> {
    #[inline]
    fn default() -> Self {
        default_types().empty.clauses.clone()
    }
}

impl<'db> Default for ClausesRef<'_, 'db> {
    #[inline]
    fn default() -> Self {
        default_types().empty.clauses.r()
    }
}

impl<'a, 'db> Deref for ClausesRef<'a, 'db> {
    type Target = [ClauseRef<'a, 'db>];

    #[inline]
    fn deref(&self) -> &Self::Target {
        (*self).as_slice()
    }
}

impl<'db> TypeSuperFoldable<DbInterner<'db>> for Clauses<'db> {
    #[inline]
    fn try_super_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        self.try_fold_with(folder)
    }

    #[inline]
    fn super_fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        self.fold_with(folder)
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Clauses<'db> {
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let result = self
            .as_slice()
            .iter()
            .map(|item| item.o().try_fold_with(folder))
            .collect::<Result<_, _>>()?;
        Ok(Clauses::new_from_vec(result))
    }
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        let result = self.as_slice().iter().map(|item| item.o().fold_with(folder)).collect();
        Clauses::new_from_vec(result)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Clauses<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for ClausesRef<'_, 'db> {
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        use rustc_type_ir::VisitorResult;
        rustc_ast_ir::walk_visitable_list!(visitor, self.as_slice());
        V::Result::output()
    }
}

impl<'db> rustc_type_ir::Flags for Clauses<'db> {
    #[inline]
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.interned.header.header.flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.interned.header.header.outer_exclusive_binder
    }
}

impl<'db> rustc_type_ir::Flags for ClausesRef<'_, 'db> {
    #[inline]
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.interned.header.header.flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.interned.header.header.outer_exclusive_binder
    }
}

impl<'db> rustc_type_ir::TypeSuperVisitable<DbInterner<'db>> for Clauses<'db> {
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> rustc_type_ir::TypeSuperVisitable<DbInterner<'db>> for ClausesRef<'_, 'db> {
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.as_slice().visit_with(visitor)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Clause<'db>(pub(crate) Predicate<'db>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ClauseRef<'a, 'db>(pub(crate) PredicateRef<'a, 'db>);

unsafe impl<'db> SameRepr for Clause<'db> {
    type Borrowed<'a>
        = ClauseRef<'a, 'db>
    where
        Self: 'a;
}

impl<'db> AsOwnedSlice for [ClauseRef<'_, 'db>] {
    type Owned = Clause<'db>;

    #[inline(always)]
    fn as_owned_slice(&self) -> &[Self::Owned] {
        <[Clause<'_>]>::as_owned_slice(self)
    }
}

impl<'db> fmt::Debug for Clause<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'db> fmt::Debug for ClauseRef<'_, 'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

// We could cram the reveal into the clauses like rustc does, probably
#[derive(Clone, Debug, Hash, PartialEq, Eq, Default, TypeVisitable, TypeFoldable)]
pub struct ParamEnv<'db> {
    pub(crate) clauses: Clauses<'db>,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Default, TypeVisitable)]
pub struct ParamEnvRef<'a, 'db> {
    pub(crate) clauses: ClausesRef<'a, 'db>,
}

impl<'a, 'db> ParamEnvRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> ParamEnv<'db> {
        ParamEnv { clauses: self.clauses.o() }
    }

    #[inline]
    pub fn caller_bounds(self) -> ClausesRef<'a, 'db> {
        self.clauses
    }
}

impl<'db> ParamEnv<'db> {
    #[inline]
    pub fn empty() -> Self {
        ParamEnv { clauses: Clauses::default() }
    }

    #[inline]
    pub fn r(&self) -> ParamEnvRef<'_, 'db> {
        ParamEnvRef { clauses: self.clauses.r() }
    }

    #[inline]
    pub fn caller_bounds(&self) -> ClausesRef<'_, 'db> {
        self.r().clauses
    }
}

impl<'a, 'db> rustc_type_ir::inherent::ParamEnv<'a, DbInterner<'db>> for ParamEnvRef<'a, 'db>
where
    'db: 'a,
{
    #[inline]
    fn caller_bounds(
        self,
    ) -> impl rustc_type_ir::inherent::SliceLike<'a, Item = ClauseRef<'a, 'db>> {
        self.clauses
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParamEnvAnd<'db, T> {
    pub param_env: ParamEnv<'db>,
    pub value: T,
}

impl<'db, T> ParamEnvAnd<'db, T> {
    pub fn into_parts(self) -> (ParamEnv<'db>, T) {
        (self.param_env, self.value)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for PredicateRef<'_, 'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        visitor.visit_predicate(*self)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Predicate<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> TypeSuperVisitable<DbInterner<'db>> for PredicateRef<'_, 'db> {
    #[inline]
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        (*self).kind().visit_with(visitor)
    }
}

impl<'db> TypeSuperVisitable<DbInterner<'db>> for Predicate<'db> {
    #[inline]
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().super_visit_with(visitor)
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Predicate<'db> {
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_predicate(self)
    }
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        folder.fold_predicate(self)
    }
}

impl<'db> TypeSuperFoldable<DbInterner<'db>> for Predicate<'db> {
    fn try_super_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let new = self.kind().clone().try_fold_with(folder)?;
        Ok(Predicate::new(new))
    }
    fn super_fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        let new = self.kind().clone().fold_with(folder);
        Predicate::new(new)
    }
}

impl<'db> Elaboratable<DbInterner<'db>> for Predicate<'db> {
    #[inline]
    fn predicate(&self) -> PredicateRef<'_, 'db> {
        self.r()
    }

    #[inline]
    fn child(&self, clause: <DbInterner<'db> as rustc_type_ir::Interner>::Clause) -> Self {
        clause.into_predicate()
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner<'db> as rustc_type_ir::Interner>::Clause,
        _span: <DbInterner<'db> as rustc_type_ir::Interner>::Span,
        _parent_trait_pred: Binder<'db, &TraitPredicate<'db>>,
        _index: usize,
    ) -> Self {
        clause.into_predicate()
    }
}

impl<'db> Flags for Predicate<'db> {
    #[inline]
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.inner().flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.inner().outer_exclusive_binder
    }
}

impl<'db> Flags for PredicateRef<'_, 'db> {
    #[inline]
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.inner().flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.inner().outer_exclusive_binder
    }
}

impl<'db> AsKind for Predicate<'db> {
    type Kind = Binder<'db, PredicateKind<'db>>;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        self.kind()
    }
}

impl<'a, 'db> AsKindRef<'a> for PredicateRef<'a, 'db> {
    type Kind = Binder<'db, PredicateKind<'db>>;

    #[inline]
    fn kind(self) -> &'a Self::Kind {
        self.kind()
    }
}

impl<'db> UpcastFrom<DbInterner<'db>, ty::PredicateKind<DbInterner<'db>>> for Predicate<'db> {
    fn upcast_from(from: ty::PredicateKind<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl<'db>
    UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::PredicateKind<DbInterner<'db>>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::PredicateKind<DbInterner<'db>>>,
        _interner: DbInterner<'db>,
    ) -> Self {
        Predicate::new(from)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::ClauseKind<DbInterner<'db>>> for Predicate<'db> {
    fn upcast_from(from: ty::ClauseKind<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        Binder::dummy(PredicateKind::Clause(from)).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::ClauseKind<DbInterner<'db>>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::ClauseKind<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        from.map_bound(PredicateKind::Clause).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, Clause<'db>> for Predicate<'db> {
    fn upcast_from(from: Clause<'db>, _interner: DbInterner<'db>) -> Self {
        from.0
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::NormalizesTo<DbInterner<'db>>> for Predicate<'db> {
    fn upcast_from(from: ty::NormalizesTo<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        PredicateKind::NormalizesTo(from).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>> for Predicate<'db> {
    fn upcast_from(from: ty::TraitRef<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        from.map_bound(|trait_ref| TraitPredicate {
            trait_ref,
            polarity: PredicatePolarity::Positive,
        })
        .upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, Binder<'db, ty::TraitPredicate<DbInterner<'db>>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: Binder<'db, ty::TraitPredicate<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Trait(it))).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, Binder<'db, ProjectionPredicate<'db>>> for Predicate<'db> {
    fn upcast_from(from: Binder<'db, ProjectionPredicate<'db>>, interner: DbInterner<'db>) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Projection(it))).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ProjectionPredicate<'db>> for Predicate<'db> {
    fn upcast_from(from: ProjectionPredicate<'db>, interner: DbInterner<'db>) -> Self {
        PredicateKind::Clause(ClauseKind::Projection(from)).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::TraitPredicate<DbInterner<'db>>> for Predicate<'db> {
    fn upcast_from(from: ty::TraitPredicate<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        PredicateKind::Clause(ClauseKind::Trait(from)).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::OutlivesPredicate<DbInterner<'db>, Ty<'db>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: ty::OutlivesPredicate<DbInterner<'db>, Ty<'db>>,
        interner: DbInterner<'db>,
    ) -> Self {
        PredicateKind::Clause(ClauseKind::TypeOutlives(from)).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::OutlivesPredicate<DbInterner<'db>, Region<'db>>>
    for Predicate<'db>
{
    fn upcast_from(
        from: ty::OutlivesPredicate<DbInterner<'db>, Region<'db>>,
        interner: DbInterner<'db>,
    ) -> Self {
        PredicateKind::Clause(ClauseKind::RegionOutlives(from)).upcast(interner)
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::OutlivesPredicate<DbInterner<'db>, Ty<'db>>>
    for Clause<'db>
{
    fn upcast_from(
        from: ty::OutlivesPredicate<DbInterner<'db>, Ty<'db>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::OutlivesPredicate<DbInterner<'db>, Region<'db>>>
    for Clause<'db>
{
    fn upcast_from(
        from: ty::OutlivesPredicate<DbInterner<'db>, Region<'db>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}

impl<'db> UpcastFrom<DbInterner<'db>, PolyRegionOutlivesPredicate<'db>> for Predicate<'db> {
    fn upcast_from(from: PolyRegionOutlivesPredicate<'db>, tcx: DbInterner<'db>) -> Self {
        from.map_bound(|p| PredicateKind::Clause(ClauseKind::RegionOutlives(p))).upcast(tcx)
    }
}

impl<'db> rustc_type_ir::inherent::Predicate<DbInterner<'db>> for Predicate<'db> {
    #[inline]
    fn as_clause(self) -> Option<Clause<'db>> {
        self.as_clause()
    }
}

impl<'a, 'db> rustc_type_ir::inherent::PredicateRef<'a, DbInterner<'db>> for PredicateRef<'a, 'db> {
    #[inline]
    fn as_clause(self) -> Option<ClauseRef<'a, 'db>> {
        self.as_clause()
    }

    /// Whether this projection can be soundly normalized.
    ///
    /// Wf predicates must not be normalized, as normalization
    /// can remove required bounds which would cause us to
    /// unsoundly accept some programs. See #91068.
    fn allow_normalization(self) -> bool {
        // TODO: this should probably live in rustc_type_ir
        match self.kind().skip_binder_ref() {
            PredicateKind::Clause(ClauseKind::WellFormed(_))
            | PredicateKind::AliasRelate(..)
            | PredicateKind::NormalizesTo(..) => false,
            PredicateKind::Clause(ClauseKind::Trait(_))
            | PredicateKind::Clause(ClauseKind::RegionOutlives(_))
            | PredicateKind::Clause(ClauseKind::TypeOutlives(_))
            | PredicateKind::Clause(ClauseKind::Projection(_))
            | PredicateKind::Clause(ClauseKind::ConstArgHasType(..))
            | PredicateKind::Clause(ClauseKind::HostEffect(..))
            | PredicateKind::Clause(ClauseKind::UnstableFeature(_))
            | PredicateKind::DynCompatible(_)
            | PredicateKind::Subtype(_)
            | PredicateKind::Coerce(_)
            | PredicateKind::Clause(ClauseKind::ConstEvaluatable(_))
            | PredicateKind::ConstEquate(_, _)
            | PredicateKind::Ambiguous => true,
        }
    }
}

impl<'db> Predicate<'db> {
    /// Matches a `PredicateKind::Clause` and turns it into a `Clause`, otherwise returns `None`.
    #[inline]
    pub fn as_clause(self) -> Option<Clause<'db>> {
        match self.kind().skip_binder_ref() {
            PredicateKind::Clause(..) => Some(Clause(self)),
            _ => None,
        }
    }

    /// Assert that the predicate is a clause.
    #[inline]
    pub fn expect_clause(self) -> Clause<'db> {
        match self.kind().skip_binder_ref() {
            PredicateKind::Clause(..) => Clause(self),
            _ => panic!("{self:?} is not a clause"),
        }
    }
}

impl<'a, 'db> PredicateRef<'a, 'db> {
    pub fn as_trait_clause(self) -> Option<Binder<'db, &'a TraitPredicate<'db>>> {
        let predicate = self.kind();
        match predicate.skip_binder_ref() {
            PredicateKind::Clause(ClauseKind::Trait(t)) => Some(predicate.rebind(t)),
            _ => None,
        }
    }

    pub fn as_projection_clause(self) -> Option<Binder<'db, &'a ProjectionPredicate<'db>>> {
        let predicate = self.kind();
        match predicate.skip_binder_ref() {
            PredicateKind::Clause(ClauseKind::Projection(t)) => Some(predicate.rebind(t)),
            _ => None,
        }
    }

    /// Matches a `PredicateKind::Clause` and turns it into a `Clause`, otherwise returns `None`.
    #[inline]
    pub fn as_clause(self) -> Option<ClauseRef<'a, 'db>> {
        match self.kind().skip_binder_ref() {
            PredicateKind::Clause(..) => Some(ClauseRef(self)),
            _ => None,
        }
    }

    /// Assert that the predicate is a clause.
    #[inline]
    pub fn expect_clause(self) -> ClauseRef<'a, 'db> {
        match self.kind().skip_binder_ref() {
            PredicateKind::Clause(..) => ClauseRef(self),
            _ => panic!("{self:?} is not a clause"),
        }
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Clause<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for ClauseRef<'_, 'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        visitor.visit_predicate((*self).as_predicate())
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Clause<'db> {
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(folder.try_fold_predicate(self.into_predicate())?.expect_clause())
    }
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        folder.fold_predicate(self.into_predicate()).expect_clause()
    }
}

impl<'a, 'db> AsOwnedKindRef<'a> for ClauseRef<'a, 'db> {
    type Kind = Binder<'db, &'a ClauseKind<'db>>;

    fn kind(self) -> Self::Kind {
        self.kind()
    }
}

impl<'db> Clause<'db> {
    #[inline]
    pub fn into_predicate(self) -> Predicate<'db> {
        self.0
    }

    #[inline]
    pub fn r(&self) -> ClauseRef<'_, 'db> {
        ClauseRef(self.0.r())
    }

    #[inline]
    pub fn kind(&self) -> Binder<'db, &ClauseKind<'db>> {
        self.r().kind()
    }

    #[inline]
    pub fn kind_skip_binder(&self) -> &ClauseKind<'db> {
        self.r().kind_skip_binder()
    }
}

impl<'a, 'db> ClauseRef<'a, 'db> {
    #[inline]
    pub fn as_predicate(self) -> PredicateRef<'a, 'db> {
        self.0
    }

    #[inline]
    pub fn o(self) -> Clause<'db> {
        Clause(self.0.o())
    }

    #[inline]
    pub fn kind(self) -> Binder<'db, &'a ClauseKind<'db>> {
        self.0.kind().map_bound_ref(|clause| match clause {
            PredicateKind::Clause(clause) => clause,
            _ => unreachable!(),
        })
    }

    #[inline]
    pub fn kind_skip_binder(self) -> &'a ClauseKind<'db> {
        match self.0.kind().skip_binder_ref() {
            PredicateKind::Clause(clause) => clause,
            _ => unreachable!(),
        }
    }
}

impl<'db> Elaboratable<DbInterner<'db>> for Clause<'db> {
    fn predicate(&self) -> PredicateRef<'_, 'db> {
        self.0.r()
    }

    fn child(&self, clause: Clause<'db>) -> Self {
        clause
    }

    fn child_with_derived_cause(
        &self,
        clause: Clause<'db>,
        _span: Span,
        _parent_trait_pred: Binder<'db, &TraitPredicate<'db>>,
        _index: usize,
    ) -> Self {
        clause
    }
}

impl<'db> UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::ClauseKind<DbInterner<'db>>>>
    for Clause<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::ClauseKind<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.map_bound(PredicateKind::Clause).upcast(interner))
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>> for Clause<'db> {
    fn upcast_from(from: ty::TraitRef<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>>>
    for Clause<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::TraitRef<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::TraitPredicate<DbInterner<'db>>> for Clause<'db> {
    fn upcast_from(from: ty::TraitPredicate<DbInterner<'db>>, interner: DbInterner<'db>) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db>
    UpcastFrom<DbInterner<'db>, ty::Binder<DbInterner<'db>, ty::TraitPredicate<DbInterner<'db>>>>
    for Clause<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::TraitPredicate<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db> UpcastFrom<DbInterner<'db>, ty::ProjectionPredicate<DbInterner<'db>>> for Clause<'db> {
    fn upcast_from(
        from: ty::ProjectionPredicate<DbInterner<'db>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl<'db>
    UpcastFrom<
        DbInterner<'db>,
        ty::Binder<DbInterner<'db>, ty::ProjectionPredicate<DbInterner<'db>>>,
    > for Clause<'db>
{
    fn upcast_from(
        from: ty::Binder<DbInterner<'db>, ty::ProjectionPredicate<DbInterner<'db>>>,
        interner: DbInterner<'db>,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}

impl<'db> rustc_type_ir::inherent::Clause<DbInterner<'db>> for Clause<'db> {
    fn as_predicate(self) -> <DbInterner<'db> as rustc_type_ir::Interner>::Predicate {
        self.0
    }
}

impl<'a, 'db> rustc_type_ir::inherent::ClauseRef<'a, DbInterner<'db>> for ClauseRef<'a, 'db>
where
    'db: 'a,
{
    fn as_predicate(self) -> PredicateRef<'a, 'db> {
        self.as_predicate()
    }

    fn instantiate_supertrait(
        self,
        cx: DbInterner<'db>,
        trait_ref: Binder<'db, &TraitRef<'db>>,
    ) -> Clause<'db> {
        tracing::debug!(?self, ?trait_ref);
        // See the rustc impl for a long comment
        let bound_pred = self.kind();
        let pred_bound_vars = bound_pred.bound_vars();
        let trait_bound_vars = trait_ref.bound_vars();
        // 1) Self: Bar1<'a, '^0.0> -> Self: Bar1<'a, '^0.1>
        let shifted_pred = cx.shift_bound_var_indices(
            trait_bound_vars.len(),
            (*bound_pred.skip_binder_ref()).clone(),
        );
        // 2) Self: Bar1<'a, '^0.1> -> T: Bar1<'^0.0, '^0.1>
        let new =
            EarlyBinder::bind(shifted_pred).instantiate(cx, trait_ref.skip_binder_ref().args.r());
        // 3) ['x] + ['b] -> ['x, 'b]
        let bound_vars =
            BoundVarKinds::new_from_iter(trait_bound_vars.iter().chain(pred_bound_vars.iter()));

        let predicate: Predicate<'db> =
            ty::Binder::bind_with_vars(PredicateKind::Clause(new), bound_vars).upcast(cx);
        predicate.expect_clause()
    }
}
