//! Things related to generic args in the next-trait-solver.

use std::{marker::PhantomData, mem::ManuallyDrop};

use hir_def::{GenericDefId, GenericParamId};
use intern::{Interned, InternedRef};
use rustc_type_ir::{
    ConstVid, FallibleTypeFolder, Interner, TyVid, TypeFoldable, TypeFolder, TypeVisitable,
    TypeVisitor,
    inherent::{AsOwnedKindRef, GenericArgsRef as _, GenericsOf, SliceLike, TyRef as _},
    relate::{Relate, RelateRef, TypeRelation, relate_args_invariantly},
};
use smallvec::SmallVec;

use crate::{
    FnAbi,
    next_solver::{
        AsBorrowedSlice, AsOwnedSlice, Const, ConstInterned, ConstRef, DbInterner,
        EarlyParamRegion, FnSig, IteratorOwnedExt, ParamConst, ParamTy, PolyFnSig, Region,
        RegionInterned, RegionRef, SameRepr, SolverDefId, Ty, TyInterned, TyRef, Tys, abi::Safety,
        generics::Generics, impl_foldable_for_interned_slice_with_borrowed,
        infer::relate::RelateResult, interned_slice_with_borrowed, interner::interned_slice,
    },
};

pub type GenericArgKind<'a, 'db> = rustc_type_ir::GenericArgKind<'a, DbInterner<'db>>;
pub type TermKind<'a, 'db> = rustc_type_ir::TermKind<'a, DbInterner<'db>>;
pub type ClosureArgs<'a, 'db> = rustc_type_ir::ClosureArgs<'a, DbInterner<'db>>;
pub type CoroutineArgs<'a, 'db> = rustc_type_ir::CoroutineArgs<'a, DbInterner<'db>>;
pub type CoroutineClosureArgs<'a, 'db> = rustc_type_ir::CoroutineClosureArgs<'a, DbInterner<'db>>;

pub enum OwnedGenericArgKind<'db> {
    Type(Ty<'db>),
    Const(Const<'db>),
    Lifetime(Region<'db>),
}

pub enum OwnedTermKind<'db> {
    Ty(Ty<'db>),
    Const(Const<'db>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct GenericArgImpl<'db> {
    // Bit packed - suffix:
    //  0b00 - Ty
    //  0b01 - Const
    //  0b10 - Region
    ptr: *const (),
    _marker: PhantomData<fn() -> &'db ()>,
}

unsafe impl Send for GenericArgImpl<'_> {}
unsafe impl Sync for GenericArgImpl<'_> {}

impl<'db> GenericArgImpl<'db> {
    const PTR_MASK: usize = !Self::KIND_MASK;
    const KIND_MASK: usize = 0b11;
    const TY_MASK: usize = 0b00;
    const CONST_MASK: usize = 0b01;
    const REGION_MASK: usize = 0b10;

    #[inline]
    fn new_ty(ptr: *const TyInterned) -> Self {
        Self { ptr: ptr.map_addr(|addr| addr | Self::TY_MASK).cast::<()>(), _marker: PhantomData }
    }

    #[inline]
    fn new_const(ptr: *const ConstInterned) -> Self {
        Self {
            ptr: ptr.map_addr(|addr| addr | Self::CONST_MASK).cast::<()>(),
            _marker: PhantomData,
        }
    }

    #[inline]
    fn new_region(ptr: *const RegionInterned) -> Self {
        Self {
            ptr: ptr.map_addr(|addr| addr | Self::REGION_MASK).cast::<()>(),
            _marker: PhantomData,
        }
    }

    #[inline]
    unsafe fn with<R>(
        self,
        ty: impl FnOnce(*const TyInterned) -> R,
        konst: impl FnOnce(*const ConstInterned) -> R,
        region: impl FnOnce(*const RegionInterned) -> R,
    ) -> R {
        let ptr = self.ptr.map_addr(|addr| addr & Self::PTR_MASK);
        unsafe {
            match self.ptr.addr() & Self::KIND_MASK {
                Self::TY_MASK => ty(ptr.cast::<TyInterned>()),
                Self::CONST_MASK => konst(ptr.cast::<ConstInterned>()),
                Self::REGION_MASK => region(ptr.cast::<RegionInterned>()),
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }

    #[inline]
    unsafe fn with_term<R>(
        self,
        ty: impl FnOnce(*const TyInterned) -> R,
        konst: impl FnOnce(*const ConstInterned) -> R,
    ) -> R {
        let ptr = self.ptr.map_addr(|addr| addr & Self::PTR_MASK);
        unsafe {
            match self.ptr.addr() & Self::KIND_MASK {
                Self::TY_MASK => ty(ptr.cast::<TyInterned>()),
                Self::CONST_MASK => konst(ptr.cast::<ConstInterned>()),
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }

    #[inline]
    unsafe fn kind<'a>(self) -> GenericArgKind<'a, 'db> {
        unsafe {
            self.with(
                |ptr| {
                    GenericArgKind::Type(TyRef {
                        interned: InternedRef::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    GenericArgKind::Const(ConstRef {
                        interned: InternedRef::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    GenericArgKind::Lifetime(RegionRef {
                        interned: InternedRef::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    unsafe fn owned_kind(self) -> OwnedGenericArgKind<'db> {
        unsafe {
            self.with(
                |ptr| {
                    OwnedGenericArgKind::Type(Ty {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    OwnedGenericArgKind::Const(Const {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    OwnedGenericArgKind::Lifetime(Region {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    unsafe fn term_kind<'a>(self) -> TermKind<'a, 'db> {
        unsafe {
            self.with_term(
                |ptr| {
                    TermKind::Ty(TyRef {
                        interned: InternedRef::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    TermKind::Const(ConstRef {
                        interned: InternedRef::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    unsafe fn owned_term_kind(self) -> OwnedTermKind<'db> {
        unsafe {
            self.with_term(
                |ptr| {
                    OwnedTermKind::Ty(Ty {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    OwnedTermKind::Const(Const {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }
}

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct GenericArg<'db>(GenericArgImpl<'db>);

impl<'db> Clone for GenericArg<'db> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            self.0.with(
                |ptr| Ty { interned: InternedRef::from_raw(ptr).o(), _marker: PhantomData }.into(),
                |ptr| {
                    Const { interned: InternedRef::from_raw(ptr).o(), _marker: PhantomData }.into()
                },
                |ptr| {
                    Region { interned: InternedRef::from_raw(ptr).o(), _marker: PhantomData }.into()
                },
            )
        }
    }
}

impl<'db> Drop for GenericArg<'db> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.0.with(
                |ptr| drop(Ty { interned: Interned::from_raw(ptr), _marker: PhantomData }),
                |ptr| drop(Const { interned: Interned::from_raw(ptr), _marker: PhantomData }),
                |ptr| drop(Region { interned: Interned::from_raw(ptr), _marker: PhantomData }),
            );
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct GenericArgRef<'a, 'db>(GenericArgImpl<'db>, PhantomData<&'a &'db ()>);

unsafe impl<'db> SameRepr for GenericArg<'db> {
    type Borrowed<'a>
        = GenericArgRef<'a, 'db>
    where
        Self: 'a;
}

impl<'db> From<Ty<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Ty<'db>) -> Self {
        Self(GenericArgImpl::new_ty(value.interned.into_raw()))
    }
}

impl<'db> From<Const<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Const<'db>) -> Self {
        Self(GenericArgImpl::new_const(value.interned.into_raw()))
    }
}

impl<'db> From<Region<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Region<'db>) -> Self {
        Self(GenericArgImpl::new_region(value.interned.into_raw()))
    }
}

impl<'db> From<Term<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Term<'db>) -> Self {
        Self(value.0)
    }
}

impl<'a, 'db> From<TyRef<'a, 'db>> for GenericArgRef<'a, 'db> {
    #[inline]
    fn from(value: TyRef<'a, 'db>) -> Self {
        Self(GenericArgImpl::new_ty(value.interned.as_raw()), PhantomData)
    }
}

impl<'a, 'db> From<ConstRef<'a, 'db>> for GenericArgRef<'a, 'db> {
    #[inline]
    fn from(value: ConstRef<'a, 'db>) -> Self {
        Self(GenericArgImpl::new_const(value.interned.as_raw()), PhantomData)
    }
}

impl<'a, 'db> From<RegionRef<'a, 'db>> for GenericArgRef<'a, 'db> {
    #[inline]
    fn from(value: RegionRef<'a, 'db>) -> Self {
        Self(GenericArgImpl::new_region(value.interned.as_raw()), PhantomData)
    }
}

impl<'a, 'db> From<TermRef<'a, 'db>> for GenericArgRef<'a, 'db> {
    #[inline]
    fn from(value: TermRef<'a, 'db>) -> Self {
        Self(value.0, PhantomData)
    }
}

impl<'db> std::fmt::Debug for GenericArgRef<'_, 'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            GenericArgKind::Type(it) => it.fmt(f),
            GenericArgKind::Lifetime(it) => it.fmt(f),
            GenericArgKind::Const(it) => it.fmt(f),
        }
    }
}

impl<'db> std::fmt::Debug for GenericArg<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.r().fmt(f)
    }
}

impl<'a, 'db> GenericArgRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> GenericArg<'db> {
        (*ManuallyDrop::new(GenericArg(self.0))).clone()
    }

    #[inline]
    pub fn kind(self) -> GenericArgKind<'a, 'db> {
        unsafe { self.0.kind() }
    }

    #[inline]
    pub fn ty(self) -> Option<TyRef<'a, 'db>> {
        match self.kind() {
            GenericArgKind::Type(ty) => Some(ty),
            _ => None,
        }
    }

    #[inline]
    pub fn expect_ty(self) -> TyRef<'a, 'db> {
        match self.kind() {
            GenericArgKind::Type(ty) => ty,
            _ => panic!("Expected ty, got {self:?}"),
        }
    }

    #[inline]
    pub fn konst(self) -> Option<ConstRef<'a, 'db>> {
        match self.kind() {
            GenericArgKind::Const(konst) => Some(konst),
            _ => None,
        }
    }

    #[inline]
    pub fn region(self) -> Option<RegionRef<'a, 'db>> {
        match self.kind() {
            GenericArgKind::Lifetime(r) => Some(r),
            _ => None,
        }
    }

    #[inline]
    pub fn expect_region(self) -> RegionRef<'a, 'db> {
        match self.kind() {
            GenericArgKind::Lifetime(region) => region,
            _ => panic!("expected a region, got {self:?}"),
        }
    }
}

impl<'db> GenericArg<'db> {
    #[inline]
    pub fn r(&self) -> GenericArgRef<'_, 'db> {
        GenericArgRef(self.0, PhantomData)
    }

    #[inline]
    pub fn kind(&self) -> GenericArgKind<'_, 'db> {
        self.r().kind()
    }

    #[inline]
    pub fn into_kind(&self) -> OwnedGenericArgKind<'db> {
        unsafe { self.0.owned_kind() }
    }

    #[inline]
    pub fn error_from_id(id: GenericParamId) -> GenericArg<'db> {
        match id {
            GenericParamId::TypeParamId(_) => Ty::new_error().into(),
            GenericParamId::ConstParamId(_) => Const::new_error().into(),
            GenericParamId::LifetimeParamId(_) => Region::new_error().into(),
        }
    }

    #[inline]
    pub fn into_type(self) -> Option<Ty<'db>> {
        match self.into_kind() {
            OwnedGenericArgKind::Type(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_const(self) -> Option<Const<'db>> {
        match self.into_kind() {
            OwnedGenericArgKind::Const(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_region(self) -> Option<Region<'db>> {
        match self.into_kind() {
            OwnedGenericArgKind::Lifetime(it) => Some(it),
            _ => None,
        }
    }
}

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Term<'db>(GenericArgImpl<'db>);

impl<'db> Clone for Term<'db> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            self.0.with_term(
                |ptr| Ty { interned: InternedRef::from_raw(ptr).o(), _marker: PhantomData }.into(),
                |ptr| {
                    Const { interned: InternedRef::from_raw(ptr).o(), _marker: PhantomData }.into()
                },
            )
        }
    }
}

impl<'db> Drop for Term<'db> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.0.with_term(
                |ptr| drop(Ty { interned: Interned::from_raw(ptr), _marker: PhantomData }),
                |ptr| drop(Const { interned: Interned::from_raw(ptr), _marker: PhantomData }),
            );
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TermRef<'a, 'db>(GenericArgImpl<'db>, PhantomData<&'a &'db ()>);

impl<'db> From<Ty<'db>> for Term<'db> {
    #[inline]
    fn from(value: Ty<'db>) -> Self {
        Self(GenericArgImpl::new_ty(value.interned.into_raw()))
    }
}

impl<'db> From<Const<'db>> for Term<'db> {
    #[inline]
    fn from(value: Const<'db>) -> Self {
        Self(GenericArgImpl::new_const(value.interned.into_raw()))
    }
}

impl<'a, 'db> From<TyRef<'a, 'db>> for TermRef<'a, 'db> {
    #[inline]
    fn from(value: TyRef<'a, 'db>) -> Self {
        Self(GenericArgImpl::new_ty(value.interned.as_raw()), PhantomData)
    }
}

impl<'a, 'db> From<ConstRef<'a, 'db>> for TermRef<'a, 'db> {
    #[inline]
    fn from(value: ConstRef<'a, 'db>) -> Self {
        Self(GenericArgImpl::new_const(value.interned.as_raw()), PhantomData)
    }
}

impl<'db> std::fmt::Debug for TermRef<'_, 'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            TermKind::Ty(it) => it.fmt(f),
            TermKind::Const(it) => it.fmt(f),
        }
    }
}

impl<'db> std::fmt::Debug for Term<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.r().fmt(f)
    }
}

impl<'a, 'db> TermRef<'a, 'db> {
    #[inline]
    pub fn o(self) -> Term<'db> {
        (*ManuallyDrop::new(Term(self.0))).clone()
    }

    #[inline]
    pub fn kind(self) -> TermKind<'a, 'db> {
        unsafe { self.0.term_kind() }
    }

    #[inline]
    pub fn ty(self) -> Option<TyRef<'a, 'db>> {
        match self.kind() {
            TermKind::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    #[inline]
    pub fn expect_ty(self) -> TyRef<'a, 'db> {
        match self.kind() {
            TermKind::Ty(ty) => ty,
            _ => panic!("Expected ty, got {self:?}"),
        }
    }

    #[inline]
    pub fn konst(self) -> Option<ConstRef<'a, 'db>> {
        match self.kind() {
            TermKind::Const(konst) => Some(konst),
            _ => None,
        }
    }

    pub fn is_trivially_wf(&self) -> bool {
        match self.kind() {
            TermKind::Ty(ty) => ty.is_trivially_wf(),
            TermKind::Const(ct) => ct.is_trivially_wf(),
        }
    }
}

impl<'db> Term<'db> {
    #[inline]
    pub fn r(&self) -> TermRef<'_, 'db> {
        TermRef(self.0, PhantomData)
    }

    #[inline]
    pub fn kind(&self) -> TermKind<'_, 'db> {
        self.r().kind()
    }

    #[inline]
    pub fn into_kind(&self) -> OwnedTermKind<'db> {
        unsafe { self.0.owned_term_kind() }
    }

    #[inline]
    pub fn into_type(self) -> Option<Ty<'db>> {
        match self.into_kind() {
            OwnedTermKind::Ty(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn expect_type(self) -> Ty<'db> {
        match self.into_kind() {
            OwnedTermKind::Ty(it) => it,
            _ => panic!("expected a type, found {self:?}"),
        }
    }

    #[inline]
    pub fn into_const(self) -> Option<Const<'db>> {
        match self.into_kind() {
            OwnedTermKind::Const(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn expect_const(self) -> Const<'db> {
        match self.into_kind() {
            OwnedTermKind::Const(it) => it,
            _ => panic!("expected a type, found {self:?}"),
        }
    }
}

impl<'a, 'db> AsOwnedKindRef<'a> for GenericArgRef<'a, 'db>
where
    'db: 'a,
{
    type Kind = GenericArgKind<'a, 'db>;

    #[inline]
    fn kind(self) -> Self::Kind {
        self.kind()
    }
}

impl<'a, 'db> AsOwnedKindRef<'a> for TermRef<'a, 'db>
where
    'db: 'a,
{
    type Kind = TermKind<'a, 'db>;

    #[inline]
    fn kind(self) -> Self::Kind {
        self.kind()
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for GenericArg<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for GenericArgRef<'_, 'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match self.kind() {
            GenericArgKind::Lifetime(it) => it.visit_with(visitor),
            GenericArgKind::Type(it) => it.visit_with(visitor),
            GenericArgKind::Const(it) => it.visit_with(visitor),
        }
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for GenericArg<'db> {
    #[inline]
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.into_kind() {
            OwnedGenericArgKind::Type(it) => it.try_fold_with(folder).map(Into::into),
            OwnedGenericArgKind::Const(it) => it.try_fold_with(folder).map(Into::into),
            OwnedGenericArgKind::Lifetime(it) => it.try_fold_with(folder).map(Into::into),
        }
    }

    #[inline]
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        match self.into_kind() {
            OwnedGenericArgKind::Type(it) => it.fold_with(folder).into(),
            OwnedGenericArgKind::Const(it) => it.fold_with(folder).into(),
            OwnedGenericArgKind::Lifetime(it) => it.fold_with(folder).into(),
        }
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Term<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        self.r().visit_with(visitor)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for TermRef<'_, 'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match self.kind() {
            TermKind::Ty(it) => it.visit_with(visitor),
            TermKind::Const(it) => it.visit_with(visitor),
        }
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Term<'db> {
    #[inline]
    fn try_fold_with<F: FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        match self.into_kind() {
            OwnedTermKind::Ty(it) => it.try_fold_with(folder).map(Into::into),
            OwnedTermKind::Const(it) => it.try_fold_with(folder).map(Into::into),
        }
    }

    #[inline]
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        match self.into_kind() {
            OwnedTermKind::Ty(it) => it.fold_with(folder).into(),
            OwnedTermKind::Const(it) => it.fold_with(folder).into(),
        }
    }
}

impl<'db> RelateRef<DbInterner<'db>> for GenericArg<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.r(), b.r())
    }
}

impl<'db> Relate<DbInterner<'db>> for GenericArgRef<'_, 'db> {
    type RelateResult = GenericArg<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self.o()
    }

    #[inline]
    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        match (a.kind(), b.kind()) {
            (GenericArgKind::Lifetime(a), GenericArgKind::Lifetime(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            (GenericArgKind::Type(a), GenericArgKind::Type(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            (GenericArgKind::Const(a), GenericArgKind::Const(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            _ => panic!("impossible case reached: can't relate: {a:?} with {b:?}"),
        }
    }
}

impl<'db> RelateRef<DbInterner<'db>> for Term<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.r(), b.r())
    }
}

impl<'db> Relate<DbInterner<'db>> for TermRef<'_, 'db> {
    type RelateResult = Term<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self.o()
    }

    #[inline]
    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        match (a.kind(), b.kind()) {
            (TermKind::Ty(a), TermKind::Ty(b)) => relation.relate(a, b).map(Into::into),
            (TermKind::Const(a), TermKind::Const(b)) => relation.relate(a, b).map(Into::into),
            _ => panic!("impossible case reached: can't relate: {a:?} with {b:?}"),
        }
    }
}

interned_slice!(
    GenericArgsStorage,
    GenericArgs,
    GenericArgsRef,
    GenericArg<'db>,
    GenericArgRef<'a, 'db>,
    GenericArg<'static>,
    generic_args,
);
impl_foldable_for_interned_slice_with_borrowed!(GenericArgs, GenericArgsRef);
interned_slice_with_borrowed!(
    GenericArgs,
    GenericArgsRef,
    GenericArg<'db>,
    GenericArgRef<'a, 'db>,
    GenericArg<'static>
);

impl<'a, 'db> rustc_type_ir::inherent::GenericArg<'a, DbInterner<'db>> for GenericArgRef<'a, 'db> where
    'db: 'a
{
}

impl<'db> GenericArgs<'db> {
    pub fn identity_for_item(interner: DbInterner<'db>, def_id: SolverDefId) -> GenericArgs<'db> {
        GenericArgs::for_item(interner, def_id, |index, kind, _| mk_param(index, kind))
    }

    /// Creates an `GenericArgs` for generic parameter definitions,
    /// by calling closures to obtain each kind.
    /// The closures get to observe the `GenericArgs` as they're
    /// being built, which can be used to correctly
    /// replace defaults of generic parameters.
    pub fn for_item<F>(
        interner: DbInterner<'db>,
        def_id: SolverDefId,
        mut mk_kind: F,
    ) -> GenericArgs<'db>
    where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        let defs = interner.generics_of(def_id);
        let count = defs.count();

        if count == 0 {
            return Default::default();
        }

        let mut args = SmallVec::with_capacity(count);
        Self::fill_item(&mut args, interner, defs, &mut mk_kind);
        GenericArgs::new_from_smallvec(args)
    }

    /// Creates an all-error `GenericArgs`.
    pub fn error_for_item(interner: DbInterner<'db>, def_id: SolverDefId) -> GenericArgs<'db> {
        GenericArgs::for_item(interner, def_id, |_, id, _| GenericArg::error_from_id(id))
    }

    /// Like `for_item`, but prefers the default of a parameter if it has any.
    pub fn for_item_with_defaults<F>(
        interner: DbInterner<'db>,
        def_id: GenericDefId,
        mut fallback: F,
    ) -> GenericArgs<'db>
    where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        let defaults = interner.db.generic_defaults(def_id);
        Self::for_item(interner, def_id.into(), |idx, id, prev| match defaults.get(idx as usize) {
            Some(default) => default.instantiate(interner, prev.as_borrowed_slice()),
            None => fallback(idx, id, prev),
        })
    }

    /// Like `for_item()`, but calls first uses the args from `first`.
    pub fn fill_rest<F>(
        interner: DbInterner<'db>,
        def_id: SolverDefId,
        first: impl IntoIterator<Item = GenericArg<'db>>,
        mut fallback: F,
    ) -> GenericArgs<'db>
    where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        let mut iter = first.into_iter();
        Self::for_item(interner, def_id, |idx, id, prev| {
            iter.next().unwrap_or_else(|| fallback(idx, id, prev))
        })
    }

    /// Appends default param values to `first` if needed. Params without default will call `fallback()`.
    pub fn fill_with_defaults<F>(
        interner: DbInterner<'db>,
        def_id: GenericDefId,
        first: impl IntoIterator<Item = GenericArg<'db>>,
        mut fallback: F,
    ) -> GenericArgs<'db>
    where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        let defaults = interner.db.generic_defaults(def_id);
        Self::fill_rest(interner, def_id.into(), first, |idx, id, prev| {
            defaults
                .get(idx as usize)
                .map(|default| default.instantiate(interner, prev.as_borrowed_slice()))
                .unwrap_or_else(|| fallback(idx, id, prev))
        })
    }

    fn fill_item<F>(
        args: &mut SmallVec<[GenericArg<'db>; 8]>,
        interner: DbInterner<'_>,
        defs: Generics,
        mk_kind: &mut F,
    ) where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        if let Some(def_id) = defs.parent {
            let parent_defs = interner.generics_of(def_id.into());
            Self::fill_item(args, interner, parent_defs, mk_kind);
        }
        Self::fill_single(args, &defs, mk_kind);
    }

    fn fill_single<F>(args: &mut SmallVec<[GenericArg<'db>; 8]>, defs: &Generics, mk_kind: &mut F)
    where
        F: FnMut(u32, GenericParamId, &[GenericArg<'db>]) -> GenericArg<'db>,
    {
        args.reserve(defs.own_params.len());
        for param in &defs.own_params {
            let kind = mk_kind(args.len() as u32, param.id, args);
            args.push(kind);
        }
    }
}

impl<'a, 'db> GenericArgsRef<'a, 'db> {
    pub fn types(self) -> impl Iterator<Item = TyRef<'a, 'db>> {
        self.iter().filter_map(|it| it.ty())
    }

    pub fn consts(self) -> impl Iterator<Item = ConstRef<'a, 'db>> {
        self.iter().filter_map(|it| it.konst())
    }

    pub fn regions(self) -> impl Iterator<Item = RegionRef<'a, 'db>> {
        self.iter().filter_map(|it| it.region())
    }

    pub fn type_at(self, i: usize) -> TyRef<'a, 'db> {
        self.as_slice()
            .get(i)
            .and_then(|g| g.ty())
            .unwrap_or_else(|| panic!("expected type: index={i}, args={self:?}"))
    }

    pub fn region_at(self, i: usize) -> RegionRef<'a, 'db> {
        self.as_slice()
            .get(i)
            .and_then(|g| g.region())
            .unwrap_or_else(|| panic!("expected type: index={i}, args={self:?}"))
    }

    pub fn const_at(self, i: usize) -> ConstRef<'a, 'db> {
        self.as_slice()
            .get(i)
            .and_then(|g| g.konst())
            .unwrap_or_else(|| panic!("expected type: index={i}, args={self:?}"))
    }

    /// Assuming these are args of a closure, this returns its signature untupled
    /// (that is, `Fn(i32, i32)` will be returned as `fn(i32, i32)`, while it's stored
    /// as `fn((i32, i32))`), and with `safety` as the safety.
    pub fn signature_unclosure(self, safety: Safety) -> PolyFnSig<'db> {
        self.as_closure().sig().map_bound(|sig| FnSig {
            inputs_and_output: Tys::new_from_iter(
                sig.inputs_and_output.as_slice()[0]
                    .tuple_fields()
                    .iter()
                    .chain(std::iter::once(sig.output()))
                    .owned(),
            ),
            c_variadic: sig.c_variadic,
            safety,
            abi: FnAbi::Rust,
        })
    }
}

impl<'db> RelateRef<DbInterner<'db>> for GenericArgs<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.r(), b.r())
    }
}

impl<'a, 'db> rustc_type_ir::relate::Relate<DbInterner<'db>> for GenericArgsRef<'a, 'db> {
    type RelateResult = GenericArgs<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self.o()
    }

    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        relate_args_invariantly(relation, a, b)
    }
}

impl<'a, 'db> rustc_type_ir::inherent::GenericArgsRef<'a, DbInterner<'db>>
    for GenericArgsRef<'a, 'db>
where
    'db: 'a,
{
    fn as_closure(self) -> ClosureArgs<'a, 'db> {
        ClosureArgs { args: self }
    }
    fn as_coroutine(self) -> CoroutineArgs<'a, 'db> {
        CoroutineArgs { args: self }
    }
    fn as_coroutine_closure(self) -> CoroutineClosureArgs<'a, 'db> {
        CoroutineClosureArgs { args: self }
    }
    fn rebase_onto(
        self,
        interner: DbInterner<'db>,
        source_def_id: SolverDefId,
        target: GenericArgsRef<'_, 'db>,
    ) -> GenericArgs<'db> {
        let defs = interner.generics_of(source_def_id);
        interner.mk_args_from_iter(target.iter().chain(self.iter().skip(defs.count())).owned())
    }

    fn identity_for_item(interner: DbInterner<'db>, def_id: SolverDefId) -> GenericArgs<'db> {
        GenericArgs::for_item(interner, def_id, |index, kind, _| mk_param(index, kind))
    }

    fn extend_with_error(
        interner: DbInterner<'db>,
        def_id: SolverDefId,
        original_args: &[GenericArg<'db>],
    ) -> GenericArgs<'db> {
        GenericArgs::for_item(interner, def_id, |index, kind, _| {
            if let Some(arg) = original_args.get(index as usize) {
                arg.clone()
            } else {
                GenericArg::error_from_id(kind)
            }
        })
    }

    fn type_at(self, i: usize) -> TyRef<'a, 'db> {
        self.type_at(i)
    }

    fn region_at(self, i: usize) -> RegionRef<'a, 'db> {
        self.region_at(i)
    }

    fn const_at(self, i: usize) -> ConstRef<'a, 'db> {
        self.const_at(i)
    }

    fn split_closure_args(self) -> rustc_type_ir::ClosureArgsParts<'a, DbInterner<'db>> {
        match *self.as_slice() {
            [ref parent_args @ .., closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty] => {
                rustc_type_ir::ClosureArgsParts {
                    parent_args,
                    closure_kind_ty: closure_kind_ty.expect_ty(),
                    closure_sig_as_fn_ptr_ty: closure_sig_as_fn_ptr_ty.expect_ty(),
                    tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                }
            }
            _ => panic!("closure args missing synthetics"),
        }
    }

    fn split_coroutine_closure_args(
        self,
    ) -> rustc_type_ir::CoroutineClosureArgsParts<'a, DbInterner<'db>> {
        match *self.as_slice() {
            [
                ref parent_args @ ..,
                closure_kind_ty,
                signature_parts_ty,
                tupled_upvars_ty,
                coroutine_captures_by_ref_ty,
            ] => rustc_type_ir::CoroutineClosureArgsParts {
                parent_args,
                closure_kind_ty: closure_kind_ty.expect_ty(),
                signature_parts_ty: signature_parts_ty.expect_ty(),
                tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                coroutine_captures_by_ref_ty: coroutine_captures_by_ref_ty.expect_ty(),
            },
            _ => panic!("closure args missing synthetics"),
        }
    }

    fn split_coroutine_args(self) -> rustc_type_ir::CoroutineArgsParts<'a, DbInterner<'db>> {
        match *self.as_slice() {
            [ref parent_args @ .., kind_ty, resume_ty, yield_ty, return_ty, tupled_upvars_ty] => {
                rustc_type_ir::CoroutineArgsParts {
                    parent_args,
                    kind_ty: kind_ty.expect_ty(),
                    resume_ty: resume_ty.expect_ty(),
                    yield_ty: yield_ty.expect_ty(),
                    return_ty: return_ty.expect_ty(),
                    tupled_upvars_ty: tupled_upvars_ty.expect_ty(),
                }
            }
            _ => panic!("coroutine args missing synthetics"),
        }
    }
}

pub fn mk_param<'db>(index: u32, id: GenericParamId) -> GenericArg<'db> {
    match id {
        GenericParamId::LifetimeParamId(id) => {
            Region::new_early_param(EarlyParamRegion { index, id }).into()
        }
        GenericParamId::TypeParamId(id) => Ty::new_param(ParamTy { id, index }).into(),
        GenericParamId::ConstParamId(id) => Const::new_param(ParamConst { index, id }).into(),
    }
}

impl<'db> rustc_type_ir::inherent::Term<DbInterner<'db>> for Term<'db> {
    #[inline]
    fn into_type(self) -> Option<Ty<'db>> {
        self.into_type()
    }

    fn into_const(self) -> Option<Const<'db>> {
        self.into_const()
    }
}

impl<'a, 'db> rustc_type_ir::inherent::TermRef<'a, DbInterner<'db>> for TermRef<'a, 'db> where
    'db: 'a
{
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TermVid {
    Ty(TyVid),
    Const(ConstVid),
}

impl From<TyVid> for TermVid {
    fn from(value: TyVid) -> Self {
        TermVid::Ty(value)
    }
}

impl From<ConstVid> for TermVid {
    fn from(value: ConstVid) -> Self {
        TermVid::Const(value)
    }
}

impl<'db> AsOwnedSlice for [GenericArgRef<'_, 'db>] {
    type Owned = GenericArg<'db>;

    #[inline(always)]
    fn as_owned_slice(&self) -> &[Self::Owned] {
        <[GenericArg<'_>]>::as_owned_slice(self)
    }
}
