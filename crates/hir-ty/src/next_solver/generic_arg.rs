//! Things related to generic args in the next-trait-solver.

use std::{marker::PhantomData, mem::ManuallyDrop, ptr::NonNull};

use hir_def::{GenericDefId, GenericParamId};
use intern::Interned;
use rustc_type_ir::{
    ConstVid, FallibleTypeFolder, InferConst, InferTy, Interner, TyVid, TypeFoldable, TypeFolder,
    TypeVisitable, TypeVisitor,
    inherent::{GenericArgs as _, GenericsOf, IntoKind, Ty as _},
    relate::{Relate, RelateRef, TypeRelation, relate_args_invariantly},
};
use smallvec::SmallVec;

use crate::{
    FnAbi,
    next_solver::{
        Const, ConstInterned, ConstKind, DbInterner, EarlyParamRegion, FnSig, ParamConst, ParamTy,
        PolyFnSig, Region, RegionInterned, RegionKind, SolverDefId, Ty, TyInterned, TyKind, Tys,
        abi::Safety, generics::Generics, impl_foldable_for_interned_slice,
        infer::relate::RelateResult, interner::interned_slice,
    },
};

pub type GenericArgKind<'db> = rustc_type_ir::GenericArgKind<DbInterner<'db>>;
pub type TermKind<'db> = rustc_type_ir::TermKind<DbInterner<'db>>;
pub type ClosureArgs<'db> = rustc_type_ir::ClosureArgs<DbInterner<'db>>;
pub type CoroutineArgs<'db> = rustc_type_ir::CoroutineArgs<DbInterner<'db>>;
pub type CoroutineClosureArgs<'db> = rustc_type_ir::CoroutineClosureArgs<DbInterner<'db>>;

pub enum GenericArgKindRef<'a, 'db> {
    Type(&'a TyKind<'db>),
    Const(&'a ConstKind<'db>),
    Lifetime(&'a RegionKind<'db>),
}

pub enum TermKindRef<'a, 'db> {
    Ty(&'a TyKind<'db>),
    Const(&'a ConstKind<'db>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct GenericArgImpl<'db> {
    // Bit packed - suffix:
    //  0b00 - Ty
    //  0b01 - Const
    //  0b10 - Region
    ptr: NonNull<()>,
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
    fn new_ty(ptr: NonNull<TyInterned>) -> Self {
        Self { ptr: ptr.map_addr(|addr| addr | Self::TY_MASK).cast::<()>(), _marker: PhantomData }
    }

    #[inline]
    fn new_const(ptr: NonNull<ConstInterned>) -> Self {
        Self {
            ptr: ptr.map_addr(|addr| addr | Self::CONST_MASK).cast::<()>(),
            _marker: PhantomData,
        }
    }

    #[inline]
    fn new_region(ptr: NonNull<RegionInterned>) -> Self {
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
        let ptr = self.ptr.as_ptr().map_addr(|addr| addr & Self::PTR_MASK);
        unsafe {
            match self.ptr.addr().get() & Self::KIND_MASK {
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
        let ptr = self.ptr.as_ptr().map_addr(|addr| addr & Self::PTR_MASK);
        unsafe {
            match self.ptr.addr().get() & Self::KIND_MASK {
                Self::TY_MASK => ty(ptr.cast::<TyInterned>()),
                Self::CONST_MASK => konst(ptr.cast::<ConstInterned>()),
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }

    #[inline]
    unsafe fn kind<'a>(&'a self) -> GenericArgKindRef<'a, 'db>
    where
        'db: 'a,
    {
        unsafe {
            let result = self.with(
                |ptr| GenericArgKindRef::Type(&(&*ptr).0.internee),
                |ptr| GenericArgKindRef::Const(&(&*ptr).0.internee),
                |ptr| GenericArgKindRef::Lifetime(&(&*ptr).0),
            );
            std::mem::transmute::<GenericArgKindRef<'a, 'static>, GenericArgKindRef<'a, 'db>>(
                result,
            )
        }
    }

    #[inline]
    unsafe fn into_kind(self) -> GenericArgKind<'db> {
        unsafe {
            self.with(
                |ptr| {
                    GenericArgKind::Type(Ty {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    GenericArgKind::Const(Const {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
                |ptr| {
                    GenericArgKind::Lifetime(Region {
                        interned: Interned::from_raw(ptr),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    unsafe fn term_kind<'a>(self) -> TermKindRef<'a, 'db>
    where
        'db: 'a,
    {
        unsafe {
            let result = self.with_term(
                |ptr| TermKindRef::Ty(&(*ptr).0.internee),
                |ptr| TermKindRef::Const(&(*ptr).0.internee),
            );
            std::mem::transmute::<TermKindRef<'a, 'static>, TermKindRef<'a, 'db>>(result)
        }
    }

    #[inline]
    unsafe fn into_term_kind(self) -> TermKind<'db> {
        unsafe {
            self.with_term(
                |ptr| TermKind::Ty(Ty { interned: Interned::from_raw(ptr), _marker: PhantomData }),
                |ptr| {
                    TermKind::Const(Const {
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
                |ptr| {
                    Ty {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    }
                    .into()
                },
                |ptr| {
                    Const {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    }
                    .into()
                },
                |ptr| {
                    Region {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    }
                    .into()
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

impl<'db> From<Ty<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Ty<'db>) -> Self {
        Self(GenericArgImpl::new_ty(unsafe {
            NonNull::new_unchecked(value.interned.into_raw().cast_mut())
        }))
    }
}

impl<'db> From<Const<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Const<'db>) -> Self {
        Self(GenericArgImpl::new_const(unsafe {
            NonNull::new_unchecked(value.interned.into_raw().cast_mut())
        }))
    }
}

impl<'db> From<Region<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Region<'db>) -> Self {
        Self(GenericArgImpl::new_region(unsafe {
            NonNull::new_unchecked(value.interned.into_raw().cast_mut())
        }))
    }
}

impl<'db> From<Term<'db>> for GenericArg<'db> {
    #[inline]
    fn from(value: Term<'db>) -> Self {
        Self(ManuallyDrop::new(value).0)
    }
}

impl<'db> std::fmt::Debug for GenericArg<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            GenericArgKindRef::Type(it) => it.fmt(f),
            GenericArgKindRef::Lifetime(it) => it.fmt(f),
            GenericArgKindRef::Const(it) => it.fmt(f),
        }
    }
}

impl<'db> GenericArg<'db> {
    #[inline]
    pub fn kind(&self) -> GenericArgKindRef<'_, 'db> {
        unsafe { self.0.kind() }
    }

    #[inline]
    pub fn to_kind(&self) -> GenericArgKind<'db> {
        self.clone().into_kind()
    }

    #[inline]
    pub fn into_kind(self) -> GenericArgKind<'db> {
        unsafe { ManuallyDrop::new(self).0.into_kind() }
    }

    #[inline]
    pub fn ty(&self) -> Option<Ty<'db>> {
        unsafe {
            self.0.with(
                |ptr| {
                    Some(Ty {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    })
                },
                |_| None,
                |_| None,
            )
        }
    }

    #[inline]
    pub fn expect_ty(&self) -> Ty<'db> {
        self.ty().unwrap_or_else(|| panic!("Expected ty, got {self:?}"))
    }

    #[inline]
    pub fn konst(&self) -> Option<Const<'db>> {
        unsafe {
            self.0.with(
                |_| None,
                |ptr| {
                    Some(Const {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    })
                },
                |_| None,
            )
        }
    }

    #[inline]
    pub fn region(&self) -> Option<Region<'db>> {
        unsafe {
            self.0.with(
                |_| None,
                |_| None,
                |ptr| {
                    Some(Region {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    pub fn expect_region(&self) -> Region<'db> {
        self.region().unwrap_or_else(|| panic!("Expected a region, got {self:?}"))
    }

    #[inline]
    pub fn to_term(&self) -> Option<Term<'db>> {
        unsafe {
            self.0.with(
                |ptr| {
                    Some(
                        Ty {
                            interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                            _marker: PhantomData,
                        }
                        .into(),
                    )
                },
                |ptr| {
                    Some(
                        Const {
                            interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                            _marker: PhantomData,
                        }
                        .into(),
                    )
                },
                |_| None,
            )
        }
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
            GenericArgKind::Type(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_const(self) -> Option<Const<'db>> {
        match self.into_kind() {
            GenericArgKind::Const(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_region(self) -> Option<Region<'db>> {
        match self.into_kind() {
            GenericArgKind::Lifetime(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_term(self) -> Option<Term<'db>> {
        match self.into_kind() {
            GenericArgKind::Type(it) => Some(it.into()),
            GenericArgKind::Const(it) => Some(it.into()),
            GenericArgKind::Lifetime(_) => None,
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
                |ptr| {
                    Ty {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    }
                    .into()
                },
                |ptr| {
                    Const {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    }
                    .into()
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

impl<'db> From<Ty<'db>> for Term<'db> {
    #[inline]
    fn from(value: Ty<'db>) -> Self {
        Self(GenericArgImpl::new_ty(unsafe {
            NonNull::new_unchecked(value.interned.into_raw().cast_mut())
        }))
    }
}

impl<'db> From<Const<'db>> for Term<'db> {
    #[inline]
    fn from(value: Const<'db>) -> Self {
        Self(GenericArgImpl::new_const(unsafe {
            NonNull::new_unchecked(value.interned.into_raw().cast_mut())
        }))
    }
}

impl<'db> std::fmt::Debug for Term<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            TermKindRef::Ty(it) => it.fmt(f),
            TermKindRef::Const(it) => it.fmt(f),
        }
    }
}

impl<'db> Term<'db> {
    #[inline]
    pub fn kind(&self) -> TermKindRef<'_, 'db> {
        unsafe { self.0.term_kind() }
    }

    #[inline]
    pub fn to_kind(&self) -> TermKind<'db> {
        self.clone().into_kind()
    }

    #[inline]
    pub fn into_kind(self) -> TermKind<'db> {
        unsafe { ManuallyDrop::new(self).0.into_term_kind() }
    }

    #[inline]
    pub fn ty(&self) -> Option<Ty<'db>> {
        unsafe {
            self.0.with_term(
                |ptr| {
                    Some(Ty {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    })
                },
                |_| None,
            )
        }
    }

    #[inline]
    pub fn expect_ty(&self) -> Ty<'db> {
        self.ty().unwrap_or_else(|| panic!("Expected ty, got {self:?}"))
    }

    #[inline]
    pub fn konst(&self) -> Option<Const<'db>> {
        unsafe {
            self.0.with_term(
                |_| None,
                |ptr| {
                    Some(Const {
                        interned: (*ManuallyDrop::new(Interned::from_raw(ptr))).clone(),
                        _marker: PhantomData,
                    })
                },
            )
        }
    }

    #[inline]
    pub fn expect_const(&self) -> Const<'db> {
        self.konst().unwrap_or_else(|| panic!("Expected a const, got {self:?}"))
    }

    pub fn is_trivially_wf(&self) -> bool {
        match self.clone().into_kind() {
            TermKind::Ty(ty) => ty.is_trivially_wf(),
            TermKind::Const(ct) => ct.is_trivially_wf(),
        }
    }

    #[inline]
    pub fn into_type(self) -> Option<Ty<'db>> {
        match self.into_kind() {
            TermKind::Ty(it) => Some(it),
            _ => None,
        }
    }

    #[inline]
    pub fn into_const(self) -> Option<Const<'db>> {
        match self.into_kind() {
            TermKind::Const(it) => Some(it),
            _ => None,
        }
    }
}

impl<'db> IntoKind for GenericArg<'db> {
    type Kind = GenericArgKind<'db>;

    #[inline]
    fn kind(self) -> Self::Kind {
        self.into_kind()
    }
}

impl<'db> IntoKind for Term<'db> {
    type Kind = TermKind<'db>;

    #[inline]
    fn kind(self) -> Self::Kind {
        self.into_kind()
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for GenericArg<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match self.clone().into_kind() {
            GenericArgKind::Lifetime(it) => visitor.visit_region(it),
            GenericArgKind::Type(it) => visitor.visit_ty(it),
            GenericArgKind::Const(it) => visitor.visit_const(it),
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
            GenericArgKind::Type(it) => it.try_fold_with(folder).map(Into::into),
            GenericArgKind::Const(it) => it.try_fold_with(folder).map(Into::into),
            GenericArgKind::Lifetime(it) => it.try_fold_with(folder).map(Into::into),
        }
    }

    #[inline]
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        match self.into_kind() {
            GenericArgKind::Type(it) => it.fold_with(folder).into(),
            GenericArgKind::Const(it) => it.fold_with(folder).into(),
            GenericArgKind::Lifetime(it) => it.fold_with(folder).into(),
        }
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Term<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match self.clone().into_kind() {
            TermKind::Ty(it) => visitor.visit_ty(it),
            TermKind::Const(it) => visitor.visit_const(it),
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
            TermKind::Ty(it) => it.try_fold_with(folder).map(Into::into),
            TermKind::Const(it) => it.try_fold_with(folder).map(Into::into),
        }
    }

    #[inline]
    fn fold_with<F: TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        match self.into_kind() {
            TermKind::Ty(it) => it.fold_with(folder).into(),
            TermKind::Const(it) => it.fold_with(folder).into(),
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
        relation.relate(a.clone(), b.clone())
    }
}

impl<'db> Relate<DbInterner<'db>> for GenericArg<'db> {
    type RelateResult = GenericArg<'db>;

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
        match (a.into_kind(), b.into_kind()) {
            (GenericArgKind::Lifetime(a), GenericArgKind::Lifetime(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            (GenericArgKind::Type(a), GenericArgKind::Type(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            (GenericArgKind::Const(a), GenericArgKind::Const(b)) => {
                relation.relate(a, b).map(Into::into)
            }
            _ => panic!("impossible case reached: can't relate"),
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
        relation.relate(a.clone(), b.clone())
    }
}

impl<'db> Relate<DbInterner<'db>> for Term<'db> {
    type RelateResult = Term<'db>;

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
        match (a.into_kind(), b.into_kind()) {
            (TermKind::Ty(a), TermKind::Ty(b)) => relation.relate(a, b).map(Into::into),
            (TermKind::Const(a), TermKind::Const(b)) => relation.relate(a, b).map(Into::into),
            _ => panic!("impossible case reached: can't relate"),
        }
    }
}

interned_slice!(
    GenericArgsStorage,
    GenericArgs,
    GenericArg<'db>,
    GenericArg<'static>,
    generic_args,
);
impl_foldable_for_interned_slice!(GenericArgs);

impl<'db> rustc_type_ir::inherent::GenericArg<DbInterner<'db>> for GenericArg<'db> {}

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
            Some(default) => default.instantiate(interner, prev),
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
                .map(|default| default.instantiate(interner, prev))
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

    pub fn types(&self) -> impl Iterator<Item = Ty<'db>> {
        self.iter().filter_map(|it| it.ty())
    }

    pub fn consts(&self) -> impl Iterator<Item = Const<'db>> {
        self.iter().filter_map(|it| it.konst())
    }

    pub fn regions(&self) -> impl Iterator<Item = Region<'db>> {
        self.iter().filter_map(|it| it.region())
    }

    pub fn type_at(&self, i: usize) -> Ty<'db> {
        self.as_slice()
            .get(i)
            .and_then(|g| g.ty())
            .unwrap_or_else(|| panic!("expected type: index={i}, args={self:?}"))
    }

    pub fn region_at(&self, i: usize) -> Region<'db> {
        self.as_slice()
            .get(i)
            .and_then(|g| g.region())
            .unwrap_or_else(|| panic!("expected type: index={i}, args={self:?}"))
    }

    pub fn const_at(&self, i: usize) -> Const<'db> {
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
                    .cloned()
                    .chain(std::iter::once(sig.output())),
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
        relation.relate(a.clone(), b.clone())
    }
}

impl<'db> rustc_type_ir::relate::Relate<DbInterner<'db>> for GenericArgs<'db> {
    type RelateResult = GenericArgs<'db>;

    #[inline]
    fn into_relate_result(self) -> Self::RelateResult {
        self
    }

    fn relate<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> RelateResult<'db, Self::RelateResult> {
        relate_args_invariantly(relation, a, b)
    }
}

impl<'db> rustc_type_ir::inherent::GenericArgs<DbInterner<'db>> for GenericArgs<'db> {
    fn as_closure(self) -> ClosureArgs<'db> {
        ClosureArgs { args: self }
    }
    fn as_coroutine(self) -> CoroutineArgs<'db> {
        CoroutineArgs { args: self }
    }
    fn as_coroutine_closure(self) -> CoroutineClosureArgs<'db> {
        CoroutineClosureArgs { args: self }
    }
    fn rebase_onto(
        &self,
        interner: DbInterner<'db>,
        source_def_id: SolverDefId,
        target: &GenericArgs<'db>,
    ) -> GenericArgs<'db> {
        let defs = interner.generics_of(source_def_id);
        interner.mk_args_from_iter(target.iter().chain(self.iter().skip(defs.count())).cloned())
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

    fn type_at(&self, i: usize) -> Ty<'db> {
        self.type_at(i)
    }

    fn region_at(&self, i: usize) -> Region<'db> {
        self.region_at(i)
    }

    fn const_at(&self, i: usize) -> Const<'db> {
        self.const_at(i)
    }

    fn split_closure_args(&self) -> rustc_type_ir::ClosureArgsParts<'_, DbInterner<'db>> {
        match self.as_slice() {
            [parent_args @ .., closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty] => {
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
        &self,
    ) -> rustc_type_ir::CoroutineClosureArgsParts<'_, DbInterner<'db>> {
        match self.as_slice() {
            [
                parent_args @ ..,
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

    fn split_coroutine_args(&self) -> rustc_type_ir::CoroutineArgsParts<'_, DbInterner<'db>> {
        match self.as_slice() {
            [parent_args @ .., kind_ty, resume_ty, yield_ty, return_ty, tupled_upvars_ty] => {
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

    #[inline]
    fn into_const(self) -> Option<Const<'db>> {
        self.into_const()
    }

    fn to_type(&self) -> Option<Ty<'db>> {
        self.ty()
    }

    fn expect_ty(&self) -> Ty<'db> {
        self.expect_ty()
    }

    fn to_const(&self) -> Option<Const<'db>> {
        self.konst()
    }

    fn expect_const(&self) -> Const<'db> {
        self.expect_const()
    }

    fn is_infer(&self) -> bool {
        match self.kind() {
            TermKindRef::Ty(ty) => matches!(ty, TyKind::Infer(InferTy::TyVar(_))),
            TermKindRef::Const(ct) => matches!(ct, ConstKind::Infer(InferConst::Var(_))),
        }
    }

    fn is_error(&self) -> bool {
        match self.kind() {
            TermKindRef::Ty(ty) => matches!(ty, TyKind::Error(..)),
            TermKindRef::Const(ct) => matches!(ct, ConstKind::Error(..)),
        }
    }

    fn to_alias_term(&self) -> Option<rustc_type_ir::AliasTerm<DbInterner<'db>>> {
        match self.kind() {
            TermKindRef::Ty(rustc_type_ir) => match rustc_type_ir {
                TyKind::Alias(_kind, alias_ty) => Some(alias_ty.clone().into()),
                _ => None,
            },
            TermKindRef::Const(ct) => match ct {
                ConstKind::Unevaluated(uv) => Some(uv.clone().into()),
                _ => None,
            },
        }
    }
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
