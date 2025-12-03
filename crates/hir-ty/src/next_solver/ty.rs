//! Things related to tys in the next-trait-solver.

use std::{marker::PhantomData, ops::ControlFlow};

use hir_def::{
    AdtId, HasModule, TypeAliasId, TypeParamId,
    hir::generics::{TypeOrConstParamData, TypeParamProvenance},
    lang_item::LangItem,
};
use hir_def::{TraitId, type_ref::Rawness};
use intern::Interned;
use rustc_abi::{Float, Integer, Size};
use rustc_ast_ir::{Mutability, try_visit, visit::VisitorResult};
use rustc_type_ir::{
    AliasTyKind, BoundVar, BoundVarIndexKind, ClosureKind, CollectAndApply, CoroutineArgs,
    CoroutineArgsParts, DebruijnIndex, FlagComputation, Flags, FloatTy, FloatVid, InferTy, IntTy,
    IntVid, Interner, TyVid, TypeFlags, TypeFoldable, TypeSuperFoldable, TypeSuperVisitable,
    TypeVisitable, TypeVisitableExt, TypeVisitor, UintTy, Upcast, WithCachedTypeInfo,
    inherent::{
        AdtDef as _, AsKind, BoundExistentialPredicates as _, BoundVarLike, GenericArgs as _,
        ParamLike, PlaceholderLike, Safety as _, Ty as _,
    },
    relate::{Relate, RelateRef, TypeRelation},
    solve::SizedTraitKind,
    walk::TypeWalker,
};

use crate::{
    db::{HirDatabase, InternedCoroutine},
    lower::GenericPredicates,
    next_solver::{
        AdtDef, AliasTy, Binder, BoundExistentialPredicates, CallableIdWrapper, Clause, ClauseKind,
        ClosureIdWrapper, Const, CoroutineIdWrapper, FnSig, GenericArgKindRef, GenericArgs,
        PolyFnSig, Region, TraitRef, TypeAliasIdWrapper,
        abi::Safety,
        default_types, impl_foldable_for_interned_slice,
        infer::relate::RelateResult,
        util::{CoroutineArgsExt, IntegerTypeExt},
    },
};

use super::{
    BoundVarKind, DbInterner, Placeholder, SolverDefId, interned_slice,
    util::{FloatExt, IntegerExt},
};

pub type SimplifiedType = rustc_type_ir::fast_reject::SimplifiedType<SolverDefId>;
pub type TyKind<'db> = rustc_type_ir::TyKind<DbInterner<'db>>;
pub type FnHeader<'db> = rustc_type_ir::FnHeader<DbInterner<'db>>;

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ty<'db> {
    pub(super) interned: Interned<TyInterned>,
    pub(super) _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(PartialEq, Eq, Hash)]
#[repr(align(4))] // Needed for GenericArg packing.
pub(super) struct TyInterned(pub(super) WithCachedTypeInfo<TyKind<'static>>);

intern::impl_internable!(TyInterned);

impl std::fmt::Debug for TyInterned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.internee.fmt(f)
    }
}

impl<'db> Ty<'db> {
    #[inline]
    pub fn new(kind: TyKind<'db>) -> Self {
        // SAFETY: FIXME
        let kind = unsafe { std::mem::transmute::<TyKind<'db>, TyKind<'static>>(kind) };
        let flags = FlagComputation::for_kind(&kind);
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Ty { interned: Interned::new(TyInterned(cached)), _marker: PhantomData }
    }

    #[inline]
    pub fn inner(&self) -> &WithCachedTypeInfo<TyKind<'db>> {
        unsafe {
            std::mem::transmute::<
                &WithCachedTypeInfo<TyKind<'static>>,
                &WithCachedTypeInfo<TyKind<'db>>,
            >(&self.interned.0)
        }
    }

    #[inline]
    pub fn kind(&self) -> &TyKind<'db> {
        &self.inner().internee
    }

    #[inline]
    pub fn new_placeholder(placeholder: PlaceholderTy) -> Self {
        Ty::new(TyKind::Placeholder(placeholder))
    }

    #[inline]
    pub fn new_infer(infer: InferTy) -> Self {
        Ty::new(TyKind::Infer(infer))
    }

    #[inline]
    pub fn new_int_var(v: IntVid) -> Self {
        Ty::new_infer(InferTy::IntVar(v))
    }

    #[inline]
    pub fn new_float_var(v: FloatVid) -> Self {
        Ty::new_infer(InferTy::FloatVar(v))
    }

    #[inline]
    pub fn new_int(i: IntTy) -> Self {
        let default = default_types();
        let ty = match i {
            IntTy::Isize => &default.types.isize,
            IntTy::I8 => &default.types.i8,
            IntTy::I16 => &default.types.i16,
            IntTy::I32 => &default.types.i32,
            IntTy::I64 => &default.types.i64,
            IntTy::I128 => &default.types.i128,
        };
        ty.clone()
    }

    #[inline]
    pub fn new_uint(ui: UintTy) -> Self {
        let default = default_types();
        let ty = match ui {
            UintTy::Usize => &default.types.usize,
            UintTy::U8 => &default.types.u8,
            UintTy::U16 => &default.types.u16,
            UintTy::U32 => &default.types.u32,
            UintTy::U64 => &default.types.u64,
            UintTy::U128 => &default.types.u128,
        };
        ty.clone()
    }

    #[inline]
    pub fn new_float(f: FloatTy) -> Self {
        let default = default_types();
        let ty = match f {
            FloatTy::F16 => &default.types.f16,
            FloatTy::F32 => &default.types.f32,
            FloatTy::F64 => &default.types.f64,
            FloatTy::F128 => &default.types.f128,
        };
        ty.clone()
    }

    #[inline]
    pub fn new_fresh(n: u32) -> Self {
        Ty::new_infer(InferTy::FreshTy(n))
    }

    #[inline]
    pub fn new_fresh_int(n: u32) -> Self {
        Ty::new_infer(InferTy::FreshIntTy(n))
    }

    #[inline]
    pub fn new_fresh_float(n: u32) -> Self {
        Ty::new_infer(InferTy::FreshFloatTy(n))
    }

    #[inline]
    pub fn new_empty_tuple() -> Self {
        default_types().types.unit.clone()
    }

    #[inline]
    pub fn new_imm_ptr(ty: Ty<'db>) -> Self {
        Ty::new_ptr(ty, Mutability::Not)
    }

    #[inline]
    pub fn new_imm_ref(region: Region<'db>, ty: Ty<'db>) -> Self {
        Ty::new_ref(region, ty, Mutability::Not)
    }

    #[inline]
    pub fn new_unit() -> Self {
        default_types().types.unit.clone()
    }

    #[inline]
    pub fn new_never() -> Self {
        default_types().types.never.clone()
    }

    #[inline]
    pub fn new_bool() -> Self {
        default_types().types.bool.clone()
    }

    #[inline]
    pub fn new_u8() -> Self {
        default_types().types.u8.clone()
    }

    #[inline]
    pub fn new_usize() -> Self {
        default_types().types.usize.clone()
    }

    #[inline]
    pub fn new_var(var: TyVid) -> Self {
        Ty::new(TyKind::Infer(InferTy::TyVar(var)))
    }

    #[inline]
    pub fn new_param(param: ParamTy) -> Self {
        Ty::new(TyKind::Param(param))
    }

    #[inline]
    pub fn new_bound(debruijn: DebruijnIndex, var: BoundTy) -> Self {
        Ty::new(TyKind::Bound(BoundVarIndexKind::Bound(debruijn), var))
    }

    #[inline]
    pub fn new_anon_bound(debruijn: DebruijnIndex, var: BoundVar) -> Self {
        Ty::new(TyKind::Bound(
            BoundVarIndexKind::Bound(debruijn),
            BoundTy { var, kind: BoundTyKind::Anon },
        ))
    }

    #[inline]
    pub fn new_canonical_bound(var: BoundVar) -> Self {
        Ty::new(TyKind::Bound(
            BoundVarIndexKind::Canonical,
            BoundTy { var, kind: BoundTyKind::Anon },
        ))
    }

    #[inline]
    pub fn new_alias(kind: AliasTyKind, alias_ty: AliasTy<'db>) -> Self {
        Ty::new(TyKind::Alias(kind, alias_ty))
    }

    #[inline]
    pub fn new_error() -> Self {
        default_types().types.error.clone()
    }

    #[inline]
    pub fn new_adt(adt_def: AdtDef, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::Adt(adt_def, args))
    }

    #[inline]
    pub fn new_adt_id(interner: DbInterner<'db>, adt_id: AdtId, args: GenericArgs<'db>) -> Self {
        Ty::new_adt(AdtDef::new(adt_id, interner), args)
    }

    #[inline]
    pub fn new_foreign(def_id: TypeAliasId) -> Self {
        Ty::new(TyKind::Foreign(def_id.into()))
    }

    #[inline]
    pub fn new_dynamic(preds: BoundExistentialPredicates<'db>, region: Region<'db>) -> Self {
        Ty::new(TyKind::Dynamic(preds, region))
    }

    #[inline]
    pub fn new_coroutine(def_id: CoroutineIdWrapper, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::Coroutine(def_id, args))
    }

    #[inline]
    pub fn new_coroutine_closure(def_id: CoroutineIdWrapper, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::CoroutineClosure(def_id, args))
    }

    #[inline]
    pub fn new_closure(def_id: ClosureIdWrapper, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::Closure(def_id, args))
    }

    #[inline]
    pub fn new_coroutine_witness(def_id: CoroutineIdWrapper, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::CoroutineWitness(def_id, args))
    }

    #[inline]
    pub fn new_coroutine_witness_for_coroutine(
        def_id: CoroutineIdWrapper,
        coroutine_args: GenericArgs<'db>,
    ) -> Self {
        // HACK: Coroutine witness types are lifetime erased, so they
        // never reference any lifetime args from the coroutine. We erase
        // the regions here since we may get into situations where a
        // coroutine is recursively contained within itself, leading to
        // witness types that differ by region args. This means that
        // cycle detection in fulfillment will not kick in, which leads
        // to unnecessary overflows in async code. See the issue:
        // <https://github.com/rust-lang/rust/issues/145151>.
        let coroutine_args =
            GenericArgs::new_from_iter(coroutine_args.iter().map(|arg| match arg.kind() {
                GenericArgKindRef::Type(_) | GenericArgKindRef::Const(_) => arg.clone(),
                GenericArgKindRef::Lifetime(_) => default_types().regions.erased.clone().into(),
            }));
        Ty::new_coroutine_witness(def_id, coroutine_args)
    }

    #[inline]
    pub fn new_ptr(ty: Self, mutbl: Mutability) -> Self {
        Ty::new(TyKind::RawPtr(ty, mutbl))
    }

    #[inline]
    pub fn new_ref(region: Region<'db>, ty: Self, mutbl: Mutability) -> Self {
        Ty::new(TyKind::Ref(region, ty, mutbl))
    }

    #[inline]
    pub fn new_array_with_const_len(ty: Self, len: Const<'db>) -> Self {
        Ty::new(TyKind::Array(ty, len))
    }

    #[inline]
    pub fn new_slice(ty: Self) -> Self {
        Ty::new(TyKind::Slice(ty))
    }

    #[inline]
    pub fn new_tup(tys: &[Ty<'db>]) -> Self {
        Ty::new(TyKind::Tuple(Tys::new_from_slice(tys)))
    }

    #[inline]
    pub fn new_tup_from_iter<I, T, Static>(iter: I) -> Ty<'db>
    where
        I: IntoIterator<Item = T>,
        T: crate::next_solver::interner::IntoStatic<Static = Static>,
        Static: ::intern::CollectAndIntern<TysStorage, Ty<'static>>,
        Static::Output:
            for<'a> crate::next_solver::interner::FromStatic<WithLifetime<'a> = Tys<'a>>,
    {
        Ty::new(TyKind::Tuple(Tys::new_from_iter(iter)))
    }

    #[inline]
    pub fn new_fn_def(def_id: CallableIdWrapper, args: GenericArgs<'db>) -> Self {
        Ty::new(TyKind::FnDef(def_id, args))
    }

    #[inline]
    pub fn new_fn_ptr(sig: Binder<'db, FnSig<'db>>) -> Self {
        let (sig_tys, header) = sig.split();
        Ty::new(TyKind::FnPtr(sig_tys, header))
    }

    #[inline]
    pub fn new_pat(ty: Self, pat: <DbInterner<'db> as Interner>::Pat) -> Self {
        Ty::new(TyKind::Pat(ty, pat))
    }

    #[inline]
    pub fn new_unsafe_binder(ty: Binder<'db, Ty<'db>>) -> Self {
        Ty::new(TyKind::UnsafeBinder(ty.into()))
    }

    #[inline]
    pub fn new_opaque(def_id: SolverDefId, args: GenericArgs<'db>) -> Self {
        Ty::new_alias(
            AliasTyKind::Opaque,
            AliasTy::new_from_args(DbInterner::conjure(), def_id, args),
        )
    }

    /// Replace infer vars with errors.
    ///
    /// This needs to be called for every type that may contain infer vars and is yielded to outside inference,
    /// as things other than inference do not expect to see infer vars.
    pub fn replace_infer_with_error(self, interner: DbInterner<'db>) -> Ty<'db> {
        self.fold_with(&mut crate::next_solver::infer::resolve::ReplaceInferWithError::new(
            interner,
        ))
    }

    pub fn from_builtin_type(ty: hir_def::builtin_type::BuiltinType) -> Ty<'db> {
        let types = default_types();
        let ty = match ty {
            hir_def::builtin_type::BuiltinType::Char => &types.types.char,
            hir_def::builtin_type::BuiltinType::Bool => &types.types.bool,
            hir_def::builtin_type::BuiltinType::Str => &types.types.str,
            hir_def::builtin_type::BuiltinType::Int(int) => match int {
                hir_def::builtin_type::BuiltinInt::Isize => &types.types.isize,
                hir_def::builtin_type::BuiltinInt::I8 => &types.types.i8,
                hir_def::builtin_type::BuiltinInt::I16 => &types.types.i16,
                hir_def::builtin_type::BuiltinInt::I32 => &types.types.i32,
                hir_def::builtin_type::BuiltinInt::I64 => &types.types.i64,
                hir_def::builtin_type::BuiltinInt::I128 => &types.types.i128,
            },
            hir_def::builtin_type::BuiltinType::Uint(uint) => match uint {
                hir_def::builtin_type::BuiltinUint::Usize => &types.types.usize,
                hir_def::builtin_type::BuiltinUint::U8 => &types.types.u8,
                hir_def::builtin_type::BuiltinUint::U16 => &types.types.u16,
                hir_def::builtin_type::BuiltinUint::U32 => &types.types.u32,
                hir_def::builtin_type::BuiltinUint::U64 => &types.types.u64,
                hir_def::builtin_type::BuiltinUint::U128 => &types.types.u128,
            },
            hir_def::builtin_type::BuiltinType::Float(float) => match float {
                hir_def::builtin_type::BuiltinFloat::F16 => &types.types.f16,
                hir_def::builtin_type::BuiltinFloat::F32 => &types.types.f32,
                hir_def::builtin_type::BuiltinFloat::F64 => &types.types.f64,
                hir_def::builtin_type::BuiltinFloat::F128 => &types.types.f128,
            },
        };
        ty.clone()
    }

    /// Returns the `Size` for primitive types (bool, uint, int, char, float).
    pub fn primitive_size(&self, interner: DbInterner<'db>) -> Size {
        match *self.kind() {
            TyKind::Bool => Size::from_bytes(1),
            TyKind::Char => Size::from_bytes(4),
            TyKind::Int(ity) => Integer::from_int_ty(&interner, ity).size(),
            TyKind::Uint(uty) => Integer::from_uint_ty(&interner, uty).size(),
            TyKind::Float(fty) => Float::from_float_ty(fty).size(),
            _ => panic!("non primitive type"),
        }
    }

    pub fn int_size_and_signed(&self, interner: DbInterner<'db>) -> (Size, bool) {
        match *self.kind() {
            TyKind::Int(ity) => (Integer::from_int_ty(&interner, ity).size(), true),
            TyKind::Uint(uty) => (Integer::from_uint_ty(&interner, uty).size(), false),
            _ => panic!("non integer discriminant"),
        }
    }

    pub fn walk(self) -> TypeWalker<DbInterner<'db>> {
        TypeWalker::new(self.into())
    }

    /// Fast path helper for testing if a type is `Sized` or `MetaSized`.
    ///
    /// Returning true means the type is known to implement the sizedness trait. Returning `false`
    /// means nothing -- could be sized, might not be.
    ///
    /// Note that we could never rely on the fact that a type such as `[_]` is trivially `!Sized`
    /// because we could be in a type environment with a bound such as `[_]: Copy`. A function with
    /// such a bound obviously never can be called, but that doesn't mean it shouldn't typecheck.
    /// This is why this method doesn't return `Option<bool>`.
    #[tracing::instrument(level = "debug")]
    pub fn has_trivial_sizedness(&self, sizedness: SizedTraitKind) -> bool {
        match self.kind() {
            TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
            | TyKind::Uint(_)
            | TyKind::Int(_)
            | TyKind::Bool
            | TyKind::Float(_)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::UnsafeBinder(_)
            | TyKind::RawPtr(..)
            | TyKind::Char
            | TyKind::Ref(..)
            | TyKind::Coroutine(..)
            | TyKind::CoroutineWitness(..)
            | TyKind::Array(..)
            | TyKind::Pat(..)
            | TyKind::Closure(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::Never
            | TyKind::Error(_) => true,

            TyKind::Str | TyKind::Slice(_) | TyKind::Dynamic(_, _) => match sizedness {
                SizedTraitKind::Sized => false,
                SizedTraitKind::MetaSized => true,
            },

            TyKind::Foreign(..) => match sizedness {
                SizedTraitKind::Sized | SizedTraitKind::MetaSized => false,
            },

            TyKind::Tuple(tys) => tys.last().is_none_or(|ty| ty.has_trivial_sizedness(sizedness)),

            TyKind::Adt(def, args) => {
                def.sizedness_constraint(DbInterner::conjure(), sizedness).is_none_or(|ty| {
                    ty.instantiate(DbInterner::conjure(), args).has_trivial_sizedness(sizedness)
                })
            }

            TyKind::Alias(..) | TyKind::Param(_) | TyKind::Placeholder(..) | TyKind::Bound(..) => {
                false
            }

            TyKind::Infer(InferTy::TyVar(_)) => false,

            TyKind::Infer(
                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_),
            ) => {
                panic!("`has_trivial_sizedness` applied to unexpected type: {self:?}")
            }
        }
    }

    /// Fast path helper for primitives which are always `Copy` and which
    /// have a side-effect-free `Clone` impl.
    ///
    /// Returning true means the type is known to be pure and `Copy+Clone`.
    /// Returning `false` means nothing -- could be `Copy`, might not be.
    ///
    /// This is mostly useful for optimizations, as these are the types
    /// on which we can replace cloning with dereferencing.
    pub fn is_trivially_pure_clone_copy(&self) -> bool {
        match self.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Never => true,

            // These aren't even `Clone`
            TyKind::Str | TyKind::Slice(..) | TyKind::Foreign(..) | TyKind::Dynamic(..) => false,

            TyKind::Infer(InferTy::FloatVar(_) | InferTy::IntVar(_))
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..) => true,

            // ZST which can't be named are fine.
            TyKind::FnDef(..) => true,

            TyKind::Array(element_ty, _len) => element_ty.is_trivially_pure_clone_copy(),

            // A 100-tuple isn't "trivial", so doing this only for reasonable sizes.
            TyKind::Tuple(field_tys) => {
                field_tys.len() <= 3 && field_tys.iter().all(Self::is_trivially_pure_clone_copy)
            }

            TyKind::Pat(ty, _) => ty.is_trivially_pure_clone_copy(),

            // Sometimes traits aren't implemented for every ABI or arity,
            // because we can't be generic over everything yet.
            TyKind::FnPtr(..) => false,

            // Definitely absolutely not copy.
            TyKind::Ref(_, _, Mutability::Mut) => false,

            // The standard library has a blanket Copy impl for shared references and raw pointers,
            // for all unsized types.
            TyKind::Ref(_, _, Mutability::Not) | TyKind::RawPtr(..) => true,

            TyKind::Coroutine(..) | TyKind::CoroutineWitness(..) => false,

            // Might be, but not "trivial" so just giving the safe answer.
            TyKind::Adt(..) | TyKind::Closure(..) | TyKind::CoroutineClosure(..) => false,

            TyKind::UnsafeBinder(_) => false,

            // Needs normalization or revealing to determine, so no is the safe answer.
            TyKind::Alias(..) => false,

            TyKind::Param(..)
            | TyKind::Placeholder(..)
            | TyKind::Bound(..)
            | TyKind::Infer(..)
            | TyKind::Error(..) => false,
        }
    }

    pub fn is_trivially_wf(&self) -> bool {
        match self.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never
            | TyKind::Param(_)
            | TyKind::Placeholder(_)
            | TyKind::Bound(..) => true,

            TyKind::Slice(ty) => {
                ty.is_trivially_wf() && ty.has_trivial_sizedness(SizedTraitKind::Sized)
            }
            TyKind::RawPtr(ty, _) => ty.is_trivially_wf(),

            TyKind::FnPtr(sig_tys, _) => {
                sig_tys.skip_binder_ref().inputs_and_output.iter().all(|ty| ty.is_trivially_wf())
            }
            TyKind::Ref(_, ty, _) => ty.is_global() && ty.is_trivially_wf(),

            TyKind::Infer(infer) => match infer {
                InferTy::TyVar(_) => false,
                InferTy::IntVar(_) | InferTy::FloatVar(_) => true,
                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_) => true,
            },

            TyKind::Adt(_, _)
            | TyKind::Tuple(_)
            | TyKind::Array(..)
            | TyKind::Foreign(_)
            | TyKind::Pat(_, _)
            | TyKind::FnDef(..)
            | TyKind::UnsafeBinder(..)
            | TyKind::Dynamic(..)
            | TyKind::Closure(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::Coroutine(..)
            | TyKind::CoroutineWitness(..)
            | TyKind::Alias(..)
            | TyKind::Error(_) => false,
        }
    }

    #[inline]
    pub fn is_never(&self) -> bool {
        matches!(self.kind(), TyKind::Never)
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        matches!(self.kind(), TyKind::Bool)
    }

    /// A scalar type is one that denotes an atomic datum, with no sub-components.
    /// (A RawPtr is scalar because it represents a non-managed pointer, so its
    /// contents are abstract to rustc.)
    #[inline]
    pub fn is_scalar(&self) -> bool {
        matches!(
            self.kind(),
            TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Float(_)
                | TyKind::Uint(_)
                | TyKind::FnDef(..)
                | TyKind::FnPtr(..)
                | TyKind::RawPtr(_, _)
                | TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
        )
    }

    #[inline]
    pub fn is_infer(&self) -> bool {
        matches!(self.kind(), TyKind::Infer(..))
    }

    #[inline]
    pub fn is_numeric(&self) -> bool {
        self.is_integral() || self.is_floating_point()
    }

    #[inline]
    pub fn is_str(&self) -> bool {
        matches!(self.kind(), TyKind::Str)
    }

    #[inline]
    pub fn is_unit(&self) -> bool {
        matches!(self.kind(), TyKind::Tuple(tys) if tys.as_slice().is_empty())
    }

    #[inline]
    pub fn is_raw_ptr(&self) -> bool {
        matches!(self.kind(), TyKind::RawPtr(..))
    }

    #[inline]
    pub fn is_array(&self) -> bool {
        matches!(self.kind(), TyKind::Array(..))
    }

    #[inline]
    pub fn is_slice(&self) -> bool {
        matches!(self.kind(), TyKind::Slice(..))
    }

    #[inline]
    pub fn is_union(&self) -> bool {
        self.as_adt().is_some_and(|(adt, _)| matches!(adt, AdtId::UnionId(_)))
    }

    #[inline]
    pub fn is_ty_var(&self) -> bool {
        matches!(self.kind(), TyKind::Infer(InferTy::TyVar(_)))
    }

    #[inline]
    pub fn is_ty_error(&self) -> bool {
        matches!(self.kind(), TyKind::Error(_))
    }

    #[inline]
    pub fn is_floating_point(&self) -> bool {
        matches!(self.kind(), TyKind::Float(_) | TyKind::Infer(InferTy::FloatVar(_)))
    }

    #[inline]
    pub fn is_integral(&self) -> bool {
        matches!(self.kind(), TyKind::Infer(InferTy::IntVar(_)) | TyKind::Int(_) | TyKind::Uint(_))
    }

    #[inline]
    pub fn is_fn_ptr(&self) -> bool {
        matches!(self.kind(), TyKind::FnPtr(..))
    }

    #[inline]
    pub fn fn_sig(&self) -> Binder<'db, FnSig<'db>> {
        self.kind().fn_sig(DbInterner::conjure())
    }

    #[inline]
    pub fn is_known_rigid(&self) -> bool {
        self.kind().is_known_rigid()
    }

    pub fn boxed_ty(&self) -> Option<Ty<'db>> {
        match self.kind() {
            TyKind::Adt(adt_def, args) if adt_def.is_box() => Some(args.type_at(0)),
            _ => None,
        }
    }

    #[inline]
    pub fn as_adt(&self) -> Option<(AdtId, GenericArgs<'db>)> {
        match self.kind() {
            TyKind::Adt(adt_def, args) => Some((adt_def.def_id().0, args.clone())),
            _ => None,
        }
    }

    #[inline]
    pub fn ty_vid(&self) -> Option<TyVid> {
        match self.kind() {
            TyKind::Infer(rustc_type_ir::TyVar(vid)) => Some(*vid),
            _ => None,
        }
    }

    /// Given a `fn` type, returns an equivalent `unsafe fn` type;
    /// that is, a `fn` type that is equivalent in every way for being
    /// unsafe.
    pub fn safe_to_unsafe_fn_ty(sig: PolyFnSig<'db>) -> Ty<'db> {
        assert!(sig.safety().is_safe());
        Ty::new_fn_ptr(sig.map_bound(|sig| FnSig { safety: Safety::Unsafe, ..sig }))
    }

    /// Returns the type of `*ty`.
    ///
    /// The parameter `explicit` indicates if this is an *explicit* dereference.
    /// Some types -- notably raw ptrs -- can only be dereferenced explicitly.
    pub fn builtin_deref(&self, explicit: bool) -> Option<Ty<'db>> {
        match self.kind() {
            TyKind::Adt(adt, substs) if adt.is_box() => Some(substs.type_at(0)),
            TyKind::Ref(_, ty, _) => Some(ty.clone()),
            TyKind::RawPtr(ty, _) if explicit => Some(ty.clone()),
            _ => None,
        }
    }

    /// Whether the type contains some non-lifetime, aka. type or const, error type.
    pub fn references_non_lt_error(&self) -> bool {
        references_non_lt_error(&self)
    }

    pub fn callable_sig(&self, interner: DbInterner<'db>) -> Option<Binder<'db, FnSig<'db>>> {
        match self.kind() {
            TyKind::FnDef(callable, args) => {
                Some(interner.fn_sig(*callable).instantiate(interner, args))
            }
            TyKind::FnPtr(sig, hdr) => Some(sig.clone().with(*hdr)),
            TyKind::Closure(_, closure_args) => {
                Some(closure_args.clone().signature_unclosure(Safety::Safe))
            }
            TyKind::CoroutineClosure(coroutine_id, args) => {
                let args = args.clone().as_coroutine_closure();
                Some(args.coroutine_closure_sig().map_bound(|sig| {
                    let unit_ty = default_types().types.unit.clone();
                    let return_ty = Ty::new_coroutine(
                        *coroutine_id,
                        CoroutineArgs::new(
                            interner,
                            CoroutineArgsParts {
                                parent_args: args.parent_args(),
                                kind_ty: unit_ty.clone(),
                                resume_ty: unit_ty.clone(),
                                yield_ty: unit_ty.clone(),
                                return_ty: sig.return_ty,
                                // FIXME: Deduce this from the coroutine closure's upvars.
                                tupled_upvars_ty: unit_ty,
                            },
                        )
                        .args,
                    );
                    FnSig {
                        inputs_and_output: Tys::new_from_iter(
                            sig.tupled_inputs_ty
                                .tuple_fields()
                                .iter()
                                .cloned()
                                .chain(std::iter::once(return_ty)),
                        ),
                        c_variadic: sig.c_variadic,
                        safety: sig.safety,
                        abi: sig.abi,
                    }
                }))
            }
            _ => None,
        }
    }

    pub fn as_reference(&self) -> Option<(Ty<'db>, Region<'db>, Mutability)> {
        match self.kind() {
            TyKind::Ref(region, ty, mutability) => Some((ty.clone(), region.clone(), *mutability)),
            _ => None,
        }
    }

    pub fn as_reference_or_ptr(&self) -> Option<(Ty<'db>, Rawness, Mutability)> {
        match self.kind() {
            TyKind::Ref(_, ty, mutability) => Some((ty.clone(), Rawness::Ref, *mutability)),
            TyKind::RawPtr(ty, mutability) => Some((ty.clone(), Rawness::RawPtr, *mutability)),
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<Tys<'db>> {
        match self.kind() {
            TyKind::Tuple(tys) => Some(tys.clone()),
            _ => None,
        }
    }

    pub fn dyn_trait(&self) -> Option<TraitId> {
        let TyKind::Dynamic(bounds, _) = self.kind() else { return None };
        Some(bounds.principal_def_id()?.0)
    }

    pub fn strip_references(&self) -> &Ty<'db> {
        let mut t = self;
        while let TyKind::Ref(_lifetime, ty, _mutability) = t.kind() {
            t = ty;
        }
        t
    }

    pub fn strip_reference(&self) -> Ty<'db> {
        self.as_reference().map_or_else(|| self.clone(), |(ty, _, _)| ty)
    }

    pub fn as_builtin(&self) -> Option<hir_def::builtin_type::BuiltinType> {
        let builtin = match self.kind() {
            TyKind::Char => hir_def::builtin_type::BuiltinType::Char,
            TyKind::Bool => hir_def::builtin_type::BuiltinType::Bool,
            TyKind::Str => hir_def::builtin_type::BuiltinType::Str,
            TyKind::Int(int) => hir_def::builtin_type::BuiltinType::Int(match int {
                rustc_type_ir::IntTy::Isize => hir_def::builtin_type::BuiltinInt::Isize,
                rustc_type_ir::IntTy::I8 => hir_def::builtin_type::BuiltinInt::I8,
                rustc_type_ir::IntTy::I16 => hir_def::builtin_type::BuiltinInt::I16,
                rustc_type_ir::IntTy::I32 => hir_def::builtin_type::BuiltinInt::I32,
                rustc_type_ir::IntTy::I64 => hir_def::builtin_type::BuiltinInt::I64,
                rustc_type_ir::IntTy::I128 => hir_def::builtin_type::BuiltinInt::I128,
            }),
            TyKind::Uint(uint) => hir_def::builtin_type::BuiltinType::Uint(match uint {
                rustc_type_ir::UintTy::Usize => hir_def::builtin_type::BuiltinUint::Usize,
                rustc_type_ir::UintTy::U8 => hir_def::builtin_type::BuiltinUint::U8,
                rustc_type_ir::UintTy::U16 => hir_def::builtin_type::BuiltinUint::U16,
                rustc_type_ir::UintTy::U32 => hir_def::builtin_type::BuiltinUint::U32,
                rustc_type_ir::UintTy::U64 => hir_def::builtin_type::BuiltinUint::U64,
                rustc_type_ir::UintTy::U128 => hir_def::builtin_type::BuiltinUint::U128,
            }),
            TyKind::Float(float) => hir_def::builtin_type::BuiltinType::Float(match float {
                rustc_type_ir::FloatTy::F16 => hir_def::builtin_type::BuiltinFloat::F16,
                rustc_type_ir::FloatTy::F32 => hir_def::builtin_type::BuiltinFloat::F32,
                rustc_type_ir::FloatTy::F64 => hir_def::builtin_type::BuiltinFloat::F64,
                rustc_type_ir::FloatTy::F128 => hir_def::builtin_type::BuiltinFloat::F128,
            }),
            _ => return None,
        };
        Some(builtin)
    }

    // FIXME: Should this be here?
    pub fn impl_trait_bounds(&self, db: &'db dyn HirDatabase) -> Option<Vec<Clause<'db>>> {
        let interner = DbInterner::new_with(db, None, None);

        match self.kind() {
            TyKind::Alias(AliasTyKind::Opaque, opaque_ty) => Some(
                opaque_ty
                    .def_id
                    .expect_opaque_ty()
                    .predicates(db)
                    .iter_instantiated_cloned(interner, opaque_ty.args.as_slice())
                    .collect(),
            ),
            TyKind::Param(param) => {
                // FIXME: We shouldn't use `param.id` here.
                let generic_params = db.generic_params(param.id.parent());
                let param_data = &generic_params[param.id.local_id()];
                match param_data {
                    TypeOrConstParamData::TypeParamData(p) => match p.provenance {
                        TypeParamProvenance::ArgumentImplTrait => {
                            let predicates = GenericPredicates::query_all(db, param.id.parent())
                                .iter_identity_cloned()
                                .filter(|wc| match wc.kind_skip_binder() {
                                    ClauseKind::Trait(tr) => tr.self_ty() == *self,
                                    ClauseKind::Projection(pred) => pred.self_ty() == *self,
                                    ClauseKind::TypeOutlives(pred) => pred.0 == *self,
                                    _ => false,
                                })
                                .collect::<Vec<_>>();

                            Some(predicates)
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            TyKind::Coroutine(coroutine_id, _args) => {
                let InternedCoroutine(owner, _) = coroutine_id.0.loc(db);
                let krate = owner.module(db).krate();
                if let Some(future_trait) = LangItem::Future.resolve_trait(db, krate) {
                    // This is only used by type walking.
                    // Parameters will be walked outside, and projection predicate is not used.
                    // So just provide the Future trait.
                    let impl_bound = TraitRef::new(interner, future_trait.into(), [self.clone()])
                        .upcast(interner);
                    Some(vec![impl_bound])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// FIXME: Get rid of this, it's not a good abstraction
    pub fn equals_ctor(&self, other: Ty<'db>) -> bool {
        match (self.kind(), other.kind()) {
            (TyKind::Adt(adt, ..), TyKind::Adt(adt2, ..)) => adt.def_id() == adt2.def_id(),
            (TyKind::Slice(_), TyKind::Slice(_)) | (TyKind::Array(_, _), TyKind::Array(_, _)) => {
                true
            }
            (TyKind::FnDef(def_id, ..), TyKind::FnDef(def_id2, ..)) => def_id == def_id2,
            (TyKind::Alias(_, alias, ..), TyKind::Alias(_, alias2)) => {
                alias.def_id == alias2.def_id
            }
            (TyKind::Foreign(ty_id, ..), TyKind::Foreign(ty_id2, ..)) => ty_id == ty_id2,
            (TyKind::Closure(id1, _), TyKind::Closure(id2, _)) => id1 == id2,
            (TyKind::Ref(.., mutability), TyKind::Ref(.., mutability2))
            | (TyKind::RawPtr(.., mutability), TyKind::RawPtr(.., mutability2)) => {
                mutability == mutability2
            }
            (TyKind::FnPtr(sig, hdr), TyKind::FnPtr(sig2, hdr2)) => sig == sig2 && hdr == hdr2,
            (TyKind::Tuple(tys), TyKind::Tuple(tys2)) => tys.len() == tys2.len(),
            (TyKind::Str, TyKind::Str)
            | (TyKind::Never, TyKind::Never)
            | (TyKind::Char, TyKind::Char)
            | (TyKind::Bool, TyKind::Bool) => true,
            (TyKind::Int(int), TyKind::Int(int2)) => int == int2,
            (TyKind::Float(float), TyKind::Float(float2)) => float == float2,
            _ => false,
        }
    }
}

pub fn references_non_lt_error<'db, T: TypeVisitableExt<DbInterner<'db>>>(t: &T) -> bool {
    t.references_error() && t.visit_with(&mut ReferencesNonLifetimeError).is_break()
}

struct ReferencesNonLifetimeError;

impl<'db> TypeVisitor<DbInterner<'db>> for ReferencesNonLifetimeError {
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, ty: Ty<'db>) -> Self::Result {
        if ty.is_ty_error() { ControlFlow::Break(()) } else { ty.super_visit_with(self) }
    }

    fn visit_const(&mut self, c: Const<'db>) -> Self::Result {
        if c.is_ct_error() { ControlFlow::Break(()) } else { c.super_visit_with(self) }
    }
}

impl<'db> std::fmt::Debug for Ty<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind().fmt(f)
    }
}

impl<'db> AsKind for Ty<'db> {
    type Kind = TyKind<'db>;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        self.kind()
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for Ty<'db> {
    #[inline]
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        visitor.visit_ty(self.clone())
    }
}

impl<'db> TypeSuperVisitable<DbInterner<'db>> for Ty<'db> {
    fn super_visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        match (*self).kind() {
            TyKind::RawPtr(ty, _mutbl) => ty.visit_with(visitor),
            TyKind::Array(typ, sz) => {
                try_visit!(typ.visit_with(visitor));
                sz.visit_with(visitor)
            }
            TyKind::Slice(typ) => typ.visit_with(visitor),
            TyKind::Adt(_, args) => args.visit_with(visitor),
            TyKind::Dynamic(trait_ty, reg) => {
                try_visit!(trait_ty.visit_with(visitor));
                reg.visit_with(visitor)
            }
            TyKind::Tuple(ts) => ts.visit_with(visitor),
            TyKind::FnDef(_, args) => args.visit_with(visitor),
            TyKind::FnPtr(sig_tys, _) => sig_tys.visit_with(visitor),
            TyKind::UnsafeBinder(f) => f.visit_with(visitor),
            TyKind::Ref(r, ty, _) => {
                try_visit!(r.visit_with(visitor));
                ty.visit_with(visitor)
            }
            TyKind::Coroutine(_did, args) => args.visit_with(visitor),
            TyKind::CoroutineWitness(_did, args) => args.visit_with(visitor),
            TyKind::Closure(_did, args) => args.visit_with(visitor),
            TyKind::CoroutineClosure(_did, args) => args.visit_with(visitor),
            TyKind::Alias(_, data) => data.visit_with(visitor),

            TyKind::Pat(ty, pat) => {
                try_visit!(ty.visit_with(visitor));
                pat.visit_with(visitor)
            }

            TyKind::Error(guar) => guar.visit_with(visitor),

            TyKind::Bool
            | TyKind::Char
            | TyKind::Str
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Infer(_)
            | TyKind::Bound(..)
            | TyKind::Placeholder(..)
            | TyKind::Param(..)
            | TyKind::Never
            | TyKind::Foreign(..) => V::Result::output(),
        }
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for Ty<'db> {
    fn try_fold_with<F: rustc_type_ir::FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_ty(self)
    }
    fn fold_with<F: rustc_type_ir::TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        folder.fold_ty(self)
    }
}

impl<'db> TypeSuperFoldable<DbInterner<'db>> for Ty<'db> {
    fn try_super_fold_with<F: rustc_type_ir::FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let kind = match self.kind() {
            TyKind::RawPtr(ty, mutbl) => TyKind::RawPtr(ty.clone().try_fold_with(folder)?, *mutbl),
            TyKind::Array(typ, sz) => {
                TyKind::Array(typ.clone().try_fold_with(folder)?, sz.clone().try_fold_with(folder)?)
            }
            TyKind::Slice(typ) => TyKind::Slice(typ.clone().try_fold_with(folder)?),
            TyKind::Adt(tid, args) => TyKind::Adt(*tid, args.clone().try_fold_with(folder)?),
            TyKind::Dynamic(trait_ty, region) => TyKind::Dynamic(
                trait_ty.clone().try_fold_with(folder)?,
                region.clone().try_fold_with(folder)?,
            ),
            TyKind::Tuple(ts) => TyKind::Tuple(ts.clone().try_fold_with(folder)?),
            TyKind::FnDef(def_id, args) => {
                TyKind::FnDef(*def_id, args.clone().try_fold_with(folder)?)
            }
            TyKind::FnPtr(sig_tys, hdr) => {
                TyKind::FnPtr(sig_tys.clone().try_fold_with(folder)?, *hdr)
            }
            TyKind::UnsafeBinder(f) => TyKind::UnsafeBinder(f.clone().try_fold_with(folder)?),
            TyKind::Ref(r, ty, mutbl) => TyKind::Ref(
                r.clone().try_fold_with(folder)?,
                ty.clone().try_fold_with(folder)?,
                *mutbl,
            ),
            TyKind::Coroutine(did, args) => {
                TyKind::Coroutine(*did, args.clone().try_fold_with(folder)?)
            }
            TyKind::CoroutineWitness(did, args) => {
                TyKind::CoroutineWitness(*did, args.clone().try_fold_with(folder)?)
            }
            TyKind::Closure(did, args) => {
                TyKind::Closure(*did, args.clone().try_fold_with(folder)?)
            }
            TyKind::CoroutineClosure(did, args) => {
                TyKind::CoroutineClosure(*did, args.clone().try_fold_with(folder)?)
            }
            TyKind::Alias(kind, data) => TyKind::Alias(*kind, data.clone().try_fold_with(folder)?),
            TyKind::Pat(ty, pat) => {
                TyKind::Pat(ty.clone().try_fold_with(folder)?, pat.try_fold_with(folder)?)
            }

            TyKind::Bool
            | TyKind::Char
            | TyKind::Str
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Error(_)
            | TyKind::Infer(_)
            | TyKind::Param(..)
            | TyKind::Bound(..)
            | TyKind::Placeholder(..)
            | TyKind::Never
            | TyKind::Foreign(..) => return Ok(self),
        };

        Ok(if *self.kind() == kind { self } else { Ty::new(kind) })
    }
    fn super_fold_with<F: rustc_type_ir::TypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Self {
        let kind = match self.kind() {
            TyKind::RawPtr(ty, mutbl) => TyKind::RawPtr(ty.clone().fold_with(folder), *mutbl),
            TyKind::Array(typ, sz) => {
                TyKind::Array(typ.clone().fold_with(folder), sz.clone().fold_with(folder))
            }
            TyKind::Slice(typ) => TyKind::Slice(typ.clone().fold_with(folder)),
            TyKind::Adt(tid, args) => TyKind::Adt(*tid, args.clone().fold_with(folder)),
            TyKind::Dynamic(trait_ty, region) => TyKind::Dynamic(
                trait_ty.clone().fold_with(folder),
                region.clone().fold_with(folder),
            ),
            TyKind::Tuple(ts) => TyKind::Tuple(ts.clone().fold_with(folder)),
            TyKind::FnDef(def_id, args) => TyKind::FnDef(*def_id, args.clone().fold_with(folder)),
            TyKind::FnPtr(sig_tys, hdr) => TyKind::FnPtr(sig_tys.clone().fold_with(folder), *hdr),
            TyKind::UnsafeBinder(f) => TyKind::UnsafeBinder(f.clone().fold_with(folder)),
            TyKind::Ref(r, ty, mutbl) => {
                TyKind::Ref(r.clone().fold_with(folder), ty.clone().fold_with(folder), *mutbl)
            }
            TyKind::Coroutine(did, args) => TyKind::Coroutine(*did, args.clone().fold_with(folder)),
            TyKind::CoroutineWitness(did, args) => {
                TyKind::CoroutineWitness(*did, args.clone().fold_with(folder))
            }
            TyKind::Closure(did, args) => TyKind::Closure(*did, args.clone().fold_with(folder)),
            TyKind::CoroutineClosure(did, args) => {
                TyKind::CoroutineClosure(*did, args.clone().fold_with(folder))
            }
            TyKind::Alias(kind, data) => TyKind::Alias(*kind, data.clone().fold_with(folder)),
            TyKind::Pat(ty, pat) => {
                TyKind::Pat(ty.clone().fold_with(folder), pat.fold_with(folder))
            }

            TyKind::Bool
            | TyKind::Char
            | TyKind::Str
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Error(_)
            | TyKind::Infer(_)
            | TyKind::Param(..)
            | TyKind::Bound(..)
            | TyKind::Placeholder(..)
            | TyKind::Never
            | TyKind::Foreign(..) => return self,
        };

        if *self.kind() == kind { self } else { Ty::new(kind) }
    }
}

impl<'db> RelateRef<DbInterner<'db>> for Ty<'db> {
    #[inline]
    fn relate_ref<R: TypeRelation<DbInterner<'db>>>(
        relation: &mut R,
        a: &Self,
        b: &Self,
    ) -> RelateResult<'db, Self> {
        relation.relate(a.clone(), b.clone())
    }
}

impl<'db> Relate<DbInterner<'db>> for Ty<'db> {
    type RelateResult = Ty<'db>;

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
        relation.tys(a, b)
    }
}

impl<'db> Flags for Ty<'db> {
    #[inline]
    fn flags(&self) -> TypeFlags {
        self.inner().flags
    }

    #[inline]
    fn outer_exclusive_binder(&self) -> DebruijnIndex {
        self.inner().outer_exclusive_binder
    }
}

impl<'db> rustc_type_ir::inherent::Ty<DbInterner<'db>> for Ty<'db> {
    fn new_unit(_interner: DbInterner<'db>) -> Self {
        Ty::new_unit()
    }

    fn new_bool(_interner: DbInterner<'db>) -> Self {
        Ty::new_bool()
    }

    fn new_u8(_interner: DbInterner<'db>) -> Self {
        Ty::new_u8()
    }

    fn new_usize(_interner: DbInterner<'db>) -> Self {
        Ty::new_usize()
    }

    fn new_infer(_interner: DbInterner<'db>, var: InferTy) -> Self {
        Ty::new_infer(var)
    }

    fn new_var(_interner: DbInterner<'db>, var: TyVid) -> Self {
        Ty::new_var(var)
    }

    fn new_param(_interner: DbInterner<'db>, param: ParamTy) -> Self {
        Ty::new_param(param)
    }

    fn new_placeholder(_interner: DbInterner<'db>, param: PlaceholderTy) -> Self {
        Ty::new_placeholder(param)
    }

    fn new_bound(_interner: DbInterner<'db>, debruijn: DebruijnIndex, var: BoundTy) -> Self {
        Ty::new_bound(debruijn, var)
    }

    fn new_anon_bound(_interner: DbInterner<'db>, debruijn: DebruijnIndex, var: BoundVar) -> Self {
        Ty::new_anon_bound(debruijn, var)
    }

    fn new_canonical_bound(_interner: DbInterner<'db>, var: BoundVar) -> Self {
        Ty::new_canonical_bound(var)
    }

    fn new_alias(_interner: DbInterner<'db>, kind: AliasTyKind, alias_ty: AliasTy<'db>) -> Self {
        Ty::new_alias(kind, alias_ty)
    }

    fn new_error(_interner: DbInterner<'db>, _guar: ErrorGuaranteed) -> Self {
        Ty::new_error()
    }

    fn new_adt(_interner: DbInterner<'db>, adt_def: AdtDef, args: GenericArgs<'db>) -> Self {
        Ty::new_adt(adt_def, args)
    }

    fn new_foreign(_interner: DbInterner<'db>, def_id: TypeAliasIdWrapper) -> Self {
        Ty::new_foreign(def_id.0)
    }

    fn new_dynamic(
        _interner: DbInterner<'db>,
        preds: BoundExistentialPredicates<'db>,
        region: Region<'db>,
    ) -> Self {
        Ty::new_dynamic(preds, region)
    }

    fn new_coroutine(
        _interner: DbInterner<'db>,
        def_id: CoroutineIdWrapper,
        args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_coroutine(def_id, args)
    }

    fn new_coroutine_closure(
        _interner: DbInterner<'db>,
        def_id: CoroutineIdWrapper,
        args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_coroutine_closure(def_id, args)
    }

    fn new_closure(
        _interner: DbInterner<'db>,
        def_id: ClosureIdWrapper,
        args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_closure(def_id, args)
    }

    fn new_coroutine_witness(
        _interner: DbInterner<'db>,
        def_id: CoroutineIdWrapper,
        args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_coroutine_witness(def_id, args)
    }

    fn new_coroutine_witness_for_coroutine(
        _interner: DbInterner<'db>,
        def_id: CoroutineIdWrapper,
        coroutine_args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_coroutine_witness_for_coroutine(def_id, coroutine_args)
    }

    fn new_ptr(_interner: DbInterner<'db>, ty: Self, mutbl: Mutability) -> Self {
        Ty::new_ptr(ty, mutbl)
    }

    fn new_ref(
        _interner: DbInterner<'db>,
        region: Region<'db>,
        ty: Self,
        mutbl: Mutability,
    ) -> Self {
        Ty::new_ref(region, ty, mutbl)
    }

    fn new_array_with_const_len(_interner: DbInterner<'db>, ty: Self, len: Const<'db>) -> Self {
        Ty::new_array_with_const_len(ty, len)
    }

    fn new_slice(_interner: DbInterner<'db>, ty: Self) -> Self {
        Ty::new_slice(ty)
    }

    fn new_tup(_interner: DbInterner<'db>, tys: &[Ty<'db>]) -> Self {
        Ty::new_tup(tys)
    }

    fn new_tup_from_iter<It, T>(_interner: DbInterner<'db>, iter: It) -> T::Output
    where
        It: Iterator<Item = T>,
        T: CollectAndApply<Self, Self>,
    {
        CollectAndApply::collect_and_apply(iter, |tys| Ty::new_tup(tys))
    }

    fn new_fn_def(
        _interner: DbInterner<'db>,
        def_id: CallableIdWrapper,
        args: GenericArgs<'db>,
    ) -> Self {
        Ty::new_fn_def(def_id, args)
    }

    fn new_fn_ptr(_interner: DbInterner<'db>, sig: Binder<'db, FnSig<'db>>) -> Self {
        Ty::new_fn_ptr(sig)
    }

    fn new_pat(
        _interner: DbInterner<'db>,
        ty: Self,
        pat: <DbInterner<'db> as Interner>::Pat,
    ) -> Self {
        Ty::new_pat(ty, pat)
    }

    fn new_unsafe_binder(_interner: DbInterner<'db>, ty: Binder<'db, Ty<'db>>) -> Self {
        Ty::new_unsafe_binder(ty)
    }

    fn from_closure_kind(_interner: DbInterner<'db>, kind: rustc_type_ir::ClosureKind) -> Self {
        let default_types = default_types();
        let ty = match kind {
            ClosureKind::Fn => &default_types.types.i8,
            ClosureKind::FnMut => &default_types.types.i16,
            ClosureKind::FnOnce => &default_types.types.i32,
        };
        ty.clone()
    }

    fn from_coroutine_closure_kind(
        _interner: DbInterner<'db>,
        kind: rustc_type_ir::ClosureKind,
    ) -> Self {
        let default_types = default_types();
        let ty = match kind {
            ClosureKind::Fn | ClosureKind::FnMut => &default_types.types.i16,
            ClosureKind::FnOnce => &default_types.types.i32,
        };
        ty.clone()
    }

    #[inline]
    fn tuple_fields(&self) -> Tys<'db> {
        match self.kind() {
            TyKind::Tuple(args) => args.clone(),
            _ => panic!("tuple_fields called on non-tuple: {self:?}"),
        }
    }

    fn to_opt_closure_kind(&self) -> Option<rustc_type_ir::ClosureKind> {
        match self.kind() {
            TyKind::Int(int_ty) => match int_ty {
                IntTy::I8 => Some(ClosureKind::Fn),
                IntTy::I16 => Some(ClosureKind::FnMut),
                IntTy::I32 => Some(ClosureKind::FnOnce),
                _ => unreachable!("cannot convert type `{:?}` to a closure kind", self),
            },

            // "Bound" types appear in canonical queries when the
            // closure type is not yet known, and `Placeholder` and `Param`
            // may be encountered in generic `AsyncFnKindHelper` goals.
            TyKind::Bound(..) | TyKind::Placeholder(_) | TyKind::Param(_) | TyKind::Infer(_) => {
                None
            }

            TyKind::Error(_) => Some(ClosureKind::Fn),

            _ => unreachable!("cannot convert type `{:?}` to a closure kind", self),
        }
    }

    fn has_unsafe_fields(&self) -> bool {
        false
    }

    fn discriminant_ty(&self, interner: DbInterner<'db>) -> Ty<'db> {
        match self.kind() {
            TyKind::Adt(adt, _) if adt.is_enum() => adt.repr().discr_type().to_ty(),
            TyKind::Coroutine(_, args) => args.clone().as_coroutine().discr_ty(),

            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Infer(InferTy::TyVar(_)) => {
                /*
                let assoc_items = tcx.associated_item_def_ids(
                    tcx.require_lang_item(hir::LangItem::DiscriminantKind, None),
                );
                TyKind::new_projection_from_args(tcx, assoc_items[0], tcx.mk_args(&[self.into()]))
                */
                unimplemented!()
            }

            TyKind::Pat(ty, _) => ty.discriminant_ty(interner),

            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Adt(..)
            | TyKind::Foreign(_)
            | TyKind::Str
            | TyKind::Array(..)
            | TyKind::Slice(_)
            | TyKind::RawPtr(_, _)
            | TyKind::Ref(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::Dynamic(..)
            | TyKind::Closure(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::CoroutineWitness(..)
            | TyKind::Never
            | TyKind::Tuple(_)
            | TyKind::Error(_)
            | TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => Ty::new_u8(),

            TyKind::Bound(..)
            | TyKind::Placeholder(_)
            | TyKind::Infer(
                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_),
            ) => {
                panic!(
                    "`dself.iter().map(|v| v.try_fold_with(folder)).collect::<Result<_, _>>()?iscriminant_ty` applied to unexpected type: {self:?}"
                )
            }
            TyKind::UnsafeBinder(..) => unimplemented!(),
        }
    }
}

interned_slice!(TysStorage, Tys, Ty<'db>, Ty<'static>, tys);
impl_foldable_for_interned_slice!(Tys);

impl<'db> Tys<'db> {
    pub fn inputs(&self) -> &[Ty<'db>] {
        self.as_slice().split_last().unwrap().1
    }

    pub fn output(&self) -> Ty<'db> {
        self.as_slice().split_last().unwrap().0.clone()
    }
}

impl<'db> rustc_type_ir::inherent::Tys<DbInterner<'db>> for Tys<'db> {
    fn inputs(&self) -> &[Ty<'db>] {
        self.inputs()
    }

    fn output(&self) -> Ty<'db> {
        self.output()
    }
}

pub type PlaceholderTy = Placeholder<BoundTy>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ParamTy {
    // FIXME: I'm not pleased with this. Ideally a `Param` should only know its index - the defining item
    // is known from the `EarlyBinder`. This should also be beneficial for memory usage. But code currently
    // assumes it can get the definition from `Param` alone - so that's what we got.
    pub id: TypeParamId,
    pub index: u32,
}

impl ParamTy {
    #[inline]
    pub fn to_ty<'db>(self) -> Ty<'db> {
        Ty::new_param(self)
    }
}

impl std::fmt::Debug for ParamTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.index)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoundTy {
    pub var: BoundVar,
    // FIXME: This is for diagnostics in rustc, do we really need it?
    pub kind: BoundTyKind,
}

impl std::fmt::Debug for BoundTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            BoundTyKind::Anon => write!(f, "{:?}", self.var),
            BoundTyKind::Param(def_id) => write!(f, "{def_id:?}"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoundTyKind {
    Anon,
    Param(SolverDefId),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ErrorGuaranteed;

impl<'db> TypeVisitable<DbInterner<'db>> for ErrorGuaranteed {
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        visitor.visit_error(*self)
    }
}

impl<'db> TypeFoldable<DbInterner<'db>> for ErrorGuaranteed {
    fn try_fold_with<F: rustc_type_ir::FallibleTypeFolder<DbInterner<'db>>>(
        self,
        _folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
    fn fold_with<F: rustc_type_ir::TypeFolder<DbInterner<'db>>>(self, _folder: &mut F) -> Self {
        self
    }
}

impl ParamLike for ParamTy {
    fn index(self) -> u32 {
        self.index
    }
}

impl<'db> BoundVarLike<DbInterner<'db>> for BoundTy {
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_ty())
    }
}

impl<'db> PlaceholderLike<DbInterner<'db>> for PlaceholderTy {
    type Bound = BoundTy;

    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, bound: BoundTy) -> Self {
        Placeholder { universe: ui, bound }
    }

    fn new_anon(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundTy { var, kind: BoundTyKind::Anon } }
    }
}
