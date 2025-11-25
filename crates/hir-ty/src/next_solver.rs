//! Things relevant to the next trait solver.

pub mod abi;
mod consts;
mod def_id;
pub mod fold;
pub mod fulfill;
mod generic_arg;
pub mod generics;
pub mod infer;
pub(crate) mod inspect;
pub mod interner;
mod ir_print;
mod ir_trait_impls;
pub mod normalize;
pub mod obligation_ctxt;
mod opaques;
pub mod predicate;
mod region;
mod solver;
mod structural_normalize;
mod ty;
pub mod util;

use std::sync::OnceLock;

pub use consts::*;
pub use def_id::*;
pub use generic_arg::*;
pub use interner::*;
pub use opaques::*;
pub use predicate::*;
pub use region::*;
use rustc_type_ir::ir_traits::MyToOwned;
pub use solver::*;
pub use ty::*;

pub use crate::lower::ImplTraitIdx;
pub use rustc_ast_ir::Mutability;

pub type Binder<'db, T> = rustc_type_ir::Binder<DbInterner<'db>, T>;
pub type EarlyBinder<'db, T> = rustc_type_ir::EarlyBinder<DbInterner<'db>, T>;
pub type Canonical<'db, T> = rustc_type_ir::Canonical<DbInterner<'db>, T>;
pub type CanonicalVarValues<'db> = rustc_type_ir::CanonicalVarValues<DbInterner<'db>>;
pub type CanonicalVarKind<'db> = rustc_type_ir::CanonicalVarKind<DbInterner<'db>>;
pub type CanonicalQueryInput<'db, V> = rustc_type_ir::CanonicalQueryInput<DbInterner<'db>, V>;
pub type AliasTy<'db> = rustc_type_ir::AliasTy<DbInterner<'db>>;
pub type FnSig<'db> = rustc_type_ir::FnSig<DbInterner<'db>>;
pub type PolyFnSig<'db> = Binder<'db, rustc_type_ir::FnSig<DbInterner<'db>>>;
pub type TypingMode<'db> = rustc_type_ir::TypingMode<DbInterner<'db>>;
pub type TypeError<'db> = rustc_type_ir::error::TypeError<DbInterner<'db>>;
pub type QueryResult<'db> = rustc_type_ir::solve::QueryResult<DbInterner<'db>>;
pub type FxIndexMap<K, V> = rustc_type_ir::data_structures::IndexMap<K, V>;

pub unsafe trait SameRepr: Sized {
    type Borrowed<'a>
    where
        Self: 'a;
}

pub trait AsBorrowedSlice {
    type Borrowed<'a>
    where
        Self: 'a;

    fn as_borrowed_slice(&self) -> &[Self::Borrowed<'_>];

    fn as_owned_slice<'a>(slice: &'a [Self::Borrowed<'_>]) -> &'a Self;
}

impl<T: SameRepr> AsBorrowedSlice for [T] {
    type Borrowed<'a>
        = T::Borrowed<'a>
    where
        T: 'a;

    #[inline(always)]
    fn as_borrowed_slice(&self) -> &[Self::Borrowed<'_>] {
        unsafe { &*(self as *const [T] as *const [Self::Borrowed<'_>]) }
    }

    #[inline(always)]
    fn as_owned_slice<'a>(slice: &'a [Self::Borrowed<'_>]) -> &'a Self {
        unsafe { &*(slice as *const [Self::Borrowed<'_>] as *const [T]) }
    }
}

pub trait AsOwnedSlice {
    type Owned;

    fn as_owned_slice(&self) -> &[Self::Owned];
}

pub trait IteratorOwnedExt<'db, T> {
    fn owned(self) -> impl Iterator<Item = T>;
}

impl<'db, I: Iterator<Item: MyToOwned<DbInterner<'db>>>>
    IteratorOwnedExt<'db, <I::Item as MyToOwned<DbInterner<'db>>>::Owned> for I
{
    #[inline]
    fn owned(self) -> impl Iterator<Item = <I::Item as MyToOwned<DbInterner<'db>>>::Owned> {
        self.map(|it| it.o())
    }
}

pub struct DefaultTypes<'db> {
    pub usize: Ty<'db>,
    pub u8: Ty<'db>,
    pub u16: Ty<'db>,
    pub u32: Ty<'db>,
    pub u64: Ty<'db>,
    pub u128: Ty<'db>,
    pub isize: Ty<'db>,
    pub i8: Ty<'db>,
    pub i16: Ty<'db>,
    pub i32: Ty<'db>,
    pub i64: Ty<'db>,
    pub i128: Ty<'db>,
    pub f16: Ty<'db>,
    pub f32: Ty<'db>,
    pub f64: Ty<'db>,
    pub f128: Ty<'db>,
    pub unit: Ty<'db>,
    pub bool: Ty<'db>,
    pub char: Ty<'db>,
    pub str: Ty<'db>,
    pub static_str_ref: Ty<'db>,
    pub never: Ty<'db>,
    pub error: Ty<'db>,
}

pub struct DefaultConsts<'db> {
    pub error: Const<'db>,
}

pub struct DefaultRegions<'db> {
    pub error: Region<'db>,
    pub statik: Region<'db>,
    pub erased: Region<'db>,
}

pub struct DefaultEmpty<'db> {
    pub tys: Tys<'db>,
    pub generic_args: GenericArgs<'db>,
    pub bound_var_kinds: BoundVarKinds<'db>,
    pub canonical_vars: CanonicalVars<'db>,
    pub variances: VariancesOf<'db>,
    pub pat_list: PatList<'db>,
    pub predefined_opaques: PredefinedOpaques<'db>,
    pub def_ids: SolverDefIds<'db>,
    pub bound_existential_predicates: BoundExistentialPredicates<'db>,
    pub clauses: Clauses<'db>,
    pub region_assumptions: RegionAssumptions<'db>,
}

pub struct DefaultAny<'db> {
    pub types: DefaultTypes<'db>,
    pub consts: DefaultConsts<'db>,
    pub regions: DefaultRegions<'db>,
    pub empty: DefaultEmpty<'db>,
    pub one_invariant: VariancesOf<'db>,
    pub one_covariant: VariancesOf<'db>,
    /// `for<'env>`
    pub coroutine_captures_by_ref_bound_var_kinds: BoundVarKinds<'db>,
}

impl std::fmt::Debug for DefaultAny<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefaultAny").finish_non_exhaustive()
    }
}

#[inline]
pub fn default_types<'a, 'db>() -> &'a DefaultAny<'db> {
    static TYPES: OnceLock<DefaultAny<'static>> = OnceLock::new();

    let types = TYPES.get_or_init(|| {
        let str = Ty::new(TyKind::Str);
        let statik = Region::new(RegionKind::ReStatic);
        let empty_tys = Tys::new_from_slice(&[]);
        DefaultAny {
            types: DefaultTypes {
                usize: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::Usize)),
                u8: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::U8)),
                u16: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::U16)),
                u32: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::U32)),
                u64: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::U64)),
                u128: Ty::new(TyKind::Uint(rustc_ast_ir::UintTy::U128)),
                isize: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::Isize)),
                i8: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::I8)),
                i16: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::I16)),
                i32: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::I32)),
                i64: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::I64)),
                i128: Ty::new(TyKind::Int(rustc_ast_ir::IntTy::I128)),
                f16: Ty::new(TyKind::Float(rustc_ast_ir::FloatTy::F16)),
                f32: Ty::new(TyKind::Float(rustc_ast_ir::FloatTy::F32)),
                f64: Ty::new(TyKind::Float(rustc_ast_ir::FloatTy::F64)),
                f128: Ty::new(TyKind::Float(rustc_ast_ir::FloatTy::F128)),
                unit: Ty::new(TyKind::Tuple(empty_tys.clone())),
                bool: Ty::new(TyKind::Bool),
                char: Ty::new(TyKind::Char),
                str: str.clone(),
                static_str_ref: Ty::new_imm_ref(statik.clone(), str),
                never: Ty::new(TyKind::Never),
                error: Ty::new(TyKind::Error(ErrorGuaranteed)),
            },
            consts: DefaultConsts { error: Const::new(ConstKind::Error(ErrorGuaranteed)) },
            regions: DefaultRegions {
                error: Region::new(RegionKind::ReError(ErrorGuaranteed)),
                statik,
                erased: Region::new(RegionKind::ReErased),
            },
            empty: DefaultEmpty {
                tys: empty_tys,
                generic_args: GenericArgs::new_from_slice(&[]),
                bound_var_kinds: BoundVarKinds::new_from_slice(&[]),
                canonical_vars: CanonicalVars::new_from_slice(&[]),
                variances: VariancesOf::new_from_slice(&[]),
                pat_list: PatList::new_from_slice(&[]),
                predefined_opaques: PredefinedOpaques::new_from_slice(&[]),
                def_ids: SolverDefIds::new_from_slice(&[]),
                bound_existential_predicates: BoundExistentialPredicates::new_from_slice(&[]),
                clauses: Clauses::new_from_slice(&[]),
                region_assumptions: RegionAssumptions::new_from_slice(&[]),
            },
            one_invariant: VariancesOf::new_from_array([rustc_type_ir::Variance::Invariant]),
            one_covariant: VariancesOf::new_from_array([rustc_type_ir::Variance::Covariant]),
            coroutine_captures_by_ref_bound_var_kinds: BoundVarKinds::new_from_array([
                BoundVarKind::Region(BoundRegionKind::ClosureEnv),
            ]),
        }
    });
    // SAFETY: FIXME
    unsafe { &*std::mem::transmute::<&'static DefaultAny<'static>, &'a DefaultAny<'db>>(types) }
}
