//! Things related to opaques in the next-trait-solver.

use std::marker::PhantomData;

use intern::Interned;
use rustc_ast_ir::try_visit;
use rustc_type_ir::{TypeVisitable, TypeVisitor};

use crate::next_solver::impl_foldable_for_interned_slice;

use super::{DbInterner, SolverDefId, Ty, interned_slice};

pub type OpaqueTypeKey<'db> = rustc_type_ir::OpaqueTypeKey<DbInterner<'db>>;

type PredefinedOpaque<'db> = (OpaqueTypeKey<'db>, Ty<'db>);
interned_slice!(
    PredefinedOpaquesStorage,
    PredefinedOpaques,
    PredefinedOpaque<'db>,
    PredefinedOpaque<'static>,
    predefined_opaques,
);
impl_foldable_for_interned_slice!(PredefinedOpaques);

pub type ExternalConstraintsData<'db> =
    rustc_type_ir::solve::ExternalConstraintsData<DbInterner<'db>>;

interned_slice!(SolverDefIdsStorage, SolverDefIds, SolverDefId, SolverDefId, def_ids);
impl_foldable_for_interned_slice!(SolverDefIds);

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExternalConstraints<'db> {
    pub(super) interned: Interned<ExternalConstraintsInterned>,
    pub(super) _marker: PhantomData<fn() -> &'db ()>,
}

#[derive(PartialEq, Eq, Hash)]
pub(super) struct ExternalConstraintsInterned(ExternalConstraintsData<'static>);

intern::impl_internable!(ExternalConstraintsInterned);

impl std::fmt::Debug for ExternalConstraintsInterned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'db> ExternalConstraints<'db> {
    #[inline]
    pub fn new(mut data: ExternalConstraintsData<'db>) -> Self {
        let ExternalConstraintsData {
            region_constraints,
            opaque_types,
            normalization_nested_goals,
        } = &mut data;
        region_constraints.shrink_to_fit();
        opaque_types.shrink_to_fit();
        normalization_nested_goals.0.shrink_to_fit();

        // SAFETY: FIXME
        let data = unsafe {
            std::mem::transmute::<ExternalConstraintsData<'db>, ExternalConstraintsData<'static>>(
                data,
            )
        };
        ExternalConstraints {
            interned: Interned::new(ExternalConstraintsInterned(data)),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn inner(&self) -> &ExternalConstraintsData<'db> {
        unsafe {
            std::mem::transmute::<&ExternalConstraintsData<'static>, &ExternalConstraintsData<'db>>(
                &self.interned.0,
            )
        }
    }
}

impl<'db> std::ops::Deref for ExternalConstraints<'db> {
    type Target = ExternalConstraintsData<'db>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner()
    }
}

impl<'db> std::fmt::Debug for ExternalConstraints<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner().fmt(f)
    }
}

impl<'db> TypeVisitable<DbInterner<'db>> for ExternalConstraints<'db> {
    fn visit_with<V: TypeVisitor<DbInterner<'db>>>(&self, visitor: &mut V) -> V::Result {
        try_visit!(self.region_constraints.visit_with(visitor));
        try_visit!(self.opaque_types.visit_with(visitor));
        self.normalization_nested_goals.visit_with(visitor)
    }
}

impl<'db> rustc_type_ir::TypeFoldable<DbInterner<'db>> for ExternalConstraints<'db> {
    fn try_fold_with<F: rustc_type_ir::FallibleTypeFolder<DbInterner<'db>>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(ExternalConstraints::new(ExternalConstraintsData {
            region_constraints: self.region_constraints.clone().try_fold_with(folder)?,
            opaque_types: self
                .opaque_types
                .iter()
                .cloned()
                .map(|opaque| opaque.try_fold_with(folder))
                .collect::<Result<_, F::Error>>()?,
            normalization_nested_goals: self
                .normalization_nested_goals
                .clone()
                .try_fold_with(folder)?,
        }))
    }
    fn fold_with<F: rustc_type_ir::TypeFolder<DbInterner<'db>>>(self, folder: &mut F) -> Self {
        ExternalConstraints::new(ExternalConstraintsData {
            region_constraints: self.region_constraints.clone().fold_with(folder),
            opaque_types: self
                .opaque_types
                .iter()
                .cloned()
                .map(|opaque| opaque.fold_with(folder))
                .collect(),
            normalization_nested_goals: self.normalization_nested_goals.clone().fold_with(folder),
        })
    }
}
