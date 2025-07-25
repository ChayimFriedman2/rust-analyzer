//! Compute the binary representation of structs, unions and enums

use std::ops::Bound;

use hir_def::AdtId;
use intern::sym;
use triomphe::Arc;

use crate::{
    Substitution, TraitEnvironment,
    db::HirDatabase,
    layout::{Layout, LayoutError},
    next_solver::{DbInterner, mapping::ChalkToNextSolver},
};

pub fn layout_of_adt_query(
    db: &dyn HirDatabase,
    def: AdtId,
    subst: Substitution,
    trait_env: Arc<TraitEnvironment>,
) -> Result<Arc<Layout>, LayoutError> {
    let interner = DbInterner::new_with(db, Some(trait_env.krate), trait_env.block);
    db.layout_of_adt_ns(def, subst.to_nextsolver(interner), trait_env)
}

pub(crate) fn layout_scalar_valid_range(
    db: &dyn HirDatabase,
    def: AdtId,
) -> (Bound<u128>, Bound<u128>) {
    let attrs = db.attrs(def.into());
    let get = |name| {
        let attr = attrs.by_key(name).tt_values();
        for tree in attr {
            if let Some(it) = tree.iter().next_as_view() {
                let text = it.to_string().replace('_', "");
                let (text, base) = match text.as_bytes() {
                    [b'0', b'x', ..] => (&text[2..], 16),
                    [b'0', b'o', ..] => (&text[2..], 8),
                    [b'0', b'b', ..] => (&text[2..], 2),
                    _ => (&*text, 10),
                };

                if let Ok(it) = u128::from_str_radix(text, base) {
                    return Bound::Included(it);
                }
            }
        }
        Bound::Unbounded
    };
    (get(sym::rustc_layout_scalar_valid_range_start), get(sym::rustc_layout_scalar_valid_range_end))
}

pub(crate) fn layout_of_adt_cycle_result(
    _: &dyn HirDatabase,
    _: AdtId,
    _: Substitution,
    _: Arc<TraitEnvironment>,
) -> Result<Arc<Layout>, LayoutError> {
    Err(LayoutError::RecursiveTypeWithoutIndirection)
}
