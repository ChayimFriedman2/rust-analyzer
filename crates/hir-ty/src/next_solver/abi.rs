//! ABI-related things in the next-trait-solver.

use crate::FnAbi;

use super::interner::DbInterner;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Safety {
    Unsafe,
    Safe,
}

impl<'db> rustc_type_ir::inherent::Safety<DbInterner<'db>> for Safety {
    fn safe() -> Self {
        Self::Safe
    }

    fn is_safe(self) -> bool {
        matches!(self, Safety::Safe)
    }

    fn prefix_str(self) -> &'static str {
        match self {
            Self::Unsafe => "unsafe ",
            Self::Safe => "",
        }
    }
}

impl<'db> rustc_type_ir::inherent::Abi<DbInterner<'db>> for FnAbi {
    fn rust() -> Self {
        FnAbi::Rust
    }

    fn is_rust(self) -> bool {
        // TODO: rustc does not consider `RustCall` to be true here, but Chalk does
        matches!(self, FnAbi::Rust | FnAbi::RustCall)
    }
}
