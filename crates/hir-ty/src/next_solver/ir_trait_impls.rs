use rustc_type_ir::{
    Interner,
    ir_traits::{MyToOwned, as_owned_kind, as_ref, reborrow},
};

use crate::DbInterner;

macro_rules! impl_reborrow {
    ( [] $( $name:ident )* ) => {
        $(
            impl<'a, 'db> reborrow::$name<'a, DbInterner<'db>>
                for <DbInterner<'db> as Interner>::$name<'a>
            where
                'db: 'a,
            {
                #[inline(always)]
                fn reborrow<'b>(self) -> <DbInterner<'db> as Interner>::$name<'b>
                where
                    'a: 'b,
                {
                    self
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_reborrowable!([] impl_reborrow);

macro_rules! impl_as_ref {
    ( [] $( $owned:ident $borrowed:ident )* ) => {
        $(
            impl<'db> as_ref::$owned<DbInterner<'db>>
                for <DbInterner<'db> as Interner>::$owned
            {
                #[inline(always)]
                fn r(&self) -> <DbInterner<'db> as Interner>::$borrowed<'_> {
                    self.r()
                }
            }

            impl<'a, 'db> MyToOwned<DbInterner<'db>> for <DbInterner<'db> as Interner>::$borrowed<'a>
            where
                'db: 'a,
            {
                type Owned = <DbInterner<'db> as Interner>::$owned;
                #[inline]
                fn o(self) -> <DbInterner<'db> as Interner>::$owned {
                    self.o()
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_owned_borrowed_pair!([] impl_as_ref);

macro_rules! impl_as_owned_kind {
    ( [] $( $name:ident = $kind:ident ),* $(,)? ) => {
        $(
            impl<'db> as_owned_kind::$name<DbInterner<'db>> for <DbInterner<'db> as Interner>::$name {
                #[inline(always)]
                fn kind(&self) -> rustc_type_ir::$kind<'_, DbInterner<'db>> {
                    (*self).kind()
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_as_owned_kind!([] impl_as_owned_kind);
