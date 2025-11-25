//! Interning of single values.

use std::{
    fmt::{self, Debug, Display},
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    mem::ManuallyDrop,
    ops::Deref,
    ptr::{self, NonNull},
    sync::OnceLock,
};

use dashmap::{DashMap, SharedValue};
use hashbrown::raw::RawTable;
use rustc_hash::FxHasher;
use triomphe::{Arc, ArcBorrow};

type InternMap<T> = DashMap<Arc<T>, (), BuildHasherDefault<FxHasher>>;
type Guard<T> = dashmap::RwLockWriteGuard<'static, RawTable<(Arc<T>, SharedValue<()>)>>;

pub struct Interned<T: Internable> {
    ptr: NonNull<T>,
}

unsafe impl<T: Send + Sync + Internable> Send for Interned<T> {}
unsafe impl<T: Send + Sync + Internable> Sync for Interned<T> {}

impl<T: Internable> Interned<T> {
    #[inline]
    pub fn new(obj: T) -> Self {
        let storage = T::storage().get();
        let (mut shard, hash) = Self::select(storage, &obj);
        // Atomically,
        // - check if `obj` is already in the map
        //   - if so, clone its `Arc` and return it
        //   - if not, box it up, insert it, and return a clone
        // This needs to be atomic (locking the shard) to avoid races with other thread, which could
        // insert the same object between us looking it up and inserting it.
        let bucket = match shard.find_or_find_insert_slot(
            hash,
            |(other, _)| **other == obj,
            |(x, _)| Self::hash(storage, x),
        ) {
            Ok(bucket) => bucket,
            // SAFETY: The slot came from `find_or_find_insert_slot()`, and the table wasn't modified since then.
            Err(insert_slot) => unsafe {
                shard.insert_in_slot(hash, insert_slot, (Arc::new(obj), SharedValue::new(())))
            },
        };
        // SAFETY: We just retrieved/inserted this bucket.
        unsafe {
            Self {
                ptr: NonNull::new_unchecked(Arc::into_raw(bucket.as_ref().0.clone()).cast_mut()),
            }
        }
    }

    #[inline]
    fn select(storage: &'static InternMap<T>, obj: &T) -> (Guard<T>, u64) {
        let hash = Self::hash(storage, obj);
        let shard_idx = storage.determine_shard(hash as usize);
        let shard = &storage.shards()[shard_idx];
        (shard.write(), hash)
    }

    #[inline]
    fn hash(storage: &'static InternMap<T>, obj: &T) -> u64 {
        storage.hasher().hash_one(obj)
    }

    #[inline]
    fn arc(&self) -> ManuallyDrop<Arc<T>> {
        unsafe { ManuallyDrop::new(Arc::from_raw(self.ptr.as_ptr())) }
    }

    #[inline]
    pub fn into_raw(self) -> *const T {
        let this = ManuallyDrop::new(self);
        this.ptr.as_ptr()
    }

    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Self { ptr: unsafe { NonNull::new_unchecked(ptr.cast_mut()) } }
    }

    #[inline(always)]
    pub fn r<'a>(&'a self) -> InternedRef<'a, T> {
        InternedRef { arc: unsafe { ArcBorrow::from_ptr(self.ptr.as_ptr()) } }
    }
}

impl<T: Internable> Drop for Interned<T> {
    #[inline]
    fn drop(&mut self) {
        // When the last `Ref` is dropped, remove the object from the global map.
        if Arc::count(&self.arc()) == 2 {
            // Only `self` and the global map point to the object.

            self.drop_slow();
        }
    }
}

impl<T: Internable> Interned<T> {
    #[cold]
    fn drop_slow(&mut self) {
        let storage = T::storage().get();
        let (mut shard, hash) = Self::select(storage, &self.arc());

        if Arc::count(&self.arc()) != 2 {
            // Another thread has interned another copy
            return;
        }

        shard.remove_entry(hash, |(other, _)| **other == **self);

        // Shrink the backing storage if the shard is less than 50% occupied.
        if shard.len() * 2 < shard.capacity() {
            let len = shard.len();
            shard.shrink_to(len, |(x, _)| Self::hash(storage, x));
        }
    }
}

/// Compares interned `Ref`s using pointer equality.
impl<T: Internable> PartialEq for Interned<T> {
    // NOTE: No `?Sized` because `ptr_eq` doesn't work right with trait objects.

    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T: Internable> Eq for Interned<T> {}

impl<T: Internable> Hash for Interned<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.ptr.as_ptr().addr())
    }
}

impl<T: Internable> AsRef<T> for Interned<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: Internable> Deref for Interned<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: Internable> Clone for Interned<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            ptr: unsafe { NonNull::new_unchecked(Arc::into_raw((*self.arc()).clone()).cast_mut()) },
        }
    }
}

impl<T: Debug + Internable> Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Debug>::fmt(&**self, f)
    }
}

impl<T: Display + Internable> Display for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Display>::fmt(&**self, f)
    }
}

#[repr(transparent)]
pub struct InternedRef<'a, T> {
    arc: ArcBorrow<'a, T>,
}

impl<'a, T: Internable> InternedRef<'a, T> {
    #[inline]
    pub fn as_raw(self) -> *const T {
        ptr::from_ref(&*self.arc)
    }

    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Self { arc: unsafe { ArcBorrow::from_ptr(ptr) } }
    }

    #[inline]
    pub fn o(self) -> Interned<T> {
        Interned {
            ptr: unsafe { NonNull::new_unchecked(Arc::into_raw(self.arc.clone_arc()).cast_mut()) },
        }
    }

    #[inline]
    pub fn get(self) -> &'a T {
        self.arc.get()
    }
}

impl<T> Clone for InternedRef<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for InternedRef<'_, T> {}

impl<T: Hash> Hash for InternedRef<'_, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr = ptr::from_ref::<T>(&*self.arc);
        state.write_usize(ptr.addr());
    }
}

impl<T: PartialEq> PartialEq for InternedRef<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ArcBorrow::ptr_eq(&self.arc, &other.arc)
    }
}

impl<T: Eq> Eq for InternedRef<'_, T> {}

impl<T> Deref for InternedRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &*self.arc
    }
}

impl<T: Debug> Debug for InternedRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.arc).fmt(f)
    }
}

impl<T: Display> Display for InternedRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.arc).fmt(f)
    }
}

pub struct InternStorage<T: ?Sized> {
    map: OnceLock<InternMap<T>>,
}

#[allow(
    clippy::new_without_default,
    reason = "this a const fn, so it can't be default yet. See <https://github.com/rust-lang/rust/issues/63065>"
)]
impl<T: ?Sized> InternStorage<T> {
    pub const fn new() -> Self {
        Self { map: OnceLock::new() }
    }
}

impl<T: Internable + ?Sized> InternStorage<T> {
    fn get(&self) -> &InternMap<T> {
        self.map.get_or_init(DashMap::default)
    }
}

pub trait Internable: Hash + Eq + 'static {
    fn storage() -> &'static InternStorage<Self>;
}

/// Implements `Internable` for a given list of types, making them usable with `Interned`.
#[macro_export]
#[doc(hidden)]
macro_rules! _impl_internable {
    ( $($t:ty),+ $(,)? ) => { $(
        impl $crate::Internable for $t {
            fn storage() -> &'static $crate::InternStorage<Self> {
                static STORAGE: $crate::InternStorage<$t> = $crate::InternStorage::new();
                &STORAGE
            }
        }
    )+ };
}
pub use crate::_impl_internable as impl_internable;

#[cfg(test)]
mod tests {
    use crate::Interned;

    crate::impl_internable!(String);

    #[test]
    fn it_works() {
        let a = Interned::new("abc".to_owned());
        let b = Interned::new("abc".to_owned());
        assert_eq!(a, b);
        assert_eq!(*a, "abc");
        assert_eq!(*b, "abc");
        let c = a.clone();
        assert_eq!(*c, "abc");
        assert_eq!(b, c);
        let a_ref = a.r();
        let b_ref = b.r();
        assert_eq!(a_ref, b_ref);
        assert_eq!(b_ref.o(), c);
        assert_eq!(*a_ref, "abc");
        drop(a);
        drop(b);
        drop(c);
    }
}
