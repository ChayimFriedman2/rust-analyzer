//! Interning of slices, potentially with a header.

use std::{
    borrow::Borrow,
    ffi::c_void,
    fmt::{self, Debug},
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::{self, NonNull},
    sync::OnceLock,
};

use dashmap::{DashMap, SharedValue};
use hashbrown::raw::RawTable;
use rustc_hash::FxHasher;
use smallvec::SmallVec;
use triomphe::{HeaderSlice, HeaderWithLength, ThinArc};

type InternMap<T> = DashMap<
    ThinArc<<T as SliceInternable>::Header, <T as SliceInternable>::SliceType>,
    (),
    BuildHasherDefault<FxHasher>,
>;
type Guard<T> = dashmap::RwLockWriteGuard<
    'static,
    RawTable<(
        ThinArc<<T as SliceInternable>::Header, <T as SliceInternable>::SliceType>,
        SharedValue<()>,
    )>,
>;
type Pointee<T> = HeaderSlice<
    HeaderWithLength<<T as SliceInternable>::Header>,
    [<T as SliceInternable>::SliceType],
>;

pub struct InternedSlice<T: SliceInternable> {
    arc: ThinArc<T::Header, T::SliceType>,
}

impl<T: SliceInternable> InternedSlice<T> {
    #[inline]
    fn new(
        header: T::Header,
        slice: impl Borrow<[T::SliceType]>
        + IntoIterator<Item = T::SliceType, IntoIter: ExactSizeIterator>,
    ) -> Self {
        let storage = T::storage().get();
        let (mut shard, hash) = Self::select(storage, &header, slice.borrow());
        // Atomically,
        // - check if `obj` is already in the map
        //   - if so, clone its `Arc` and return it
        //   - if not, box it up, insert it, and return a clone
        // This needs to be atomic (locking the shard) to avoid races with other thread, which could
        // insert the same object between us looking it up and inserting it.
        let bucket = match shard.find_or_find_insert_slot(
            hash,
            |(other, _)| other.header.header == header && other.slice == *slice.borrow(),
            |(x, _)| storage.hasher().hash_one(x),
        ) {
            Ok(bucket) => bucket,
            // SAFETY: The slot came from `find_or_find_insert_slot()`, and the table wasn't modified since then.
            Err(insert_slot) => unsafe {
                shard.insert_in_slot(
                    hash,
                    insert_slot,
                    (
                        ThinArc::from_header_and_iter(header, slice.into_iter()),
                        SharedValue::new(()),
                    ),
                )
            },
        };
        // SAFETY: We just retrieved/inserted this bucket.
        unsafe { Self { arc: bucket.as_ref().0.clone() } }
    }

    #[inline]
    pub fn from_header_and_slice(header: T::Header, slice: &[T::SliceType]) -> Self
    where
        T::SliceType: Clone,
    {
        return Self::new(header, Iter(slice));

        struct Iter<'a, T>(&'a [T]);

        impl<'a, T: Clone> IntoIterator for Iter<'a, T> {
            type IntoIter = std::iter::Cloned<std::slice::Iter<'a, T>>;
            type Item = T;
            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                self.0.iter().cloned()
            }
        }

        impl<T> Borrow<[T]> for Iter<'_, T> {
            #[inline]
            fn borrow(&self) -> &[T] {
                self.0
            }
        }
    }

    #[inline]
    unsafe fn from_header_and_slice_assume_owned(
        header: T::Header,
        slice: &mut [ManuallyDrop<T::SliceType>],
    ) -> Self {
        return Self::new(header, IntoIter(slice));

        struct IntoIter<'a, T>(&'a mut [ManuallyDrop<T>]);

        impl<'a, T> IntoIterator for IntoIter<'a, T> {
            type IntoIter = Iter<'a, T>;
            type Item = T;
            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                let this = ManuallyDrop::new(self);
                Iter(unsafe { &*ptr::from_ref::<[ManuallyDrop<T>]>(this.0) }.iter())
            }
        }

        impl<T> Borrow<[T]> for IntoIter<'_, T> {
            #[inline]
            fn borrow(&self) -> &[T] {
                unsafe { &*(self.0 as *const [ManuallyDrop<T>] as *const [T]) }
            }
        }

        impl<T> Drop for IntoIter<'_, T> {
            #[inline]
            fn drop(&mut self) {
                // Item already interned, need to free the memory.
                unsafe {
                    (self.0 as *mut [ManuallyDrop<T>] as *mut [T]).drop_in_place();
                }
            }
        }

        struct Iter<'a, T>(std::slice::Iter<'a, ManuallyDrop<T>>);

        impl<T> Iterator for Iter<'_, T> {
            type Item = T;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next().map(|item| unsafe { ptr::from_ref::<T>(&**item).read() })
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
        }

        impl<T> ExactSizeIterator for Iter<'_, T> {
            #[inline]
            fn len(&self) -> usize {
                self.0.len()
            }
        }
    }

    #[inline]
    pub fn from_header_and_vec(header: T::Header, vec: Vec<T::SliceType>) -> Self {
        Self::new(header, vec)
    }

    #[inline]
    pub fn from_header_and_smallvec<const N: usize>(
        header: T::Header,
        vec: SmallVec<[T::SliceType; N]>,
    ) -> Self {
        Self::new(header, vec)
    }

    #[inline]
    pub fn from_header_and_array<const N: usize>(
        header: T::Header,
        array: [T::SliceType; N],
    ) -> Self {
        Self::new(header, array)
    }

    #[inline]
    pub fn from_header_and_iter(
        header: T::Header,
        iter: impl IntoIterator<Item = T::SliceType>,
    ) -> Self {
        Self::from_header_and_vec(header, iter.into_iter().collect())
    }

    #[inline]
    fn select(
        storage: &'static InternMap<T>,
        header: &T::Header,
        slice: &[T::SliceType],
    ) -> (Guard<T>, u64) {
        let hash = Self::hash(storage, header, slice);
        let shard_idx = storage.determine_shard(hash as usize);
        let shard = &storage.shards()[shard_idx];
        (shard.write(), hash)
    }

    #[inline]
    fn hash(storage: &'static InternMap<T>, header: &T::Header, slice: &[T::SliceType]) -> u64 {
        storage.hasher().hash_one(HeaderSlice {
            header: HeaderWithLength { header, length: slice.len() },
            slice,
        })
    }

    #[inline(always)]
    fn ptr(&self) -> *const c_void {
        unsafe { ptr::from_ref(&self.arc).read().into_raw() }
    }

    #[inline(always)]
    pub fn r(&self) -> InternedSliceRef<'_, T> {
        InternedSliceRef {
            ptr: unsafe { NonNull::new_unchecked(self.ptr().cast_mut()) },
            _marker: PhantomData,
        }
    }
}

impl<T: SliceInternable> Drop for InternedSlice<T> {
    #[inline]
    fn drop(&mut self) {
        // When the last `Ref` is dropped, remove the object from the global map.
        if ThinArc::strong_count(&self.arc) == 2 {
            // Only `self` and the global map point to the object.

            self.drop_slow();
        }
    }
}

impl<T: SliceInternable> InternedSlice<T> {
    #[cold]
    fn drop_slow(&mut self) {
        let storage = T::storage().get();
        let (mut shard, hash) = Self::select(storage, &self.arc.header.header, &self.arc.slice);

        if ThinArc::strong_count(&self.arc) != 2 {
            // Another thread has interned another copy
            return;
        }

        shard.remove_entry(hash, |(other, _)| **other == *self.arc);

        // Shrink the backing storage if the shard is less than 50% occupied.
        if shard.len() * 2 < shard.capacity() {
            let len = shard.len();
            shard.shrink_to(len, |(x, _)| storage.hasher().hash_one(x));
        }
    }
}

/// Compares interned `Ref`s using pointer equality.
impl<T: SliceInternable> PartialEq for InternedSlice<T> {
    // NOTE: No `?Sized` because `ptr_eq` doesn't work right with trait objects.

    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.arc.as_ptr() == other.arc.as_ptr()
    }
}

impl<T: SliceInternable> Eq for InternedSlice<T> {}

impl<T: SliceInternable> Hash for InternedSlice<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.ptr().addr())
    }
}

impl<T: SliceInternable> Deref for InternedSlice<T> {
    type Target = Pointee<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.arc
    }
}

impl<T: SliceInternable> Clone for InternedSlice<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { arc: self.arc.clone() }
    }
}

impl<T> Debug for InternedSlice<T>
where
    T: SliceInternable,
    T::SliceType: Debug,
    T::Header: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.arc).fmt(f)
    }
}

#[repr(transparent)]
pub struct InternedSliceRef<'a, T> {
    ptr: NonNull<c_void>,
    _marker: PhantomData<&'a T>,
}

unsafe impl<T: Send + Sync> Send for InternedSliceRef<'_, T> {}
unsafe impl<T: Send + Sync> Sync for InternedSliceRef<'_, T> {}

impl<'a, T: SliceInternable> InternedSliceRef<'a, T> {
    #[inline(always)]
    fn arc(self) -> ManuallyDrop<ThinArc<T::Header, T::SliceType>> {
        unsafe { ManuallyDrop::new(ThinArc::from_raw(self.ptr.as_ptr())) }
    }

    #[inline]
    pub fn o(self) -> InternedSlice<T> {
        InternedSlice { arc: (*self.arc()).clone() }
    }

    #[inline]
    pub fn get(self) -> &'a Pointee<T> {
        unsafe { &*ptr::from_ref::<Pointee<T>>(&*self.arc()) }
    }
}

impl<T> Clone for InternedSliceRef<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for InternedSliceRef<'_, T> {}

impl<T: SliceInternable> Hash for InternedSliceRef<'_, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.ptr.as_ptr().addr());
    }
}

impl<T: SliceInternable> PartialEq for InternedSliceRef<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T: SliceInternable> Eq for InternedSliceRef<'_, T> {}

impl<T: SliceInternable> Deref for InternedSliceRef<'_, T> {
    type Target = Pointee<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<T> Debug for InternedSliceRef<'_, T>
where
    T: SliceInternable,
    T::SliceType: Debug,
    T::Header: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

pub struct InternSliceStorage<T: SliceInternable> {
    map: OnceLock<InternMap<T>>,
}

#[allow(
    clippy::new_without_default,
    reason = "this a const fn, so it can't be default yet. See <https://github.com/rust-lang/rust/issues/63065>"
)]
impl<T: SliceInternable> InternSliceStorage<T> {
    pub const fn new() -> Self {
        Self { map: OnceLock::new() }
    }
}

impl<T: SliceInternable> InternSliceStorage<T> {
    fn get(&self) -> &InternMap<T> {
        self.map.get_or_init(DashMap::default)
    }
}

pub trait SliceInternable: Sized + 'static {
    type Header: Eq + Hash;
    type SliceType: Eq + Hash + 'static;
    fn storage() -> &'static InternSliceStorage<Self>;
}

/// Implements `Internable` for a given list of types, making them usable with `Interned`.
#[macro_export]
#[doc(hidden)]
macro_rules! _impl_slice_internable {
    ( $tag:ident, $h:ty, $t:ty $(,)? ) => {
        pub struct $tag;
        impl $crate::SliceInternable for $tag {
            type Header = $h;
            type SliceType = $t;
            fn storage() -> &'static $crate::InternSliceStorage<Self> {
                static STORAGE: $crate::InternSliceStorage<$tag> =
                    $crate::InternSliceStorage::new();
                &STORAGE
            }
        }
    };
}
pub use crate::_impl_slice_internable as impl_slice_internable;

pub trait CollectAndIntern<I: SliceInternable<SliceType = T>, T> {
    type Output;

    fn collect_and_intern<Iter>(header: impl FnOnce(&[T]) -> I::Header, iter: Iter) -> Self::Output
    where
        Iter: Iterator<Item = Self>;
}

/// The blanket impl that always collects all elements and applies `f`.
impl<I: SliceInternable<SliceType = T>, T> CollectAndIntern<I, T> for T {
    type Output = InternedSlice<I>;

    /// Equivalent to `f(&iter.collect::<Vec<_>>())`.
    fn collect_and_intern<Iter>(
        header: impl FnOnce(&[Self]) -> I::Header,
        mut iter: Iter,
    ) -> Self::Output
    where
        Iter: Iterator<Item = T>,
    {
        // This code is hot enough that it's worth specializing for the most
        // common length lists, to avoid the overhead of `Vec` creation.
        #[inline(always)]
        fn create<I: SliceInternable>(
            header: impl FnOnce(&[I::SliceType]) -> I::Header,
            args: &mut [ManuallyDrop<I::SliceType>],
        ) -> InternedSlice<I> {
            let header = header(unsafe {
                &*(args as *const [ManuallyDrop<I::SliceType>] as *const [I::SliceType])
            });
            unsafe { InternedSlice::from_header_and_slice_assume_owned(header, args) }
        }

        let m = ManuallyDrop::new;

        let Some(t0) = iter.next() else {
            return create(header, &mut []);
        };

        let Some(t1) = iter.next() else {
            return create(header, &mut [m(t0)]);
        };

        let Some(t2) = iter.next() else {
            return create(header, &mut [m(t0), m(t1)]);
        };

        let Some(t3) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2)]);
        };

        let Some(t4) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2), m(t3)]);
        };

        let Some(t5) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4)]);
        };

        let Some(t6) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5)]);
        };

        let Some(t7) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5), m(t6)]);
        };

        let Some(t8) = iter.next() else {
            return create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5), m(t6), m(t7)]);
        };

        let first = [t0, t1, t2, t3, t4, t5, t6, t7, t8];
        let vec = first.into_iter().chain(iter).collect::<Vec<_>>();
        InternedSlice::from_header_and_vec(header(&vec), vec)
    }
}

/// A fallible impl that will fail, without calling `f`, if there are any
/// errors during collection.
impl<I: SliceInternable<SliceType = T>, T, E> CollectAndIntern<I, T> for Result<T, E> {
    type Output = Result<InternedSlice<I>, E>;

    /// Equivalent to `Ok(f(&iter.collect::<Result<Vec<_>>>()?))`.
    fn collect_and_intern<Iter>(
        header: impl FnOnce(&[T]) -> I::Header,
        mut iter: Iter,
    ) -> Self::Output
    where
        Iter: Iterator<Item = Result<T, E>>,
    {
        // This code is hot enough that it's worth specializing for the most
        // common length lists, to avoid the overhead of `Vec` creation.
        // This code is hot enough that it's worth specializing for the most
        // common length lists, to avoid the overhead of `Vec` creation.
        #[inline(always)]
        fn create<I: SliceInternable>(
            header: impl FnOnce(&[I::SliceType]) -> I::Header,
            args: &mut [ManuallyDrop<I::SliceType>],
        ) -> InternedSlice<I> {
            let header = header(unsafe {
                &*(args as *const [ManuallyDrop<I::SliceType>] as *const [I::SliceType])
            });
            unsafe { InternedSlice::from_header_and_slice_assume_owned(header, args) }
        }

        let m = ManuallyDrop::new;

        let Some(t0) = iter.next() else {
            return Ok(create(header, &mut []));
        };
        let t0 = t0?;

        let Some(t1) = iter.next() else {
            return Ok(create(header, &mut [m(t0)]));
        };
        let t1 = t1?;

        let Some(t2) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1)]));
        };
        let t2 = t2?;

        let Some(t3) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1), m(t2)]));
        };
        let t3 = t3?;

        let Some(t4) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1), m(t2), m(t3)]));
        };
        let t4 = t4?;

        let Some(t5) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4)]));
        };
        let t5 = t5?;

        let Some(t6) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5)]));
        };
        let t6 = t6?;

        let Some(t7) = iter.next() else {
            return Ok(create(header, &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5), m(t6)]));
        };
        let t7 = t7?;

        let Some(t8) = iter.next() else {
            return Ok(create(
                header,
                &mut [m(t0), m(t1), m(t2), m(t3), m(t4), m(t5), m(t6), m(t7)],
            ));
        };
        let t8 = t8?;

        let first = [t0, t1, t2, t3, t4, t5, t6, t7, t8];
        let all = first.into_iter().map(Ok).chain(iter).collect::<Result<Vec<_>, _>>()?;
        Ok(InternedSlice::from_header_and_vec(header(&all), all))
    }
}

#[cfg(test)]
mod tests {
    use crate::CollectAndIntern;

    crate::impl_slice_internable!(MyStorage, String, Vec<u8>);

    type InternedSlice = crate::InternedSlice<MyStorage>;
    // type InternedSliceRef<'a> = crate::InternedSliceRef<'a, MyStorage>;

    #[test]
    fn it_works() {
        let a = InternedSlice::from_header_and_array("abc".to_owned(), [vec![0, 1, 2]]);
        let b = InternedSlice::from_header_and_iter("abc".to_owned(), [vec![0, 1, 2]]);
        assert_eq!(a, b);
        assert_eq!(a.header.header, "abc");
        assert_eq!(b.header.header, "abc");
        assert_eq!(b.header.length, 1);
        let c = a.clone();
        assert_eq!(&c.slice, &[vec![0, 1, 2]]);
        assert_eq!(b, c);
        let a_ref = a.r();
        let b_ref = b.r();
        assert_eq!(a_ref, b_ref);
        assert_eq!(b_ref.o(), c);
        assert_eq!(a_ref.header.header, "abc");
        drop(a);
        drop(b);
        drop(c);
    }

    #[test]
    fn collect_and_intern() {
        let a = CollectAndIntern::<MyStorage, _>::collect_and_intern(
            |_| "abc".to_owned(),
            std::array::repeat::<_, 5>(vec![1]).into_iter(),
        );
        assert_eq!(a.header.header, "abc");
        assert_eq!(a.header.length, 5);
        let b = CollectAndIntern::<MyStorage, _>::collect_and_intern(
            |_| "abc".to_owned(),
            std::array::repeat::<_, 3>(Ok::<_, ()>(vec![1]))
                .into_iter()
                .chain(std::array::repeat::<_, 2>(Ok(vec![1]))),
        )
        .unwrap();
        assert_eq!(a, b);
        let c = CollectAndIntern::<MyStorage, _>::collect_and_intern(
            |_| "abc".to_owned(),
            std::array::repeat::<_, 100>(vec![1]).into_iter(),
        );
        assert_eq!(c.header.length, 100);
        CollectAndIntern::<MyStorage, _>::collect_and_intern(
            |_| "abc".to_owned(),
            std::array::repeat::<_, 2>(Ok(vec![1])).into_iter().chain(std::iter::once(Err(()))),
        )
        .unwrap_err();
        CollectAndIntern::<MyStorage, _>::collect_and_intern(
            |_| "abc".to_owned(),
            std::array::repeat::<_, 100>(Ok(vec![1])).into_iter().chain(std::iter::once(Err(()))),
        )
        .unwrap_err();
    }
}
