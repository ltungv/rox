//! Implementation of a dynamic array with fixed capacity. Operations that modify the list don't
//! perform bounds checking and may result in undefined behaviors.

use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

#[derive(Debug)]
pub struct List<T, const N: usize> {
    buf: RawList<T, N>,
    len: usize,
}

impl<T, const N: usize> Default for List<T, N> {
    fn default() -> Self {
        Self {
            buf: RawList::default(),
            len: 0,
        }
    }
}

impl<T, const N: usize> Deref for List<T, N> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.ptr(), self.len) }
    }
}

impl<T, const N: usize> DerefMut for List<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr(), self.len) }
    }
}

impl<T, const N: usize> List<T, N> {
    /// Get a reference to the value at the end of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the list currently has.
    pub fn last(&self, n: usize) -> &T {
        // SAFETY: All items at index below `self.len` must be valid and initialized
        unsafe { self.get_unchecked(self.len - n - 1) }
    }

    /// Get a mutable reference to the value at the ned of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the list currently has.
    pub fn last_mut(&mut self, n: usize) -> &mut T {
        let len = self.len;
        // SAFETY: All items at index below `self.len` must be valid and initialized
        unsafe { self.get_unchecked_mut(len - n - 1) }
    }

    /// Get a slice of `count` values at the end of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// get more items than what the list currently has.
    pub const fn last_slice(&self, len: usize) -> &[T] {
        let offset = self.len - len;
        // SAFETY:
        // + The pointer we read from always points to a valid memory region because we allocated
        // for an array of size `N`, and `self.len <= N` when all invariants are held.
        // + Any pointer between `self.ptr().add(offset)` and `self.ptr().add(self.len)` is
        // guaranteed to have been initialized.
        unsafe { std::slice::from_raw_parts(self.ptr().add(offset), len) }
    }

    /// Add a value to the end of the list.
    ///
    /// # Safety
    ///
    /// The caller must never push onto a full list. Doing so is an undefined behavior since no
    /// bounds checking is done and the capacity of the list is static
    pub unsafe fn push_unchecked(&mut self, value: T) {
        debug_assert!(
            self.len < N,
            "Pushing to a full list is an undefined behavior"
        );
        // SAFETY: The caller is responsible for ensuring that `self.len < N` upon calling this
        // method. If that is the case, the pointer we write to always points to a valid memory
        // region because we allocated for an array of size `N`.
        unsafe {
            std::ptr::write(self.ptr().add(self.len), value);
        }
        self.len += 1;
    }

    /// Remove the value at the end of the list and return it.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when the list is empty.
    pub fn pop(&mut self) -> T {
        // A panic will occur when we try to subtract with overflow, preventing us from potentially
        // reading from an offset larger than `N`.
        self.len -= 1;
        // SAFETY:
        // + The pointer we read from always points to a valid memory region because we allocated
        // for an array of size `N`, and `self.len <= N` when all invariants are held.
        // + Any pointer between `self.ptr()` and `self.ptr().add(self.len)` is guaranteed to have
        // been initialized.
        unsafe { std::ptr::read(self.ptr().add(self.len)) }
    }

    /// Shortens the list, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        // https://github.com/rust-lang/rust/pull/78884
        if len > self.len {
            return;
        }
        // SAFETY:
        // + The pointer we read from always points to a valid memory region because we allocated
        // for an array of size `N`, and `self.len <= N` when all invariants are held.
        // + Any pointer between `self.ptr().add(len)` and `self.ptr().add(self.len)` is guaranteed
        // to have been initialized.
        unsafe {
            let s = std::ptr::slice_from_raw_parts_mut(self.ptr().add(len), self.len - len);
            std::ptr::drop_in_place(s);
        }
        self.len = len;
    }

    /// Remove all values from the list.
    pub fn clear(&mut self) {
        // SAFETY:
        // + The pointer we read from always points to a valid memory region because we allocated
        // for an array of size `N`, and `self.len <= N` when all invariants are held.
        // + Any pointer between `self.ptr()` and `self.ptr().add(self.len)` is guaranteed to have
        // been initialized.
        unsafe {
            let s = std::ptr::slice_from_raw_parts_mut(self.ptr(), self.len);
            std::ptr::drop_in_place(s);
        }
        self.len = 0;
    }

    /// Returns the number of values currently contained by the list.
    pub const fn len(&self) -> usize {
        self.len
    }

    const fn ptr(&self) -> *mut T {
        self.buf.ptr()
    }
}

#[derive(Debug)]
struct RawList<T, const N: usize> {
    ptr: NonNull<T>,
    marker: PhantomData<[T; N]>,
}

impl<T, const N: usize> Default for RawList<T, N> {
    fn default() -> Self {
        let ptr = if Self::is_zst() {
            NonNull::<T>::dangling()
        } else {
            let layout = Self::layout();
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable.cast()) else {
                std::alloc::handle_alloc_error(layout);
            };
            ptr
        };
        Self {
            ptr,
            marker: PhantomData,
        }
    }
}

impl<T, const N: usize> Drop for RawList<T, N> {
    fn drop(&mut self) {
        if !Self::is_zst() {
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr().cast(), Self::layout());
            }
        }
    }
}

impl<T, const N: usize> RawList<T, N> {
    const fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    fn layout() -> std::alloc::Layout {
        std::alloc::Layout::array::<T>(N).unwrap()
    }

    const fn is_zst() -> bool {
        std::mem::size_of::<T>() == 0 || N == 0
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    const TEST_VEC_SIZE: usize = 256;
    type TestVec = List<usize, TEST_VEC_SIZE>;

    #[test]
    fn test_vec_init() {
        let s = TestVec::default();
        assert_eq!(0, s.len());
    }

    #[test]
    fn test_vec_push_until_limit() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        assert_eq!(TEST_VEC_SIZE, s.len());
    }

    #[test]
    fn test_vec_pop_returns_in_lifo_order() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        // Should receive things in reverse order
        for i in (0..TEST_VEC_SIZE).rev() {
            assert_eq!(i, s.pop());
        }
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_vec_pop_panics_on_empty() {
        let mut s = TestVec::default();
        // BOOOMM
        s.pop();
    }

    #[test]
    fn test_vec_at_returns_correct_item() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        // Should receive the correct item at each index
        for i in 0..TEST_VEC_SIZE {
            assert_eq!(i, unsafe { *s.get_unchecked(i) });
        }
    }

    #[test]
    fn test_vec_at_mut_modifies_correct_item() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        // Change the values
        for (i, v) in (0..TEST_VEC_SIZE).zip((0..TEST_VEC_SIZE).rev()) {
            unsafe { *s.get_unchecked_mut(i) = v }
        }
        // Should receive things in increasing order
        for i in 0..TEST_VEC_SIZE {
            assert_eq!(i, s.pop());
        }
    }

    #[test]
    fn test_vec_top_returns_correct_item() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        // Top should return the same value as pop
        for _ in 0..TEST_VEC_SIZE {
            let top = *s.last(0);
            assert_eq!(s.pop(), top);
        }
    }

    #[test]
    fn test_vec_top_mut_modifies_correct_item() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        // Top should return the same value as pop
        for i in 0..TEST_VEC_SIZE {
            *s.last_mut(0) = i;
            let pop = s.pop();
            assert_eq!(pop, i);
        }
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_vec_top_panics_when_empty() {
        let s = TestVec::default();
        s.last(0);
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_vec_top_mut_panics_when_empty() {
        let mut s = TestVec::default();
        s.last_mut(0);
    }

    #[test]
    fn test_vec_iter() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        for (i, it) in (0..TEST_VEC_SIZE).zip(s.iter()) {
            assert_eq!(i, *it);
        }
    }

    #[test]
    fn test_vec_iter_rev() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        for (i, it) in (0..TEST_VEC_SIZE).rev().zip(s.iter().rev()) {
            assert_eq!(i, *it);
        }
    }
}
