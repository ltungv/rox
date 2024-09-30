//! Implementation of a dynamic array with fixed capacity.

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

impl<T, const N: usize> Drop for List<T, N> {
    fn drop(&mut self) {
        let s = std::ptr::slice_from_raw_parts_mut(self.ptr(), self.len);
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe {
            std::ptr::drop_in_place(s);
        }
    }
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
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { std::slice::from_raw_parts(self.ptr(), self.len) }
    }
}

impl<T, const N: usize> DerefMut for List<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { std::slice::from_raw_parts_mut(self.ptr(), self.len) }
    }
}

impl<T, const N: usize> List<T, N> {
    /// Gets a reference to the value at the end of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the list currently has.
    pub fn last(&self, n: usize) -> &T {
        // SAFETY:
        // + `n` must be smaller than `self.len`, otherwise, a panic occurs before the access.
        // + Only elements whose index is in `[0, self.len)` are accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { self.get_unchecked(self.len - n - 1) }
    }

    /// Gets a mutable reference to the value at the end of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the list currently has.
    pub fn last_mut(&mut self, n: usize) -> &mut T {
        let len = self.len;
        // SAFETY:
        // + `n` must be smaller than `self.len`, otherwise, a panic occurs before the access.
        // + Only elements whose index is in `[0, self.len)` are accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { self.get_unchecked_mut(len - n - 1) }
    }

    /// Gets a slice of the last `count` values of the list.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when `len` is larger than the number
    /// of elements currently in the list.
    pub const fn last_slice(&self, len: usize) -> &[T] {
        let offset = self.len - len;
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + `len <= self.len`, otherwise, a panic occurs before reaching here.
        // + Only elements whose index is in `[0, self.len)` are accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { std::slice::from_raw_parts(self.ptr().add(offset), len) }
    }

    /// Adds a value to the end of the list.
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
        // SAFETY:
        // + `self.len < N`, guaranteed by the caller.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + Only the element at index `self.len` is accessed.
        unsafe {
            std::ptr::write(self.ptr().add(self.len), value);
        }
        self.len += 1;
    }

    /// Removes the value at the end of the list and return it.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when the list is empty.
    pub fn pop(&mut self) -> T {
        // A panic will occur when we try to subtract with overflow, preventing us from potentially
        // reading from an offset larger than `N`.
        self.len -= 1;
        // SAFETY:
        // + `self.len < N`, guaranteed by the invariant that `self.len <= N`.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + Only the element at index `self.len` is accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe { std::ptr::read(self.ptr().add(self.len)) }
    }

    /// Shortens the list, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        // https://github.com/rust-lang/rust/pull/78884
        if len > self.len {
            return;
        }
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + `len <= self.len` due to the if statement.
        // + Only elements whose index is in `[len, self.len)` are accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
        unsafe {
            let s = std::ptr::slice_from_raw_parts_mut(self.ptr().add(len), self.len - len);
            std::ptr::drop_in_place(s);
        }
        self.len = len;
    }

    /// Remove all values from the list.
    pub fn clear(&mut self) {
        // SAFETY:
        // + `self.len <= N` is an invariant.
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `N`.
        // + Only elements whose index is in `[0, self.len)` are accessed.
        // + The first `self.len` elements are guaranteed to be initialized.
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
            // SAFETY:
            // + `N > 0` due to the if statement.
            // + `size_of::<T>() > 0` due to the if statement.
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
            // SAFETY:
            // + `N > 0` due to the if statement.
            // + `size_of::<T>() > 0` due to the if statement.
            // + `self.ptr()` is valid and non-null.
            // + `self.ptr()` points to an aligned array of size `N`.
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
    use std::rc::Rc;

    const TEST_LIST_SIZE: usize = 256;
    type List<T> = super::List<T, TEST_LIST_SIZE>;

    #[test]
    fn last_in_first_out() {
        let mut l = List::default();
        for i in 0..TEST_LIST_SIZE {
            unsafe {
                l.push_unchecked(i);
            }
        }
        for i in (0..TEST_LIST_SIZE).rev() {
            assert_eq!(i, l.pop());
        }
    }

    #[test]
    fn last() {
        let mut l = List::default();
        for i in 0..TEST_LIST_SIZE {
            unsafe {
                l.push_unchecked(i);
            }
        }
        for i in 0..TEST_LIST_SIZE {
            let top = *l.last(i);
            assert_eq!(TEST_LIST_SIZE - i - 1, top);
        }
    }

    #[test]
    fn last_mut() {
        let mut l = List::default();
        for i in 0..TEST_LIST_SIZE {
            unsafe {
                l.push_unchecked(i);
            }
        }
        for i in 0..TEST_LIST_SIZE {
            *l.last_mut(i) = i;
        }
        for i in 0..TEST_LIST_SIZE {
            assert_eq!(TEST_LIST_SIZE - i - 1, l.get(i).copied().unwrap());
        }
    }

    #[test]
    fn values_are_dropped_when_calling_pop() {
        let mut l = List::default();
        let v0 = Rc::new(());
        let v1 = Rc::new(());
        let w0 = Rc::downgrade(&Rc::clone(&v0));
        let w1 = Rc::downgrade(&Rc::clone(&v1));
        unsafe {
            l.push_unchecked(v0);
            l.push_unchecked(v1);
        }

        assert_eq!(1, w0.strong_count());
        assert_eq!(1, w1.strong_count());

        l.pop();
        assert_eq!(1, w0.strong_count());
        assert_eq!(0, w1.strong_count());

        l.pop();
        assert_eq!(0, w0.strong_count());
        assert_eq!(0, w1.strong_count());
    }

    #[test]
    fn values_are_dropped_when_calling_truncate() {
        let mut l = List::default();
        let v0 = Rc::new(());
        let v1 = Rc::new(());
        let w0 = Rc::downgrade(&Rc::clone(&v0));
        let w1 = Rc::downgrade(&Rc::clone(&v1));
        unsafe {
            l.push_unchecked(v0);
            l.push_unchecked(v1);
        }

        assert_eq!(1, w0.strong_count());
        assert_eq!(1, w1.strong_count());

        l.truncate(1);
        assert_eq!(1, w0.strong_count());
        assert_eq!(0, w1.strong_count());
    }

    #[test]
    fn values_are_dropped_when_calling_clear() {
        let mut l = List::default();
        let v0 = Rc::new(());
        let v1 = Rc::new(());
        let w0 = Rc::downgrade(&Rc::clone(&v0));
        let w1 = Rc::downgrade(&Rc::clone(&v1));
        unsafe {
            l.push_unchecked(v0);
            l.push_unchecked(v1);
        }

        assert_eq!(1, w0.strong_count());
        assert_eq!(1, w1.strong_count());

        l.clear();
        assert_eq!(0, w0.strong_count());
        assert_eq!(0, w1.strong_count());
    }

    #[test]
    fn values_are_dropped_when_dropping_list() {
        let mut l = List::default();
        let v0 = Rc::new(());
        let v1 = Rc::new(());
        let w0 = Rc::downgrade(&Rc::clone(&v0));
        let w1 = Rc::downgrade(&Rc::clone(&v1));
        unsafe {
            l.push_unchecked(v0);
            l.push_unchecked(v1);
        }

        assert_eq!(1, w0.strong_count());
        assert_eq!(1, w1.strong_count());

        drop(l);
        assert_eq!(0, w0.strong_count());
        assert_eq!(0, w1.strong_count());
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn panics_when_calling_pop_on_empty_list() {
        List::<()>::default().pop();
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn panics_when_calling_last_on_empty_list() {
        List::<()>::default().last(0);
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn panics_when_calling_last_mut_on_empty_list() {
        List::<()>::default().last_mut(0);
    }
}
