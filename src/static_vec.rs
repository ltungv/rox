//! Implementation of a vector with fixed capacity supporting only operations
//! that do not perform bound checking.

use std::mem::MaybeUninit;

#[derive(Debug)]
pub struct StaticVec<T, const N: usize> {
    ptr: Box<[MaybeUninit<T>; N]>,
    len: usize,
}

impl<T, const N: usize> StaticVec<T, N> {
    /// Add a value to the end of the vector.
    ///
    /// # Safety
    ///
    /// The caller must never push onto a full vector. Doing so is an undefined
    /// behavior since no bound checking is done and the capacity of the vector
    /// is static.
    pub unsafe fn push_unchecked(&mut self, value: T) {
        self.ptr.get_unchecked_mut(self.len).write(value);
        self.len += 1;
    }

    /// Remove the value at the end of the vector and return it.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when the vector
    /// is empty.
    pub fn pop(&mut self) -> T {
        self.len -= 1;
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.ptr.get_unchecked(self.len).assume_init_read() }
    }

    /// Remove `count` values from the end of the vector.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// remove more items than what the vector currently has.
    pub fn remove(&mut self, count: usize) {
        self.len -= count;
    }

    /// Remove all values from the vector.
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Returns the number of values contained within the vector.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Get a slice of `count` values at the end of the vector.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// get more items than what the vector currently has.
    pub fn last_chunk(&self, count: usize) -> &[T] {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { &*(std::ptr::addr_of!(self.ptr[self.len - count..self.len]) as *const [T]) }
    }

    /// Get a reference to the value at the end of the vector.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the vector currently has.
    pub fn last(&self, n: usize) -> &T {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.get_unchecked(self.len - n - 1) }
    }

    /// Get a mutable reference to the value at the ned of the vector.
    ///
    /// # Panics
    ///
    /// This function panics with an overflow on subtraction when trying to
    /// index passes more items than what the vector currently has.
    pub fn last_mut(&mut self, n: usize) -> &mut T {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.get_unchecked_mut(self.len - n - 1) }
    }

    /// Get a reference to the value at the given index in the vector.
    ///
    /// ## Safety
    ///
    /// Caller must ensure that the index points to a valid item in the vector.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.ptr.get_unchecked(index).assume_init_ref()
    }

    /// Get a mutable reference to the value at the given index in the vector.
    ///
    /// ## Safety
    ///
    /// Caller must ensure that the index points to a valid item in the vector.
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        self.ptr.get_unchecked_mut(index).assume_init_mut()
    }
}

impl<T, const N: usize> Default for StaticVec<T, N> {
    fn default() -> Self {
        // SAFETY: Casting an uninitialized array into an array of uninitialized is ok.
        let arr: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        Self {
            ptr: Box::new(arr),
            len: 0,
        }
    }
}

impl<'vec, T, const N: usize> IntoIterator for &'vec StaticVec<T, N> {
    type Item = &'vec T;

    type IntoIter = Iter<'vec, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let top = self.len;
        Self::IntoIter {
            vec: self,
            bot: 0,
            top,
        }
    }
}

#[derive(Debug)]
pub struct Iter<'vec, T, const N: usize> {
    vec: &'vec StaticVec<T, N>,
    bot: usize,
    top: usize,
}

impl<'vec, T, const N: usize> Iterator for Iter<'vec, T, N> {
    type Item = &'vec T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bot >= self.top {
            None
        } else {
            // SAFETY: We already checked if `self.bot >= self.top` and can't
            // be out of bound at this point.
            let it = unsafe { self.vec.get_unchecked(self.bot) };
            self.bot += 1;
            Some(it)
        }
    }
}
impl<'vec, T, const N: usize> DoubleEndedIterator for Iter<'vec, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bot >= self.top {
            None
        } else {
            self.top -= 1;
            // SAFETY: We already checked if `self.bot >= self.top` and can't
            // be out of bound at this point.
            let it = unsafe { self.vec.get_unchecked(self.top) };
            Some(it)
        }
    }
}

impl<'vec, T, const N: usize> ExactSizeIterator for Iter<'vec, T, N> {
    fn len(&self) -> usize {
        self.top - self.bot
    }
}

#[cfg(test)]
mod tests {
    use crate::static_vec::StaticVec;

    const TEST_VEC_SIZE: usize = 256;
    type TestVec = StaticVec<usize, TEST_VEC_SIZE>;

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
        for (i, it) in (0..TEST_VEC_SIZE).zip(s.into_iter()) {
            assert_eq!(i, *it);
        }
    }

    #[test]
    fn test_vec_iter_rev() {
        let mut s = TestVec::default();
        for i in 0..TEST_VEC_SIZE {
            unsafe { s.push_unchecked(i) };
        }
        for (i, it) in (0..TEST_VEC_SIZE).rev().zip(s.into_iter().rev()) {
            assert_eq!(i, *it);
        }
    }
}
