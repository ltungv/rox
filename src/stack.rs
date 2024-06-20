//! Implementation of a simple static stack structure.

use std::mem::MaybeUninit;

#[derive(Debug)]
pub struct Stack<T, const N: usize> {
    items: Box<[MaybeUninit<T>; N]>,
    len: usize,
}

impl<T, const N: usize> Stack<T, N> {
    /// Add a value to the top of the stack. This method panics if the stack is full.
    pub fn push(&mut self, value: T) {
        self.items[self.len].write(value);
        self.len += 1;
    }

    /// Remove the value at the top of the stack and return it. This method panics if the stack
    /// is empty
    pub fn pop(&mut self) -> T {
        self.len -= 1;
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.items[self.len].assume_init_read() }
    }

    /// Remove `count` values from the top of the stack. This method only adjusts the stack pointer
    /// and makes no modification to the underlying data array.
    pub fn remove(&mut self, count: usize) {
        self.len -= count;
    }

    /// Remove all values from the stack. This method only adjusts the stack pointer and makes no
    /// modification to the underlying data array.
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Returns the number of values contained within the stack.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Get a slice of `count` values at the top of the stack.
    pub fn topn(&self, count: usize) -> &[T] {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { &*(std::ptr::addr_of!(self.items[self.len - count..self.len]) as *const [T]) }
    }

    /// Get a reference to the value at the top of the stack.
    pub fn top(&self, n: usize) -> &T {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.at(self.len - n - 1) }
    }

    /// Get a mutable reference to the value at the top of the stack.
    pub fn top_mut(&mut self, n: usize) -> &mut T {
        // SAFETY: All items at index below self.len must have been initialized
        unsafe { self.at_mut(self.len - n - 1) }
    }

    /// Get a reference to the value at the given index in the stack.
    ///
    /// ## Safety
    ///
    /// Caller must ensure that the index points to a valid item in the stack.
    pub unsafe fn at(&self, index: usize) -> &T {
        self.items.get_unchecked(index).assume_init_ref()
    }

    /// Get a mutable reference to the value at the given index in the stack.
    ///
    /// ## Safety
    ///
    /// Caller must ensure that the index points to a valid item in the stack.
    pub unsafe fn at_mut(&mut self, index: usize) -> &mut T {
        self.items.get_unchecked_mut(index).assume_init_mut()
    }
}

impl<T, const N: usize> Default for Stack<T, N> {
    fn default() -> Self {
        // SAFETY: Coercing an uninitialized array into an array of uninitialized should be ok.
        let items: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        Self {
            items: Box::new(items),
            len: 0,
        }
    }
}

impl<'stack, T, const N: usize> IntoIterator for &'stack Stack<T, N> {
    type Item = &'stack T;

    type IntoIter = Iter<'stack, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let top = self.len;
        Self::IntoIter {
            stack: self,
            bot: 0,
            top,
        }
    }
}

#[derive(Debug)]
pub struct Iter<'stack, T, const N: usize> {
    stack: &'stack Stack<T, N>,
    top: usize,
    bot: usize,
}

impl<'stack, T, const N: usize> Iterator for Iter<'stack, T, N> {
    type Item = &'stack T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bot >= self.top {
            None
        } else {
            // SAFETY: The iterator only accesses initialized data.
            let it = unsafe { self.stack.at(self.bot) };
            self.bot += 1;
            Some(it)
        }
    }
}
impl<'stack, T, const N: usize> DoubleEndedIterator for Iter<'stack, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.bot >= self.top {
            None
        } else {
            // SAFETY: The iterator only accesses initialized data.
            self.top -= 1;
            let it = unsafe { self.stack.at(self.top) };
            Some(it)
        }
    }
}

impl<'stack, T, const N: usize> ExactSizeIterator for Iter<'stack, T, N> {
    fn len(&self) -> usize {
        self.top - self.bot
    }
}

#[cfg(test)]
mod tests {
    use crate::stack::Stack;

    const TEST_STACK_SIZE: usize = 256;
    type TestStack = Stack<usize, TEST_STACK_SIZE>;

    #[test]
    fn test_stack_init() {
        let s = TestStack::default();
        assert_eq!(0, s.len());
    }

    #[test]
    fn test_stack_push_until_limit() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        assert_eq!(TEST_STACK_SIZE, s.len());
    }

    #[test]
    #[should_panic(expected = "out of bounds")]
    fn test_stack_push_through_limit() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // BOOOMM
        s.push(TEST_STACK_SIZE);
    }

    #[test]
    fn test_stack_pop_returns_in_lifo_order() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // Should receive things in reverse order
        for i in (0..TEST_STACK_SIZE).rev() {
            assert_eq!(i, s.pop());
        }
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_stack_pop_panics_on_empty() {
        let mut s = TestStack::default();
        // BOOOMM
        s.pop();
    }

    #[test]
    fn test_stack_at_returns_correct_item() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // Should receive the correct item at each index
        for i in 0..TEST_STACK_SIZE {
            assert_eq!(i, unsafe { *s.at(i) });
        }
    }

    #[test]
    fn test_stack_at_mut_modifies_correct_item() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // Change the values
        for (i, v) in (0..TEST_STACK_SIZE).zip((0..TEST_STACK_SIZE).rev()) {
            unsafe { *s.at_mut(i) = v }
        }
        // Should receive things in increasing order
        for i in 0..TEST_STACK_SIZE {
            assert_eq!(i, s.pop());
        }
    }

    #[test]
    fn test_stack_top_returns_correct_item() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // Top should return the same value as pop
        for _ in 0..TEST_STACK_SIZE {
            let top = *s.top(0);
            assert_eq!(s.pop(), top);
        }
    }

    #[test]
    fn test_stack_top_mut_modifies_correct_item() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        // Top should return the same value as pop
        for i in 0..TEST_STACK_SIZE {
            *s.top_mut(0) = i;
            let pop = s.pop();
            assert_eq!(pop, i);
        }
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_stack_top_panics_when_empty() {
        let s = TestStack::default();
        s.top(0);
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn test_stack_top_mut_panics_when_empty() {
        let mut s = TestStack::default();
        s.top_mut(0);
    }

    #[test]
    fn test_stack_iter() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        for (i, it) in (0..TEST_STACK_SIZE).zip(s.into_iter()) {
            assert_eq!(i, *it);
        }
    }

    #[test]
    fn test_stack_iter_rev() {
        let mut s = TestStack::default();
        for i in 0..TEST_STACK_SIZE {
            s.push(i);
        }
        for (i, it) in (0..TEST_STACK_SIZE).rev().zip(s.into_iter().rev()) {
            assert_eq!(i, *it);
        }
    }
}
