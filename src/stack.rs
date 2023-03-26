use std::{
    mem::{self, MaybeUninit},
    ops::{Index, IndexMut},
};

#[derive(Debug)]
pub(crate) struct Stack<T, const N: usize> {
    items: [MaybeUninit<T>; N],
    pointer: usize,
}

impl<T, const N: usize> Default for Stack<T, N> {
    #[allow(unsafe_code)]
    fn default() -> Self {
        // SAFETY: This is safe because an uninitialized array is the same as an array of
        // uninitialized items
        let items = unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() };
        Self { items, pointer: 0 }
    }
}

impl<T, const N: usize> Stack<T, N> {
    /// The the current size of the stack.
    pub(crate) fn len(&self) -> usize {
        self.pointer
    }

    /// Push a value onto the stack.
    ///
    /// # Errors
    ///
    /// If the stack is full, return RuntimeError::StackOverflown.
    pub(crate) fn push(&mut self, value: T) -> Option<usize> {
        if self.pointer == N {
            return None;
        }
        self.items[self.pointer] = MaybeUninit::new(value);
        self.pointer += 1;
        Some(self.pointer - 1)
    }

    /// Remove the value at the top of the stack and return it.
    ///
    /// # Errors
    ///
    /// If the stack is empty, return RuntimeError::StackExhausted.
    #[allow(unsafe_code)]
    pub(crate) fn pop(&mut self) -> Option<T> {
        if self.pointer == 0 {
            return None;
        }
        self.pointer -= 1;
        let value = {
            let mut tmp = MaybeUninit::uninit();
            mem::swap(&mut tmp, &mut self.items[self.pointer]);
            // SAFETY: We ensure that pointer always points to initialized items. Thus, after
            // swapping, tmp must contain initialized data.
            unsafe { tmp.assume_init() }
        };
        Some(value)
    }

    #[allow(unsafe_code)]
    pub(crate) fn top(&self) -> Option<&T> {
        if self.pointer == 0 {
            return None;
        }
        let value = {
            let tmp = &self.items[self.pointer - 1];
            // SAFETY: We ensure that pointer always points to initialized items. Thus, tmp
            // must contain initialized data.
            unsafe { &*tmp.as_ptr() }
        };
        Some(value)
    }

    #[allow(unsafe_code)]
    pub(crate) fn top_mut(&mut self) -> Option<&mut T> {
        if self.pointer == 0 {
            return None;
        }
        let value = {
            let tmp = &mut self.items[self.pointer - 1];
            // SAFETY: We ensure that pointer always points to initialized items. Thus, tmp
            // must contain initialized data.
            unsafe { &mut *tmp.as_mut_ptr() }
        };
        Some(value)
    }
}

impl<'stack, T, const N: usize> IntoIterator for &'stack Stack<T, N> {
    type Item = &'stack T;

    type IntoIter = StackIter<'stack, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            stack: self,
            pointer: 0,
        }
    }
}

pub(crate) struct StackIter<'stack, T, const N: usize> {
    stack: &'stack Stack<T, N>,
    pointer: usize,
}

impl<'stack, T, const N: usize> Iterator for StackIter<'stack, T, N> {
    type Item = &'stack T;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pointer >= self.stack.pointer {
            return None;
        }
        let value = {
            let tmp = &self.stack.items[self.pointer];
            // SAFETY: We ensure that indices less than the stack pointer always point to
            // initialized items. Thus, tmp must contain initialized data.
            unsafe { &*tmp.as_ptr() }
        };
        self.pointer += 1;
        Some(value)
    }
}

impl<T, const N: usize> Index<usize> for Stack<T, N> {
    type Output = T;

    #[allow(unsafe_code)]
    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.pointer {
            panic!("Index is out-of-bound.");
        }
        let tmp = &self.items[index];
        // SAFETY: We ensure that indices less than the stack pointer always point to
        // initialized items. Thus, tmp must contain initialized data.
        unsafe { &*tmp.as_ptr() }
    }
}

impl<T, const N: usize> IndexMut<usize> for Stack<T, N> {
    #[allow(unsafe_code)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index >= self.pointer {
            panic!("Index is out-of-bound.");
        }
        let tmp = &mut self.items[index];
        // SAFETY: We ensure that indices less than the stack pointer always point to
        // initialized items. Thus, tmp must contain initialized data.
        unsafe { &mut *tmp.as_mut_ptr() }
    }
}

#[cfg(test)]
mod tests {
    use super::Stack;

    const DEFAULT_STACK_SIZE: usize = 256;

    #[test]
    fn stack_init() {
        let stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();
        assert_eq!(0, stack.pointer);
        assert_eq!(DEFAULT_STACK_SIZE, stack.items.len());
    }

    #[test]
    fn stack_push_increase_pointer() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();

        stack.push(0).unwrap();
        assert_eq!(1, stack.pointer);

        stack.push(1).unwrap();
        stack.push(2).unwrap();
        assert_eq!(3, stack.pointer);
    }

    #[test]
    fn stack_pop_decrease_pointer() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();

        stack.push(0).unwrap();
        assert_eq!(1, stack.pointer);

        stack.push(1).unwrap();
        stack.push(2).unwrap();
        assert_eq!(3, stack.pointer);
    }

    #[test]
    fn stack_operations_are_lifo() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();
        for i in 0..3 {
            stack.push(i).unwrap();
        }
        for i in (0..3).rev() {
            assert_eq!(i, stack.pop().unwrap());
        }
    }

    #[test]
    fn stack_exhausted_error_is_returned() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();
        assert_eq!(None, stack.pop());
    }

    #[test]
    fn stack_exceeded_error_is_returned() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();
        for i in 0..DEFAULT_STACK_SIZE {
            stack.push(i).unwrap();
        }
        assert_eq!(None, stack.push(DEFAULT_STACK_SIZE));
    }
}
