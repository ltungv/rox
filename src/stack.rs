use std::mem::{self, MaybeUninit};

/// An enumeration of potential errors occur when using the stack.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum StackError {
    /// Can't pop on an empty stack.
    #[error("Stack is exhausted.")]
    Exhausted,

    /// Can't push on a full stack.
    #[error("Stack is overflown.")]
    Overflown,
}

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

impl<T: Default, const N: usize> Stack<T, N> {
    /// Push a value onto the stack.
    ///
    /// # Errors
    ///
    /// If the stack is full, return RuntimeError::StackOverflown.
    pub(crate) fn push(&mut self, value: T) -> Result<(), StackError> {
        if self.pointer == N {
            return Err(StackError::Overflown);
        }
        self.items[self.pointer] = MaybeUninit::new(value);
        self.pointer += 1;
        Ok(())
    }

    /// Remove the value at the top of the stack and return it.
    ///
    /// # Errors
    ///
    /// If the stack is empty, return RuntimeError::StackExhausted.
    #[allow(unsafe_code)]
    pub(crate) fn pop(&mut self) -> Result<T, StackError> {
        if self.pointer == 0 {
            return Err(StackError::Exhausted);
        }
        self.pointer -= 1;
        let value = {
            let mut tmp = MaybeUninit::uninit();
            mem::swap(&mut tmp, &mut self.items[self.pointer]);
            // SAFETY: We ensure that pointer always points to initialized items. Thus, after
            // swapping, tmp must contain initialized data.
            unsafe { tmp.assume_init() }
        };
        Ok(value)
    }

    #[allow(unsafe_code)]
    pub(crate) fn top_mut(&mut self) -> Result<&mut T, StackError> {
        if self.pointer == 0 {
            return Err(StackError::Exhausted);
        }
        let value = {
            let tmp = &mut self.items[self.pointer - 1];
            // SAFETY: We ensure that pointer always points to initialized items. Thus, tmp
            // must contain initialized data.
            unsafe { &mut *tmp.as_mut_ptr() }
        };
        Ok(value)
    }

    pub(crate) fn apply_unary<E, F>(&mut self, mut func: F) -> Result<(), E>
    where
        T: Copy,
        E: From<StackError>,
        F: FnMut(T) -> Result<T, E>,
    {
        let v = self.top_mut()?;
        *v = func(*v)?;
        Ok(())
    }

    pub(crate) fn apply_binary<E, F>(&mut self, mut func: F) -> Result<(), E>
    where
        T: Copy,
        E: From<StackError>,
        F: FnMut(T, T) -> Result<T, E>,
    {
        let rhs = self.pop()?;
        let lhs = self.top_mut()?;
        *lhs = func(*lhs, rhs)?;
        Ok(())
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

#[cfg(test)]
mod tests {
    use super::{Stack, StackError};

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
        match stack.pop() {
            Ok(_) => unreachable!(),
            Err(err) => assert_eq!(StackError::Exhausted, err),
        }
    }

    #[test]
    fn stack_exceeded_error_is_returned() {
        let mut stack = Stack::<usize, DEFAULT_STACK_SIZE>::default();
        for i in 0..DEFAULT_STACK_SIZE {
            stack.push(i).unwrap();
        }
        match stack.push(DEFAULT_STACK_SIZE) {
            Ok(()) => unreachable!(),
            Err(err) => assert_eq!(StackError::Overflown, err),
        }
    }
}
