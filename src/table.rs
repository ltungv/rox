use std::{alloc::Layout, cell::Cell, marker::PhantomData, ops::Mul, ptr::NonNull};

use crate::object::{Gc, RefString};

/// A hash table mapping from `RefString` to `V`. Conflicting keys are resolved using linear probing.
#[derive(Debug)]
pub struct Table<V> {
    ptr: Cell<NonNull<Entry<V>>>,
    cap: Cell<usize>,
    lives: Cell<usize>,
    deads: Cell<usize>,
    marker: PhantomData<[Entry<V>]>,
}

impl<V> Default for Table<V> {
    fn default() -> Self {
        Self {
            ptr: Cell::new(NonNull::dangling()),
            cap: Cell::new(0),
            lives: Cell::new(0),
            deads: Cell::new(0),
            marker: PhantomData,
        }
    }
}

impl<V> Drop for Table<V> {
    fn drop(&mut self) {
        let s = std::ptr::slice_from_raw_parts_mut(self.ptr(), self.cap.get());
        // SAFETY:
        // + `self.ptr()` is valid and non-null.
        // + `self.ptr()` points to an aligned array of size `self.cap`.
        // + All `self.cap` elements are guaranteed to be initialized.
        unsafe {
            std::ptr::drop_in_place(s);
            Self::dealloc(self.ptr(), self.cap.get());
        }
    }
}

impl<'table, V> IntoIterator for &'table Table<V> {
    type Item = (&'table RefString, &'table V);

    type IntoIter = Iter<'table, V>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            ptr: self.ptr.get(),
            idx: 0,
            cap: self.cap.get(),
            marker: PhantomData,
        }
    }
}

impl<V> Table<V> {
    /// Gets the number of entries in the table.
    pub fn len(&self) -> usize {
        self.lives.get()
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, key: RefString) -> Option<&V> {
        if self.lives.get() == 0 {
            return None;
        }
        // SAFETY:
        // + `self.probe(_)` returns a valid pointer to a properly aligned and initialized entry.
        if let Entry::Live(e) = unsafe { &*self.probe(key) } {
            Some(&e.val)
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    /// In this case, the key is not updated.
    pub fn set(&self, key: RefString, val: V) -> Option<V> {
        let cap = self.cap.get();
        let lives = self.lives.get();
        let deads = self.deads.get();
        if lives + deads >= cap * 3 / 4 {
            self.resize();
        }
        let entry_ptr = self.probe(key);
        let entry_new = Entry::Live(EntryInner { key, val });
        // SAFETY:
        // + `self.probe(_)` returns a valid pointer to a properly aligned and initialized entry.
        match unsafe { std::ptr::replace(entry_ptr, entry_new) } {
            Entry::Free => {
                self.lives.set(lives + 1);
                None
            }
            Entry::Dead => {
                self.lives.set(lives + 1);
                self.deads.set(deads - 1);
                None
            }
            Entry::Live(e) => Some(e.val),
        }
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    pub fn del(&self, key: RefString) -> Option<V> {
        let lives = self.lives.get();
        if lives == 0 {
            return None;
        }
        let entry_ptr = self.probe(key);
        // SAFETY:
        // + `self.probe(_)` returns a valid pointer to a properly aligned and initialized entry.
        let entry_old = unsafe { std::ptr::replace(entry_ptr, Entry::Dead) };
        let Entry::Live(entry_old) = entry_old else {
            return None;
        };
        let deads = self.deads.get();
        self.lives.set(lives - 1);
        self.deads.set(deads + 1);
        Some(entry_old.val)
    }

    /// Returns a reference to the string object that matches the given string slice and hash value.
    pub fn find(&self, s: &str, hash: u32) -> Option<RefString> {
        if self.lives.get() == 0 {
            return None;
        }
        let cap = self.cap.get();
        let mut index = hash as usize & (cap - 1);
        loop {
            // SAFETY:
            // + `index < self.cap`, guaranteed by the probing procedure.
            // + `self.ptr()` is valid and non-null.
            // + `self.ptr()` points to an aligned array of size `self.cap`.
            // + Only elements whose index is in `[0, self.cap)` are accessed.
            match unsafe { &*self.ptr().add(index) } {
                Entry::Free => return None,
                Entry::Live(e) if e.key.as_ref().data == s => {
                    return Some(e.key);
                }
                _ => {}
            }
            // Linear probing.
            index = (index + 1) & (cap - 1);
        }
    }

    /// Returns a pointer to the entry corresponding to the key. The pointer is guaranteed to be
    /// valid and pointers to an properly aligned and initialized `Entry<V>`.
    ///
    /// If the map did not have this key present, the returned pointer points to either a free
    /// entry or the first dead entry corresponding to the key's hash.
    ///
    /// If the map did have this key present, the returned pointer points to a live entry
    /// corresponding to the key.
    fn probe(&self, key: RefString) -> *mut Entry<V> {
        let cap = self.cap.get();
        debug_assert!(cap > 0, "Capacity must be greater than 0");
        let mut dead = None;
        let mut index = key.as_ref().hash as usize & (cap - 1);
        loop {
            // SAFETY:
            // + `index < self.cap`, guaranteed by the probing procedure.
            // + `self.ptr()` is valid and non-null.
            // + `self.ptr()` points to an aligned array of size `self.cap`.
            // + Only elements whose index is in `[0, self.cap)` are accessed.
            let entry_ptr = unsafe { self.ptr().add(index) };
            // SAFETY:
            // + The pointer is valid and points to a properly aligned and initialized entry,
            // guaranteed by `Self::alloc(_)`.
            match unsafe { &*entry_ptr } {
                Entry::Free => {
                    return dead.unwrap_or(entry_ptr);
                }
                Entry::Dead if dead.is_none() => {
                    dead = Some(entry_ptr);
                }
                Entry::Live(e) if Gc::ptr_eq(e.key, key) => {
                    return entry_ptr;
                }
                _ => {}
            }
            // Linear probing.
            index = (index + 1) & (cap - 1);
        }
    }

    /// Resizes the table by doubling its current capacity.
    fn resize(&self) {
        // Allocate the new array.
        let old_cap = self.cap.get();
        let new_cap = old_cap.mul(2).max(8);
        let old_ptr = self.ptr();
        self.ptr.set(Self::alloc(new_cap));
        self.cap.set(new_cap);
        self.deads.set(0);
        // Rehash existing entries and copy them over to the new array. Dead entries are ignored.
        for i in 0..old_cap {
            // SAFETY:
            // + `i < old_cap`, guaranteed by the loop condition.
            // + `old_ptr` is valid and non-null.
            // + `old_ptr` points to an aligned array of size `old_cap`.
            // + Only elements whose index is in `[0, old_cap)` are accessed.
            let entry_old_ptr = unsafe { old_ptr.add(i) };
            // SAFETY:
            // + The pointer is valid and points to a properly aligned and initialized entry,
            // guaranteed by `Self::alloc(_)`.
            if let Entry::Live(e) = unsafe { &*entry_old_ptr } {
                let entry_new_ptr = self.probe(e.key);
                // SAFETY:
                // + Both pointers is valid and points to a properly aligned and initialized entry,
                // guaranteed by `Self::alloc(_)`.
                unsafe {
                    std::ptr::swap(entry_new_ptr, entry_old_ptr);
                }
            }
        }
        // SAFETY:
        // + `old_ptr` is valid and non-null.
        // + `old_ptr` points to an aligned array of size `old_cap`.
        unsafe {
            Self::dealloc(old_ptr, old_cap);
        }
    }

    fn ptr(&self) -> *mut Entry<V> {
        self.ptr.get().as_ptr()
    }

    /// Allocates an array of `Entry<V>` of size `cap` and return the raw pointer to the
    /// beginning of the array.
    fn alloc(cap: usize) -> NonNull<Entry<V>> {
        if cap == 0 {
            NonNull::dangling()
        } else {
            let layout = Self::layout(cap);
            // SAFETY:
            // + `cap > 0`, due to the if statement.
            // + size_of::<Entry<V>>() can never be 0.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable.cast()) else {
                std::alloc::handle_alloc_error(layout);
            };
            for i in 0..cap {
                // SAFETY:
                // + `i < cap`, guaranteed by the loop condition.
                // + `ptr` is valid and non-null.
                // + `ptr` points to an aligned array of size `cap`.
                // + Only elements whose index is in `[0, cap)` are accessed.
                unsafe {
                    ptr.add(i).write(Entry::Free);
                }
            }
            ptr
        }
    }

    /// Deallocates the array of `Entry<V>` of size `cap`.
    ///
    /// # Safety
    ///
    /// + `ptr` is valid and non-null.
    /// + `ptr` points to an aligned array of size `cap`.
    unsafe fn dealloc(ptr: *mut Entry<V>, cap: usize) {
        if cap > 0 {
            // Safety:
            // + `cap > 0`, due to the if statement.
            // + size_of::<Entry<V>>() can never be 0.
            // + `ptr` is valid and non-null, guaranteed by the caller.
            // + `ptr` points to an aligned array of size `cap`, guaranteed by the caller.
            unsafe {
                std::alloc::dealloc(ptr.cast(), Self::layout(cap));
            }
        }
    }

    /// Return the memory layout of an array of `Entry<V>` of size `cap`.
    fn layout(cap: usize) -> Layout {
        Layout::array::<Entry<V>>(cap).expect("invalid layout.")
    }
}

#[derive(Debug)]
enum Entry<V> {
    Free,
    Dead,
    Live(EntryInner<V>),
}

#[derive(Debug)]
struct EntryInner<V> {
    key: RefString,
    val: V,
}

#[derive(Debug)]
pub struct Iter<'table, V> {
    ptr: NonNull<Entry<V>>,
    idx: usize,
    cap: usize,
    marker: PhantomData<&'table Table<V>>,
}

impl<'table, V> Iterator for Iter<'table, V> {
    type Item = (&'table RefString, &'table V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.cap {
            // SAFETY:
            // + `self.idx < self.cap`, guaranteed by the loop condition.
            // + `self.ptr` is valid and non-null.
            // + `self.ptr` points to an aligned array of size `self.cap`.
            // + Only elements whose index is in `[0, self.cap)` are accessed.
            let entry = unsafe { &*self.ptr.as_ptr().add(self.idx) };
            self.idx += 1;
            if let Entry::Live(x) = entry {
                return Some((&x.key, &x.val));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::{f64::consts::PI, rc::Rc};

    use crate::{heap::Heap, object::Gc, value::Value};

    use super::Table;

    #[test]
    fn get_returns_previously_set_value() {
        let mut heap = Heap::default();
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());
        let table = Table::default();

        assert_eq!(0, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(None, table.get(key1));

        table.set(key1, Value::Bool(true));
        table.set(key2, Value::Number(PI));

        assert_eq!(2, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(Some(Value::Bool(true)), table.get(key1).copied());
        assert_eq!(Some(Value::Number(PI)), table.get(key2).copied());
    }

    #[test]
    fn set_updates_existing_entry() {
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());
        let table = Table::default();

        let prev = table.set(key, Value::Bool(true));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(None, prev);
        assert_eq!(Some(Value::Bool(true)), table.get(key).copied());

        let prev = table.set(key, Value::Number(PI));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(Some(Value::Bool(true)), prev);
        assert_eq!(Some(Value::Number(PI)), table.get(key).copied());
    }

    #[test]
    fn del_removes_existing_entry() {
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());
        let table = Table::default();

        let prev = table.set(key, Value::Bool(true));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(None, prev);
        assert_eq!(Some(Value::Bool(true)), table.get(key).copied());

        table.del(key);
        assert_eq!(0, table.lives.get());
        assert_eq!(1, table.deads.get());
        assert_eq!(None, table.get(key));

        let prev = table.set(key, Value::Bool(false));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(None, prev);
        assert_eq!(Some(Value::Bool(false)), table.get(key).copied());
    }

    #[test]
    fn find_returns_previously_set_key() {
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());
        let table = Table::default();

        table.set(key1, Value::Nil);
        table.set(key2, Value::Nil);

        let s = table.find(&key.as_ref().data, key.as_ref().hash);
        let s1 = table.find(&key1.as_ref().data, key1.as_ref().hash).unwrap();
        let s2 = table.find(&key2.as_ref().data, key2.as_ref().hash).unwrap();
        assert!(s.is_none());
        assert!(Gc::ptr_eq(s1, key1));
        assert!(Gc::ptr_eq(s2, key2));
    }

    #[test]
    fn value_are_dropped_when_calling_set() {
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());
        let val = Rc::new(());
        let weak = Rc::downgrade(&Rc::clone(&val));
        let table = Table::default();

        table.set(key, val);
        assert_eq!(1, weak.strong_count());

        table.set(key, Rc::new(()));
        assert_eq!(0, weak.strong_count());
    }

    #[test]
    fn value_are_dropped_when_calling_del() {
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());
        let val = Rc::new(());
        let weak = Rc::downgrade(&Rc::clone(&val));
        let table = Table::default();

        table.set(key, val);
        assert_eq!(1, weak.strong_count());

        table.del(key);
        assert_eq!(0, weak.strong_count());
    }

    #[test]
    fn value_are_not_dropped_when_resizing_table() {
        let mut heap = Heap::default();
        let mut weaks = Vec::default();
        let table = Table::default();

        for i in 0..6 {
            let key = heap.intern(i.to_string());
            let val = Rc::new(());
            let weak = Rc::downgrade(&Rc::clone(&val));
            weaks.push(weak);
            table.set(key, val);
        }

        // Check that values are initially not dropped.
        assert_eq!(8, table.cap.get());
        for weak in &weaks {
            assert_eq!(1, weak.strong_count());
        }

        let key = heap.intern("resize".to_string());
        let val = Rc::new(());
        let weak = Rc::downgrade(&Rc::clone(&val));
        weaks.push(weak);
        table.set(key, val);

        // Check that values are not dropped after a resize.
        assert_eq!(16, table.cap.get());
        for weak in &weaks {
            assert_eq!(1, weak.strong_count());
        }
    }

    #[test]
    fn value_are_not_dropped_when_dropping_table() {
        let mut heap = Heap::default();
        let mut weaks = Vec::default();
        let table = Table::default();

        for i in 0..256 {
            let key = heap.intern(i.to_string());
            let val = Rc::new(());
            let weak = Rc::downgrade(&Rc::clone(&val));
            weaks.push(weak);
            table.set(key, val);
        }

        // Check that values are initially not dropped.
        for weak in &weaks {
            assert_eq!(1, weak.strong_count());
        }

        // Check that values are not dropped after dropping the table.
        drop(table);
        for weak in &weaks {
            assert_eq!(0, weak.strong_count());
        }
    }
}
