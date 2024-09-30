use std::{alloc, cell::Cell, marker::PhantomData, ops::Mul, ptr::NonNull};

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
        unsafe {
            std::ptr::drop_in_place(s);
            Self::dealloc(self.ptr(), self.cap.get());
        }
    }
}

impl<'table, V> IntoIterator for &'table Table<V>
where
    V: Copy,
{
    type Item = (&'table RefString, &'table V);

    type IntoIter = Iter<'table, V>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            ptr: self.ptr.get(),
            offset: 0,
            capacity: self.cap.get(),
            marker: PhantomData,
        }
    }
}

impl<V> Table<V> {
    /// Get the number of entries that are currently stored in the table.
    pub fn len(&self) -> usize {
        self.lives.get()
    }

    /// Set the value associated with the given key.
    /// If the key is already present, the previous value is returned.
    pub fn set(&self, key: RefString, val: V) -> Option<V> {
        let capacity = self.cap.get();
        let lives = self.lives.get();
        let deads = self.deads.get();
        if lives + deads >= capacity * 3 / 4 {
            self.resize();
        }

        let inner = EntryInner { key, val };
        let entry_ptr = self.probe(key);
        let existing = unsafe { std::ptr::replace(entry_ptr, Entry::Live(inner)) };

        match existing {
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

    // Delete the value associated with the given key and return it.
    // If the key is not present, `None` is returned.
    pub fn del(&self, key: RefString) -> Option<V> {
        let lives = self.lives.get();
        if lives == 0 {
            return None;
        }

        let entry_ptr = self.probe(key);
        let existing = unsafe { std::ptr::replace(entry_ptr, Entry::Dead) };
        let Entry::Live(existing) = existing else {
            return None;
        };

        let deads = self.deads.get();
        self.lives.set(lives - 1);
        self.deads.set(deads + 1);
        Some(existing.val)
    }

    /// Find the pointer to the key that matches the given string and hash.
    // If no key matches, `None` is returned.
    pub fn find(&self, s: &str, hash: u32) -> Option<RefString> {
        if self.lives.get() == 0 {
            return None;
        }
        let capacity = self.cap.get();
        let mut index = hash as usize & (capacity - 1);
        loop {
            match unsafe { &*self.ptr().add(index) } {
                Entry::Free => return None,
                Entry::Live(e) if e.key.as_ref().data == s => {
                    return Some(e.key);
                }
                _ => {}
            }
            // Linear probing.
            index = (index + 1) & (capacity - 1);
        }
    }

    /// Find the pointer to the entry associated with the given key. If the 2 different keys
    /// have the same hash, linear probing is used to find the correct entry.
    fn probe(&self, key: RefString) -> *mut Entry<V> {
        let capacity = self.cap.get();
        let mut dead = None;
        let mut index = key.as_ref().hash as usize & (capacity - 1);
        loop {
            let entry_ptr = unsafe { self.ptr().add(index) };
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
            index = (index + 1) & (capacity - 1);
        }
    }

    /// Resize the table to the given capacity.
    fn resize(&self) {
        // Allocate the new array.
        let old_capacity = self.cap.get();
        let new_capacity = old_capacity.mul(2).max(8);
        let old_ptr = self.ptr();
        let ptr = unsafe { Self::alloc(new_capacity) };
        self.ptr.set(ptr);
        self.cap.set(new_capacity);
        self.deads.set(0);
        // Rehash existing entries and copy them over to the new array. Dead entries are ignored.
        for i in 0..old_capacity {
            let entry_old_ptr = unsafe { old_ptr.add(i) };
            let entry_old = unsafe { &*entry_old_ptr };
            if let Entry::Live(e) = entry_old {
                let entry_new_ptr = self.probe(e.key);
                unsafe {
                    std::ptr::swap(entry_new_ptr, entry_old_ptr);
                }
            }
        }
        unsafe {
            Self::dealloc(old_ptr, old_capacity);
        }
    }

    fn ptr(&self) -> *mut Entry<V> {
        self.ptr.get().as_ptr()
    }

    /// Allocate an array of `Entry<V>` with the given capacity and return the raw pointer
    /// to the beginning of the array.
    ///
    /// ## Safety
    ///
    /// `capacity` must be larger than 0, otherwise, it's undefined behavior.
    unsafe fn alloc(capacity: usize) -> NonNull<Entry<V>> {
        let ptr: *mut Entry<V> = unsafe { alloc::alloc(Self::entries_layout(capacity)).cast() };
        for i in 0..capacity {
            unsafe {
                ptr.add(i).write(Entry::Free);
            }
        }
        unsafe { NonNull::new_unchecked(ptr) }
    }

    /// Deallocate the array of `Entry<V>` with the given capacity.
    ///
    /// ## Safety
    ///
    /// + `ptr` must be a valid pointer to the array of `Entry<V>` with the given `capacity`.
    /// + `ptr` must be allocated with the same allocator as `Self::alloc`.
    unsafe fn dealloc(ptr: *mut Entry<V>, capacity: usize) {
        if capacity > 0 {
            unsafe {
                alloc::dealloc(ptr.cast(), Self::entries_layout(capacity));
            }
        }
    }

    /// Return the memory layout of an array of `Entry<V>` with the given capacity.
    fn entries_layout(cap: usize) -> alloc::Layout {
        alloc::Layout::array::<Entry<V>>(cap).expect("invalid layout.")
    }
}

impl<V> Table<V>
where
    V: Copy,
{
    // Get the value associated with the given key.
    // If the key is not present, `None` is returned.
    pub fn get(&self, key: RefString) -> Option<V> {
        if self.lives.get() == 0 {
            return None;
        }
        let entry = unsafe { &*self.probe(key) };
        if let Entry::Live(e) = entry {
            Some(e.val)
        } else {
            None
        }
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
    offset: usize,
    capacity: usize,
    marker: PhantomData<&'table Table<V>>,
}

impl<'table, V> Iterator for Iter<'table, V>
where
    V: Copy,
{
    type Item = (&'table RefString, &'table V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.offset < self.capacity {
            let entry_ptr = unsafe { self.ptr.as_ptr().add(self.offset) };
            self.offset += 1;
            if let Entry::Live(x) = unsafe { &*entry_ptr } {
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
        assert_eq!(Some(Value::Bool(true)), table.get(key1));
        assert_eq!(Some(Value::Number(PI)), table.get(key2));
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
        assert_eq!(Some(Value::Bool(true)), table.get(key));

        let prev = table.set(key, Value::Number(PI));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(Some(Value::Bool(true)), prev);
        assert_eq!(Some(Value::Number(PI)), table.get(key));
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
        assert_eq!(Some(Value::Bool(true)), table.get(key));

        table.del(key);
        assert_eq!(0, table.lives.get());
        assert_eq!(1, table.deads.get());
        assert_eq!(None, table.get(key));

        let prev = table.set(key, Value::Bool(false));
        assert_eq!(1, table.lives.get());
        assert_eq!(0, table.deads.get());
        assert_eq!(None, prev);
        assert_eq!(Some(Value::Bool(false)), table.get(key));
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

        for i in 6..7 {
            let key = heap.intern(i.to_string());
            let val = Rc::new(());
            let weak = Rc::downgrade(&Rc::clone(&val));
            weaks.push(weak);
            table.set(key, val);
        }

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
