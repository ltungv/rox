use std::{alloc, cell::Cell, marker::PhantomData, ops::Mul, ptr::NonNull};

use crate::object::{Gc, RefString};

/// A hash table mapping from `RefString` to `V`. Conflicting keys are resolved using linear probing.
#[derive(Debug)]
pub struct Table<V> {
    ptr: Cell<NonNull<Entry<V>>>,
    capacity: Cell<usize>,
    occupants: Cell<usize>,
    tombstones: Cell<usize>,
    marker: PhantomData<[Entry<V>]>,
}

impl<V> Default for Table<V> {
    fn default() -> Self {
        Self {
            ptr: Cell::new(NonNull::dangling()),
            capacity: Cell::new(0),
            occupants: Cell::new(0),
            tombstones: Cell::new(0),
            marker: PhantomData,
        }
    }
}

impl<V> Drop for Table<V> {
    fn drop(&mut self) {
        unsafe { Self::dealloc(self.ptr.get().as_ptr(), self.capacity.get()) };
    }
}

impl<'table, V> IntoIterator for &'table Table<V>
where
    V: Copy,
{
    type Item = (RefString, V);

    type IntoIter = Iter<'table, V>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            ptr: self.ptr.get(),
            offset: 0,
            capacity: self.capacity.get(),
            marker: PhantomData,
        }
    }
}

impl<V> Table<V> {
    /// Get the number of entries that are currently stored in the table.
    pub fn len(&self) -> usize {
        self.occupants.get()
    }

    /// Set the value associated with the given key.
    /// If the key is already present, the previous value is returned.
    pub fn set(&self, key: RefString, val: V) -> Option<V> {
        let capacity = self.capacity.get();
        let occupants = self.occupants.get();
        let tombstones = self.tombstones.get();
        if occupants + tombstones >= capacity * 3 / 4 {
            self.resize();
        }

        let entry_ptr = self.probe(key);
        let existing =
            unsafe { std::ptr::replace(entry_ptr, Entry::Occupied(EntryInner { key, val })) };

        match existing {
            Entry::Vacant => {
                self.occupants.set(occupants + 1);
                None
            }
            Entry::Tombstone => {
                self.occupants.set(occupants + 1);
                self.tombstones.set(tombstones - 1);
                None
            }
            Entry::Occupied(e) => Some(e.val),
        }
    }

    // Delete the value associated with the given key and return it.
    // If the key is not present, `None` is returned.
    pub fn del(&self, key: RefString) -> Option<V> {
        let occupants = self.occupants.get();
        if occupants == 0 {
            return None;
        }

        let entry_ptr = self.probe(key);
        let existing = unsafe { std::ptr::replace(entry_ptr, Entry::Tombstone) };
        let Entry::Occupied(existing) = existing else {
            return None;
        };

        let tombstones = self.tombstones.get();
        self.occupants.set(occupants - 1);
        self.tombstones.set(tombstones + 1);
        Some(existing.val)
    }

    /// Find the pointer to the key that matches the given string and hash.
    // If no key matches, `None` is returned.
    pub fn find(&self, s: &str, hash: u32) -> Option<RefString> {
        if self.occupants.get() == 0 {
            return None;
        }
        let capacity = self.capacity.get();
        let mut index = hash as usize & (capacity - 1);
        loop {
            match unsafe { &*self.ptr.get().as_ptr().add(index) } {
                Entry::Vacant => return None,
                Entry::Occupied(e) if e.key.as_ref().data == s => {
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
        let capacity = self.capacity.get();
        let mut tombstone = None;
        let mut index = key.as_ref().hash as usize & (capacity - 1);
        loop {
            let entry_ptr = unsafe { self.ptr.get().as_ptr().add(index) };
            match unsafe { &*entry_ptr } {
                Entry::Vacant => {
                    return tombstone.unwrap_or(entry_ptr);
                }
                Entry::Tombstone if tombstone.is_none() => {
                    tombstone = Some(entry_ptr);
                }
                Entry::Occupied(e) if Gc::ptr_eq(e.key, key) => {
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
        let old_capacity = self.capacity.get();
        let new_capacity = old_capacity.mul(2).max(8);
        let old_ptr = self.ptr.get().as_ptr();
        let ptr = unsafe { Self::alloc(new_capacity) };
        self.ptr.set(ptr);
        self.capacity.set(new_capacity);
        self.tombstones.set(0);
        // Rehash existing entries and copy them over to the new array. Tombstones are ignored.
        for i in 0..old_capacity {
            let entry_old_ptr = unsafe { old_ptr.add(i) };
            let entry_old = unsafe { &*entry_old_ptr };
            if let Entry::Occupied(e) = entry_old {
                let entry_new_ptr = self.probe(e.key);
                unsafe {
                    std::ptr::swap(entry_new_ptr, entry_old_ptr);
                }
            }
        }
        unsafe { Self::dealloc(old_ptr, old_capacity) };
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
            unsafe { ptr.add(i).write(Entry::Vacant) };
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
            unsafe { alloc::dealloc(ptr.cast(), Self::entries_layout(capacity)) };
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
        if self.occupants.get() == 0 {
            return None;
        }
        let entry = unsafe { &*self.probe(key) };
        if let Entry::Occupied(e) = entry {
            Some(e.val)
        } else {
            None
        }
    }
}

#[derive(Debug)]
enum Entry<V> {
    Vacant,
    Tombstone,
    Occupied(EntryInner<V>),
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
    type Item = (RefString, V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.offset < self.capacity {
            let entry_ptr = unsafe { self.ptr.as_ptr().add(self.offset) };
            self.offset += 1;
            if let Entry::Occupied(x) = unsafe { &*entry_ptr } {
                return Some((x.key, x.val));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::f64::consts::PI;

    use crate::{heap::Heap, object::Gc, value::Value};

    use super::Table;

    #[test]
    fn table_should_be_empty_on_creation() {
        let table = Table::<Value>::default();
        assert_eq!(0, table.capacity.get());
        assert_eq!(0, table.occupants.get());
        assert_eq!(0, table.tombstones.get());
    }

    #[test]
    fn set_should_update_table_metadata() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());

        table.set(key1, Value::Number(PI));
        assert_eq!(8, table.capacity.get());
        assert_eq!(1, table.occupants.get());
        assert_eq!(0, table.tombstones.get());

        table.set(key2, Value::Number(PI));
        assert_eq!(8, table.capacity.get());
        assert_eq!(2, table.occupants.get());
        assert_eq!(0, table.tombstones.get());
    }

    #[test]
    fn set_should_return_previous_value() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let prev = table.set(key, Value::Bool(true));
        assert!(prev.is_none());

        let prev = table.set(key, Value::Number(PI));
        assert!(matches!(prev, Some(Value::Bool(true))));
    }

    #[test]
    fn set_should_not_change_number_of_occupants_when_overwriting() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants.get());
        table.set(key, Value::Number(PI));
        assert_eq!(1, table.occupants.get());
    }

    #[test]
    fn set_should_update_tombstones_count() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants.get());
        assert_eq!(0, table.tombstones.get());

        table.del(key);
        assert_eq!(0, table.occupants.get());
        assert_eq!(1, table.tombstones.get());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants.get());
        assert_eq!(0, table.tombstones.get());
    }

    #[test]
    fn get_from_empty_table() {
        let table = Table::<Value>::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let val = table.get(key);
        assert!(val.is_none());
    }

    #[test]
    fn get_existing_keys() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        let val = table.get(key);
        assert!(matches!(val, Some(Value::Bool(true))));
    }

    #[test]
    fn get_last_set_value() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        let val = table.get(key);
        assert!(matches!(val, Some(Value::Bool(true))));

        table.set(key, Value::Bool(false));
        let val = table.get(key);
        assert!(matches!(val, Some(Value::Bool(false))));
    }

    #[test]
    fn del_should_update_len_and_tombstones_count() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants.get());
        assert_eq!(0, table.tombstones.get());

        let prev = table.del(key);
        assert!(matches!(prev, Some(Value::Bool(true))));
        assert_eq!(0, table.occupants.get());
        assert_eq!(1, table.tombstones.get());
    }

    #[test]
    fn del_should_remove_key() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        let get_result = table.get(key);
        let del_result = table.del(key);
        assert_eq!(get_result, del_result);
        let del_result = table.del(key);
        assert!(del_result.is_none());
    }

    #[test]
    fn find_should_return_none_when_empty() {
        let table = Table::<Value>::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let s = table.find(&key.as_ref().data, key.as_ref().hash);
        assert!(s.is_none());
    }

    #[test]
    fn find_should_return_inserted_strings() {
        let table = Table::default();
        let mut heap = Heap::default();
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());

        table.set(key1, Value::Nil);
        table.set(key2, Value::Nil);

        let s1 = table.find(&key1.as_ref().data, key1.as_ref().hash).unwrap();
        let s2 = table.find(&key2.as_ref().data, key2.as_ref().hash).unwrap();
        assert!(Gc::ptr_eq(s1, key1));
        assert!(Gc::ptr_eq(s2, key2));
    }
}
