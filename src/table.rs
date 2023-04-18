use std::{alloc, marker::PhantomData, mem, ops::Mul, ptr::NonNull};

use crate::object::{Gc, RefString};

/// A hash table mapping from `RefString` to `V`. Conflicting keys are resolved using linear probing.
#[derive(Debug)]
pub(crate) struct Table<V> {
    ptr: NonNull<Entry<V>>,
    capacity: usize,
    occupants: usize,
    tombstones: usize,
}

impl<V> Table<V> {
    /// Get the number of entries that are currently stored in the table.
    pub(crate) fn len(&self) -> usize {
        self.occupants
    }

    /// Set the value associated with the given key.
    /// If the key is already present, the previous value is returned.
    pub(crate) fn set(&mut self, key: RefString, val: V) -> Option<V> {
        if self.occupants + self.tombstones >= self.capacity * 3 / 4 {
            self.resize();
        }
        let entry = self.find_entry_mut(key);
        let entry_old = mem::replace(entry, Entry::Occupied(EntryInner { key, val }));
        match entry_old {
            Entry::Vaccant => {
                self.occupants += 1;
                None
            }
            Entry::Tombstone => {
                self.occupants += 1;
                self.tombstones -= 1;
                None
            }
            Entry::Occupied(e) => Some(e.val),
        }
    }

    // Get the value associated with the given key.
    // If the key is not present, `None` is returned.
    pub(crate) fn get(&self, key: RefString) -> Option<&V> {
        if self.occupants == 0 {
            return None;
        }
        let entry = self.find_entry(key);
        if let Entry::Occupied(e) = entry {
            Some(&e.val)
        } else {
            None
        }
    }

    // Delete the value associated with the given key and return it.
    // If the key is not present, `None` is returned.
    pub(crate) fn del(&mut self, key: RefString) -> Option<V> {
        if self.occupants == 0 {
            return None;
        }
        let entry = self.find_entry_mut(key);
        let entry_old = mem::replace(entry, Entry::Tombstone);
        if let Entry::Occupied(e) = entry_old {
            self.occupants -= 1;
            self.tombstones += 1;
            Some(e.val)
        } else {
            None
        }
    }

    /// Find the pointer to the key that matches the given string and hash.
    // If no key matches, `None` is returned.
    pub(crate) fn find(&self, s: &str, hash: u32) -> Option<RefString> {
        if self.occupants == 0 {
            return None;
        }
        let mut index = hash as usize & (self.capacity - 1);
        loop {
            // SAFETY: `index` is always less than `self.capacity` because `index = x mod self.capacity`,
            // where `x` is an arbitrary integer value.
            let entry = unsafe { &*self.ptr.as_ptr().add(index) };
            match &entry {
                Entry::Vaccant => return None,
                Entry::Occupied(e) => {
                    if e.key.data == s {
                        return Some(e.key);
                    }
                }
                _ => {}
            }
            // Linear probing.
            index = (index + 1) & (self.capacity - 1);
        }
    }

    /// Get the iterator over all entries in the table.
    pub fn iter(&self) -> TableIter<'_, V> {
        TableIter {
            ptr: self.ptr,
            ptr_: PhantomData,
            offset: 0,
            capacity: self.capacity,
        }
    }

    /// Get a shared reference the entry associated with the given key.
    fn find_entry(&self, key: RefString) -> &Entry<V> {
        // SAFETY: We make sure `probe` always returns a valid and initialized pointer.
        unsafe { &*self.probe(key) }
    }

    /// Get an exclusive reference the entry associated with the given key.
    fn find_entry_mut(&mut self, key: RefString) -> &mut Entry<V> {
        // SAFETY: We make sure `probe` always returns a valid and initialized pointer.
        unsafe { &mut *self.probe(key) }
    }

    /// Find the pointer to the entry associated with the given key. If the 2 different keys
    /// have the same hash, linear probing is used to find the correct entry.
    fn probe(&self, key: RefString) -> *mut Entry<V> {
        let mut tombstone = None;
        let mut index = key.hash as usize & (self.capacity - 1);
        loop {
            // SAFETY: `index` is always less than `self.capacity` because `index = x mod self.capacity`,
            // where `x` is an arbitrary integer value.
            let entry_ptr = unsafe { self.ptr.as_ptr().add(index) };
            // SAFETY: `entry_ptr` is always a valid pointer to an initialized `Entry<V>`.
            let entry = unsafe { &*entry_ptr };
            match &entry {
                Entry::Vaccant => {
                    return match tombstone {
                        None => entry_ptr,
                        Some(ptr) => ptr,
                    }
                }
                Entry::Tombstone => {
                    if tombstone.is_none() {
                        tombstone = Some(entry_ptr);
                    }
                }
                Entry::Occupied(e) => {
                    if Gc::ptr_eq(&e.key, &key) {
                        return entry_ptr;
                    }
                }
            }
            // Linear probing.
            index = (index + 1) & (self.capacity - 1);
        }
    }

    /// Resize the table to the given capacity.
    fn resize(&mut self) {
        // Allocate the new array.
        let old_ptr = self.ptr.as_ptr();
        let old_capacity = self.capacity;
        let new_capacity = self.capacity.mul(2).max(8);
        // SAFETY: We ensure that `new_capacity` has a minimum value of 8.
        self.ptr = unsafe { Self::alloc(new_capacity) };
        self.capacity = new_capacity;
        self.tombstones = 0;
        // Rehash existing entries and copy them over to the new array. Tombstones are ignored.
        for i in 0..old_capacity {
            // SAFETY: We only access pointers in the range of `old_ptr` and `old_ptr + old_capacity`.
            let entry_old = unsafe { &mut *old_ptr.add(i) };
            if let Entry::Occupied(e) = entry_old {
                let entry_new = self.find_entry_mut(e.key);
                mem::swap(entry_new, entry_old)
            }
        }
        // Deallocate the old array.
        // SAFETY: We ensure both `self.ptr` and `self.capacity` represent a valid array
        // that was previously allocated.
        unsafe { Self::dealloc(old_ptr, old_capacity) };
    }

    /// Allocate an array of `Entry<V>` with the given capacity and return the raw pointer
    /// to the beginning of the array.
    ///
    /// ## Safety
    ///
    /// `capacity` must be larger than 0, otherwise, it's undefined behaviour.
    unsafe fn alloc(capacity: usize) -> NonNull<Entry<V>> {
        // SAFETY: The caller of this function must ensure that `capacity` is larger than 0.
        let ptr: *mut Entry<V> = unsafe { alloc::alloc(Self::entries_layout(capacity)).cast() };
        for i in 0..capacity {
            // SAFETY: We only access pointers in the range of `ptr` and `ptr + capacity`.
            unsafe { ptr.add(i).write(Entry::Vaccant) };
        }
        // SAFETY: We just allocated, thus `ptr` must be non-null.
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
            // SAFETY: The caller of this function must ensure that `ptr` is a valid pointer to
            // the array of `Entry<V>` with the given `capacity`.
            unsafe { alloc::dealloc(ptr.cast(), Self::entries_layout(capacity)) };
        }
    }

    /// Return the memory layout of an array of `Entry<V>` with the given capacity.
    fn entries_layout(cap: usize) -> alloc::Layout {
        alloc::Layout::array::<Entry<V>>(cap).expect("Invalid layout.")
    }
}

impl<V> Default for Table<V> {
    fn default() -> Self {
        Self {
            ptr: NonNull::dangling(),
            capacity: 0,
            occupants: 0,
            tombstones: 0,
        }
    }
}

impl<V> Drop for Table<V> {
    fn drop(&mut self) {
        // SAFETY: We ensure both `self.ptr` and `self.capacity` represent a valid array.
        unsafe { Self::dealloc(self.ptr.as_ptr(), self.capacity) };
    }
}

#[derive(Debug)]
enum Entry<V> {
    Vaccant,
    Tombstone,
    Occupied(EntryInner<V>),
}

#[derive(Debug)]
struct EntryInner<V> {
    key: RefString,
    val: V,
}

pub struct TableIter<'table, V> {
    ptr: NonNull<Entry<V>>,
    ptr_: PhantomData<&'table Entry<V>>,
    offset: usize,
    capacity: usize,
}

impl<'table, V> Iterator for TableIter<'table, V> {
    type Item = (RefString, &'table V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.offset < self.capacity {
            // SAFETY: The caller of this function must ensure that `ptr` is a valid pointer to
            // the array of `Entry<V>` with the given `capacity`. Additionally, `self.offset`
            // is always less than `self.capacity`.
            let entry = unsafe { &*self.ptr.as_ptr().add(self.offset) };
            self.offset += 1;
            if let Entry::Occupied(x) = entry {
                return Some((x.key, &x.val));
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
        assert_eq!(0, table.capacity);
        assert_eq!(0, table.occupants);
        assert_eq!(0, table.tombstones);
    }

    #[test]
    fn set_should_update_table_metadata() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());

        table.set(key1, Value::Number(PI));
        assert_eq!(8, table.capacity);
        assert_eq!(1, table.occupants);
        assert_eq!(0, table.tombstones);

        table.set(key2, Value::Number(PI));
        assert_eq!(8, table.capacity);
        assert_eq!(2, table.occupants);
        assert_eq!(0, table.tombstones);
    }

    #[test]
    fn set_should_return_previous_value() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let prev = table.set(key, Value::Bool(true));
        assert!(matches!(prev, None));

        let prev = table.set(key, Value::Number(PI));
        assert!(matches!(prev, Some(Value::Bool(true))));
    }

    #[test]
    fn set_should_not_change_number_of_occupants_when_overwriting() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants);
        table.set(key, Value::Number(PI));
        assert_eq!(1, table.occupants);
    }

    #[test]
    fn set_should_update_tombstones_count() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants);
        assert_eq!(0, table.tombstones);

        table.del(key);
        assert_eq!(0, table.occupants);
        assert_eq!(1, table.tombstones);

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants);
        assert_eq!(0, table.tombstones);
    }

    #[test]
    fn get_from_empty_table() {
        let table = Table::<Value>::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let val = table.get(key);
        assert!(matches!(val, None));
    }

    #[test]
    fn get_existing_keys() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        let val = table.get(key);
        assert!(matches!(val, Some(Value::Bool(true))));
    }

    #[test]
    fn get_last_set_value() {
        let mut table = Table::default();
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
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        assert_eq!(1, table.occupants);
        assert_eq!(0, table.tombstones);

        let prev = table.del(key);
        assert!(matches!(prev, Some(Value::Bool(true))));
        assert_eq!(0, table.occupants);
        assert_eq!(1, table.tombstones);
    }

    #[test]
    fn del_should_remove_key() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        table.set(key, Value::Bool(true));
        let get_result = table.get(key).copied();
        let del_result = table.del(key);
        assert_eq!(get_result, del_result);
        let del_result = table.del(key);
        assert!(matches!(del_result, None));
    }

    #[test]
    fn find_should_return_none_when_empty() {
        let table = Table::<Value>::default();
        let mut heap = Heap::default();
        let key = heap.intern("key".to_string());

        let s = table.find(&key.data, key.hash);
        assert!(matches!(s, None));
    }

    #[test]
    fn find_should_return_inserted_strings() {
        let mut table = Table::default();
        let mut heap = Heap::default();
        let key1 = heap.intern("key1".to_string());
        let key2 = heap.intern("key2".to_string());

        table.set(key1, Value::Nil);
        table.set(key2, Value::Nil);

        let s1 = table.find(&key1.data, key1.hash).unwrap();
        let s2 = table.find(&key2.data, key2.hash).unwrap();
        assert!(Gc::ptr_eq(&s1, &key1));
        assert!(Gc::ptr_eq(&s2, &key2));
    }
}
