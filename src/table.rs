use std::{alloc, mem, ptr::NonNull};

use crate::object::{Gc, RefStringV2};

#[derive(Debug)]
pub(crate) struct Table<V> {
    ptr: NonNull<Entry<V>>,
    capacity: usize,
    occupants: usize,
    tombstones: usize,
}

impl<V> Table<V> {
    pub(crate) fn del(&mut self, key: RefStringV2) -> Option<V> {
        if self.occupants == 0 {
            return None;
        }
        let entry = unsafe { &mut *self.find_entry(key) };
        let entry_old = mem::replace(entry, Entry::Tombstone);
        if let Entry::Occupied(e) = entry_old {
            self.occupants -= 1;
            self.tombstones += 1;
            Some(e.val)
        } else {
            None
        }
    }

    pub(crate) fn find(&self, s: &str, hash: u32) -> Option<RefStringV2> {
        if self.occupants == 0 {
            return None;
        }
        let mut index = hash as usize & (self.capacity - 1);
        loop {
            let entry_ptr = unsafe { self.ptr.as_ptr().add(index) };
            let entry = unsafe { &*entry_ptr };
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

    pub fn iter(&self) -> TableIter<V> {
        TableIter {
            ptr: self.ptr.as_ptr(),
            end: unsafe { self.ptr.as_ptr().add(self.capacity) },
        }
    }

    /// Find the entry associated with the given key. If the 2 different keys have the same hash,
    /// linear probing is used to find the correct entry.
    fn find_entry(&self, key: RefStringV2) -> *mut Entry<V> {
        let mut tombstone = None;
        let mut index = key.hash as usize & (self.capacity - 1);
        loop {
            let entry_ptr = unsafe { self.ptr.as_ptr().add(index) };
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

    fn entries_layout(cap: usize) -> alloc::Layout {
        alloc::Layout::array::<Entry<V>>(cap).expect("Invalid layout.")
    }
}

impl<V: Copy> Table<V> {
    /// Set the value associated with the given key.
    /// If the key is already present, the previous value is returned.
    pub(crate) fn set(&mut self, key: RefStringV2, val: V) -> Option<V> {
        if self.occupants + self.tombstones >= self.capacity * 3 / 4 {
            let cap = self.capacity * 2;
            self.resize(cap.max(8));
        }
        let entry = unsafe { &mut *self.find_entry(key) };
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

    pub(crate) fn get(&self, key: RefStringV2) -> Option<V> {
        if self.occupants == 0 {
            return None;
        }
        let entry = unsafe { &*self.find_entry(key) };
        if let Entry::Occupied(e) = entry {
            Some(e.val)
        } else {
            None
        }
    }

    /// Resize the table to the given capacity.
    fn resize(&mut self, cap_new: usize) {
        // Allocate the new array.
        let cap_old = self.capacity;
        let ptr_old = self.ptr.as_ptr();
        self.capacity = cap_new;
        self.ptr = unsafe {
            NonNull::new_unchecked(alloc::alloc(Self::entries_layout(self.capacity)).cast())
        };
        // Initalized the new array.
        for i in 0..self.capacity {
            let entry = unsafe { &mut *self.ptr.as_ptr().add(i) };
            *entry = Entry::Vaccant;
        }
        // Rehash existing entries and copy them over to the new array.
        self.tombstones = 0;
        for i in 0..cap_old {
            let entry_old = unsafe { &*ptr_old.add(i) };
            if let Entry::Occupied(e) = &entry_old {
                let entry_new = unsafe { &mut *self.find_entry(e.key) };
                *entry_new = Entry::Occupied(EntryInner {
                    key: e.key,
                    val: e.val,
                });
            }
        }
        // Deallocate the old array.
        if cap_old > 0 {
            unsafe { alloc::dealloc(ptr_old.cast(), Self::entries_layout(cap_old)) };
        }
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
        if self.capacity > 0 {
            unsafe {
                alloc::dealloc(
                    self.ptr.as_ptr().cast(),
                    Self::entries_layout(self.capacity),
                );
            }
        }
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
    key: RefStringV2,
    val: V,
}

pub struct TableIter<V> {
    ptr: *mut Entry<V>,
    end: *const Entry<V>,
}

impl<V: Copy> Iterator for TableIter<V> {
    type Item = (RefStringV2, V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.ptr as *const Entry<V> != self.end {
            let entry = unsafe { &*self.ptr };
            self.ptr = unsafe { self.ptr.add(1) };
            if let Entry::Occupied(x) = entry {
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
        let get_result = table.get(key);
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
