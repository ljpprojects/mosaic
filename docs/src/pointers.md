# Pointers

Pointers are possibly the most unsafe construct in Mosaic.
Internally, they do not store a type, which allows for easy casting.
If you can, it is recommended to use mutable/constant references, which
are much safer than pointers.

In memory, all pointers are simply `*mut [ReprByte]`,
where `type ReprByte = u8` and the bytes are the
internal representation of values.

## Heap Allocation

### Example
```
use std::ptr

# array of numbers
# capacity of 5
def ptr::Heap<i32> nums 
    -> ptr::heap_alloc<i32>(internal::size_of_repr<i32>() * 5)

nums.0 = 1
nums.1 = 2
nums.2 = 3
nums.3 = 4
nums.4 = 5
```

## `std::casts::reinterpret_cast`
When using `reinterpret_cast`, it takes a pointer of type `T`
and outputs a pointer of type `K` by dereferencing the pointer's contents,
converting it to it's internal representation (`[u8]`)
and using `std::internal::

### Implementation
```
use std::internal

mod casts

fn reinterpret_cast<T, K>(*T ptr) public -> *K {
    def internal::ptr_addr bytes -> internal::get_repr<T>(*ptr)
    return internal::ptr_from_addr<K>(addr)
}
```

## `std::casts:ptr_to_ref`
This cast simply converts a pointer to a constant reference.

### Example
```
use std::internal
use std::casts

def ptr::Heap<i32> ptr 
    -> ptr::heap_alloc<i32>(internal::size_of_repr<i32>())

def &'static i32 ref -> casts::ptr_to_ref(ptr)

internal::assert_eq(*ref, *ptr)
```