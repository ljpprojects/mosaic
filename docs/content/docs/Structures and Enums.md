> In Mosaic, structures and enums are very low level, and you should learn pointer arithmetic before even attempting to do this.

**It is highly encouraged to make structs packed, since it is easier to develop.**

## Structures

To define a structure in Mosaic, first declare a type alias equal to either `*any` or a pointer to the type of every field in the structure if they are the same.

```
# x: i32
# y: i32
# ratio: f64
type Foo = *any # Has multiple field types

# foo: i32
type Bar = *i32 # Only has i32 fields
```

**Try to use comments to document the fields of a struct.**

Once you have declared this, you will need the following functions to be implemented:

- `alloc() alloc -> YourStruct` (static)
- `size() -> i32` (static)
- `init(...) alloc -> YourStruct` (static)
- `deinit(self: YourStruct) dealloc -> null (member)
- Any getters and/or setters for fields

`alloc` should allocate an empty struct of the required (maximum) size. `init` should call the `alloc` function, initialise the struct, and return it. `deinit` should free any required memory used by the struct.

We will implement these functions for the `Foo` struct we declared earlier.

```
include core::alloc # import memalloc and memfree

fn Foo::size -> i32 {
    return 2 * 4 + 8
}

fn Foo::alloc export alloc -> Foo {
    return memalloc(Foo::size()) as Foo
}

fn Foo::init(x: i32, y: i32) export alloc -> Foo {
    let ptr = Foo::alloc() # get the pointer
    let ratio = (x as f64) / (y as f64) # get the ratio as an f64

    (ptr as *f64)[1] = ratio # assign Foo::ratio
    (ptr as *i32)[0] = x     # assign Foo::x
    (ptr as *i32)[1] = y     # assign Foo::y

    return ptr
}

fn Foo::deinit(self: Foo) export dealloc -> null {
    return memfree(self) # free memory allocated by Foo::alloc
}

fn Foo::x(self: Foo) -> 
```

