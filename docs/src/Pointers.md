Pointers in Mosaic are always mutable. This means that the following code returns an error:

```
let foo: i32 = 0
let ptr: *i32 = &foo
```

This is because the pointer can be dereferenced and mutated, even though `foo` is declared to be constant.

There is more than one kind of pointer in Mosaic. They all compile to normal C pointers. The first, which is explicitly a C pointer, is declared like this: `*T`. The next is a sized array type, or slice. It is declared like this: `*N[T]`, where N is the number of elements. No metadata needs to be stored in the value, since the length is stored in the type, which the compiler always knows. The last ones are special. They are terminated pointers. These are only to be used for null-terminated strings (i.e. A C string). There are 2 valid variants, `*:0[i8]` and `*:0[u8]`.

## Writing to a Pointer
In Mosaic, there is only 1 way to write to pointers. It is to use the assignment operation and dereference the left-hand side of the assignment, like Rust:

```
*ptr = VALUE
```

## Casting Pointers
In Mosaic, there are 2 ways to cast pointers. One is to use a standard `as` cast:

```
ptr as *T
```

Since this cast is always unsafe (as the compiler does not type checking), it is recommended to use the `std::ptr::pcast` function if you cannot be sure that the cast is safe:

```
include std::ptr

pcast<T>(ptr)
```

One example where you cannot be sure that the cast is safe is when using type generics:

```
include std::ptr

fn some_ptr_thing<T>(*any ptr, bool should_cast) -> null {
	if should_cast {
		let casted: *T = pcast<T>(ptr)
		# use the pointer
	}
}
```

The `pcast` function is safe because it uses the type system in Mosaic to make sure that the pointer types are compatible at compile time. It is defined with this signature:

```
fn pcast<A: inner, B: inner[conforms[A]]>(from: A) -> B {
	return from as B
}
```

See [[Type Bounds]] for more info.

If you need to iterate over a `*T`, there are 2 options:

Use the `@to_sized(ptr, len)` macro if `len` is known at compile time.

 If you do not know the length of the array at compile time, or it is a function parameter (e.g. `i32 argc` of a main function), use the `List` structure:

```
List::from_ptr_and_len(ptr, len)
```