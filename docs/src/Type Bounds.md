There are X type bounds in Mosaic:
- `iter[T]` requires that the type can iterate over T. This works on `*N[T]` and `*:0[i8/u8]` if `T == i8/u8`, or any type that implements `Iter<T>`.
- `conforms[T]` requires that a pointer of the type is:
	-  The same size as T or
	- Inherits from T

You can combine bounds with `+`, negate them with `!` or require that either is true with `|`.

For example, if `T` has to be a string, this could be a function that takes a string and iterates over it:

```
fn iter_str<T: iter[i8] | iter[u8]>(T string) -> null { ... }
```