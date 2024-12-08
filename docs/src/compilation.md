# Compilation

## Modules
When compiling, if you use `std::internal::print`,
the compiler looks for `std/internal.o` (for linking),
but when trying to perform type checking, looks for `std/internal.mosaic`.

**std/internal.mosaic**
```
mod internal

extern fn print(cstr s) -> null
extern fn println(cstr s) -> null
extern fn readln() -> cstr
```

if you used `project::fns::do_stuff` and `project/fns.o` didn't exist,
then `project/fns.mosaic` would be compiled alongside the current file being compiled.