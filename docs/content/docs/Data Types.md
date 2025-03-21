+++
date = '2025-02-10T07:04:46+11:00'
draft = true
title = 'Data Types'
+++

In Mosaic, types are needed in most declarations, since it is a statically typed language. There is 1 zero-sized type, `null`, which is like `void` in other languages. To create a null pointer, see [[Pointers]].

## Zero-sized types

In Mosaic, there is one zero-sized type (ZST), `null`, which is equivalent to C's `void` type.

## Unsized types

In Mosaic, all types have a size known at compile time, so any unsized types (UTs) must always be behind some kind of indirection (see [[Indirection]].) One UT is the `any` type, which is most commonly used as `*any`, which allows any Mosaic pointer, after a cast (see [[Casts]].) At the moment, you cannot declare custom UTs.

This is a list of Mosaic's UTs:
* `any`
* `[T]`

## Scalar Types

In Mosaic, most of the core types are scalar, and hold just one value. These include integer types (see [[Integers]]), floating point types (see [[Floats]]) and all pointers (see [[Pointers]]).

### Integers

In Mosaic, these are the integer types:

| Size   | Signed type | Unsigned type |
| ------ | ----------- | ------------- |
| 8-bit  | `i8`        | `u8`          |
| 16-bit | `i16`       | `u16`         |
| 32-bit | `i32`       | `u32`         |
| 64-bit | `i64`       | `u64`         |
| arch   | `iarch`     | `uarch`       |
If a type is unsigned, is simply means that it cannot be negative. This allows for a higher maximum value. Unsigned types can store values within these limits, assuming `n` is the size (in bits) of the integer type.

$$max=2^n-1$$
$$min=0$$

Signed types can store any value within these limits.

$$max = 2^{n-1} - 1$$
$$min=-(2^{n-1})$$

This means that `i8` (which is equivalent to C's `char`) can store values from 127 to -128. `u8` can store values from 0 to 255.

The `iarch` and `uarch` types represent the integer type that has the same size as pointers on the target device. This means that the size of all pointers are equal to the size of `isize` and `usize`. For example, if your target is a 32-bit device, then the size of pointers is 32 bits, so the size of `iarch` and `uarch` is also 32 bits.

All integer literals have the type `i32`.

### Floats

In Mosaic, there are 2 types of floats:

| Size    | Type  |
| ------- | ----- |
| 32-bits | `f32` |
| 64-bits | `f64` |
These floating point types are always signed. See the [IEEE 754 standard](https://en.wikipedia.org/wiki/IEEE_754#Basic_and_interchange_formats) for more info.

All floating point literals have the type `f64`.

### Pointers

**NOTE:** This section expects that you know what a pointer is and how they work.

In Mosaic, there are 5 kinds of pointers. This is a lot, until you realise Rust has 4 (`*const`, `*mut`, `&`, `&mut`). In Mosaic, however, the different types of pointers do not represent mutability, but instead the type of data it points to and how to interpret that data.

| Type      | Description                               | Rust equivalent                   |
| --------- | ----------------------------------------- | --------------------------------- |
| `*T`      | A regular pointer to `T`                  | `*mut T`                          |
| `*[T]`    | A pointer to `T` with runtime length      | N/A (closest to `*mut [T]`)       |
| `*N[T]`   | A pointer to `T` with compile-time length | `*mut [T; N]` + compile-time info |
| `*:0[i8]` | A C string (of signed characters)         | `*mut i8` + null-termination      |
| `*:0[u8]` | A C string (of unsigned characters)       | `*mut u8` + null-termination      |
|           |                                           |                                   |
The most unusual one is the fat pointer (the 2nd one), as it has no direct Rust equivalent. it is a normal pointer in every way except that the first 4 bytes that it points to are always reserved to store the length.

```
[length 0-3] [data 3-end]
```

This means that when allocated a slice, add 4 extra bytes to the size or use `@sizeof([T])`.
