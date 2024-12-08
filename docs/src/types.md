# Mosaic Types
Every type in Mosaic is sized.

## Size Table
| Type     | Size (bytes)           | Bounds          |
|----------|------------------------|-----------------|
| `i8`     | 1 byte                 |                 |
| `i16`    | 2 bytes                |                 |
| `i32`    | 4 bytes                |                 |
| `i64`    | 8 bytes                |                 |
| `u8`     | 1 byte                 |                 |
| `u16`    | 2 bytes                |                 |
| `[T N]`  | `\sizeof T\` * N       |                 |
| `*T`     | 8 bytes                |                 |
| `*N[T]`  | 8 + 4 bytes            |                 |
| `*:E[T]` | 8 + `\sizeof T\` bytes | `typeof E == T` |

## Strings
For growable strings, use the `std::String` struct.
For fixed-length strings, use one of the following types:

- `[u8 N]` for strings of length N
- `*[u8 :0]` for null-terminated strings
- `*[u8]` for strings where the length is stored separately

If you need *direct* C interop, use `*u8`.
To convert `[u8 N]` to `*u8`, use `slice as *u8`.
To convert `*:0[u8]` to `*u8`, use `std::read_term_ptr(term_ptr)`
To convert `*N[u8]` to `*u8`, use `std::read_sized_ptr(sized_ptr)`

By default, string literals have a type of `[u8 N]` (where N = length of string).
The parameter `argv` of the `main` function must have type `**:0[u8]`.
