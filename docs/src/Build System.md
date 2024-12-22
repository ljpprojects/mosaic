The Mosaic Build System (`mbs`) uses a custom format for compiling libraries and executables that are hosted on the Mosaic Module Registry.

## Static Libraries

We will create two modules named 'math' and 'libc'.

**math.msc**
```rust
fn add(i32 left, i32 right) export -> i32 {
	return left + right
}

fn sub(i32 left, i32 right) export -> i32 {
	return left - right
}

fn mul(i32 left, i32 right) export -> i32 {
	return left * right
}

fn div(i32 left, i32 right) export -> f32 {
	return left / right
}
```

**libc.msc**
```rust
include std::safety
include core::casts

extern fn malloc(i32 size) -> *null

fn amalloc<T>() auto_free export -> Maybe<*T> {
	def *null ptr -> malloc(@sizeof(T))

	if ptr as isize == 0 {
		return Maybe<*T>::None
	}

	return Maybe<*T>::Some[ptr as *T]
}
```

```toml
[math]
kind="static"
dist="build/libmath.a"
backend="cranelift"
libs="$LIBS"

# 0 = none
# s = speed
# z = speed & size
opt="z"

[math.linker]
flags=["-flto", "-dead_strip"]
```