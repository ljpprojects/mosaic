Mosaic does not have direct `struct` declarations, but instead has `type` declarations, which declares an alias to another type. If a type alias is an alias to any unsized type (i.e. `any`), it must be opaque. if a type is opaque, it can only be used when behind a pointer.

```ruby
# Foo is opaque
type *Foo = any

# Bar is not
type Bar = i32
```

Since types can have extension functions, an alias for a type is only equal to the type it aliases if the alias has no extension functions. If Foo had 2 fields — `x` and `y` — you would need to generate 3 or 5 functions — a `new` function, and getters & setters for `x` and `y`.

```ruby
include core::alloc

fn Foo::new(x: i32, y: i32) static must_free -> *Foo {
	# Foo is a packed struct
	let PADDING: i32 = 0

	mut allocation: *Foo = manmalloc(@size(x, y) + PADDING) as *Foo

	(allocation as *i32)[0] = x
	(allocation as *i32)[1] = y

	return allocation
}

fn Foo::x(self: *Foo) getter -> i32 {
	return (self as *i32)[0]
}

fn Foo::y(self: *Foo) getter -> i32 {
	return (self as *i32)[1]
}

fn Foo::x(self: *Foo, val: i32) setter -> null {
	(self as *i32)[0] = val
	return null
}

fn Foo::y(self: *Foo, val: i32) setter -> null {
	(self as *i32)[1] = val
	return null
}
```

Instead of writing this all manually, you can use the `struct` macro, which converts a sequence of strings to a struct.

```ruby
@struct(Foo, "x: i32", "y: i32")
```