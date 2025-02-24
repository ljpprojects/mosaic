In Mosaic, there are 2 kinds of variables. Immutable and mutable variables.

Immutable variables are declared using the `let` keyword, and cannot be modified. This means that you can use neither the assignment operator (`=`) nor get the address of the variable (using `&`.) Immutable variables are represented with the value that they were initialised to.

Mutable variables are declared using the `mut` keyword, and can be modified. You can use both the `=` and `&` operators on it.

```
let x: i32 = 9
mut y: i32 = 2

x = 6 # error
y = 7
```

Since Mosaic supports type inference on variables, you shouldn't include the type in the declaration.

```
let x = 9
mut y = 2
```

## Representation

In Mosaic, constant variables are represented the actual value they contain, since they do not change. Mutable variables are represented by pointers, since they can change.

```
let x = 9 # does not allocate
mut y = 2 # allocates on the stack
```