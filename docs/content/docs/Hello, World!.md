+++
date = '2025-02-10T07:04:46+11:00'
draft = true
title = 'Hello, World!'
+++

In Mosaic, all programs use `main` as their entry point. The `main` function cannot be mangled, so for now, you must specify `no_mangle` (see [[Modifiers]].)

To declare the entry point, you must declare a function. Function declarations look like this.

```
fn NAME(PARAM_NAME: TYPE, ...) MODIFIERS -> RET_TYPE {
	CODE
}
```

If a function has no parameters, you can omit the parentheses.

```
fn NAME MODIFIERS -> RET_TYPE {
	CODE
}
```

A simple "Hello, World!" program in mosaic would look like this:

```
include std::io

fn main no_mangle -> i32 {
    println("Hello, World!" as *[i8])

    return 0
}
```

The first line imports the `std::io` module, which has the `println` function.
Inside the main function, we call `println` and cast our string (which is a slice — see [[Slices & Fat Pointers]]) to a fat pointer, which allows the string to be iterated over (see [[Iterators]]) character-by-character, writing it to stdout. The final instruction of the function is the mandatory `return` statement. This is the exit code for the program.

## Running the Code

To run this code, execute the below commands in a terminal:

```shell
msc build hello.msc
./hello
```

The first command builds the program for your current architecture, and the second one executes the generated binary.

When using tab characters, the default is to be equivalent to 4 spaces. You can change this using the `tab-space-count` option. This is only needed for debugging purposes (to provide accurate info.)

To change the output binary, use the `-o` option.
