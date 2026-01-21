![logo (a black letter m on a blue-green gradient background)](icons/mosaic-logo.svg)

# Mosaic

WELCOME TRAVELLER

Mosaic is a simple (?) compiled programming language.

This is the generally most stable release of the Mosaic compiler. See the
`nightly` branch for a probably broken compiler with new features.

## Admission of Responsiblity

I did this. I made this. I wrote it. Thank me later.

(I cannot use the excuse of the common drug known as Caffeine™ because it had no place in the development of Mosaic.)

## Dependencies

- Rust & Cargo
- `ld` unless a custom linker is specified, forgot how to though
- Bash

`install.sh` will install the `msc` binary system-wide and copy tests/std and
tests/core to the appropriate directories for them to be found by the compiler.

So to install Mosaic you would run (note that modules are added to the user's
home, so each user needs their own copy of std and core, I will fix this
eventually)

```
curl -fsSL "https://github.com/ljpprojects/mosaic/raw/refs/heads/nightly/install.sh" | bash
```

## Quirks

All operators are right precedent. ALL OF THEM. EVERY SINGLE ONE.

Operator associavity is all over the place (wait, I think the words got mixed up)

**_DO NOT EVER END A BLOCK WITH A SEMICOLON LIKE DO NOT EVER DO IT YOU WILL GET
AN ERROR AND IT WILL NOT INDICATE THAT THE ISSUE IS THE TRAILING SEMICOLON IT
WILL COMPLAIN ABOUT NOT BEING ABLE TO COMPILE STATEMENTS AND EXPRESSIONS
GLOBALLY PLEASE DO NOT DITCH THE LANGUAGE BECAUSE OF THIS OH MY GOD I NEED THIS
PLEASE_**

I have thrown you a bone and included my implementations of the stdlib and core
into `tests`.

## Documentation

Documentation can be found in [`src/lexer.rs`](src/lexer.rs),
[`src/parser.rs`](src/parser.rs), and [`src/compiler/cranelift`](src/compiler/cranelift)

## Supported Targets (tested)

- `aarch64-apple-darwin` Apple Silicon iMacs, MacBooks, etc…
- `aarch64-unknown-linux-gnu` Any Linux distro with an ARM64 chip (worked on a previosu version)
- `x86_64-apple-darwin` Intel iMacs, MacBooks, etc… (worked on a previosu version)
- `x86_64-unknown-linux-gnu` Windows WSL or any Linux distro with an x86_64 chip. (worked on a previosu version)

With extra configuration, compiling on Windows without WSL _may be_ possible.
