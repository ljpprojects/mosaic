![logo (a black letter m on a blue-green gradient background)](icons/mosaic-logo.svg)

# Mosaic

WELCOME TRAVELLER

`tests/hello.msc` is the only working test, and it requires the standard
library, which only I have lol so yeah good luck

A simple compiled programming language "heavily inspired" by Rust.

## Admission of Responsiblity

I did this. I made this. I wrote it. Thank me later.

(I cannot use the excuse of the common drug known as Caffeine™ because it had no place in the development of Mosaic.)

## Dependencies

- Rust & Cargo
- `ld` unless a custom linker is specified, forgot how though
- Shell

DO NOT USE install.sh it downloads defunct mosaic-std and mosaic-core onto your
system just use declare bindings to libc in your code

## Quirks

All operators are right precedent. ALL OF THEM. EVERY SINGLE ONE.

Operator associavity is all over the place (wait, I think the words got mixed up)

The parser will **not** be forgiving, just try.

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
