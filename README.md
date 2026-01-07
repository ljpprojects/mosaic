![logo (a black letter m on a blue-green gradient background)](icons/mosaic-logo.svg)

# Mosaic

WELCOME TRAVELLER
examples/hello.msc is the only working one, and it requires the standard
library, which only I have lol so yeah good luck

A simple compiled programming language "heavily inspired" by Rust.

## Dependencies

- Rust & Cargo
- `ld` unless a custom linker is specified, forgot how though
- Shell

DO NOT USE install.sh it downloads defunct mosaic-std and mosaic-core onto your
system just use C bindings

## Documentation

Documentation can be found in [`src/lexer.rs`](src/lexer.rs),
[`src/parser.rs`](src/parser.rs), and [`src/compiler/cranelift`](src/compiler/cranelift)

## Supported Targets (tested)

- `aarch64-apple-darwin` Apple Silicon iMacs, MacBooks, etc…
- `aarch64-unknown-linux-gnu` Any Linux distro with an ARM64 chip
- `x86_64-apple-darwin` Intel iMacs, MacBooks, etc…
- `x86_64-unknown-linux-gnu` Windows WSL or any Linux distro with an x86_64 chip.

With extra configuration, compiling on Windows without WSL is possible.
