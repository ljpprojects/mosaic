![logo (a black letter m on a blue-green gradient background)](icons/mosaic-logo.svg)

# Mosaic

A simple compiled programming language piggybacking off of other's
work.

**ONLY FOR PEOPLE WHO KNOW WHAT THEY'RE DOING**

## Dependencies
* Rust & Cargo
* `ld` unless a custom linker is specified
* Shell
* Bash (if you plan to run install.sh)
* About 3.5GB of free space

## Documentation
Just look at the compiler source code, specifically the parser.
If you cannot do this, go use Scratch or something, imbecile.
Go back from where you came, *Scratchers*.

## Supported Targets (tested)
* `aarch64-apple-darwin` Apple Silicon iMacs, MacBooks, etc…
* `aarch64-unknown-linux-gnu` Any Linux distro with an ARM64 chip
* `x86_64-apple-darwin` Intel iMacs, MacBooks, etc…
* `x86_64-unknown-linux-gnu` Windows WSL or any Linux distro with an x86_64 chip.

With extra configuration, compiling on Windows without WSL is possible.