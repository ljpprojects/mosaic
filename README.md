![logo (a black letter m on a blue-green gradient background)](icons/mosaic-logo.svg)

# Mosaic

Mosaic is a small compiled language built using cranelift.

## Prerequisites
Mosaic needs the following libraries to run properly:
* GCC (unless you specify a custom link command every time you run `msc build`)
* Rust
* Shell (located at `/bin/sh` unless a custom path is specified)

## Documentation
Documentation can be found in the [docs](docs/src) directory
or at [the Mosaic website](https://msc.ljpprojects.org/docs/).

## Supported Targets (tested)
* `aarch64-apple-darwin` Apple Silicon iMacs, MacBooks, etc…
* `aarch64-unknown-linux-gnu` Any Linux distro with an ARM64 chip
* `x86_64-apple-darwin` Intel iMacs, MacBooks, etc…
* `x86_64-unknown-linux-gnu` Windows WSL or any Linux distro with an x86_64 chip.

Theoretically, any architecture that cranelift supports and
uses traditional UNIX paths (e.g. foo/bar/mod.msc) should work with Mosaic.

## Planned targets
* `WASM`

## Known Bugs (also on the [GitHub Repo](https://github.com/ljp-projects/mosaic) issues page)
* Insufficient compiler tracking of pointer lifetimes
leading to problems with the `must_free` annotation (temporarily removed)

## If You Are Trying to Mark My Work

First of all, wrong branch.
Second of all, please take a gander through the source code in the CORRECT branch and maybe there you can find my work. Bootstrapped.
