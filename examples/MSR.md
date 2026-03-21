# Mosaic Static Regions
 
Mosaic is a language with many quirks. MSR is no exception.
 
## What's the General Idea?

MSR, or Mosaic Static Regions, is a memory management model that loosely has
lifetimes, but only at compile-time, and only implicitly.

Each function and scope generally is given its own static region by the
compiler if it is found to allocate *anywhere*, whether it be on the heap or
stack.

Unlike Rust, which has a values-own-allocations model generally, MSR uses a
regions-own-allocations model. This means that the compiler hands ownership of
an allocation over to the static region in which it exists.

All allocations owned by a static region *at its end* will be deallocated at
the end of the region. That is, its core::mem::Ref::drop method will be called.

If MSR had no idea of *allocation escaping*, then no allocations could escape,
as this would cause use-after-frees. Thus, MSR does have allocation escaping.
Allocation escaping under MSR is simply the static transfer of ownership from
one static region to another.

Allocation escaping does not neccessarily require transferral to a static
region that is higher than it, and in fact it probably happens more often when
handing over control of references temporarily to functions which take
arguments by reference.

## References

Simply put, a reference under MSR is an allocation owned by some static region.
They have one core invariant, and that is of non-nullability. References will
never be null while in scope.

There are two types of references under the MSR model: immutable (&.T) and
mutable (&T). Immutable references cannot have mutating methods of T called on
them, and furthermore the value at the address in memory specified by the
reference won't be modified while an immutable reference exists. This means
that, akin to Rust, you can have EITHER many immutable (or shared) references,
OR you can have ONE mutable (or unique) reference. This rule applies across all
static regions and is checked across static regions.

A reference does not necessarily have to be an allocation on the heap. They may
also be an allocation on the stack. The compiler will mark such references as
non-escaping, as escaping a reference to an allocation on the stack is
guaranteed to cause undefined behaviour.

If a static region uses a reference it *must* have ownership of the allocation
which the reference points to. If it does not, an error will be emmitted by the
compiler.

## Taking and Keeping Ownership of References

If you have a function which needs to take ownership of arguments passed by
reference into it and must not return ownership back to the callee's region,
then you should use the `@take` modifier on that parameter.

For example, the primary use case for this is in core::mem::Ref::drop, as once
you free an allocation once you can never use a reference to it again, lest you
cause undefined behaviour. With the `@take` modifier on `self` in the
implementation for `drop`, the compiler will not return ownership of the
allocation back to the callee's static region, and thus if it is later used an
error will be emitted by the compiler, as that region doesnt have ownership of
the reference.

Given this invariant of references, the implementation for `Ref::drop` is
actually empty by default, as the compiler, under MSR, will add a call to
deallocate `self` (as it cannot call `drop` again because programs would then
busy-wait forever whenever allocation are freed).

The default `Ref::drop` implementation under MSR would look something like this
in code:

```
fn Ref::drop(self: &Ref @take) {}
```

## Dereferencing

Most references point to class instances, which are a reference value and thus
cannot be dereferenced. For the references which point to a value type, however,
dereferencing simply copies the value into the current scope.

In this example, `x` is the value of 5. The value is stored on the stack so
that the later reference we request of it can be given to us, and technically
this counts an a sort of allocation under MSR. That reference we then assign
to `xp`. We then set `y` to be a copy of the value referenced by `xp`.`y`'s
value is stored in a register because we do not need try to obtain a reference
to it at any point. The value in the register is a copy of the value which was
on the stack in `x`.

This is a copy, but a simple bit-for-bit copy, not a full clone. Thus, the type
must implement `core::mem::Reloc` as less of a way as to indicate that it can
be cloned (this is what `core::mem::Clone` is for,  `core::mem::CheapClone`
would be closer to Rust's `Copy` trait) but rather as a marker that the type
is safe to copy and relocate to a register, stack, or  generally other place
separate from where the allocation itself lives.

```
fn main -> void @nomangle {
  let x = 5;
  let xp = &x;
  
  let y = *xp;
}
```

Given this, `core::mem::CheapClone` and `core::msr::Reloc`, while technically
independent, should usually both be implemented if either one is, as often the
`CheapClone` implementation is a simple bit-for-bit copy and thus if a
bit-for-bit copy is a valid copy than the type meets the requirements to be
safely `Reloc`.

Crucially, `CheapClone` doesn't mean 'bit-for-bit copy', it just means a clone
operation is cheap (e.g. no allocations). This means that `RefCount` can and
does implement `CheapClone` because cloning an RC is cheap. `RefCount` cannot,
however, implement `Reloc`, as a bit-for-bit copy of a `RefCount` breaks the
RC's semantic invariants.
