# Mosaic

Mosaic is a <s>simple,</s> statically-typed compiled programming language.

**_Happy new year 1997!_**

## Statistics

It has **<s>43</s><s>117</s>133 keywords**, **22 modifiers**, and **17 string escape sequences**.

Assuming modifiers are reserved words, Mosaic has **<s>65</s><s>139</s>155 reserved words**.

## Who Created... Whatever The Hell This Thing Is?

<s>The voices in my head</s> literally look at the owner of the repo.

## Prerequisites

- C knowledge
- Objective-C MRR understanding if intending to use MRC
- Maybe just like general systems programming knowledge
- Device with architecture supported by cranelift (`aarch64`, `x86-64`, `riscv64`, `s390x`)
- OS 2000
- Rust & cargo if you build from source
- `ld` for use as the default linker
- `bash` for installer script if you use it (<s>don't</s>)
- Your user to be in the `video` group if on Linux

**NO `libc` REQUIRED** <s>the voices said I am not worthy of libc.</s> _however_
on macOS `libSystem` (which _technically_ has `libc`) is technically required
but it should be installed anyway, but on Linux no need to link with `libc` for
some tasks (e.g. basic syscalls don't need libc) and Windows users can
<s>GO TO _HELL_</s> go to hell.

## Wait if no libc then how do allocate memory

Well on macOS it just kinda uses `libmalloc` which just kinda uses `libSystem`
which just kinda has `libc`, but it doesn't explciitly need to be linked so it
may as well not be there

On Linux it kinda just uses `brk` and `sbrk` if you need big allocations just
use `libc` for now I guess

And as said previously **WINDOWS USERS CAN _GO TO HELL_**

The name of the allocator mosaic uses is `MMA` (Mosaic Multiplatform Allocator).

## Quirks

WHAT QUIRKS??!?!?!??!??!?!?! MOSAIC IS PERFECT!!!!!!!! PERFECT!!

## Documentation

Documentation can be found in <s>HELL</s> hell.

## UPDATE NEW YEAR 1997

Mr. Ant "TV Time" Tenna is FUCKING CONTAGIOUS he infects ALL of your binaries.
He embeds his little dance 10 times across mutliple sections (one in .bss (he is
initialised from one of the other sections in main), one in .data/.rodata, one
in .text, and the others in their own sections).

The section names are as follows:

1. `.lmnopolololollipop`
2. `_mr_ant_tv_time_tenna_doing_his_funny_little_jig_gif`
3. `fancy_man`
4. `HES_COMING`
5. `the_tv_time_inator`
6. `hes_groovy_and_never_glooby`
7. `_w..._w$w_w..w__w.`

And if you specify `-Oz` (speed and size) for the optimisation, it adds another 23:

8. `_________________`
9. `malwarebytes` (executable) which conatins the GIF and a function to load them into a `*u8`
10. `perms` (executable) contains GIF + no-op function named `_check_sudo`
11. `.A$B_.._.`
12. `.A$$A.BB__A`
13. `.A.AC_A$AD`
14. `.A_A.A5A$AA_1`
15. `.AV5_$AA.A.2AL.A`
16. `A.AD7___G.AA$AA$AK2`
17. `AP_A4.A$AA$XA.AA__AZW`
18. `GAA$A.AQ.GI$A.A.B_A.AA.A$W`
19. `TK$AA.26A_AXZ.LGIF_A_A0_A`
20. `.AS_AA$AA.ZA_XX$A.42A_A$A8.A$A3`

And then 10 random ones with names matching the regex: `/[a-zA-Z0-9._$]{20,40}/`

In size optimised or `--release` builds the small version of Mr. Ant
"TV Time" Tenna will appear in these sections (he is only 28KB).

In debug builds or `-O0` builds the full version of Mr. Ant "TV Time" Tenna
embeds himself into your binary (he is 168KB).
