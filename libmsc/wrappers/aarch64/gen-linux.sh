#! /bin/bash

# This file generates an assembly file from the aarch64 linux syscall table
# It will have a general outline similar to this:
#     int _do_syscall(int nr, int argc, size_t *argv)
#     int _nr_openat()
#     int _nr_write()
#     etc...

# aarch64 system calls on Linux
# source: https://github.com/torvalds/linux/blob/master/scripts/syscall.tbl
# format (or what we care about it):
# NR	ABI	NAME

curl https://raw.githubusercontent.com/torvalds/linux/refs/heads/master/scripts/syscall.tbl | sed '/^#/d' | sed 's/  /\t/g' | sed 's/ //g' | sed '/^$/d' | sed -E $'s/([0-9]+)[ \t]+[a-zA-Z0-9]+[\t]+([_a-zA-Z0-9]+).*/\\1 \\2/' | awk '!seen[$2]++' > linux-syscalls.tbl

GENERATED_ASSEMBLY=""

gen_prelude() {
    GENERATED_ASSEMBLY+=".rodata"$'\n\n'
    GENERATED_ASSEMBLY+="jmp_tbl:"$'\n'

    for i in {0..5}; do
        GENERATED_ASSEMBLY+=$'\t'".quad case$i"$'\n'
    done

    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=".text"$'\n\n'
}

gen_do_syscall() {
    # w0 = int nr
    # x1 = size_t argc
    # x2 = size_t *argv

    # We will use x9 as n
    # We will use x10 as i
    # We will use x11 as v
    # We will use x12 to temporarily store adresses

    GENERATED_ASSEMBLY+=$'.globl _do_syscall\n'
    GENERATED_ASSEMBLY+=$'_do_syscall:\n'
    GENERATED_ASSEMBLY+=$'\tmov x9, x1\n' # n = argc
    GENERATED_ASSEMBLY+=$'loop:'
    GENERATED_ASSEMBLY+=$'\tcbz x9, end\n' # Break if n == 0
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tsub x10, x1, x9\n' # i = argc - n
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tcmp x10, #5\n'
    GENERATED_ASSEMBLY+=$'\tbgt case_end\n' # If i > 5, go to default
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tadrp x12, jmp_tbl\n' # Get the adress of jmp_tbl (relative to PC) to the nearest page (without lower 12 bits)
    GENERATED_ASSEMBLY+=$'\tadd x12, x12, :lo12:jmp_tbl\n' # Add the lower 12 bits back
    GENERATED_ASSEMBLY+=$'\tlsl x13, x10, #3\n' # Calculate offset (i << 3 = i * 8)
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tldr x11, [x2, x13]\n' # v = argv[i]
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tldr x12, [x12, x13]\n' # Load the adress from jmp_tbl with offset
    GENERATED_ASSEMBLY+=$'\tbr x12\n'

    REGISTERS=("x0" "x1" "x2" "x3" "x4" "x5")

    for i in {0..5}; do
        GENERATED_ASSEMBLY+="case$i:"$'\n'
        GENERATED_ASSEMBLY+=$'\t'"mov ${REGISTERS[i]}, x11"$'\n'
        GENERATED_ASSEMBLY+=$'\tb case_end\n'
    done;

    GENERATED_ASSEMBLY+=$'case_end:\n'
    GENERATED_ASSEMBLY+=$'\tsub x9, x9, #1\n'
    GENERATED_ASSEMBLY+=$'\tb loop\n'
    GENERATED_ASSEMBLY+=$'end:\n'
    GENERATED_ASSEMBLY+=$'\tsxtw x8, w0\n'
    GENERATED_ASSEMBLY+=$'\tsvc #0\n'
    GENERATED_ASSEMBLY+=$'\tret\n\n'
}

create_wrapper() {
    local NR="$1"
    local NAME="$2"

    GENERATED_ASSEMBLY+=".globl _nr_$2"$'\n'
    GENERATED_ASSEMBLY+="_nr_$2:"$'\n'
    GENERATED_ASSEMBLY+=$'\t'"mov x0, #$1"$'\n'
    GENERATED_ASSEMBLY+=$'\tret\n\n'
}

gen_prelude
gen_do_syscall

while IFS= read -r syscall; do
    create_wrapper $syscall
done < linux-syscalls.tbl

echo "$GENERATED_ASSEMBLY" > linux.S