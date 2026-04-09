#! /bin/bash

# This file generates an assembly file from the x86-64 linux syscall table
# It will have a general outline similar to this:
#     int _do_syscall(int nr, int argc, size_t *argv)
#     int _nr_openat()
#     int _nr_write()
#     etc...

# x86-64 MACH syscalls on Darwin
# source: https://github.com/apple-opensource/xnu/blob/master/osfmk/mach/syscall_sw.h
# format (or what we care about it):
# ITS A FUCKING C FILE but we can just use a regex

curl https://raw.githubusercontent.com/apple-opensource/xnu/refs/heads/master/osfmk/kern/syscall_sw.c | pcregrep -M "(const char \* const mach_syscall_name_table\[MACH_TRAP_TABLE_COUNT\] = {[^}]+})" | sed '/^[^/]/d' | sed -E 's/^\/\* ([0-9]+) \*\/ \"([_a-zA-Z0-9]+)\",/\1\t\2/g' | sed '/^\//d' | sed '/kern_invalid/d' | sed '/^$/d' > darwin-mach.tbl

# x86-64 BSD syscalls on Darwin
# source: https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl
# format (or what we care about it):
# NR	DEF	FLAGS	{ RT NAME(...) ...; }

curl https://raw.githubusercontent.com/apple-opensource/xnu/refs/heads/master/bsd/kern/syscalls.master | sed '/^[^0-9]/d' | sed '/nosys/d' | sed -E $'s/([0-9]+)[ \t]+[_A-Z0-9]+[ \t]+[A-Z]+[ \t]+{ [_a-zA-Z0-9]+ ([_a-zA-Z0-9]+).+/\\1\t\\2/g' | sed '/^$/d' > darwin-bsd.tbl

# MACH + BSD syscall numbers is generous enough

GENERATED_ASSEMBLY=""

gen_prelude() {
    GENERATED_ASSEMBLY+=".data"$'\n\n'
    GENERATED_ASSEMBLY+="jmp_tbl:"$'\n'

    for i in {0..5}; do
        GENERATED_ASSEMBLY+=$'\t'".quad case$i"$'\n'
    done

    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=".text"$'\n\n'
}

gen_do_syscall() {
    # %edi = int nr
    # %rsi = size_t argc
    # %rdx = size_t *argv

    # We will use %rsi as n
    # We will use %rax as i
    # We will use %r11 as v
    # We save argc into %rcx
    # We will use %r9 to hold rip relative adress of jmp_tbl

    GENERATED_ASSEMBLY+=$'.globl _do_syscall\n'
    GENERATED_ASSEMBLY+=$'_do_syscall:\n'
    GENERATED_ASSEMBLY+=$'\tmovq %rsi, %rcx\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\ttest %rsi, %rsi\n'
    GENERATED_ASSEMBLY+=$'\tjz end\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tmovq %rcx, %rax\n'
    GENERATED_ASSEMBLY+=$'\tsubq %rsi, %rax\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tcmpq $5, %rax\n'
    GENERATED_ASSEMBLY+=$'\tja case_end\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tpushq %rax\n'
    GENERATED_ASSEMBLY+=$'\tmovq %rax, %rdx\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tlea jmp_tbl(%rip), %rax\n'
    GENERATED_ASSEMBLY+=$'\tmovq (%rax, %rdx, 8), %rdx\n'
    GENERATED_ASSEMBLY+=$'\tadd %rdx, %rax\n'
    GENERATED_ASSEMBLY+=$'\n'
    GENERATED_ASSEMBLY+=$'\tjmp *%rax\n'

    REGISTERS=("rdi" "rsi" "rdx" "r10" "r8" "r9")

    for i in {0..5}; do
        GENERATED_ASSEMBLY+="case$i:"$'\n'
        GENERATED_ASSEMBLY+=$'\t'"movq %r11, %${REGISTERS[i]}"$'\n'
        GENERATED_ASSEMBLY+=$'\tjmp case_end\n'
    done;

    GENERATED_ASSEMBLY+=$'case_end:\n'
    GENERATED_ASSEMBLY+=$'\tpopq %rax\n'
    GENERATED_ASSEMBLY+=$'\tsubq $1, %rsi\n'
    GENERATED_ASSEMBLY+=$'\tjmp _do_syscall\n'
    GENERATED_ASSEMBLY+=$'end:\n'
    GENERATED_ASSEMBLY+=$'\tmovl %edi, %eax\n'
    GENERATED_ASSEMBLY+=$'\tsyscall\n'
    GENERATED_ASSEMBLY+=$'\tret\n\n'
}

create_wrapper() {
    local NR="$1"
    local NAME="$2"
    local CLASS="$3"

    if [[ "$CLASS" == "mach" ]]; then
        NR="$(echo "obase=16; $((NR + (1 << 24)))" | bc)"
    elif [[ "$CLASS" == "bsd" ]]; then
        NR="$(echo "obase=16; $((NR + (2 << 24)))" | bc)"
    fi;

   GENERATED_ASSEMBLY+=".globl _nr_$NAME"$'\n'
   GENERATED_ASSEMBLY+="_nr_$NAME:"$'\n'
   GENERATED_ASSEMBLY+=$'\t'"movl \$0x$NR, %eax"$'\n'
   GENERATED_ASSEMBLY+=$'\t'"ret"$'\n\n'
}

gen_prelude
gen_do_syscall

while IFS= read -r syscall; do
    create_wrapper $syscall bsd
done < darwin-bsd.tbl

while IFS= read -r syscall; do
    create_wrapper $syscall mach
done < darwin-mach.tbl

echo "$GENERATED_ASSEMBLY" > darwin.S