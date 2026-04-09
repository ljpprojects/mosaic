//! Various methods of exiting the program

use std::{alloc::{Layout, alloc}, fs::File, mem::MaybeUninit, process::exit};

/// Exit the program by calling exit(c)
pub fn normal_exit(c: i32) -> ! {
    exit(c)
}

/// Exit the program by dereferencing a null pointer
pub fn segfault_exit() -> ! {
    unsafe { *(0 as *const ()) }
    loop {}
}

/// Exit the program in the most heinous way possible
/// Usually this ends up in a SIGSEGV
pub fn weird_exit() -> ! {
    use std::arch::asm;

    unsafe {
        let mut sp: usize = 0;
        let mut fp: usize = 0;

        // If none of the below apply we will dereference a null pointer anyway

        #[cfg(target_arch = "x86_64")]
        {
            asm!("mov {}, rsp", out(reg) sp);
            asm!("mov {}, rbp", out(reg) fp);
        }

        #[cfg(target_arch = "riscv64")]
        {
            asm!("addi {}, sp, 0", out(reg) sp);
            asm!("addi {}, s0, 0", out(reg) fp);
        }

        #[cfg(target_arch = "aarch64")]
        {
            asm!("mov {}, sp", out(reg) sp);
            asm!("mov {}, fp", out(reg) fp);
        }

        let sp = (sp - 32) as *mut u8;
        let fp = (fp - 32) as *mut u8;

        // load garbage into the 32 bytes before the stack pointer we got which
        // could be anything
        // Also the frame pointer too it isn't safe either
        for i in 0..32 {
            *sp = i;
            *fp = 31 - i;
        }

        // Overwrite a callee saved register (the frame pointer)
        #[cfg(target_arch = "x86_64")]
        asm!("mov rbp, 111", in(reg) sp);

        #[cfg(target_arch = "riscv64")]
        asm!("addi fp, x0, 111");

        #[cfg(target_arch = "aarch64")]
        asm!("mov x29, 111");

        // x86 stores the return address on the stack and we already messed that up

        // Overwrite the return address (make it a null pointer)
        #[cfg(target_arch = "riscv64")]
        asm!("addi ra, x0, 0");

        // Overwrite the return address (make it a null pointer)
        #[cfg(target_arch = "aarch64")]
        asm!("mov lr, 0");

        // Force the stack to be used
        let mut data = [0u8; 1024];

        for i in 0u8..1024 {
            data[i as usize] = i;
        }

        // If our program hasnt exited yet somehow just ret so it tries to jump
        // to the return address and segfaults

        #[cfg(target_arch = "x86_64")]
        asm!("ret");

        #[cfg(target_arch = "riscv64")]
        asm!("jalr x0, 0(ra)");

        #[cfg(target_arch = "aarch64")]
        asm!("ret");
    }

    loop {}
}

/// Make the program nondeterministic by changing bytes on the stack
///
/// Adds some spice to the program
///
/// Call it in mutliple varied places for better results
///
/// Sometimes it might SIGSEGV but that just increases the flavour depth
pub fn nondeterminism() {
    use std::arch::asm;

    unsafe {
        let mut sp: usize = 0;

        // If none of the below apply we will dereference a null pointer anyway

        #[cfg(target_arch = "x86_64")]
        asm!("mov {}, rsp", out(reg) sp);

        #[cfg(target_arch = "riscv64")]
        asm!("addi {}, sp, 0", out(reg) sp);

        #[cfg(target_arch = "aarch64")]
        asm!("mov {}, sp", out(reg) sp);

        let n = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as u8).unwrap_or_default() as usize;
        let sp = (sp + 13 * n) as *mut u8;

        // load garbage into some of the bytes before and after the stack
        // pointer we got
        for i in 0usize..4096 {
            if i % n >= 12 {
                continue;
            }

            let probably_now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_millis() as u8).unwrap_or_default(); // Not actully the timestamp but it will do

            *sp.sub(i) = probably_now ^ ((i % 256) as u8) << 3 ^ (i % 128) as u8;
        }
    }
}