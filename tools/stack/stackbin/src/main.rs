//! Bare-metal and static-linked entry for the stack analysis: calls every wrapper once.
#![no_std]
#![no_main]

use stackbin as _;

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    stackbin::call_all();
    loop {}
}
