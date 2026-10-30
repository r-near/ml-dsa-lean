//! One exported wrapper per public `api` function. The wrappers take no arguments and read their inputs from
//! statics through `black_box`, so the compiler cannot fold the call away and each wrapper has a tiny frame of
//! its own (the returned arrays live in the wrapper's frame, which is the caller's side of the measurement).
//! The analysis walks the call graph from the `api` symbols themselves, not from these wrappers.
#![no_std]

use core::hint::black_box;
use core::ptr::addr_of;
use ml_dsa_verified::api;

static mut XI: [u8; 32] = [7; 32];
static mut RND: [u8; 32] = [9; 32];
static mut MSG: [u8; 64] = [3; 64];
static mut CTX: [u8; 16] = [5; 16];
// Largest sizes; each wrapper uses a prefix of the right size through a typed pointer cast.
static mut SK: [u8; 4896] = [1; 4896];
static mut PK: [u8; 2592] = [2; 2592];
static mut SIG: [u8; 4627] = [4; 4627];

#[cfg(not(test))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

macro_rules! exports {
    ($($n:literal, $m:ident, $keygen:ident, $sign:ident, $verify:ident, $sign_i:ident, $verify_i:ident, $wf:ident,
       $skl:literal, $pkl:literal, $sigl:literal;)*) => {$(
        pub mod $m {
            use super::*;
            #[unsafe(export_name = concat!("stk_keygen_", $n))] #[inline(never)]
            pub extern "C" fn keygen() { unsafe { black_box(api::$keygen(&*black_box(addr_of!(XI)))); } }
            #[unsafe(export_name = concat!("stk_sign_", $n))] #[inline(never)]
            pub extern "C" fn sign() { unsafe {
                let sk = &*(black_box(addr_of!(SK)) as *const [u8; $skl]);
                black_box(api::$sign(sk, &*black_box(addr_of!(MSG)), &*black_box(addr_of!(CTX)), &*black_box(addr_of!(RND))));
            } }
            #[unsafe(export_name = concat!("stk_verify_", $n))] #[inline(never)]
            pub extern "C" fn verify() { unsafe {
                let pk = &*(black_box(addr_of!(PK)) as *const [u8; $pkl]);
                let sig = &*(black_box(addr_of!(SIG)) as *const [u8; $sigl]);
                black_box(api::$verify(pk, &*black_box(addr_of!(MSG)), &*black_box(addr_of!(CTX)), sig));
            } }
            #[unsafe(export_name = concat!("stk_sign_internal_", $n))] #[inline(never)]
            pub extern "C" fn sign_internal() { unsafe {
                let sk = &*(black_box(addr_of!(SK)) as *const [u8; $skl]);
                black_box(api::$sign_i(sk, &*black_box(addr_of!(MSG)), &*black_box(addr_of!(RND))));
            } }
            #[unsafe(export_name = concat!("stk_verify_internal_", $n))] #[inline(never)]
            pub extern "C" fn verify_internal() { unsafe {
                let pk = &*(black_box(addr_of!(PK)) as *const [u8; $pkl]);
                let sig = &*(black_box(addr_of!(SIG)) as *const [u8; $sigl]);
                black_box(api::$verify_i(pk, &*black_box(addr_of!(MSG)), sig));
            } }
            #[unsafe(export_name = concat!("stk_sk_is_well_formed_", $n))] #[inline(never)]
            pub extern "C" fn sk_is_well_formed() { unsafe {
                let sk = &*(black_box(addr_of!(SK)) as *const [u8; $skl]);
                black_box(api::$wf(sk));
            } }
        }
    )*};
}

exports! {
    "44", w44, keygen_44, sign_44, verify_44, sign_internal_44, verify_internal_44, sk_is_well_formed_44, 2560, 1312, 2420;
    "65", w65, keygen_65, sign_65, verify_65, sign_internal_65, verify_internal_65, sk_is_well_formed_65, 4032, 1952, 3309;
    "87", w87, keygen_87, sign_87, verify_87, sign_internal_87, verify_internal_87, sk_is_well_formed_87, 4896, 2592, 4627;
}

/// Calls every wrapper once (used by the bare-metal `main.rs` so that nothing is garbage collected).
pub fn call_all() {
    w44::keygen(); w44::sign(); w44::verify(); w44::sign_internal(); w44::verify_internal(); w44::sk_is_well_formed();
    w65::keygen(); w65::sign(); w65::verify(); w65::sign_internal(); w65::verify_internal(); w65::sk_is_well_formed();
    w87::keygen(); w87::sign(); w87::verify(); w87::sign_internal(); w87::verify_internal(); w87::sk_is_well_formed();
}
