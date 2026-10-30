//! Dynamic stack measurement by stack painting (x86_64 Linux). Each public `api` function runs on a fresh
//! thread with a large stack. Before the call, the unused part of the stack below the current frame is filled
//! with a pattern; after it, the lowest overwritten word gives the high-water mark. The reported number is
//! measured from the stack pointer at the call instruction, so it includes the pushed return address and the
//! frames of everything the function calls, but not the caller's frame or the caller's result slot.
use ml_dsa_verified::api;
use std::arch::asm;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};

const THREAD_STACK: usize = 16 << 20;
const PAINT: usize = 12 << 20;
const PATTERN: u64 = 0xA5A5_A5A5_A5A5_A5A5;

static SP_AT_CALL: AtomicUsize = AtomicUsize::new(0);

#[inline(always)]
fn read_sp() -> usize {
    let sp: usize;
    unsafe { asm!("mov {}, rsp", out(reg) sp, options(nomem, nostack, preserves_flags)) };
    sp
}

/// Marks the stack pointer right before the measured call.
#[inline(always)]
fn mark() {
    SP_AT_CALL.store(read_sp(), Ordering::Relaxed);
}

/// Paints, runs `f`, returns the number of bytes used below the marked stack pointer (including the return
/// address pushed by the call). `usize::MAX` if the whole painted area was touched.
#[inline(never)]
fn measure(f: &mut dyn FnMut()) -> usize {
    let sp0 = read_sp();
    let top = (sp0 - 16) & !7;
    let bottom = top - PAINT;
    let mut a = bottom;
    while a < top {
        unsafe { (a as *mut u64).write_volatile(PATTERN) };
        a += 8;
    }
    f();
    let mut a = bottom;
    while a < top && unsafe { (a as *const u64).read_volatile() } == PATTERN {
        a += 8;
    }
    if a == bottom {
        return usize::MAX;
    }
    SP_AT_CALL.load(Ordering::Relaxed) - a
}

/// Runs `body` (which must call `mark()` immediately before the api call) on a fresh big-stack thread.
fn on_thread(body: impl FnOnce() + Send + 'static) -> usize {
    std::thread::Builder::new()
        .stack_size(THREAD_STACK)
        .spawn(move || {
            let mut body = Some(body);
            measure(&mut || (body.take().unwrap())())
        })
        .unwrap()
        .join()
        .unwrap()
}

macro_rules! set {
    ($tag:literal, $keygen:ident, $sign:ident, $verify:ident, $sign_i:ident, $verify_i:ident, $wf:ident,
     $out:ident) => {{
        let xi = [0x42u8; 32];
        let (pk, sk) = api::$keygen(&xi);
        let rnd = [0u8; 32];
        let msg = b"stack measurement message".to_vec();
        let ctx = b"ctx".to_vec();
        let sig = api::$sign(&sk, &msg, &ctx, &rnd).unwrap();
        assert!(api::$verify(&pk, &msg, &ctx, &sig));
        assert!(api::$wf(&sk));
        let sig_i = api::$sign_i(&sk, &msg, &rnd).unwrap();
        assert!(api::$verify_i(&pk, &msg, &sig_i));
        // Three runs each; report the maximum (the paths are deterministic, so they should agree).
        let rep = |f: &dyn Fn() -> usize| (0..3).map(|_| f()).max().unwrap();
        $out.push((concat!("keygen_", $tag), rep(&|| on_thread(move || { mark(); black_box(api::$keygen(black_box(&xi))); }))));
        $out.push((concat!("sign_", $tag), rep(&|| { let (sk, msg, ctx) = (sk, msg.clone(), ctx.clone()); on_thread(move || { mark(); black_box(api::$sign(black_box(&sk), &msg, &ctx, &rnd)); }) })));
        $out.push((concat!("verify_", $tag), rep(&|| { let (pk, sig, msg, ctx) = (pk, sig, msg.clone(), ctx.clone()); on_thread(move || { mark(); black_box(api::$verify(black_box(&pk), &msg, &ctx, &sig)); }) })));
        $out.push((concat!("sign_internal_", $tag), rep(&|| { let (sk, msg) = (sk, msg.clone()); on_thread(move || { mark(); black_box(api::$sign_i(black_box(&sk), &msg, &rnd)); }) })));
        $out.push((concat!("verify_internal_", $tag), rep(&|| { let (pk, sig_i, msg) = (pk, sig_i, msg.clone()); on_thread(move || { mark(); black_box(api::$verify_i(black_box(&pk), &msg, &sig_i)); }) })));
        $out.push((concat!("sk_is_well_formed_", $tag), rep(&|| { let sk = sk; on_thread(move || { mark(); black_box(api::$wf(black_box(&sk))); }) })));
    }};
}

fn main() {
    let mut out: Vec<(&'static str, usize)> = Vec::new();
    // Baseline: a thread that does nothing between mark and return.
    let base = (0..3).map(|_| on_thread(|| { mark(); black_box(0u8); })).max().unwrap();
    println!("dyn baseline {base}");
    set!("44", keygen_44, sign_44, verify_44, sign_internal_44, verify_internal_44, sk_is_well_formed_44, out);
    set!("65", keygen_65, sign_65, verify_65, sign_internal_65, verify_internal_65, sk_is_well_formed_65, out);
    set!("87", keygen_87, sign_87, verify_87, sign_internal_87, verify_internal_87, sk_is_well_formed_87, out);
    for (name, bytes) in out {
        println!("dyn {name} {bytes}");
    }
}
