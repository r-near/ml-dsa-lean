//! Probe for scripts/check-feature-independence.sh. The function reads the build's target features, so the gate can check that the
//! flags it passes to the second extraction reach the compiler: extracted with `-C target-feature=+avx,+avx2` it must come out as
//! `true`, without them as `false`. The crate itself has no such function (scripts/cfg_inventory.py rejects `target_feature`).
#![no_std]

pub mod probe {
    pub fn avx2_enabled() -> bool {
        cfg!(target_feature = "avx2")
    }
}
