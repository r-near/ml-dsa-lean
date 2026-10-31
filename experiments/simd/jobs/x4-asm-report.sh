#!/usr/bin/env bash
# Summarize the asm/remarks produced by x4-asm.sh (reads $HOME/rx/scratch/simd-asm).
d="$HOME/rx/scratch/simd-asm"
echo "== real crate (x86-64-v3): statistics for the NTT/field functions"
python3 experiments/simd/jobs/asm-stats.py "$d/real_v3.s" ntt barrett field 2>&1 | head -40
echo "== x4_ntt (x86-64-v3): statistics"
python3 experiments/simd/jobs/asm-stats.py "$d/x4_v3.s" ntt shoup fold lazy mont 2>&1 | head -60
echo "== loop-vectorizer remarks for the real crate (src/ntt.rs, src/field.rs), deduplicated"
grep -E "remark|missed|loop not vectorized|vectorized loop" "$d/real.build.txt" | grep -E "ntt.rs|field.rs" | sed -E 's#/[^ ]*/(src/[a-z_]+\.rs)#\1#' | sort | uniq -c | sort -rn | head -25
echo "== loop-vectorizer remarks for x4_ntt"
grep -E "remark|missed|loop not vectorized|vectorized loop" "$d/x4.build.txt" | sed -E 's#/[^ ]*/(src/[a-z_0-9]+\.rs)#\1#' | sort | uniq -c | sort -rn | head -25
