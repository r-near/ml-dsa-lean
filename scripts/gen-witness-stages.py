# Generates the stage modules lean/Proofs/TopWitness{KA,KS,Nf1,Nf2,Ni,Nc1,Nc2,Nc3,Misc}.lean (run from lean/).
# Usage: python3 -I ../scripts/gen-witness-stages.py [dev]   ("dev" writes `by sorry`: quick elaboration checks only).
import sys
dev = len(sys.argv) > 1 and sys.argv[1] == 'dev'
PR = "by sorry" if dev else "by decide +kernel"
def hdr(extra_imports, doc):
    return ("import Proofs.TopWitnessLit\n" + "".join(f"import {m}\n" for m in extra_imports) +
            f"\n/-!\n{doc}\n-/\n\nopen Spec\n\nnamespace Proofs\nnamespace TopWitness\n\n")
def thm(name, stmt, doc):
    return (f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 4000000 in\n/-- {doc} -/\n"
            f"theorem {name} :\n    {stmt} := {PR}\n\n")
END = "end TopWitness\nend Proofs\n"
files = {}

# KA: ExpandA entries
s = hdr(["Proofs.SampleA"], "# `RejNTTPoly` on the 16 seeds of `ExpandA` (ML-DSA-44, `ρ = rhoS`), with the sampled polynomials named\n\nOne kernel evaluation each (measured 10 GB, 40 s). `Data.a_r_s` are native candidates; the kernel checks them.")
for r in range(4):
    for t in range(4):
        s += thm(f"rejA_{r}_{t}", f"Spec.RejNTTPoly 512 (SampleA.pSeed rhoS {r} {t}) = some (Pl Data.a_{r}_{t})",
                 f"Entry `({r}, {t})` of `Â`.")
files["TopWitnessKA"] = s + END

# KS: ExpandS entries
s = hdr([], "# `RejBoundedPoly` on the 8 seeds of `ExpandS` (ML-DSA-44, `ρ′ = rho1S`), with the sampled polynomials named")
for r in range(4):
    s += thm(f"rejS_{r}", f"Spec.RejBoundedPoly Spec.ML_DSA_44 512 (rho1S ++ IntegerToBytes {r} 2) = some (Rl Data.s1_{r})", f"`s₁[{r}]`.")
for r in range(4):
    s += thm(f"rejS_{r+4}", f"Spec.RejBoundedPoly Spec.ML_DSA_44 512 (rho1S ++ IntegerToBytes {r+4} 2) = some (Rl Data.s2_{r})", f"`s₂[{r}]`.")
files["TopWitnessKS"] = s + END

# Nf1: forward NTT of s1, s2
s = hdr(["Proofs.TopWitnessKA"], "# Forward NTTs (kernel stage lemmas): `ŝ₁`, `ŝ₂`\n\nEach `NTT` is one kernel evaluation (measured about 15 GB and 65 s). The modules `TopWitnessKA`, ... are imported only to schedule the heavy modules one after another.")
for i in range(4):
    s += thm(f"nttF_s1_{i}", f"NTT (RPoly.toZq (Rl Data.s1_{i})) = Pl Data.s1h_{i}", f"`NTT(s₁[{i}])`.")
for i in range(4):
    s += thm(f"nttF_s2_{i}", f"NTT (RPoly.toZq (Rl Data.s2_{i})) = Pl Data.s2h_{i}", f"`NTT(s₂[{i}])`.")
files["TopWitnessNf1"] = s + END

# Nf2: forward NTT of t0, y, c
s = hdr(["Proofs.TopWitnessKS"], "# Forward NTTs (kernel stage lemmas): `t̂₀`, `NTT(y)`, `ĉ`")
for i in range(4):
    s += thm(f"nttF_t0_{i}", f"NTT (RPoly.toZq (Rl Data.t0_{i})) = Pl Data.t0h_{i}", f"`NTT(t₀[{i}])`.")
for i in range(4):
    s += thm(f"nttF_y_{i}", f"NTT (Pl Data.y_{i}) = Pl Data.yh_{i}", f"`NTT(y[{i}])`.")
s += thm("nttF_c", "NTT (RPoly.toZq (Rl Data.cL)) = Pl Data.ch", "`ĉ = NTT(c)`.")
files["TopWitnessNf2"] = s + END

# Ni: inverse NTT for t and w (imports Misc)
s = hdr(["Proofs.TopWitnessMisc"], "# Inverse NTTs (kernel stage lemmas): `t = NTT⁻¹(Â ŝ₁) + s₂` of KeyGen, `w = NTT⁻¹(Â NTT(y))` of Sign")
for i in range(4):
    s += thm(f"nttI_t_{i}", f"NTTInv (Pl Data.mv_{i}) + RPoly.toZq (Rl Data.s2_{i}) = Pl Data.t_{i}", f"`t[{i}]`.")
for i in range(4):
    s += thm(f"nttI_w_{i}", f"NTTInv (Pl Data.wmv_{i}) = Pl Data.w_{i}", f"`w[{i}]`.")
files["TopWitnessNi"] = s + END

def prod(a, b): return f"Vector.zipWith (· * ·) (Pl Data.{a}) (Pl Data.{b})"
for name, pred, tag, src in [("TopWitnessNc1", "Proofs.TopWitnessNf1", "cs1", "s1h"),
                             ("TopWitnessNc2", "Proofs.TopWitnessNf2", "cs2", "s2h"),
                             ("TopWitnessNc3", "Proofs.TopWitnessNi", "ct0", "t0h")]:
    s = hdr([pred], f"# Inverse NTTs of `ĉ ∘ ·` (kernel stage lemmas): `{tag}`")
    for i in range(4):
        s += thm(f"nttI_{tag}_{i}", f"NTTInv ({prod('ch', f'{src}_{i}')}) = Pl Data.{tag}_{i}", f"`{tag}[{i}]`.")
    files[name] = s + END

# Misc: the cheaper kernel stage lemmas
s = hdr(["Proofs.TopWitnessFast"], "# Cheaper kernel stage lemmas of the witnesses (matrix-vector products, rounding, hashes, packing)")
s += thm("mv_lit", "Spec.MatrixVectorNTT Av S1hv = MVv", "`Â ∘ ŝ₁` (KeyGen step 5).").replace(PR, "by rw [MatrixVectorNTT_fast]; " + PR[3:])
s += thm("p2r_lit", "Spec.Power2RoundVec Spec.ML_DSA_44 Tv = (T1v, T0v)", "KeyGen step 6.")
s += thm("pk_lit", "pkEncodeF Spec.ML_DSA_44 rhoS T1v = Data.pkL", "The public key (`pkEncode` with the fast packing).")
s += thm("tr_lit", "Spec.H Data.pkL 64 = Data.trL", "`tr = H(pk, 64)`.")
s += thm("kL_eq", "Spec.slice outL 96 32 = Data.kL", "`K`.")
s += thm("mu_lit", "Spec.H (Data.trL ++ [0, 0, 0]) 64 = Data.muL", "`μ = H(tr ‖ M′, 64)` for `M′ = 0 ‖ 0 ‖ [0]`.")
s += thm("rho2_lit", "Spec.H (Data.kL ++ List.replicate 32 0 ++ Data.muL) 64 = Data.rho2L", "`ρ″ = H(K ‖ rnd ‖ μ, 64)`.")
for r in range(4):
    s += thm(f"yb_{r}", f"Spec.H (Data.rho2L ++ IntegerToBytes (0 + {r}) 2) (32 * (1 + bitlen (Spec.ML_DSA_44.γ₁ - 1))) = Data.yb_{r}", f"The SHAKE256 bytes of `ExpandMask` row {r}.")
for r in range(4):
    s += thm(f"mask_{r}", f"RPoly.toZq (BitUnpackF Data.yb_{r} (Spec.ML_DSA_44.γ₁ - 1) Spec.ML_DSA_44.γ₁) = Pl Data.y_{r}", f"`y[{r}]` (`BitUnpack` with the fast unpacking).")
s += thm("wmv_lit", "Spec.MatrixVectorNTT Av Yhv = WMVv", "`Â ∘ NTT(y)` (Sign step 12).").replace(PR, "by rw [MatrixVectorNTT_fast]; " + PR[3:])
s += thm("w1_lit", "Spec.HighBitsVec Spec.ML_DSA_44 Wv = W1v", "`w₁ = HighBits(w)`.")
s += thm("w1b_lit", "w1EncodeF Spec.ML_DSA_44 W1v = Data.w1bL", "`w1Encode(w₁)` with the fast packing.")
s += thm("ct_lit", "Spec.H (Data.muL ++ Data.w1bL) (Spec.ML_DSA_44.lam / 4) = Data.ctL", "`c̃ = H(μ ‖ w1Encode(w₁), λ/4)`.")
s += thm("sib_lit", "Spec.SampleInBall Spec.ML_DSA_44 512 Data.ctL = some Cp", "`c = SampleInBall(c̃)`.")
files["TopWitnessMisc"] = s + END

for n, c in files.items():
    open(f"Proofs/{n}.lean", "w").write(c)
print("wrote", list(files))
