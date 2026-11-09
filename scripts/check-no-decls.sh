#!/usr/bin/env bash
# Fails if any `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` or `extern` exists anywhere in lean/Impl,
# lean/Spec or lean/Proofs. The axiom gate (check-axioms.sh) looks only at the dependencies of the declarations it is told
# about; this step looks at everything the three directories declare, in two independent ways:
#   * text: scripts/no_decls_text.py scans every .lean file (comments and strings removed), built or not;
#   * Lean: scripts/lean/NoDecls.lean imports every module of the three directories and walks the environment's constants for
#     the modules it imports (axiomInfo, opaqueInfo, implemented_by, extern, direct use of a non-standard axiom, and the
#     transitive closure's axioms). It selects by module, not by constant name. A source file that has no built .olean
#     is named in the output and left to the text scan (the TopWitness* modules are built only by scripts/witness-check.sh);
#     with --all-built it is a failure, so after that script's build the scan covers every file.
# Needs the Lean libraries built (scripts/lean-check.sh builds them first).
# Usage: scripts/check-no-decls.sh [--all-built] [--env-only|--text-only]
#        scripts/check-no-decls.sh --self-test    injects declarations into a scanned directory and fails unless each is caught
set -uo pipefail
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
DIRS=(Impl Spec Proofs)
MODE=all
ALL_BUILT=0
for a in "$@"; do
  case "$a" in
    --all-built) ALL_BUILT=1 ;;
    --env-only) MODE=env ;;
    --text-only) MODE=text ;;
    --self-test) MODE=self-test ;;
    *) echo "usage: $0 [--all-built] [--env-only|--text-only|--self-test]" >&2; exit 2 ;;
  esac
done

# Modules of the three directories (every .lean file), as Lean names.
modules() { for d in "${DIRS[@]}"; do find "$d" -name '*.lean' | sort; done | sed -e 's/\.lean$//' -e 's#/#.#g'; }

# env_scan: write the driver file, run it, print its output; returns 1 on a violation or a Lean error (and, with --all-built,
# on a module without a built .olean).
env_scan() {
  local drv=.lake/no-decls-check.lean out=.lake/no-decls-check.out m libdir built=() unbuilt=()
  libdir="$PWD/.lake/build/lib/lean"
  if [ ! -d "$libdir" ]; then echo "NODECLS FAIL (env): $libdir does not exist: build the Lean libraries first (scripts/lean-check.sh)"; return 1; fi
  for m in $(modules); do
    if [ -f "$libdir/$(echo "$m" | tr . /).olean" ]; then built+=("$m")
    # Impl/FunsExternal_Template.lean is the file Aeneas generates; extraction copies it to Impl/FunsExternal.lean, which is the
    # module Funs.lean imports. Nothing imports the template, so it has no .olean; while it is byte-identical to the scanned
    # FunsExternal it adds no constant the scan has not seen.
    elif [ "$m" = Impl.FunsExternal_Template ] && cmp -s Impl/FunsExternal.lean Impl/FunsExternal_Template.lean; then :
    else unbuilt+=("$m"); fi
  done
  if [ "${#unbuilt[@]}" -gt 0 ]; then
    if [ "$ALL_BUILT" -eq 1 ]; then
      printf 'NODECLS FAIL (env): module %s has no built .olean\n' "${unbuilt[@]}"
      return 1
    fi
    echo "note: ${#unbuilt[@]} module(s) have no built .olean and get the text scan only: ${unbuilt[*]}"
  fi
  { echo 'import Lean'; for m in "${built[@]}"; do echo "import $m"; done; cat ../scripts/lean/NoDecls.lean; } > "$drv"
  timeout 1800 lake env lean "$drv" > "$out" 2>&1
  local rc=$?
  cat "$out"
  [ "$rc" -eq 0 ] && grep -q '^NODECLS ENV OK' "$out"
}

text_scan() { python3 -I ../scripts/no_decls_text.py "${DIRS[@]}"; }

if [ "$MODE" = self-test ]; then
  python3 -I ../scripts/no_decls_text.py --self-test || exit 1
  # Inject a module into a scanned directory, compile it to an .olean in the build directory, and expect both scans to fail
  # on it; then remove it and expect the tree to pass again.
  libdir="$PWD/.lake/build/lib/lean"
  [ -d "$libdir" ] || { echo "SELF-TEST FAIL: $libdir does not exist"; exit 1; }
  inj=Impl/ZZNoDeclsInjected.lean
  olean="$libdir/Impl/ZZNoDeclsInjected.olean"
  cleanup() { rm -f "$inj" "$olean" "${olean%.olean}.ilean" "${olean%.olean}.trace" ".lake/no-decls-selftest.out"; }
  trap cleanup EXIT
  cat > "$inj" <<'LEAN'
import Lean
axiom zzInjectedAxiom : False
opaque zzInjectedOpaque : Nat
def zzImplTarget : Nat := 1
@[implemented_by zzImplTarget] def zzInjectedImpl : Nat := 2
@[extern "zz_c"] def zzInjectedExtern : Nat := 3
theorem zzInjectedSorry : 1 = 2 := sorry
theorem zzInjectedNative : 2 + 2 = 4 := by native_decide
LEAN
  lake env lean -o "$olean" "$inj" > .lake/no-decls-selftest.out 2>&1 || { cat .lake/no-decls-selftest.out; echo "SELF-TEST FAIL: could not compile the injected module"; exit 1; }
  rc=0
  out="$(env_scan 2>&1)" && { echo "$out"; echo "SELF-TEST FAIL: the Lean scan passed with injected declarations"; rc=1; }
  for want in "axiom zzInjectedAxiom" "opaque zzInjectedOpaque" "implemented_by on zzInjectedImpl" "extern/export on zzInjectedExtern" \
              "zzInjectedSorry uses axiom sorryAx" "zzInjectedNative uses axiom"; do
    echo "$out" | grep -qF "NODECLS FAIL (env): $want" || { echo "SELF-TEST FAIL: the Lean scan did not report: $want"; rc=1; }
  done
  tout="$(text_scan 2>&1)" && { echo "SELF-TEST FAIL: the text scan passed with injected declarations"; rc=1; }
  echo "$tout" | grep -q 'ZZNoDeclsInjected' || { echo "SELF-TEST FAIL: the text scan did not name the injected file"; rc=1; }
  cleanup; trap - EXIT
  [ "$rc" -eq 0 ] || exit 1
  echo "no-decls self-test OK: the Lean scan reported axiom, opaque, implemented_by, extern, sorry and native_decide in an injected Impl module; the text scan named it"
  exit 0
fi

rc=0
[ "$MODE" = env ] || text_scan || rc=1
[ "$MODE" = text ] || env_scan || rc=1
if [ "$rc" -ne 0 ]; then echo "NO-DECLS GATE FAIL"; exit 1; fi
echo "NO-DECLS GATE OK"
