#!/usr/bin/env bash
# Fails if any `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` or `extern` exists anywhere in lean/Impl,
# lean/Spec or lean/Proofs, or in their root modules (lean/Impl.lean, lean/Spec.lean, lean/Proofs.lean). The axiom gate
# (check-axioms.sh) looks only at the dependencies of the declarations it is told about; this step looks at everything the
# three directories and their roots declare, in two independent ways:
#   * text: scripts/no_decls_text.py scans every .lean file (comments and strings removed), built or not, including the root
#     modules, for the constructs above and for the syntax that makes an opaque or unsafe declaration (`partial`, `unsafe`,
#     `initialize`, `run_cmd`, ...);
#   * Lean: scripts/lean/NoDecls.lean imports every module of the three directories and the three roots and walks the
#     environment's constants for the modules it imports (axiomInfo, opaqueInfo, implemented_by, extern, direct use of a
#     non-standard axiom, and the transitive closure's axioms). It selects by module, not by constant name.
# Scope. A source file with no built .olean cannot be scanned by the Lean half. Every module of the three directories and
# the roots must be built, with these exceptions, which are named in the output and left to the text scan:
#   * the TopWitness* modules (UNBUILT_OK below): built only by scripts/witness-check.sh, which runs this script with
#     --all-built after building them, so there the environment scan covers them too. In scripts/lean-check.sh's run the
#     scope of the environment scan is every module except those; the text scan covers all of them;
#   * Impl.FunsExternal_Template while it is byte-identical to FunsExternal (nothing imports the template).
# Any other module without a built .olean (a file nobody imports, such as a stray Proofs/Unbuilt.lean) is a failure: it
# would be skipped by the environment scan, so either import it from the root or delete it. With --all-built nothing is
# excused.
# Needs the Lean libraries built (scripts/lean-check.sh builds them first).
# Usage: scripts/check-no-decls.sh [--all-built] [--env-only|--text-only]
#        scripts/check-no-decls.sh --self-test    injects declarations into a scanned directory, and builds a fixture tree with a
#                                                 compiled root module holding an axiom and an unbuilt module holding a
#                                                 `partial def`; fails unless each is caught
set -uo pipefail
SCRIPTS="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPTS/../lean"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
DIRS=(Impl Spec Proofs)
# Modules that may stay unbuilt (named in the output, text scan only); everything else must have an .olean.
UNBUILT_OK='^Proofs\.TopWitness'
BASE=.
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

# Modules of the three directories (every .lean file) and their root modules (Impl.lean, Spec.lean, Proofs.lean), as Lean
# names. BASE is the directory that holds them (lean/, or a fixture tree in the self-test).
modules() {
  for d in "${DIRS[@]}"; do
    (cd "$BASE" && { [ -f "$d.lean" ] && echo "$d.lean"; find "$d" -name '*.lean' | sort; })
  done | sed -e 's/\.lean$//' -e 's#/#.#g'
}

# env_scan: write the driver file, run it, print its output; returns 1 on a violation or a Lean error (and, with --all-built,
# on a module without a built .olean).
env_scan() {
  local drv=.lake/no-decls-check.lean out=.lake/no-decls-check.out m libdir built=() unbuilt=() excused=()
  libdir="${LIBDIR:-$PWD/.lake/build/lib/lean}"
  if [ ! -d "$libdir" ]; then echo "NODECLS FAIL (env): $libdir does not exist: build the Lean libraries first (scripts/lean-check.sh)"; return 1; fi
  for m in $(modules); do
    if [ -f "$libdir/$(echo "$m" | tr . /).olean" ]; then built+=("$m")
    # Impl/FunsExternal_Template.lean is the file Aeneas generates; extraction copies it to Impl/FunsExternal.lean, which is the
    # module Funs.lean imports. Nothing imports the template, so it has no .olean; while it is byte-identical to the scanned
    # FunsExternal it adds no constant the scan has not seen.
    elif [ "$m" = Impl.FunsExternal_Template ] && cmp -s "$BASE/Impl/FunsExternal.lean" "$BASE/Impl/FunsExternal_Template.lean"; then :
    elif [ "$ALL_BUILT" -eq 0 ] && [[ "$m" =~ $UNBUILT_OK ]]; then excused+=("$m")
    else unbuilt+=("$m"); fi
  done
  if [ "${#unbuilt[@]}" -gt 0 ]; then
    printf 'NODECLS FAIL (env): module %s has no built .olean and is not an allowed unbuilt module (import it from its root or delete it)\n' "${unbuilt[@]}"
    return 1
  fi
  if [ "${#excused[@]}" -gt 0 ]; then
    echo "note: ${#excused[@]} allowed unbuilt module(s) (built only by scripts/witness-check.sh, which scans them with --all-built) get the text scan only: ${excused[*]}"
  fi
  { echo 'import Lean'; for m in "${built[@]}"; do echo "import $m"; done; cat "$SCRIPTS/lean/NoDecls.lean"; } > "$drv"
  if [ -n "${LIBDIR:-}" ]; then
    # Fixture tree (self-test): its modules must shadow the real ones of the same name, but `lake env` puts the workspace
    # first, so put the fixture library first on the search path and run `lean` directly.
    LEAN_PATH="$LIBDIR:$(lake env printenv LEAN_PATH)" timeout 1800 lean "$drv" > "$out" 2>&1
  else
    timeout 1800 lake env lean "$drv" > "$out" 2>&1
  fi
  local rc=$?
  cat "$out"
  [ "$rc" -eq 0 ] && grep -q '^NODECLS ENV OK' "$out"
}

text_scan() {
  local args=() d
  for d in "${DIRS[@]}"; do args+=("$BASE/$d"); [ -f "$BASE/$d.lean" ] && args+=("$BASE/$d.lean"); done
  python3 -I "$SCRIPTS/no_decls_text.py" "${args[@]}"
}

if [ "$MODE" = self-test ]; then
  python3 -I "$SCRIPTS/no_decls_text.py" --self-test || exit 1
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
  # The two coverage holes, on a fixture tree (never the real roots): a compiled root module Proofs.lean that holds an axiom,
  # and a module that nothing imports (so it has no .olean) holding a `partial def`.
  fx="$(mktemp -d)"
  trap 'rm -rf "$fx"' EXIT
  mkdir -p "$fx/Impl" "$fx/Spec" "$fx/Proofs" "$fx/lib"
  echo 'def zzImplRoot := 1' > "$fx/Impl.lean"; echo 'def zzSpecRoot := 1' > "$fx/Spec.lean"
  printf 'axiom zzRootAxiom : False\ndef zzProofsRoot := 1\n' > "$fx/Proofs.lean"
  echo 'partial def zzUnbuilt (n : Nat) : Nat := zzUnbuilt n' > "$fx/Proofs/Unbuilt.lean"
  for r in Impl Spec Proofs; do
    lake env lean -R "$fx" -o "$fx/lib/$r.olean" "$fx/$r.lean" > .lake/no-decls-selftest.out 2>&1 || { cat .lake/no-decls-selftest.out; echo "SELF-TEST FAIL: could not compile the fixture root $r"; exit 1; }
  done
  BASE="$fx"; LIBDIR="$fx/lib"
  [ "$(modules | tr '\n' ' ')" = "Impl Spec Proofs Proofs.Unbuilt " ] || { echo "SELF-TEST FAIL: the module inventory of the fixture is: $(modules | tr '\n' ' ')"; rc=1; }
  out="$(env_scan 2>&1)" && { echo "$out"; echo "SELF-TEST FAIL: the Lean scan passed a fixture with an axiom in a compiled root module and an unbuilt module"; rc=1; }
  echo "$out" | grep -qF "NODECLS FAIL (env): module Proofs.Unbuilt has no built .olean and is not an allowed unbuilt module" || { echo "SELF-TEST FAIL: the unbuilt module was not reported"; rc=1; }
  # Without the unbuilt module the Lean scan must find the axiom in the root.
  rm "$fx/Proofs/Unbuilt.lean"
  out="$(env_scan 2>&1)" && { echo "$out"; echo "SELF-TEST FAIL: the Lean scan passed an axiom in a compiled root module"; rc=1; }
  echo "$out" | grep -qF "NODECLS FAIL (env): axiom zzRootAxiom (module Proofs)" || { echo "SELF-TEST FAIL: the axiom in the root module was not reported: $out"; rc=1; }
  tout="$(text_scan 2>&1)" && { echo "SELF-TEST FAIL: the text scan passed the fixture root with an axiom"; rc=1; }
  echo "$tout" | grep -q 'Proofs.lean' || { echo "SELF-TEST FAIL: the text scan did not name the root module: $tout"; rc=1; }
  echo 'partial def zzUnbuilt (n : Nat) : Nat := zzUnbuilt n' > "$fx/Proofs/Unbuilt.lean"
  rm "$fx/Proofs.lean"; echo 'def zzProofsRoot := 1' > "$fx/Proofs.lean"
  tout="$(text_scan 2>&1)" && { echo "SELF-TEST FAIL: the text scan passed a partial def in an unbuilt module"; rc=1; }
  echo "$tout" | grep -q 'Unbuilt.lean' || { echo "SELF-TEST FAIL: the text scan did not name the unbuilt module: $tout"; rc=1; }
  rm -rf "$fx"; trap - EXIT
  [ "$rc" -eq 0 ] || exit 1
  echo "no-decls self-test OK: the Lean scan reported axiom, opaque, implemented_by, extern, sorry and native_decide in an injected Impl module and an axiom in a compiled root module, and refused an unbuilt module; the text scan named the injected module, the root module and a partial def in an unbuilt module"
  exit 0
fi

rc=0
[ "$MODE" = env ] || text_scan || rc=1
[ "$MODE" = text ] || env_scan || rc=1
if [ "$rc" -ne 0 ]; then echo "NO-DECLS GATE FAIL"; exit 1; fi
echo "NO-DECLS GATE OK"
