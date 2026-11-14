#!/usr/bin/env python3
"""The injected bugs of the sensitivity check (see inject.sh): each is a textual edit of a file of a scratch copy of lean/Spec.

    inject.py list
    inject.py check-dest DEST ROOT RUN   # validate the scratch project DEST before inject.sh writes anything to it; prints
                                         # its resolved path.  Refuses an empty path, `/`, the home directory or one of its
                                         # ancestors, a symbolic link, anything that equals, contains or lies inside ROOT (the
                                         # repository), RUN (the run directory) or a git work tree, and a non-empty directory
                                         # that this script did not create (no `.inject-scratch` marker): `rsync --delete`
                                         # runs there.
    inject.py apply NAME LEANDIR         # edit LEANDIR/Spec/<file> (a scratch copy; refuses a path under a git work tree)

Every edit must match exactly `count` times in the pristine file, so a change of the specification that moves the
code makes this script fail loudly instead of injecting nothing.
"""
import os
import subprocess
import sys

# name: (description, file, [(old, new, count)])
INJECTIONS = {
    "usehint-bound": (
        "UseHint (Algorithm 40) step 3 tests r0 >= 0 instead of r0 > 0", "Rounding.lean",
        [("if h ∧ r₀ > 0 then (r₁ + 1) % m", "if h ∧ r₀ ≥ 0 then (r₁ + 1) % m", 1)]),
    "rejbounded-bound": (
        "CoeffFromHalfByte (Algorithm 15) accepts b = 9 for eta = 4 (b < 10 instead of b < 9)", "Sampling.lean",
        [("else if η = 4 ∧ b < 9 then", "else if η = 4 ∧ b < 10 then", 1)]),
    "ctilde-order": (
        "c~ = H(w1Encode(w1) || mu) instead of H(mu || w1Encode(w1)) in Sign (step 15) and Verify (step 12)", "MLDSA.lean",
        [("H (μ ++ w1Encode p w₁) (p.lam / 4)", "H (w1Encode p w₁ ++ μ) (p.lam / 4)", 1),
         ("H (μ ++ w1Encode p w₁') (p.lam / 4)", "H (w1Encode p w₁' ++ μ) (p.lam / 4)", 1)]),
    "hintunpack-increasing": (
        "HintBitUnpack (Algorithm 21) steps 8-10 (indices strictly increasing within a row) removed", "Encode.lean",
        [("if y[Index - 1]! ≥ y[Index]! then return none", "if false then return none", 1)]),
    "hintunpack-padding": (
        "HintBitUnpack (Algorithm 21) steps 16-18 (zero padding after the last index) removed", "Encode.lean",
        [("if y[i]! ≠ 0 then return none", "if false then return none", 1)]),
    "verify-znorm": (
        "Verify_internal (Algorithm 8) step 13 tests ||z|| <= gamma1 - beta instead of < gamma1 - beta", "MLDSA.lean",
        [("decide (‖z‖∞ < p.γ₁ - p.β)", "decide (‖z‖∞ ≤ p.γ₁ - p.β)", 1)]),
    "ctx-255": (
        "Algorithms 2 and 3 refuse contexts of 255 bytes (>= 255 instead of > 255)", "MLDSA.lean",
        [("if ctx.length > 255 then return none", "if ctx.length ≥ 255 then return none", 1),
         ("if ctx.length > 255 then return some false", "if ctx.length ≥ 255 then return some false", 1)]),
}


MARKER = ".inject-scratch"


def overlaps(a, b):
    """True iff the (resolved) paths a and b are equal or one contains the other."""
    a, b = a.rstrip(os.sep) + os.sep, b.rstrip(os.sep) + os.sep
    return a.startswith(b) or b.startswith(a)


def check_dest(raw, root, run):
    """Return the resolved destination, or exit with the reason it is refused.  Writes nothing."""
    if not raw or not raw.strip():
        sys.exit("inject: INJECT_DIR is empty")
    if os.path.islink(raw.rstrip(os.sep) or os.sep):
        sys.exit(f"inject: refusing INJECT_DIR {raw!r}: it is a symbolic link")
    dest = os.path.realpath(raw)
    if dest == os.sep:
        sys.exit("inject: refusing INJECT_DIR /")
    home = os.path.realpath(os.path.expanduser("~"))
    if dest == home or (home + os.sep).startswith(dest.rstrip(os.sep) + os.sep):
        sys.exit(f"inject: refusing INJECT_DIR {dest}: it is the home directory or one of its ancestors")
    protected = {"the repository": os.path.realpath(root), "the run directory": os.path.realpath(run)}
    try:
        wt = subprocess.run(["git", "-C", root, "worktree", "list", "--porcelain"], capture_output=True, text=True)
        for ln in wt.stdout.splitlines() if wt.returncode == 0 else []:
            if ln.startswith("worktree "):
                protected[f"the git work tree {ln[9:]!r}"] = os.path.realpath(ln[9:])
    except OSError:
        pass   # no git: the realpath comparisons above and below still apply
    for what, path in protected.items():
        if overlaps(dest, path):
            sys.exit(f"inject: refusing INJECT_DIR {dest}: it overlaps {what} ({path})")
    probe = dest
    while not os.path.exists(probe):
        probe = os.path.dirname(probe)
    try:
        top = subprocess.run(["git", "-C", probe, "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    except OSError:
        top = None   # no git on this machine
    if top is not None and top.returncode == 0:
        sys.exit(f"inject: refusing INJECT_DIR {dest}: it is inside the git work tree {top.stdout.strip()}")
    if os.path.exists(dest):
        if not os.path.isdir(dest):
            sys.exit(f"inject: INJECT_DIR {dest} is not a directory")
        if os.listdir(dest) and not os.path.exists(os.path.join(dest, MARKER)):
            sys.exit(f"inject: refusing INJECT_DIR {dest}: it is not empty and has no {MARKER} marker (not created by inject.sh)")
    return dest


def main():
    if sys.argv[1] == "check-dest":
        print(check_dest(sys.argv[2], sys.argv[3], sys.argv[4]))
        return
    if sys.argv[1] == "list":
        for n, (d, f, _) in INJECTIONS.items():
            print(f"{n}\t{f}\t{d}")
        return
    assert sys.argv[1] == "apply"
    name, leandir = sys.argv[2], sys.argv[3]
    desc, fname, edits = INJECTIONS[name]
    path = os.path.join(leandir, "Spec", fname)
    try:
        top = subprocess.run(["git", "-C", leandir, "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    except OSError:
        top = None
    if top is not None and top.returncode == 0:
        sys.exit(f"refusing to edit {path}: inside a git work tree ({top.stdout.strip()}); use a scratch copy")
    s = open(path).read()
    for old, new, count in edits:
        if s.count(old) != count:
            sys.exit(f"inject {name}: expected {count} occurrence(s) of {old!r} in {fname}, found {s.count(old)}")
        s = s.replace(old, new)
    open(path, "w").write(s)
    print(f"injected {name}: {desc}")


if __name__ == "__main__":
    main()
