#!/usr/bin/env bash
# Release gate: succeeds only if the Lean workflow (.github/workflows/lean.yml) has a run for exactly the given commit in which
# the job `lean-check` finished with the conclusion `success`. A skipped job, a cancelled or failed run, a run for another
# commit and no run at all are all failures; a run that is still going is waited for.
#
# Why. The release workflow publishes whatever commit the release pull request was merged as. The proofs (lean-check: the
# Lean build, the axiom and declaration gates, the re-extraction compared with lean/Impl, the feature-independence gate) run
# in lean.yml on the same push; this script makes the release job depend on that run, so a release cannot go out from a commit
# whose proofs did not check, whatever the other required checks said.
#
# Usage: scripts/require-lean-run.sh OWNER/REPO SHA        needs `gh` and GH_TOKEN with `actions: read`
#        scripts/require-lean-run.sh --self-test           runs the cases below against a stub `gh`
# Environment (defaults): LEAN_GATE_APPEAR_SECS=900 (how long to wait for the run to show up, since the push starts both
# workflows at once), LEAN_GATE_MAX_SECS=10800 (total wait), LEAN_GATE_POLL_SECS=60, GH_BIN=gh.
set -euo pipefail

JOB="lean-check"
WORKFLOW="lean.yml"

gate() {
  local repo="$1" sha="$2"
  local gh="${GH_BIN:-gh}" appear="${LEAN_GATE_APPEAR_SECS:-900}" max="${LEAN_GATE_MAX_SECS:-10800}" poll="${LEAN_GATE_POLL_SECS:-60}"
  [[ "$sha" =~ ^[0-9a-f]{40}$ ]] || { echo "require-lean-run: not a full commit SHA: $sha" >&2; return 2; }
  local start=$SECONDS runs id status conclusion job ok pending
  while :; do
    runs="$("$gh" api "repos/$repo/actions/workflows/$WORKFLOW/runs?head_sha=$sha&per_page=50" \
              --jq '.workflow_runs[] | [.id, .status, (.conclusion // "none")] | @tsv')"
    ok=0; pending=0
    if [ -n "$runs" ]; then
      while IFS=$'\t' read -r id status conclusion; do
        if [ "$status" != completed ]; then
          pending=1; echo "Lean run $id for $sha is $status"
          continue
        fi
        job="$("$gh" api "repos/$repo/actions/runs/$id/jobs?per_page=100" \
                 --jq ".jobs[] | select(.name == \"$JOB\") | (.conclusion // \"none\")")"
        echo "Lean run $id for $sha: workflow $conclusion, job $JOB: ${job:-absent}"
        [ "$job" = success ] && ok=1
      done <<< "$runs"
    fi
    if [ "$ok" -eq 1 ]; then
      echo "require-lean-run OK: $JOB succeeded for $sha"
      return 0
    fi
    if [ -z "$runs" ]; then
      if [ $((SECONDS - start)) -ge "$appear" ]; then
        echo "require-lean-run FAIL: no $WORKFLOW run for $sha (it runs on every push to main; a release needs one)" >&2
        return 1
      fi
      echo "no $WORKFLOW run for $sha yet"
    elif [ "$pending" -eq 0 ]; then
      echo "require-lean-run FAIL: every $WORKFLOW run for $sha has finished and none has a successful $JOB job" >&2
      return 1
    fi
    if [ $((SECONDS - start)) -ge "$max" ]; then
      echo "require-lean-run FAIL: no successful $JOB job for $sha after ${max}s" >&2
      return 1
    fi
    sleep "$poll"
  done
}

self_test() {
  local t fails=0 rc
  t="$(mktemp -d)"
  trap 'rm -rf "$t"' RETURN
  # A stub gh: the runs call prints $STUB/runs.<n>.tsv (n = number of runs calls so far, the last file repeats); the jobs call
  # prints $STUB/jobs.<run id>.
  cat > "$t/gh" <<'STUB'
#!/usr/bin/env bash
case "$2" in
  */workflows/lean.yml/runs\?head_sha=*)
    n=$(( $(cat "$STUB/n" 2>/dev/null || echo 0) + 1 )); echo "$n" > "$STUB/n"
    f="$STUB/runs.$n.tsv"; while [ ! -e "$f" ] && [ "$n" -gt 1 ]; do n=$((n - 1)); f="$STUB/runs.$n.tsv"; done
    [ -e "$f" ] && cat "$f" ;;
  */actions/runs/*/jobs*) id="${2#*/runs/}"; id="${id%%/*}"; cat "$STUB/jobs.$id" 2>/dev/null || true ;;
  *) echo "stub gh: unexpected $*" >&2; exit 9 ;;
esac
exit 0
STUB
  chmod +x "$t/gh"
  local sha=0123456789abcdef0123456789abcdef01234567
  # case NAME WANT_RC: set up files in $t/s, run the gate with no waiting.
  expect() {
    local name="$1" want="$2" rc=0
    STUB="$t/s" GH_BIN="$t/gh" LEAN_GATE_APPEAR_SECS=0 LEAN_GATE_MAX_SECS="${MAXS:-0}" LEAN_GATE_POLL_SECS=0 \
      gate o/r "$sha" > "$t/out" 2>&1 || rc=$?
    if [ "$rc" -ne "$want" ]; then echo "require-lean-run self-test FAIL: $name: rc=$rc, want $want"; cat "$t/out"; fails=$((fails + 1)); fi
  }
  fresh() { rm -rf "$t/s"; mkdir -p "$t/s"; }
  export STUB="$t/s"
  fresh; printf '11\tcompleted\tsuccess\n' > "$t/s/runs.1.tsv"; echo success > "$t/s/jobs.11"
  expect 'a successful run' 0
  fresh; printf '11\tcompleted\tfailure\n' > "$t/s/runs.1.tsv"; echo failure > "$t/s/jobs.11"
  expect 'a failed job' 1
  fresh; printf '11\tcompleted\tsuccess\n' > "$t/s/runs.1.tsv"; echo skipped > "$t/s/jobs.11"
  expect 'a skipped job in a green run (the audited failure mode)' 1
  fresh; printf '11\tcompleted\tsuccess\n' > "$t/s/runs.1.tsv"; : > "$t/s/jobs.11"
  expect 'a green run without the lean-check job' 1
  fresh; printf '11\tcompleted\tcancelled\n' > "$t/s/runs.1.tsv"; echo cancelled > "$t/s/jobs.11"
  expect 'a cancelled run' 1
  fresh
  expect 'no run at all' 1
  fresh; printf '11\tcompleted\tfailure\n12\tcompleted\tsuccess\n' > "$t/s/runs.1.tsv"; echo failure > "$t/s/jobs.11"; echo success > "$t/s/jobs.12"
  expect 'an earlier failed run and a later successful rerun' 0
  fresh; printf '11\tin_progress\tnone\n' > "$t/s/runs.1.tsv"
  expect 'a run that never finishes (times out)' 1
  fresh; printf '11\tin_progress\tnone\n' > "$t/s/runs.1.tsv"; printf '11\tcompleted\tsuccess\n' > "$t/s/runs.3.tsv"; echo success > "$t/s/jobs.11"
  MAXS=60 expect 'a run that finishes successfully while waited for' 0
  fresh; printf '11\tin_progress\tnone\n' > "$t/s/runs.1.tsv"; printf '11\tcompleted\tfailure\n' > "$t/s/runs.2.tsv"; echo failure > "$t/s/jobs.11"
  MAXS=60 expect 'a run that finishes with a failure while waited for' 1
  fresh; printf '11\tcompleted\tsuccess\n' > "$t/s/runs.1.tsv"; echo success > "$t/s/jobs.11"
  rc=0; STUB="$t/s" GH_BIN="$t/gh" gate o/r not-a-sha > /dev/null 2>&1 || rc=$?
  [ "$rc" -eq 2 ] || { echo "require-lean-run self-test FAIL: a malformed SHA gave rc=$rc, want 2"; fails=$((fails + 1)); }
  if [ "$fails" -eq 0 ]; then echo "require-lean-run self-test OK"; return 0; fi
  return 1
}

case "${1:-}" in
  --self-test) self_test ;;
  "") echo "usage: $0 OWNER/REPO SHA | --self-test" >&2; exit 2 ;;
  -h | --help) sed -n '2,/^set -/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//' ;;
  *) [ $# -eq 2 ] || { echo "usage: $0 OWNER/REPO SHA | --self-test" >&2; exit 2; }; gate "$1" "$2" ;;
esac
