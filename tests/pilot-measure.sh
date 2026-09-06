#!/usr/bin/env bash
# Measurement harness for the cached-clone performance pilot.
#
# For every workload and every `--core=` variant it reports three
# metrics, using this project's recorded methods:
#
#   instructions  perf stat -e instructions:u, median of 3
#   wall          seconds, median of 3
#   peak RSS      process-tree ru_maxrss (RUSAGE_CHILDREN), max of 3 —
#                 this follows the re-exec'd supervised child, which a
#                 sampler on the parent would miss
#
# Every run is under `timeout` and a 16 GB address-space ulimit.
#
# THE PARITY-LANE CAVEAT, CARRIED BY THE HARNESS (task #161 S13; the
# ledger's process lesson — a caveat must live with the measurement,
# not only in prose).  `--trusted` is the unverified/parity mode, but
# only ONE of its cores is a cert-skipping parity ENGINE:
#
#   --trusted --core=production      CheckerNC/CoreNC — certificates
#                                     stripped, internals infer-only.
#                                     THE PARITY LANE, always.
#   --trusted --core=cached-parsed   a parity engine ONLY IF
#                                     `Setlec/Cached/CoreT.lean` is in
#                                     the tree (landed at `1fa6444f`).
#                                     Without it this dispatches to the
#                                     CERTIFIED cached driver with
#                                     `CheckMode.verifiedChecks = false` — the
#                                     two mode-gated checks off and
#                                     NOTHING else, every internal
#                                     certificate still running.
#   --trusted --core=cached          never a parity engine (the shared
#   --trusted --core=interned-shared pilot cores have no NC twins).
#
# A still-certifying cell's distance from `--verified` is NOT a
# verification tax; quoting it as one is the canonical table's caveat 5,
# and it has been mis-quoted at least twice.  So the `core` column below
# labels itself — `(parity)` / `*STILL-CERT`, decided by reading the
# tree — and a cell can never be quoted without its caveat.
#
# Usage:
#   tests/pilot-measure.sh [--variants=a,b,c] [--reps=N] WORKLOAD...
# where a WORKLOAD is `label=path` or `label=path::extra-flags`.
# With no workloads the default set (arena perf family + init-prelude)
# runs.
set -u
cd "$(dirname "$0")/.."

BIN=${BIN:-.lake/build/bin/setlec}
VARIANTS=${VARIANTS:-production,interned-shared,cached}
REPS=${REPS:-3}
TIMEOUT=${PILOT_TIMEOUT:-900}
MEMLIMIT_KB=${PILOT_MEMLIMIT_KB:-16777216}
MODEFLAG=${MODEFLAG:---verified}

args=()
for a in "$@"; do
  case "$a" in
    --variants=*) VARIANTS="${a#--variants=}";;
    --reps=*) REPS="${a#--reps=}";;
    --mode=*) MODEFLAG="${a#--mode=}";;
    *) args+=("$a");;
  esac
done
set -- ${args+"${args[@]}"}

[ -x "$BIN" ] || { echo "checker binary $BIN not found" >&2; exit 1; }
if ! perf stat -e instructions:u true >/dev/null 2>&1; then
  echo "perf counters unavailable — instruction counts will be blank" >&2
  HAVE_PERF=0
else
  HAVE_PERF=1
fi

WORKLOADS=("$@")
if [ "${#WORKLOADS[@]}" = 0 ]; then
  P=_tmp/arena-tests/good/perf
  WORKLOADS=(
    "init-prelude=_tmp/arena-tests/good/init-prelude.ndjson"
    "app-lam=$P/app-lam.ndjson"
    "beta-ladder=$P/beta-ladder.ndjson"
    "shared-subterm=$P/shared-subterm.ndjson"
    "repeated-subproblem=$P/repeated-subproblem.ndjson"
    "shift-cascade=$P/shift-cascade.ndjson"
    "church-numerals=$P/church-numerals.ndjson"
    "grind-ring-5=$P/grind-ring-5.ndjson"
  )
fi

median() { printf '%s\n' "$@" | sort -n | awk '{a[NR]=$0} END{print a[int((NR+1)/2)]}'; }
maxof()  { printf '%s\n' "$@" | sort -n | tail -1; }

# one run under the memory limit; prints "instr wall rss exit"
one_run() { # <core> <file> <extra...>
  local core=$1 file=$2; shift 2
  python3 - "$BIN" "$MODEFLAG" "--core=$core" "$file" "$TIMEOUT" "$MEMLIMIT_KB" "$HAVE_PERF" "$@" <<'EOF'
import os, resource, subprocess, sys, time, tempfile
binp, modeflag, coreflag, f, to, memkb, haveperf = sys.argv[1:8]
extra = sys.argv[8:]
inner = ["timeout", to, "nice", "-n", "10", binp, modeflag, coreflag] + extra + [f]
def limit():
    lim = int(memkb) * 1024
    resource.setrlimit(resource.RLIMIT_AS, (lim, lim))
perf_out = None
if haveperf == "1":
    perf_out = tempfile.mktemp()
    cmd = ["perf", "stat", "-e", "instructions:u", "-x,", "-o", perf_out] + inner
else:
    cmd = inner
t0 = time.time()
r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                   preexec_fn=limit)
wall = time.time() - t0
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
instr = ""
if perf_out:
    try:
        for line in open(perf_out):
            if "instructions" in line:
                instr = line.split(",")[0]
                break
        os.unlink(perf_out)
    except OSError:
        pass
print(f"{instr} {wall:.3f} {rss} {r.returncode}")
EOF
}

# The mode×engine label: a `--trusted` cell that is NOT a
# cert-skipping engine says so out loud (canonical table caveat 5), and
# the ones that are say `(parity)`.  Whether `--core=cached-parsed` has
# a real parity engine used to be read OFF THE TREE (`Cached/CoreT.lean`).
# Since 2026-09-06 that twin is retired and the trusted lane IS the shared
# cached driver at `.trusted` (DESIGN.md, "CORET RETIRED"), so the cached
# lane is always the trusted engine.
CACHED_PARITY_WIRED=1

core_label() {
  case "$MODEFLAG:$1" in
    --trusted:production) printf '%s' "$1(parity)";;
    --trusted:cached-parsed)
      if [ "$CACHED_PARITY_WIRED" = 1 ]
      then printf '%s' "$1(parity)"
      else printf '%s' "$1*STILL-CERT"; fi;;
    --trusted:cached|--trusted:interned-shared) printf '%s' "$1*STILL-CERT";;
    *) printf '%s' "$1";;
  esac
}

if [ "$MODEFLAG" = "--trusted" ]; then
  echo "note: *STILL-CERT = the certified driver with verified=false," \
       "NOT a cert-skipping parity engine (caveat 5); only (parity) is one."
fi
printf '%-22s %-26s %14s %9s %10s %5s\n' workload core instructions wall_s rss_MB exit
for w in "${WORKLOADS[@]}"; do
  label="${w%%=*}"; rest="${w#*=}"
  file="${rest%%::*}"
  extra=""
  [ "$rest" != "$file" ] && extra="${rest#*::}"
  if [ ! -f "$file" ]; then
    printf '%-22s %-26s %14s\n' "$label" "-" "MISSING($file)"
    continue
  fi
  for core in ${VARIANTS//,/ }; do
    instrs=(); walls=(); rsss=(); ec=0
    for i in $(seq 1 "$REPS"); do
      # shellcheck disable=SC2086
      read -r a b c d <<<"$(one_run "$core" "$file" $extra)"
      [ -n "$a" ] && instrs+=("$a")
      walls+=("$b"); rsss+=("$c"); ec=$d
    done
    mi="-"; [ "${#instrs[@]}" -gt 0 ] && mi=$(median "${instrs[@]}")
    mw=$(median "${walls[@]}")
    mr=$(maxof "${rsss[@]}")
    mrmb=$(awk -v k="$mr" 'BEGIN{printf "%.1f", k/1024}')
    mig="-"; [ "$mi" != "-" ] && mig=$(awk -v n="$mi" 'BEGIN{printf "%.2fG", n/1e9}')
    printf '%-22s %-26s %14s %9s %10s %5s\n' "$label" "$(core_label "$core")" "$mig" "$mw" "$mrmb" "$ec"
  done
done
