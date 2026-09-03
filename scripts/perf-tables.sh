#!/usr/bin/env bash
# Regenerate PERF.md from scratch: the systematic mode x core x stream
# performance battery, preprocessed input on both sides.
#
#   scripts/perf-tables.sh              # full battery, writes PERF.md
#   scripts/perf-tables.sh --render     # re-render PERF.md from the last TSV
#   PERF_STREAMS="let-ladder beta-ladder" scripts/perf-tables.sh
#
# METHOD (the established discipline, unchanged from the task-#161
# canonical table and the perf-eng "honest gap" round):
#   * `perf stat -e instructions:u`, MEDIAN OF 3 per cell; instructions
#     are the primary metric (contention-independent), wall is secondary.
#   * every run under `ulimit -v 40G`, `nice -n 5`, `timeout`,
#     `SETLEC_SUPERVISED=1` (no supervisor re-exec).
#   * PREPROCESSED INPUT ON BOTH SIDES: the `lean-inductive-models`
#     preprocessor is run once per stream, off the clock, and BOTH the
#     official kernel and setlec (`--pre`) ingest that same file.  This
#     removes the preprocessor floor and the spawn from every setlec
#     cell and puts the two checkers on the same bytes.
#   * ALL flags are passed EXPLICITLY: no cell relies on a default.
#   * one timed cell at a time; before each cell the script waits until
#     no other measurement process (setlec / official kernel / perf /
#     the preprocessor) is running anywhere on the machine.
#
# Environment overrides: PERF_REPS, PERF_TIMEOUT, PERF_STREAMS,
# PERF_CONFIGS, PERF_CACHE, SETLEC_OFFICIAL_KERNEL,
# SETLEC_INDUCTIVE_MODELS.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BIN=$ROOT/.lake/build/bin/setlec
OFFICIAL=${SETLEC_OFFICIAL_KERNEL:-$ROOT/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel}
PREPROC=${SETLEC_INDUCTIVE_MODELS:-$ROOT/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models}
ARENA=$ROOT/_tmp/arena-tests/good
CACHE=${PERF_CACHE:-$ROOT/_tmp/perf-tables}
TSV=$CACHE/table.tsv
LOG=$CACHE/battery.log
REPS=${PERF_REPS:-3}
TIMEOUT=${PERF_TIMEOUT:-1800}
VLIMIT=41943040            # 40 GB virtual, the standing ceiling

# Streams: label -> raw arena ndjson.  Ordered cheapest first so a
# broken kit surfaces in seconds, not hours.
STREAM_LABELS=(let-ladder beta-ladder init-prelude grind-ring-5 app-lam init-full)
stream_path() {
  case "$1" in
    let-ladder)   echo "$ARENA/perf/let-ladder.ndjson" ;;
    beta-ladder)  echo "$ARENA/perf/beta-ladder.ndjson" ;;
    init-prelude) echo "$ARENA/init-prelude.ndjson" ;;
    grind-ring-5) echo "$ARENA/perf/grind-ring-5.ndjson" ;;
    app-lam)      echo "$ARENA/perf/app-lam.ndjson" ;;
    init-full)    echo "$ROOT/_tmp/init-exports/init-full.ndjson" ;;
    *) echo "" ;;
  esac
}

# The seven cells per stream.  Every flag explicit; no defaults relied on.
# NOTE (reconciliation with the work order): `--tt-model` is RETIRED in
# Main.lean (task #148 T7b) and `--core=cached` is an unverified pilot
# instrument, while `--core=cached-parsed` is the supported, verified
# cached core (task #163).  The tt cells are measured anyway so the table
# records their real exit code rather than silently dropping the column.
CONFIG_IDS=(official sm-prod sm-cached tt-prod tt-cached nm-prod nm-cached)
config_cmd() { # $1 = config id, $2 = stream file -> fills CMD
  case "$1" in
    official)  CMD=("$OFFICIAL" "$2") ;;
    sm-prod)   CMD=("$BIN" --set-model --core=production    --pre "$2") ;;
    sm-cached) CMD=("$BIN" --set-model --core=cached-parsed --pre "$2") ;;
    tt-prod)   CMD=("$BIN" --tt-model  --core=production    --pre "$2") ;;
    tt-cached) CMD=("$BIN" --tt-model  --core=cached-parsed --pre "$2") ;;
    nm-prod)   CMD=("$BIN" --no-model  --core=production    --pre "$2") ;;
    nm-cached) CMD=("$BIN" --no-model  --core=cached-parsed --pre "$2") ;;
    *) echo "unknown config $1" >&2; exit 1 ;;
  esac
}

STREAMS=${PERF_STREAMS:-${STREAM_LABELS[*]}}
CONFIGS=${PERF_CONFIGS:-${CONFIG_IDS[*]}}

say() { echo "$(date +%T) $*" | tee -a "$LOG" >&2; }

median() { printf '%s\n' "$@" | sort -n | awk '{a[NR]=$0} END{print a[int((NR+1)/2)]}'; }

# Measurement hygiene: never two timed cells at once, anywhere on the
# machine (a concurrent perf campaign may be running).
wait_idle() {
  local waited=0
  while pgrep -x setlec >/dev/null 2>&1 \
     || pgrep -x kernel >/dev/null 2>&1 \
     || pgrep -x perf >/dev/null 2>&1 \
     || pgrep -x lean-inductive-models >/dev/null 2>&1; do
    if [ "$waited" -eq 0 ]; then say "waiting for the machine to go idle"; fi
    sleep 10; waited=$((waited + 10))
    if [ "$waited" -ge 7200 ]; then
      say "WARNING: still busy after 2h; proceeding anyway"
      return
    fi
  done
}

# Preprocess once per stream, off the clock, cached on disk.
preprocess() { # $1 = label, $2 = raw path -> echoes the preprocessed path
  local out=$CACHE/pre/$1.pre.ndjson
  if [ ! -s "$out" ]; then
    say "preprocessing $1"
    mkdir -p "$CACHE/pre"
    if ! "$PREPROC" --quiet -o "$out.part" "$2" >/dev/null 2>"$CACHE/pre/$1.err"; then
      say "FATAL: preprocessor failed on $1 (see $CACHE/pre/$1.err)"
      rm -f "$out.part"; return 1
    fi
    mv "$out.part" "$out"
  fi
  echo "$out"
}

# One cell: REPS timed runs, median instructions and wall.
# Emits one TSV line: stream cfg instr wall exit decls loadavg verdict
cell() { # $1 = stream label, $2 = config id, $3 = preprocessed stream
  local instrs=() walls=() ex=0 decls="" verdict="" load=""
  config_cmd "$2" "$3"
  local r po t0 t1 out i
  for r in $(seq 1 "$REPS"); do
    wait_idle
    po=$(mktemp)
    load=$(cut -d' ' -f1 /proc/loadavg)
    t0=$(date +%s.%N)
    out=$( (ulimit -v $VLIMIT; SETLEC_SUPERVISED=1 \
              perf stat -e instructions:u -x, -o "$po" \
              timeout "$TIMEOUT" nice -n 5 "${CMD[@]}") 2>&1 )
    ex=$?
    t1=$(date +%s.%N)
    i=$(awk -F, '/instructions/{print $1}' "$po" | head -1)
    rm -f "$po"
    instrs+=("${i:-0}")
    walls+=("$(awk "BEGIN{printf \"%.2f\", $t1 - $t0}")")
    decls=$(printf '%s' "$out" | grep -oE '[0-9]+ declarations' | head -1 | cut -d' ' -f1)
    verdict=$(printf '%s' "$out" | tr '\n' ' ' | sed 's/\t/ /g' | cut -c1-90)
  done
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$1" "$2" "$(median "${instrs[@]}")" "$(median "${walls[@]}")" \
    "$ex" "${decls:-}" "$load" "${verdict:-NONE}" >> "$TSV"
  say "  $1/$2: $(median "${instrs[@]}") instr, $(median "${walls[@]}") s, exit $ex, ${decls:-?} decls"
}

render() {
  python3 "$ROOT/scripts/perf-tables-render.py" "$TSV" "$ROOT/PERF.md" \
    "$CACHE/meta.txt"
}

# ---------------------------------------------------------------- main
mkdir -p "$CACHE"
if [ "${1:-}" = "--render" ]; then render; echo "PERF.md rewritten from $TSV"; exit 0; fi

for f in "$BIN" "$OFFICIAL" "$PREPROC"; do
  [ -x "$f" ] || { echo "missing binary: $f  (lake build setlec)" >&2; exit 1; }
done

{
  echo "sha	$(git -C "$ROOT" rev-parse HEAD)"
  echo "shashort	$(git -C "$ROOT" rev-parse --short HEAD)"
  echo "dirty	$(git -C "$ROOT" status --porcelain -- ':!PERF.md' | wc -l)"
  echo "date	$(date -Iseconds)"
  echo "host	$(hostname)"
  echo "cpu	$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
  echo "cores	$(nproc)"
  echo "mem	$(awk '/MemTotal/{printf "%.0f GB", $2/1048576}' /proc/meminfo)"
  echo "kernelver	$(uname -r)"
  echo "official	$(readlink -f "$OFFICIAL")"
  echo "preproc	$(readlink -f "$PREPROC")"
  echo "reps	$REPS"
  echo "timeout	$TIMEOUT"
} > "$CACHE/meta.txt"

: > "$TSV"
say "BATTERY START — sha $(git -C "$ROOT" rev-parse --short HEAD), reps $REPS"
for s in $STREAMS; do
  raw=$(stream_path "$s")
  [ -n "$raw" ] && [ -s "$raw" ] || { say "SKIP $s (no stream at $raw)"; continue; }
  pre=$(preprocess "$s" "$raw") || continue
  say "stream $s ($(stat -c%s "$pre") bytes preprocessed)"
  for c in $CONFIGS; do cell "$s" "$c" "$pre"; done
  render   # keep PERF.md current after every stream
done
say "BATTERY DONE"
render
echo "wrote $ROOT/PERF.md (raw cells: $TSV)"
