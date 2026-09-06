#!/usr/bin/env bash
# Regenerate PERF.md from scratch: the three-column stream battery
# (official / trusted / verified), preprocessed input on both sides.
#
#   scripts/perf-tables.sh              # full battery, writes PERF.md
#   scripts/perf-tables.sh --render     # re-render PERF.md from the last TSV
#   PERF_STREAMS="let-ladder beta-ladder" scripts/perf-tables.sh
#
# METHOD (the established discipline, unchanged from the task-#161
# canonical table and the perf-eng "honest gap" round):
#   * `perf stat -e instructions:u`, ONE run per cell; instructions are
#     the only metric reported (contention-independent).
#   * every run under `ulimit -v 16G`, `nice -n 5`, `timeout`,
#     `LECH_SUPERVISED=1` (no supervisor re-exec).
#   * PREPROCESSED INPUT ON BOTH SIDES: the preprocessor
#     (`lech-preprocess`, task #178 — `lean-inductive-models` told
#     which blocks lech installs natively) is run once per stream,
#     off the clock, and BOTH the
#     official kernel and lech (`--pre`) ingest that same file.  This
#     removes the preprocessor floor and the spawn from every lech
#     cell and puts the two checkers on the same bytes.
#   * ALL flags are passed EXPLICITLY: no cell relies on a default.
#   * one timed cell at a time; before each cell the script waits until
#     no other measurement process (lech / official kernel / perf /
#     the preprocessor) is running anywhere on the machine.
#
# Environment overrides: PERF_REPS, PERF_TIMEOUT, PERF_STREAMS,
# PERF_CONFIGS, PERF_CACHE, LECH_OFFICIAL_KERNEL,
# LECH_INDUCTIVE_MODELS.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BIN=$ROOT/.lake/build/bin/lech
OFFICIAL=${LECH_OFFICIAL_KERNEL:-$ROOT/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel}
PREPROC=${LECH_INDUCTIVE_MODELS:-$ROOT/.lake/build/bin/lech-preprocess}
ARENA=$ROOT/_tmp/arena-tests/good
CACHE=${PERF_CACHE:-$ROOT/_tmp/perf-tables}
TSV=$CACHE/table.tsv
LOG=$CACHE/battery.log
# The TRACKED record.  $CACHE lives under the gitignored _tmp, so the raw
# cells behind PERF.md would not survive a clean of that directory; a full
# run therefore snapshots its cells here.  A run supersedes the previous
# snapshot wholesale — PERF.md shows the current matrix and nothing else.
DATA=${PERF_DATA:-$ROOT/perf-data}
# ONE run per cell.  The medians-of-3 round measured the spreads at
# 0.01-0.5 % on instructions:u, so the third significant figure is
# stable off a single run and tripling every cell buys nothing.  If a
# number ever looks wrong, re-run that cell (PERF_STREAMS/PERF_CONFIGS)
# rather than re-running all of them.
REPS=${PERF_REPS:-1}
TIMEOUT=${PERF_TIMEOUT:-3000}
VLIMIT=${PERF_VLIMIT:-16000000}   # 16 GB virtual, the standing ceiling

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

# THE MATRIX: exactly three columns, every flag explicit, no defaults
# relied on.  One representation, so there is no core axis; the R column
# went 2026-09-05 with the R core and `--set-model=r` (a hard error now).
# Nothing retired is measured and nothing retired is printed.
CONFIG_IDS=(official trusted verified)
config_cmd() { # $1 = config id, $2 = stream file -> fills CMD
  case "$1" in
    official)  CMD=("$OFFICIAL" "$2") ;;
    trusted)   CMD=("$BIN" --trusted  --pre "$2") ;;
    verified)  CMD=("$BIN" --verified --pre "$2") ;;
    *) echo "unknown config $1" >&2; exit 1 ;;
  esac
}

STREAMS=${PERF_STREAMS:-${STREAM_LABELS[*]}}
CONFIGS=${PERF_CONFIGS:-${CONFIG_IDS[*]}}

say() { echo "$(date +%T) $*" | tee -a "$LOG" >&2; }

median() { printf '%s\n' "$@" | sort -n | awk '{a[NR]=$0} END{print a[int((NR+1)/2)]}'; }

# Measurement hygiene: never two timed cells at once, anywhere on the
# machine (a concurrent perf campaign may be running).  The battery
# itself runs cells strictly one at a time regardless; this wait is only
# about FOREIGN work.  `PERF_NO_WAIT=1` skips it — on a 96-core box a
# single unrelated single-threaded checker run does not move
# instructions:u, and blocking on one can cost hours (the Mathlib
# frontier campaign holds one such process for up to four hours).
wait_idle() {
  local waited=0
  [ -n "${PERF_NO_WAIT:-}" ] && return
  # NB `pgrep -x` matches /proc/PID/comm, which the kernel truncates to
  # 15 characters — hence the truncated preprocessor name.
  while pgrep -x lech >/dev/null 2>&1 \
     || pgrep -x kernel >/dev/null 2>&1 \
     || pgrep -x perf >/dev/null 2>&1 \
     || pgrep -x lean-inductive- >/dev/null 2>&1; do
    if [ "$waited" -eq 0 ]; then say "waiting for the machine to go idle"; fi
    sleep 10; waited=$((waited + 10))
    if [ "$waited" -ge "${PERF_IDLE_MAX:-7200}" ]; then
      say "WARNING: still busy after ${PERF_IDLE_MAX:-7200}s; proceeding anyway"
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
    po=$(mktemp "$CACHE/perfstat.XXXXXX")
    load=$(cut -d' ' -f1 /proc/loadavg)
    t0=$(date +%s.%N)
    out=$( (ulimit -v $VLIMIT; LECH_SUPERVISED=1 \
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

# Render from the working copy when a run has produced one, else from
# the tracked record — `--render` must work on a clean checkout, where
# the gitignored _tmp cache does not exist.
render() {
  local t=$TSV m=$CACHE/meta.txt
  if [ ! -s "$t" ]; then t=$DATA/table.tsv; m=$DATA/meta.txt; fi
  python3 "$ROOT/scripts/perf-tables-render.py" "$t" "$ROOT/PERF.md" "$m"
}

# After a full run: refresh the tracked snapshot.
snapshot() {
  mkdir -p "$DATA"
  cp "$TSV" "$DATA/table.tsv"
  cp "$CACHE/meta.txt" "$DATA/meta.txt"
  say "tracked snapshot refreshed at $DATA"
}

# ---------------------------------------------------------------- main
mkdir -p "$CACHE"
if [ "${1:-}" = "--render" ]; then render; echo "PERF.md rewritten from $TSV"; exit 0; fi

for f in "$BIN" "$OFFICIAL" "$PREPROC"; do
  [ -x "$f" ] || { echo "missing binary: $f  (lake build lech)" >&2; exit 1; }
done

# PERF_APPEND=1 resumes an interrupted battery: keep the cells already
# in the TSV (and the run's metadata) and only measure what is asked
# for now.  Cells are appended, so re-running a stream duplicates its
# rows and the renderer keeps the LAST one.
if [ -n "${PERF_APPEND:-}" ] && [ -s "$TSV" ]; then
  say "APPEND mode: keeping $(wc -l < "$TSV") existing cells"
else
  : > "$TSV"
  {
    echo "sha	$(git -C "$ROOT" rev-parse HEAD)"
    echo "shashort	$(git -C "$ROOT" rev-parse --short HEAD)"
    # the last commit that could change the measured binary (script-only
    # commits do not rebuild it)
    echo "binsha	$(git -C "$ROOT" log -1 --format=%H -- . ':!scripts' ':!PERF.md')"
    echo "dirty	$(git -C "$ROOT" status --porcelain -- ':!PERF.md' | wc -l)"
    echo "date	$(date -Iseconds)"
    echo "host	$(hostname)"
    echo "cpu	$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
    echo "cores	$(nproc)"
    echo "mem	$(awk '/MemTotal/{printf "%.0f GB", $2/1048576}' /proc/meminfo)"
    echo "kernelver	$(uname -r)"
    echo "official	$(readlink -f "$OFFICIAL")"
    echo "preproc	$(readlink -f "$PREPROC")"
    # optional one-line provenance note for the header (e.g. which
    # master commit the measured tree is a merge of)
    [ -n "${PERF_NOTE:-}" ] && echo "note	$PERF_NOTE"
    # what else was live on the machine while the battery ran
    [ -n "${PERF_LOAD_NOTE:-}" ] && echo "loadnote	$PERF_LOAD_NOTE"
    # the live matrix: exactly the columns the renderer may print
    echo "configs	$CONFIGS"
    echo "reps	$REPS"
    echo "timeout	$TIMEOUT"
    echo "vlimit	$VLIMIT"
  } > "$CACHE/meta.txt"
fi

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
# Only a full sweep may replace the tracked record; a partial run
# (PERF_STREAMS/PERF_CONFIGS) would snapshot a hole.
if [ -z "${PERF_STREAMS:-}${PERF_CONFIGS:-}" ]; then snapshot; fi
render
echo "wrote $ROOT/PERF.md (raw cells: $TSV, tracked record: $DATA)"
