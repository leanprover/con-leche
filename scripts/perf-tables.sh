#!/usr/bin/env bash
# Regenerate PERF.md from scratch: the three-column stream battery
# (official / trusted / verified) on RAW lean4export streams.
#
#   scripts/perf-tables.sh              # full battery, writes PERF.md
#   scripts/perf-tables.sh --render     # re-render PERF.md from the last TSV
#   PERF_STREAMS="let-ladder beta-ladder" scripts/perf-tables.sh
#
# METHOD (the established discipline, unchanged from the task-#161
# canonical table and the perf-eng "honest gap" round):
#   * `perf stat -e instructions:u`, ONE run per cell; instructions are
#     the only metric reported (contention-independent).
#   * every run under `ulimit -v 16G`, `nice -n 5`, `timeout`.  (Until
#     task #230 this line also carried the environment variable that
#     kept the driver from re-exec'ing itself under the OOM supervisor;
#     the supervisor is gone, so the checker is always the one process
#     `perf stat` counts.)
#   * RAW INPUT ON BOTH SIDES (task #207).  Both checkers ingest the
#     same raw `lean4export` file, as it comes off the exporter.  Until
#     #207 con-leche needed a preprocessing step the official kernel
#     did not, so the battery ran the tool once per stream off the
#     clock and fed BOTH sides its output, to keep the two on the same
#     bytes; there is no such step any more, so the honest input is the
#     raw stream and the comparison is between the two checkers doing
#     the SAME job — inductive blocks included, which con-leche used to
#     have done for it.  The numbers are therefore NOT comparable, cell
#     for cell, with any PERF.md before this regeneration.
#   * ALL flags are passed EXPLICITLY: no cell relies on a default.
#   * one timed cell at a time; before each cell the script waits until
#     no other measurement process (con-leche / official kernel /
#     perf) is running anywhere on the machine.
#
# Environment overrides: PERF_REPS, PERF_TIMEOUT, PERF_STREAMS,
# PERF_CONFIGS, PERF_CACHE, CON_LECHE_OFFICIAL_KERNEL.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BIN=$ROOT/.lake/build/bin/con-leche
OFFICIAL=${CON_LECHE_OFFICIAL_KERNEL:-$ROOT/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel}
ARENA=$ROOT/_tmp/arena-tests/good
CACHE=${PERF_CACHE:-$ROOT/_tmp/perf-tables}
TSV=$CACHE/table.tsv
CENSUS=$CACHE/census.tsv
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
# broken kit surfaces in seconds, not hours.  `mathlib-full` (task #187)
# is last and is a different weight class: see MATHLIB SCALE below.
STREAM_LABELS=(let-ladder beta-ladder init-prelude grind-ring-5 app-lam init-full mathlib-full)
stream_path() {
  case "$1" in
    let-ladder)   echo "$ARENA/perf/let-ladder.ndjson" ;;
    beta-ladder)  echo "$ARENA/perf/beta-ladder.ndjson" ;;
    init-prelude) echo "$ARENA/init-prelude.ndjson" ;;
    grind-ring-5) echo "$ARENA/perf/grind-ring-5.ndjson" ;;
    app-lam)      echo "$ARENA/perf/app-lam.ndjson" ;;
    init-full)    echo "$ROOT/_tmp/init-exports/init-full.ndjson" ;;
    mathlib-full) echo "$ROOT/_tmp/mathlib-scoping/mathlib-full.ndjson" ;;
    *) echo "" ;;
  esac
}

# MATHLIB SCALE (task #187).  The full-Mathlib row is measured the same
# way as every other row — `perf stat -e instructions:u`, one run, all
# flags explicit — but three things about it are different, and each is
# a decision, not an accident:
#
#  * The stream is the raw full-Mathlib export, cut once by hand and
#    named by `stream_path`.  If the file is absent the row is skipped.
#  * The caps are the user's Mathlib ceiling: 22 GB virtual, 8 h.
#  * The con-leche cells run under `--progress=5000` so a stalled hour is
#    visible in a timestamped log rather than as silence.  Measured cost
#    of that on init-full (2026-09-06): 666 084 645 143 instructions
#    with the progress loop against 666 088 947 489 without — −0.0006 %,
#    i.e. below the run-to-run spread.  The progress loop is the
#    unverified IO twin of `checkDecls`; the user ruled it an
#    acceptable producer for Mathlib-scale runs.
# The Mathlib row also records peak RSS (`time -v`) and wall minutes,
# which the renderer prints for that row only, as data.
stream_vlimit()  { case "$1" in mathlib-full) echo 22000000 ;; *) echo "$VLIMIT" ;; esac; }
stream_timeout() { case "$1" in mathlib-full) echo 28800 ;; *) echo "$TIMEOUT" ;; esac; }
stream_progress(){ case "$1" in mathlib-full) echo 5000 ;; *) echo 0 ;; esac; }

# THE MATRIX: exactly three columns, every flag explicit, no defaults
# relied on.  One representation, so there is no core axis; the R column
# went 2026-09-05 with the R core and `--set-model=r` (a hard error now).
# Nothing retired is measured and nothing retired is printed.
CONFIG_IDS=(official trusted verified)
config_cmd() { # $1 = config id, $2 = stream file -> fills CMD
  case "$1" in
    official)  CMD=("$OFFICIAL" "$2") ;;
    trusted)   CMD=("$BIN" --trusted  "$2") ;;
    verified)  CMD=("$BIN" --verified "$2") ;;
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
  while pgrep -x con-leche >/dev/null 2>&1 \
     || pgrep -x kernel >/dev/null 2>&1 \
     || pgrep -x perf >/dev/null 2>&1; do
    if [ "$waited" -eq 0 ]; then say "waiting for the machine to go idle"; fi
    sleep 10; waited=$((waited + 10))
    if [ "$waited" -ge "${PERF_IDLE_MAX:-7200}" ]; then
      say "WARNING: still busy after ${PERF_IDLE_MAX:-7200}s; proceeding anyway"
      return
    fi
  done
}

# One cell: REPS timed runs, median instructions and wall.
# Emits one TSV line:
#   stream cfg instr wall exit decls loadavg verdict [maxrss-KB]
# The ninth field is present only for the Mathlib row (see MATHLIB
# SCALE): `time -v`'s maximum resident set size, in KB.
TIMEBIN=$(command -v time)
cell() { # $1 = stream label, $2 = config id, $3 = stream path
  local instrs=() walls=() ex=0 decls="" verdict="" load="" rss=""
  config_cmd "$2" "$3"
  local r po tv t0 t1 out i vl to pg
  vl=$(stream_vlimit "$1"); to=$(stream_timeout "$1"); pg=$(stream_progress "$1")
  # the progress heartbeat is a con-leche knob; official has none
  [ "$2" = official ] && pg=0
  # ... and it is a FLAG since task #229, so it goes into the command
  # rather than the environment (position is free: the driver accepts it
  # in any order with the mode flag and the file)
  if [ "$pg" != 0 ]; then CMD+=("--progress=$pg"); fi
  for r in $(seq 1 "$REPS"); do
    wait_idle
    po=$(mktemp "$CACHE/perfstat.XXXXXX")
    tv=$(mktemp "$CACHE/timev.XXXXXX")
    load=$(cut -d' ' -f1 /proc/loadavg)
    t0=$(date +%s.%N)
    if [ "$1" = mathlib-full ]; then
      # the Mathlib row: `time -v` for peak RSS, and the progress lane's
      # timestamped stderr kept as a receipt
      out=$( (ulimit -v $vl; \
                perf stat -e instructions:u -x, -o "$po" \
                timeout "$to" nice -n 5 "$TIMEBIN" -v -o "$tv" "${CMD[@]}" \
                2> >(awk '{ printf "%d %s\n", systime(), $0; fflush() }' \
                       >> "$CACHE/$1.$2.err")) 2>&1 )
      ex=$?
      rss=$(awk '/Maximum resident/{print $NF}' "$tv" 2>/dev/null)
    else
      out=$( (ulimit -v $vl; \
                perf stat -e instructions:u -x, -o "$po" \
                timeout "$to" nice -n 5 "${CMD[@]}") 2>&1 )
      ex=$?
    fi
    t1=$(date +%s.%N)
    i=$(awk -F, '/instructions/{print $1}' "$po" | head -1)
    rm -f "$po" "$tv"
    instrs+=("${i:-0}")
    walls+=("$(awk "BEGIN{printf \"%.2f\", $t1 - $t0}")")
    decls=$(printf '%s' "$out" | grep -oE '[0-9]+ declarations' | head -1 | cut -d' ' -f1)
    verdict=$(printf '%s' "$out" | tr '\n' ' ' | sed 's/\t/ /g' | cut -c1-90)
  done
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$1" "$2" "$(median "${instrs[@]}")" "$(median "${walls[@]}")" \
    "$ex" "${decls:-}" "$load" "${verdict:-NONE}" "${rss:-}" >> "$TSV"
  say "  $1/$2: $(median "${instrs[@]}") instr, $(median "${walls[@]}") s, exit $ex, ${decls:-?} decls${rss:+, maxRSS ${rss} KB}"
}

# Render from the working copy when a run has produced one, else from
# the tracked record — `--render` must work on a clean checkout, where
# the gitignored _tmp cache does not exist.
render() {
  local t=$TSV m=$CACHE/meta.txt
  if [ ! -s "$t" ]; then t=$DATA/table.tsv; m=$DATA/meta.txt; fi
  local cn=$CENSUS
  if [ ! -s "$cn" ]; then cn=$DATA/census.tsv; fi
  python3 "$ROOT/scripts/perf-tables-render.py" "$t" "$ROOT/PERF.md" "$m" "$cn"
}

# After a full run: refresh the tracked snapshot.
snapshot() {
  mkdir -p "$DATA"
  cp "$TSV" "$DATA/table.tsv"
  cp "$CACHE/meta.txt" "$DATA/meta.txt"
  [ -s "$CENSUS" ] && cp "$CENSUS" "$DATA/census.tsv"
  say "tracked snapshot refreshed at $DATA"
}

# ---------------------------------------------------------------- main
mkdir -p "$CACHE"
if [ "${1:-}" = "--render" ]; then render; echo "PERF.md rewritten from $TSV"; exit 0; fi

for f in "$BIN" "$OFFICIAL"; do
  [ -x "$f" ] || { echo "missing binary: $f  (lake build con-leche)" >&2; exit 1; }
done

# PERF_APPEND=1 resumes an interrupted battery: keep the cells already
# in the TSV (and the run's metadata) and only measure what is asked
# for now.  Cells are appended, so re-running a stream duplicates its
# rows and the renderer keeps the LAST one.
if [ -n "${PERF_APPEND:-}" ] && [ -s "$TSV" ]; then
  say "APPEND mode: keeping $(wc -l < "$TSV") existing cells"
else
  : > "$TSV"; : > "$CENSUS"
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
    echo "binmd5	$(md5sum "$BIN" | cut -d' ' -f1)"
    ml=$(stream_path mathlib-full)
    if [ -s "$ml" ]; then
      echo "mathlibstream	\`$ml\` ($(stat -c%s "$ml") bytes, raw)"
    fi
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
  say "stream $s ($(stat -c%s "$raw") bytes, raw)"
  for c in $CONFIGS; do cell "$s" "$c" "$raw"; done
  # the input's own census, off the clock and AFTER the cells: record
  # count, what official's `constMap.size` counts on the same file, the
  # fold's record count, and the native-block split (task #187)
  python3 "$ROOT/scripts/stream-census.py" "$raw" | tail -n +2 \
    | sed "s|^[^\t]*|$s|" >> "$CENSUS"
  render   # keep PERF.md current after every stream
done
say "BATTERY DONE"
# Only a full sweep may replace the tracked record; a partial run
# (PERF_STREAMS/PERF_CONFIGS) would snapshot a hole.
if [ -z "${PERF_STREAMS:-}${PERF_CONFIGS:-}" ]; then snapshot; fi
render
echo "wrote $ROOT/PERF.md (raw cells: $TSV, tracked record: $DATA)"
