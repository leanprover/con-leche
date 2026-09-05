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
# The TRACKED record.  $CACHE lives under the gitignored _tmp, so the raw
# cells behind PERF.md would not survive a clean of that directory — and
# a record that can evaporate cannot be relabelled later.  A full run
# therefore snapshots its cells here, and carries the cells of any
# configuration it can no longer measure into `retired.tsv` instead of
# dropping them (the relabel-don't-erase convention).
DATA=${PERF_DATA:-$ROOT/perf-data}
# ONE run per cell.  The medians-of-3 round measured the spreads at
# 0.01-0.5 % on instructions:u, so the third significant figure is
# stable off a single run and tripling every cell buys nothing.  If a
# number ever looks wrong, re-run that cell (PERF_STREAMS/PERF_CONFIGS)
# rather than re-running all of them.
REPS=${PERF_REPS:-1}
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

# Does the tree still have the INTERNED representation and its
# `--core=production` dispatch?  Task #172 (the tri-core refactor) drops
# it on the user's ruling — "one expr type with computed fields
# everywhere" — after which those flags no longer name a core and the
# matrix halves to the cached columns plus official.  Probed, not
# assumed, so this script needs no edit on the day it lands.
if [ -f "$ROOT/Setlec/Kernel/CoreI.lean" ] \
   && grep -q '"production"' "$ROOT/Main.lean" 2>/dev/null; then
  INTERNED=yes
else
  INTERNED=no
fi

# The cells per stream.  Every flag explicit; no defaults relied on.
# Only LIVE, MUTUALLY COMPARABLE configurations are measured — the table
# is meant to be read, not decoded.  Nothing retired appears: `--tt-model`
# (task #148 T7b) and `--core=cached` (an unverified pilot instrument)
# are simply not in the matrix, and cells of anything dropped later are
# archived, not printed (see carry_retired).
if [ "$INTERNED" = yes ]; then
  # TRANSITIONAL, while two representations exist: mode x core.
  CONFIG_IDS=(official sm-prod sm-cached nm-prod nm-cached)
else
  # POST-TRI-CORE (task #172): one representation, so the core axis is
  # gone and the columns are official + the checker's lanes.  The R
  # column went 2026-09-05 with the R core and `--set-model=r` (which
  # is now a hard error, so leaving the arm in would make the
  # regeneration invoke a retired flag).
  CONFIG_IDS=(official parity P)
fi
config_cmd() { # $1 = config id, $2 = stream file -> fills CMD
  case "$1" in
    official)  CMD=("$OFFICIAL" "$2") ;;
    # transitional (mode x core)
    sm-prod)   CMD=("$BIN" --set-model --core=production    --pre "$2") ;;
    sm-cached) CMD=("$BIN" --set-model --core=cached-parsed --pre "$2") ;;
    nm-prod)   CMD=("$BIN" --no-model  --core=production    --pre "$2") ;;
    nm-cached) CMD=("$BIN" --no-model  --core=cached-parsed --pre "$2") ;;
    # post-tri-core (the two lanes on the one representation)
    parity)    CMD=("$BIN" --no-model    --pre "$2") ;;
    P)         CMD=("$BIN" --set-model=p --pre "$2") ;;
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
  # NB `pgrep -x` matches /proc/PID/comm, which the kernel truncates to
  # 15 characters — hence the truncated preprocessor name.
  while pgrep -x setlec >/dev/null 2>&1 \
     || pgrep -x kernel >/dev/null 2>&1 \
     || pgrep -x perf >/dev/null 2>&1 \
     || pgrep -x lean-inductive- >/dev/null 2>&1; do
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

# Render from the working copy when a run has produced one, else from
# the tracked record — `--render` must work on a clean checkout, where
# the gitignored _tmp cache does not exist.
render() {
  local t=$TSV m=$CACHE/meta.txt
  if [ ! -s "$t" ]; then t=$DATA/table.tsv; m=$DATA/meta.txt; fi
  python3 "$ROOT/scripts/perf-tables-render.py" "$t" "$ROOT/PERF.md" "$m" "$DATA"
}

# Before a full run truncates the table: the outgoing TRACKED snapshot
# is superseded wholesale — its cells came from an older binary, and any
# configuration this run will not measure has left the matrix outright.
# Archive every one of those rows, stamped with the binary that produced
# them, so nothing is lost and nothing stale can leak into the live
# tables.  PERF.md prints one pointer line at them and no more.
carry_retired() {
  [ -s "$DATA/table.tsv" ] || return 0
  local oldsha olddate keep=" $CONFIGS " gone n
  oldsha=$(awk -F'\t' '$1=="binsha"{print $2}' "$DATA/meta.txt" 2>/dev/null)
  olddate=$(awk -F'\t' '$1=="date"{print $2}' "$DATA/meta.txt" 2>/dev/null)
  mkdir -p "$DATA"
  # 9th column = the binary that measured the row; readers take the
  # first 8, so the archive stays format-compatible with table.tsv.
  awk -F'\t' -v OFS='\t' -v sha="${oldsha:-unknown}" \
    '{print $0, sha}' "$DATA/table.tsv" >> "$DATA/retired.tsv"
  gone=$(awk -F'\t' -v keep="$keep" \
           'index(keep, " " $2 " ") == 0 { print $2 }' "$DATA/table.tsv" \
         | sort -u)
  for n in ${gone:-}; do
    printf '%s\t%s\t%s\t%s\n' "$n" "$(date -Iseconds)" \
      "${oldsha:-unknown}" "${olddate:-unknown}" >> "$DATA/retired.meta"
    say "RETIRED config $n — left the matrix; cells archived"
  done
  say "archived $(wc -l < "$DATA/table.tsv") superseded cells to $DATA/retired.tsv"
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
  [ -x "$f" ] || { echo "missing binary: $f  (lake build setlec)" >&2; exit 1; }
done

# PERF_APPEND=1 resumes an interrupted battery: keep the cells already
# in the TSV (and the run's metadata) and only measure what is asked
# for now.  Cells are appended, so re-running a stream duplicates its
# rows and the renderer keeps the LAST one.
if [ -n "${PERF_APPEND:-}" ] && [ -s "$TSV" ]; then
  say "APPEND mode: keeping $(wc -l < "$TSV") existing cells"
else
  carry_retired
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
    # Does the measured tree have the cached PARITY engine
    # (Setlec/Cached/CoreNC.lean, dispatched for --no-model
    # --core=cached-parsed)?  Before it landed, that cell was the
    # certified cached engine with two checks gated off — a different
    # measurement wearing the same flags, so the renderer must label
    # the column differently.  See DESIGN.md, "The cached parity lane
    # and the confound correction".
    if [ -f "$ROOT/Setlec/Cached/CoreNC.lean" ] \
       && grep -q "checkDeclsSPCachedNM" "$ROOT/Main.lean" 2>/dev/null; then
      echo "cachednc	yes"
    else
      echo "cachednc	no"
    fi
    echo "interned	$INTERNED"
    # the live matrix: exactly the columns the renderer may print
    echo "configs	$CONFIGS"
    echo "reps	$REPS"
    echo "timeout	$TIMEOUT"
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
