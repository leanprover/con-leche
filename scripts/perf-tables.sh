#!/usr/bin/env bash
# Regenerate PERF.md: con-leche (`--verified`) against the official
# kernel on raw `lean4export` streams.
#
#   scripts/perf-tables.sh              # the battery, then render
#   scripts/perf-tables.sh --parallel   # the worker-count sweep, then render
#   scripts/perf-tables.sh --render     # re-render from perf-data/
#   PERF_STREAMS="let-ladder init-full" PERF_APPEND=1 scripts/perf-tables.sh
#
# Method: `perf stat -e instructions:u`, ONE run per cell (instruction
# counts are stable to well under 1 %), con-leche at `--jobs=1`, every
# flag explicit, `nice -n 5`, a `timeout`, and no `ulimit -v` (the worker
# threads' stack reservations count against it; CLAUDE.md).  Wall time
# is recorded as data only, except in the `--parallel` sweep, where it is
# the quantity and every cell is five runs (median, min, max).
#
# Inputs live in the main checkout's `_tmp/` (gitignored, shared by the
# worktrees):
#   ref/arena-tests/good/        the arena's test streams
#   ref/init-exports/init-full.ndjson
#                                `lean4export` of `Init` at v4.33.0
#   ref/mathlib-full.ndjson      `lean4export` (15f6055, the v4.33.0 bump)
#                                of `Mathlib` at mathlib4 6f1ef4e5 (the last
#                                mathlib4 commit on v4.33.0): in a checkout
#                                of that commit, `lake exe cache get`, then
#                                `lake env lean4export Mathlib > …`
#   ref/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel
#                                the arena's official checker at v4.33.0
#                                (lean-kernel-arena `aa259bf^`, built by its
#                                own recipe), matching the streams' version
# A missing stream skips its row.
set -uo pipefail
ulimit -c 0   # an aborting run would write gigabytes of core

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
MAIN=$(dirname "$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)")
REF=${PERF_REF:-$MAIN/_tmp/ref}
BIN=$ROOT/.lake/build/bin/con-leche
OFFICIAL=${CON_LECHE_OFFICIAL_KERNEL:-$REF/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel}
OFFICIAL_LABEL="official v4.33.0"
CACHE=${PERF_CACHE:-$ROOT/_tmp/perf-tables}
DATA=$ROOT/perf-data          # the tracked record PERF.md is rendered from
TSV=$CACHE/table.tsv
LOG=$CACHE/battery.log
TIMEOUT=${PERF_TIMEOUT:-3000}

# Cheapest first, so a broken kit shows in seconds.
STREAM_LABELS=(let-ladder beta-ladder init-prelude grind-ring-5 app-lam init-full mathlib-full)
stream_path() {
  case "$1" in
    init-prelude) echo "$REF/arena-tests/good/init-prelude.ndjson" ;;
    init-full)    echo "$REF/init-exports/init-full.ndjson" ;;
    mathlib-full) echo "$REF/mathlib-full.ndjson" ;;
    *)            echo "$REF/arena-tests/good/perf/$1.ndjson" ;;
  esac
}
stream_timeout() { case "$1" in mathlib-full) echo 28800 ;; *) echo "$TIMEOUT" ;; esac; }

config_cmd() { # $1 = config, $2 = stream -> CMD
  case "$1" in
    official) CMD=("$OFFICIAL" "$2") ;;
    verified) CMD=("$BIN" --verified --jobs=1 "$2") ;;
    *) echo "unknown config $1" >&2; exit 1 ;;
  esac
}

STREAMS=${PERF_STREAMS:-${STREAM_LABELS[*]}}
CONFIGS=${PERF_CONFIGS:-official verified}

say() { echo "$(date +%T) $*" | tee -a "$LOG" >&2; }

# One cell, one run.  TSV line:
#   stream config instr wall exit decls loadavg verdict maxrss-KB
TIMEBIN=$(command -v time)
cell() { # $1 = stream label, $2 = config, $3 = stream path
  config_cmd "$2" "$3"
  local po tv t0 t1 out ex i decls verdict load rss
  po=$(mktemp "$CACHE/perfstat.XXXXXX"); tv=$(mktemp "$CACHE/timev.XXXXXX")
  load=$(cut -d' ' -f1 /proc/loadavg)
  t0=$(date +%s.%N)
  out=$( (perf stat -e instructions:u -x, -o "$po" \
          timeout "$(stream_timeout "$1")" nice -n 5 \
          "$TIMEBIN" -v -o "$tv" "${CMD[@]}") 2>&1 )
  ex=$?
  t1=$(date +%s.%N)
  i=$(awk -F, '/instructions/{print $1}' "$po" | head -1)
  rss=$(awk '/Maximum resident/{print $NF}' "$tv")
  rm -f "$po" "$tv"
  decls=$(printf '%s' "$out" | grep -ioE 'accepted [0-9]+ declarations' | head -1 | cut -d' ' -f2)
  verdict=$(printf '%s\n' "$out" | grep -v ': stats:' | tr '\n\t' '  ' | cut -c1-90)
  printf '%s\t%s\t%s\t%.2f\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "${i:-0}" \
    "$(echo "$t1 - $t0" | bc)" "$ex" "${decls:-}" "$load" "${verdict:-NONE}" "${rss:-}" >> "$TSV"
  say "  $1/$2: ${i:-?} instr, exit $ex, ${decls:-?} decls, maxRSS ${rss:-?} KB"
}

render() {
  python3 "$ROOT/scripts/perf-tables-render.py" "$DATA/table.tsv" "$ROOT/PERF.md" "$DATA/meta.txt"
}

mkdir -p "$CACHE"
case "${1:-}" in
  --render) render; exit 0 ;;
  --parallel)
    # Wall time at --jobs=1/4/8, five runs each: median, min, max.
    [ -x "$BIN" ] || { echo "missing $BIN (lake build con-leche)" >&2; exit 1; }
    PAR=$CACHE/parallel.tsv; : > "$PAR"
    for s in ${PERF_STREAMS:-init-full mathlib-full}; do
      f=$(stream_path "$s"); [ -s "$f" ] || { say "SKIP $s"; continue; }
      for j in 1 4 8; do
        ws=()
        for r in 1 2 3 4 5; do
          t0=$(date +%s.%N)
          out=$(timeout "$(stream_timeout "$s")" nice -n 5 "$BIN" --verified --jobs=$j "$f" 2>&1)
          ex=$?; t1=$(date +%s.%N)
          [ $ex = 0 ] || { say "$s --jobs=$j run $r: exit $ex"; exit 1; }
          [ $r = 1 ] && say "  $s --jobs=$j: $(printf '%s\n' "$out" | grep -i 'accepted')"
          ws+=("$(echo "$t1 - $t0" | bc)")
        done
        printf '%s\n' "${ws[@]}" | sort -n | awk -v s="$s" -v j="$j" \
          '{a[NR]=$0} END{printf "%s\t%s\t%.2f\t%.2f\t%.2f\n", s, j, a[3], a[1], a[5]}' >> "$PAR"
        say "  $s --jobs=$j: $(tail -1 "$PAR" | cut -f3-)"
      done
    done
    cp "$PAR" "$DATA/parallel.tsv"; render; exit 0 ;;
esac

for f in "$BIN" "$OFFICIAL"; do
  [ -x "$f" ] || { echo "missing binary: $f" >&2; exit 1; }
done

if [ -n "${PERF_APPEND:-}" ] && [ -s "$TSV" ]; then
  say "APPEND mode: keeping $(wc -l < "$TSV") cells (the last row per cell wins)"
else
  : > "$TSV"
  {
    echo "sha	$(git -C "$ROOT" rev-parse --short HEAD)"
    echo "dirty	$(git -C "$ROOT" status --porcelain -- ':!PERF.md' ':!perf-data' ':!scripts' | wc -l)"
    echo "toolchain	$(sed 's/.*://' "$ROOT/lean-toolchain")"
    echo "date	$(date -Iseconds)"
    echo "cpu	$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
    echo "cores	$(nproc)"
    echo "mem	$(awk '/MemTotal/{printf "%.0f GB", $2/1048576}' /proc/meminfo)"
    echo "officiallabel	$OFFICIAL_LABEL"
    echo "official	the lean-kernel-arena's \`checkers/official-v4.33.0\` (md5 \`$(md5sum "$OFFICIAL" | cut -d' ' -f1)\`)"
    echo "streams	Lean v4.33.0 \`lean4export\` NDJSON: the arena's tests, \`Init\`, and \`Mathlib\` at mathlib4 \`6f1ef4e5\`"
  } > "$CACHE/meta.txt"
fi

say "BATTERY START at $(git -C "$ROOT" rev-parse --short HEAD)"
for s in $STREAMS; do
  raw=$(stream_path "$s")
  [ -s "$raw" ] || { say "SKIP $s (no stream at $raw)"; continue; }
  say "stream $s ($(stat -c%s "$raw") bytes)"
  for c in $CONFIGS; do cell "$s" "$c" "$raw"; done
done
say "BATTERY DONE"

# The tracked record: cells and provenance.  Hand-written notes
# (`parsenote`, `parallelnote`, `extranote`) in the old meta.txt are kept.
mkdir -p "$DATA"
if [ -z "${PERF_STREAMS:-}${PERF_CONFIGS:-}" ]; then cp "$TSV" "$DATA/table.tsv"
else # a partial run replaces its own cells and keeps the others
  cat "$DATA/table.tsv" "$TSV" 2>/dev/null | awk -F'\t' \
    '{k=$1 FS $2; if (!(k in row)) ord[n++]=k; row[k]=$0}
     END{for (i=0;i<n;i++) print row[ord[i]]}' > "$CACHE/merged.tsv"
  mv "$CACHE/merged.tsv" "$DATA/table.tsv"
fi
grep -E '^(parsenote|parallelnote|extranote)	' "$DATA/meta.txt" 2>/dev/null \
  | grep -vFf <(cut -f1 "$CACHE/meta.txt" | sed 's/$/\t/') >> "$CACHE/meta.txt"
cp "$CACHE/meta.txt" "$DATA/meta.txt"
render
