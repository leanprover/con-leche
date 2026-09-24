#!/usr/bin/env bash
# tests/target-shadow.sh — THE TARGET KERNEL, measured beside today's
# (lane TSHADOW, 2026-09-23).
#
# The target kernel is GATED out of the install: `--target-shadow` runs
# it BESIDE the install at every inductive block that is not a pinned
# basis block (ConLeche/Kernel/Inductives/TargetInstall.lean,
# RecCheck.lean) and prints, after the fold's own step,
#
#     con-leche: target-shadow <block> today=<w> target=<w> rec=<w>
#       conf=<w> pos=<w> aux=<n> keys=[...] | <messages>
#
# `today` is the fold step's verdict for the block, `target` the
# target installer's end to end, `rec` the classification-free
# recursor check on the stream's recursor family, `conf` the reject-only
# conformance check after it (`skip` where the generator cannot read
# `nestPos`'s kinds: a container occurrence), `pos` `nestPos` on
# the stored constructors.
#
# This gate runs every e2e fixture (`tests/e2e-expected.txt`) with the
# flag — and, with `CON_LECHE_INMODEL=0`, every fixture whose nested
# block the in-process modeller declines at parse time
# (`tests/nested-shadow-expected.txt`'s `0` rows) and every forged
# `corner_tshadow_*` family, so that the fold reaches it — and compares with `tests/target-shadow-expected.txt`:
#
#     <fixture> <INMODEL> <exit> <block=today/target/rec/conf/pos/aux,...>
#
# the run's EXIT CODE (the flag moves no verdict: it must be the e2e
# row's at INMODEL=1) and every block whose line is not the trivial
# `accept/accept/accept/accept/accept/0`, in fold order (`-` when
# there is none).  `--census DIR` writes every run's full lines to DIR
# instead of comparing; `--update` rewrites the expected file.
#
# Usage: tests/target-shadow.sh [--census DIR | --update]
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

BIN=.lake/build/bin/con-leche
EXP=tests/target-shadow-expected.txt
[ -x "$BIN" ] || { echo "target-shadow: $BIN not built"; exit 1; }
WORK=$(mktemp -d "$TMPDIR/target-shadow.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

MODE=gate; CENSUS=""
case "${1:-}" in
  --census) MODE=census; CENSUS="$2"; mkdir -p "$CENSUS";;
  --update) MODE=update;;
esac

# the runs: every e2e fixture at INMODEL=1, the modeller-declined ones
# again at INMODEL=0
{
  grep -v '^#' tests/e2e-expected.txt | awk 'NF>=2 {print "tests/e2e/" $2, 1}'
  grep -v '^#' tests/nested-shadow-expected.txt | awk '$2==0 {print $1, 0}'
  # this lane's forged families: their blocks go to the modelled route
  # today, and the modeller may decline one at parse time
  ls tests/e2e/corner_tshadow_*.ndjson | awk '{print $1, 0}'
} | awk '!seen[$0]++' > "$WORK/runs"

run_one() {
  fx=$1; inmodel=$2; work=$3
  f="$fx"
  if [ ! -f "$f" ] && [ -f "$f.gz" ]; then
    f="$work/$(basename "$fx").$inmodel"; zcat "$fx.gz" > "$f"
  fi
  key=$(basename "$fx").$inmodel
  CON_LECHE_INMODEL="$inmodel" timeout 1200 "$BIN" --target-shadow "$f" \
    >/dev/null 2>"$work/$key.err"
  echo $? > "$work/$key.exit"
  grep '^con-leche: target-shadow ' "$work/$key.err" > "$work/$key.lines"
  [ "$f" != "$fx" ] && rm -f "$f"
  return 0
}
export -f run_one
export BIN
xargs -P "${JOBS:-8}" -L 1 bash -c 'run_one "$0" "$1" '"$WORK" < "$WORK/runs"

row() {  # fixture inmodel -> the gate row
  fx=$1; inmodel=$2
  key=$(basename "$fx").$inmodel
  sig=$(awk '{
      split($3, n, "="); blk = n[1]
      v = ""
      for (k = 4; k <= 9; k++) { split($k, kv, "="); v = v (k > 4 ? "/" : "") kv[2] }
      if (v != "accept/accept/accept/accept/accept/0") print blk "=" v
    }' "$WORK/$key.lines" | paste -sd, -)
  echo "$fx $inmodel $(cat "$WORK/$key.exit") ${sig:--}"
}

if [ "$MODE" = census ]; then
  while read -r fx inmodel; do
    key=$(basename "$fx").$inmodel
    cp "$WORK/$key.lines" "$CENSUS/$key.lines"
    cp "$WORK/$key.exit" "$CENSUS/$key.exit"
    row "$fx" "$inmodel"
  done < "$WORK/runs" > "$CENSUS/rows.txt"
  echo "target-shadow census: $(wc -l < "$CENSUS/rows.txt") runs in $CENSUS"
  exit 0
fi

while read -r fx inmodel; do row "$fx" "$inmodel"; done < "$WORK/runs" > "$WORK/rows"

# the flag moves no verdict: the exit code is the e2e row's
fail=0
while read -r fx inmodel ex _; do
  [ "$inmodel" = 1 ] || continue
  want=$(grep -v '^#' tests/e2e-expected.txt | awk -v f="$(basename "$fx")" '$2==f {print $1}')
  if [ "$ex" != "$want" ]; then
    echo "  VERDICT MOVED $fx: exit $ex, e2e row $want"; fail=1
  fi
done < "$WORK/rows"

if [ "$MODE" = update ]; then
  { sed -n '/^#/p' "$EXP" 2>/dev/null; cat "$WORK/rows"; } > "$EXP.new" && mv "$EXP.new" "$EXP"
  echo "target-shadow: $EXP updated ($(wc -l < "$WORK/rows") rows)"
  exit $fail
fi

ok=0; total=0
while read -r fx inmodel rest; do
  total=$((total + 1))
  want=$(grep -v '^#' "$EXP" | awk -v f="$fx" -v i="$inmodel" '$1==f && $2==i {print $3, $4}')
  if [ "$rest" = "$want" ]; then ok=$((ok + 1))
  else echo "  FAIL $fx (INMODEL=$inmodel): got '$rest', want '$want'"; fail=1
  fi
done < "$WORK/rows"
echo "target-shadow gate: $ok/$total as expected"
exit $fail
