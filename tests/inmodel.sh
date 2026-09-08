#!/usr/bin/env bash
# tests/inmodel.sh — THE IN-PROCESS MODELLER'S GATE (task #200).
#
# For each raw fixture below, the in-process modeller
# (`ConLeche/Frontend/InModel/*`) generates the `_model` families of its
# mutual/nested blocks at parse time.  The generated AUXILIARY family is a
# recursive indexed inductive the direct fixpoint route (task #188)
# installs, so the raw run ACCEPTS outright.
#
# THE DUMP IS NO LONGER RE-CHECKED (task #219).  `CON_LECHE_INMODEL_DUMP`
# still writes the raw input with the generated records spliced in — the
# instrument for reading what the modeller built — but that stream is
# not a valid input any more: stream `_model` records are ordinary
# declarations now, the modeller does not stand down for them, and
# re-checking the dump rejects on the duplicate declaration.  That is
# the ruling in action, so the stage that re-checked it is replaced by
# a count check: the dump carries exactly the records the receipt says
# were generated.  (What the re-check used to gate — that every
# generated record type-checks — the RAW run already gates: the fold
# checks each of them as a declaration.)
#
#   * raw run (in-process modelling on): exit 0, or exit 2 at a block
#     no route installs — either is recorded, a REJECT or an error
#     fails;
#   * the dump: written, and longer than the input by exactly the
#     number of generated records the receipt reports;
#   * `CON_LECHE_INMODEL=0` on the raw export: the blocks reach the fold bare
#     and the run declines with "no install route" (the flag is honoured).
#
# Usage: tests/inmodel.sh [FIXTURE.ndjson ...]   (default: the list below)
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

BIN=.lake/build/bin/con-leche
[ -x "$BIN" ] || { echo "inmodel: $BIN not built"; exit 1; }

fixtures=("$@")
if [ ${#fixtures[@]} = 0 ]; then
  fixtures=(tests/e2e/inmodel_mutual.ndjson tests/e2e/inmodel_mutual_idx.ndjson
            tests/e2e/inmodel_nested.ndjson tests/e2e/nested_rec.ndjson
            tests/e2e/nested_struct_proj.ndjson tests/e2e/inmodel_groups.ndjson
            tests/e2e/ind_mutual_three.ndjson tests/e2e/ind_mutual_idxsort.ndjson)
fi

WORK=$(mktemp -d "$TMPDIR/inmodel.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0
for f in "${fixtures[@]}"; do
  name=$(basename "$f" .ndjson)
  rm -f "$WORK/dump.ndjson"
  # 1. the raw run, dumping
  CON_LECHE_INMODEL_DUMP="$WORK/dump.ndjson" timeout 300 "$BIN" "$f" > "$WORK/raw.log" 2>&1
  rawexit=$?
  blocks=$(sed -n 's/^con-leche: \([0-9]*\) inductive blocks modelled in-process: .*/\1/p' "$WORK/raw.log")
  case "$rawexit" in
    0) echo "  $name: raw run accepted (the fixpoint route installs the auxiliary families); ${blocks:-0} blocks in-process";;
    2) if grep -q "no install route for " "$WORK/raw.log"; then
         at=$(sed -n 's/.*no install route for inductive block \([^:]*\):.*/\1/p' "$WORK/raw.log" | head -1)
         echo "  $name: raw run declines at $at (a block no route installs: the residual class); ${blocks:-0} blocks in-process"
       elif grep -q "projection on a non-structure-like type" "$WORK/raw.log"; then
         # a projection function of a recursive structure the fixpoint
         # route installs natively (task #202 Stage B: reflexive
         # structure-likes at `Type`): no `_model.proj_i.iota` artifact
         # on a raw run, so the frontend's projection rewrite does not
         # fire and the raw `.proj` declines by design rule W5 — task
         # #210's prerequisite (native projections on the fix route)
         at=$(sed -n 's/.*\[at \(def [^,]*\),.*/\1/p' "$WORK/raw.log" | head -1)
         echo "  $name: raw run declines at the projection function $at of a natively installed recursive structure (W5; task #210); ${blocks:-0} blocks in-process"
       else
         echo "  FAIL $name: raw run declined elsewhere:"; tail -3 "$WORK/raw.log"; fail=1; continue
       fi;;
    *) echo "  FAIL $name: raw run exit $rawexit:"; tail -3 "$WORK/raw.log"; fail=1; continue;;
  esac
  [ -f "$WORK/dump.ndjson" ] || { echo "  FAIL $name: no dump written"; fail=1; continue; }
  # 2. the dump — the raw input with the generated records spliced in —
  #    carries exactly the records the receipt reports as generated
  gen=$(sed -n 's/^con-leche: [0-9]* inductive blocks modelled in-process: .*(\([0-9]*\) generated records.*/\1/p' "$WORK/raw.log")
  gen=${gen:-0}
  recs() { grep -c '^{"\(def\|thm\|axiom\|opaque\|inductive\|quot\)"' "$1"; }
  added=$(( $(recs "$WORK/dump.ndjson") - $(recs "$f") ))
  if [ "$added" != "$gen" ]; then
    echo "  FAIL $name: dump has $added extra records, receipt says $gen generated"; fail=1; continue
  fi
  echo "  $name: dump carries the $gen generated records (not re-checked: a stream \
model is an ordinary declaration since task #219, so the modeller would generate a second)"
  # 3. the off switch
  CON_LECHE_INMODEL=0 timeout 300 "$BIN" "$f" > "$WORK/off.log" 2>&1
  oexit=$?
  if [ "$oexit" = 2 ] && grep -q "no install route" "$WORK/off.log"; then
    echo "  $name: CON_LECHE_INMODEL=0 declines at the bare block (flag honoured)"
  elif [ "$oexit" = 0 ] && ! grep -q "modelled in-process" "$WORK/off.log"; then
    echo "  $name: CON_LECHE_INMODEL=0 accepted without in-process models (a direct route took every block)"
  else
    echo "  FAIL $name: CON_LECHE_INMODEL=0 exit $oexit:"; tail -3 "$WORK/off.log"; fail=1
  fi
done
if [ "$fail" = 0 ]; then echo "inmodel: OK"; else echo "inmodel: FAIL"; fi
exit $fail
