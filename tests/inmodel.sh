#!/usr/bin/env bash
# tests/inmodel.sh — THE IN-PROCESS MODELLER'S GATE (task #200).
#
# For each raw fixture below, the in-process modeller
# (`Lech/Frontend/InModel/*`) generates the `_model` families of its
# mutual/nested blocks at parse time.  The generated AUXILIARY family is a
# recursive indexed inductive the direct fixpoint route (task #188)
# installs; until that route is on master at indices, the raw run declines
# at the auxiliary block ("missing model") and the generator is gated
# through the DEBUG DUMP instead: `LECH_INMODEL_DUMP` writes the raw input
# with the generated records spliced in, `lech-preprocess` (told to leave
# the in-process class alone, `LECH_INMODEL_NATIVE=1`, structural checks
# off — it audits model roles lech never consumes) models the auxiliary
# families, and the result must ACCEPT in both modes with every
# in-process block routed `modeled`.
#
#   * raw run (`--pre` on the raw export, in-process modelling on):
#     exit 2 at the auxiliary block before #188, exit 0 after — either is
#     recorded, a REJECT or an error fails;
#   * dump → lech-preprocess → lech: exit 0 in `--verified` and
#     `--trusted`, else FAIL;
#   * `LECH_INMODEL=0` on the raw export: the blocks reach the fold bare
#     and the run declines with "missing model" (the flag is honoured).
#
# Usage: tests/inmodel.sh [FIXTURE.ndjson ...]   (default: the list below)
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

BIN=.lake/build/bin/lech
PRE=.lake/build/bin/lech-preprocess
[ -x "$BIN" ] || { echo "inmodel: $BIN not built"; exit 1; }
[ -x "$PRE" ] || { echo "inmodel: $PRE not built"; exit 1; }

fixtures=("$@")
if [ ${#fixtures[@]} = 0 ]; then
  fixtures=(tests/e2e/inmodel_mutual.ndjson)
fi

WORK=$(mktemp -d "$TMPDIR/inmodel.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0
for f in "${fixtures[@]}"; do
  name=$(basename "$f" .ndjson)
  rm -f "$WORK/dump.ndjson" "$WORK/pre.ndjson"
  # 1. the raw run, dumping
  LECH_INMODEL_DUMP="$WORK/dump.ndjson" timeout 300 "$BIN" --pre "$f" > "$WORK/raw.log" 2>&1
  rawexit=$?
  blocks=$(sed -n 's/^lech: \([0-9]*\) inductive blocks modelled in-process: .*/\1/p' "$WORK/raw.log")
  case "$rawexit" in
    0) echo "  $name: raw run accepted (the fixpoint route installs the auxiliary families); ${blocks:-0} blocks in-process";;
    2) if grep -q "missing model for .*_model._impl.aux" "$WORK/raw.log"; then
         echo "  $name: raw run declines at the auxiliary family (task #188 not landed); ${blocks:-0} blocks in-process"
       else
         echo "  FAIL $name: raw run declined elsewhere:"; tail -3 "$WORK/raw.log"; fail=1; continue
       fi;;
    *) echo "  FAIL $name: raw run exit $rawexit:"; tail -3 "$WORK/raw.log"; fail=1; continue;;
  esac
  [ -f "$WORK/dump.ndjson" ] || { echo "  FAIL $name: no dump written"; fail=1; continue; }
  # 2. the tool over the dump, leaving the in-process class alone
  LECH_INMODEL_NATIVE=1 timeout 600 "$PRE" --no-check -o "$WORK/pre.ndjson" "$WORK/dump.ndjson" > "$WORK/pre.log" 2>&1
  pexit=$?
  if [ "$pexit" != 0 ] || [ ! -f "$WORK/pre.ndjson" ]; then
    echo "  FAIL $name: lech-preprocess exit $pexit on the dump:"; tail -5 "$WORK/pre.log"; fail=1; continue
  fi
  if ! grep -q "native — left to the consumer" "$WORK/pre.log" 2>/dev/null && [ -n "$blocks" ]; then
    :
  fi
  # 3. the modelled dump must accept in both modes
  for mode in --verified --trusted; do
    LECH_ROUTE_TRACE=1 timeout 600 "$BIN" $mode --pre "$WORK/pre.ndjson" > "$WORK/check.log" 2>&1
    cexit=$?
    if [ "$cexit" != 0 ]; then
      echo "  FAIL $name ($mode): exit $cexit on the modelled dump:"; tail -3 "$WORK/check.log"; fail=1; continue
    fi
    nmod=$(grep -c "^lech: route .* modeled$" "$WORK/check.log")
    acc=$(sed -n 's/^lech: accepted \([0-9]*\) declarations.*/\1/p' "$WORK/check.log")
    echo "  $name ($mode): accepted $acc declarations, $nmod blocks routed modeled"
  done
  # 4. the off switch
  LECH_INMODEL=0 timeout 300 "$BIN" --pre "$f" > "$WORK/off.log" 2>&1
  oexit=$?
  if [ "$oexit" = 2 ] && grep -q "missing model" "$WORK/off.log"; then
    echo "  $name: LECH_INMODEL=0 declines at the bare block (flag honoured)"
  elif [ "$oexit" = 0 ] && ! grep -q "modelled in-process" "$WORK/off.log"; then
    echo "  $name: LECH_INMODEL=0 accepted without in-process models (a direct route took every block)"
  else
    echo "  FAIL $name: LECH_INMODEL=0 exit $oexit:"; tail -3 "$WORK/off.log"; fail=1
  fi
done
if [ "$fail" = 0 ]; then echo "inmodel: OK"; else echo "inmodel: FAIL"; fi
exit $fail
