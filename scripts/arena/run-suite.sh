#!/usr/bin/env bash
# Run the *upstream* Lean Kernel Arena suite against this working tree's
# setlec, through the arena's own orchestration (`lka.py`), so the exports
# are produced exactly the way the arena produces them.
#
#   scripts/arena/run-suite.sh clone           # clone/refresh the arena
#   scripts/arena/run-suite.sh build-tests …   # lka.py build-test (patterns)
#   scripts/arena/run-suite.sh run …           # lka.py run   --checker setlec
#   scripts/arena/run-suite.sh table            # print the result table
#   scripts/arena/run-suite.sh all              # everything but mathlib
#
# Everything lives under $WORK (default `_tmp/arena-suite`, gitignored).
# Mathlib is never built or run here: it is a multi-hour lane of its own.
#
# THE BIG FOUR (`run-big`: init, std, cedar, cslib — 0.3 to 2.0 GB of raw
# export each).  They are Mathlib-scale in memory, so: strictly one at a time,
# `ulimit -v 22000000`, and never while another lane's Mathlib-scale run is
# live on the machine (`pgrep -f '\.lake/build/bin/setlec'` — check for a
# FOREIGN one; the cgroup will kill a run otherwise).  `run-small` is the rest
# and is harmless (the biggest cell is perf/app-lam at ~4 GB).
#
# WHAT THE ARENA NEEDS, AND WHERE IT COMES FROM ON THIS MACHINE
#   * python + pyyaml/jsonschema/markdown/jinja2 — via `uv run lka.py`
#     (the PEP-723 header in lka.py pins them); no venv to maintain.
#   * elan — on PATH already; lka.py drives it to fetch the toolchain named
#     in tests/lean-toolchain and to build `lean4export` against it.
#   * GNU `time` — NOT installed system-wide here (only the shell builtin),
#     and lka.py shells out to it for max-RSS.  We put a symlink to the
#     nixpkgs `time` on PATH; without it every RSS figure reads 0.
#   * perf — on PATH; lka.py uses it for instructions/task-clock.
#   * rustc/cargo — only needed to BUILD the Rust checkers upstream.  We
#     never build another checker, so they are not required.
#
# The checker definition is scripts/arena/setlec.yaml; it is copied into the
# clone's checkers/ on every run, and takes the binary, the preprocessor, the
# mode and the limits from the environment (see below), so the arena clone
# stays a pure checkout.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
WORK=${SETLEC_ARENA_WORK:-$ROOT/_tmp/arena-suite}
ARENA=${SETLEC_ARENA_DIR:-$WORK/lean-kernel-arena}
ARENA_URL=${SETLEC_ARENA_URL:-https://github.com/leanprover/lean-kernel-arena}

export SETLEC_BIN=${SETLEC_BIN:-$ROOT/.lake/build/bin/setlec}
export SETLEC_PREPROC=${SETLEC_PREPROC:-$ROOT/.lake/build/bin/setlec-preprocess}
export SETLEC_MODE=${SETLEC_MODE:---verified}
# Scratch for the preprocessor's temp stream — MUST be on disk: /tmp is a
# tmpfs here and a Cedar/cslib/Init preprocessing run would put gigabytes of
# it in RAM.  Exported so the checker's `run` command inherits it, and set as
# TMPDIR for this script's own children too.
export SETLEC_TMPDIR=${SETLEC_TMPDIR:-$WORK/tmp}
mkdir -p "$SETLEC_TMPDIR"
export TMPDIR=$SETLEC_TMPDIR
# The standing ceilings for this project: 22 GB / 4 h for the large streams
# (cedar, cslib, init, std), 16 GB / 50 min otherwise.  Set per invocation.
export SETLEC_VLIMIT=${SETLEC_VLIMIT:-16000000}
export SETLEC_TIMEOUT=${SETLEC_TIMEOUT:-3000}

# GNU time (see above).  Anything already on PATH wins.
# NB `time` is a bash KEYWORD, so `time --version` and `command -v time` both
# answer about the builtin; `env time` is the probe that means the binary.
if ! env time --version >/dev/null 2>&1; then
  gtime=$(type -P gtime || true)
  if [ -z "$gtime" ] && command -v nix-shell >/dev/null 2>&1; then
    gtime=$(nix-shell -p time --run 'which time' 2>/dev/null | tail -1)
  fi
  if [ -n "${gtime:-}" ] && [ -x "$gtime" ]; then
    mkdir -p "$WORK/bin"; ln -sf "$gtime" "$WORK/bin/time"
    PATH=$WORK/bin:$PATH; export PATH
  else
    echo "warning: no GNU time found; max-RSS will be reported as 0" >&2
  fi
fi

lka() { (cd "$ARENA" && uv run lka.py "$@"); }

do_clone() {
  mkdir -p "$WORK"
  if [ -d "$ARENA/.git" ]; then
    git -C "$ARENA" fetch --quiet origin && git -C "$ARENA" checkout --quiet -f origin/HEAD
  else
    git clone "$ARENA_URL" "$ARENA" || exit 1
  fi
  git -C "$ARENA" log --oneline -1
}

install_checker() {
  [ -d "$ARENA/checkers" ] || { echo "no arena clone at $ARENA (run 'clone')" >&2; exit 1; }
  cp "$ROOT/scripts/arena/setlec.yaml" "$ARENA/checkers/setlec.yaml"
  for f in "$SETLEC_BIN" "$SETLEC_PREPROC"; do
    [ -x "$f" ] || { echo "missing binary: $f  (lake build)" >&2; exit 1; }
  done
  lka build-checker setlec
}

# The four multi-hundred-megabyte streams: they get the large ceilings and run
# strictly one at a time.  `mathlib` is never in any list here.
BIG="init std cedar cslib"

# Every test EXCEPT mathlib, as lka.py names them.  The subdirectory groups are
# collapsed to one glob each so a run is ~30 `lka.py` invocations, not 200.
all_tests() {
  (cd "$ARENA/tests" && find . -name '*.yaml' | sed 's|^\./||; s|\.yaml$||') \
    | grep -v '^mathlib$' | sort
}
small_tests() {
  all_tests | grep -v -E "^($(echo $BIG | tr ' ' '|'))$" \
            | grep -v -E '^(corner-cases|perf)/' | grep -v '^tutorial$'
  echo 'corner-cases/*'; echo 'perf/*'; echo 'tutorial/*'
}

run_group() { # $@ = lka test patterns
  install_checker >/dev/null
  for p in "$@"; do lka run --checker setlec --test "$p"; done
}

case "${1:-all}" in
  clone) do_clone ;;
  build-checker) install_checker ;;
  build-tests)
    shift
    if [ $# -gt 0 ]; then for p in "$@"; do lka build-test "$p"; done
    else for p in $(all_tests); do lka build-test "$p"; done; fi ;;
  run)
    shift
    if [ $# -gt 0 ]; then run_group "$@"; else run_group $(small_tests | tr '\n' ' '); fi ;;
  run-small)
    IFS=$'\n' read -r -d '' -a pats < <(small_tests; printf '\0')
    run_group "${pats[@]}" ;;
  run-big)
    # one at a time, 22 GB / 4 h, and nothing else of ours running
    SETLEC_VLIMIT=${SETLEC_VLIMIT_BIG:-22000000} \
    SETLEC_TIMEOUT=${SETLEC_TIMEOUT_BIG:-14400} \
      run_group $BIG ;;
  table)
    shift
    python3 "$ROOT/scripts/arena/table.py" "$ARENA" setlec "${1:-$ARENA/_results}" ;;
  all)
    do_clone
    for p in $(all_tests); do lka build-test "$p"; done
    "${BASH_SOURCE[0]}" run-small
    "${BASH_SOURCE[0]}" run-big
    python3 "$ROOT/scripts/arena/table.py" "$ARENA" ;;
  *) sed -n '2,30p' "${BASH_SOURCE[0]}"; exit 1 ;;
esac
