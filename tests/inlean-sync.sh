#!/usr/bin/env bash
# tests/inlean-sync.sh — the in-core copy of InLean, generated without lean4.
#
# `scripts/inlean-sync.py generate` writes the copy lean4 carries at
# `src/Lean/Kernel/InLean/` from `InLean/*` by a fixed rule list (the
# script's docstring); `check` compares a lean4 checkout's copy with it and
# runs at lean4 sync rounds.  This gate needs no lean4 checkout and no
# build; it checks what can be checked here:
#
#   * the generation is deterministic (two runs, byte-identical trees);
#   * every `InLean/**/*.lean` is mapped, and nothing else is written;
#   * every generated file starts with the copyright block, `module` and
#     `prelude`, and imports nothing of con-leche (`ConLeche*`) and nothing
#     under the unrenamed `InLean.` prefix; no `namespace`/`end`/`open` is
#     left at `InLean`;
#   * every pin dump an `include_str` names exists in `pins/`;
#   * the comments carry nothing the copy cannot use: no con-leche-relative
#     path (`ConLeche/…`, `InLean/…`, `InLeanProof/…`, `scripts/`, `tests/`)
#     and no task number.  A comment cites a module by its name
#     (`InLean.CoreC`, renamed with the namespace) instead.
set -u
cd "$(dirname "$0")/.."
tmp=$(mktemp -d "${TMPDIR:-/tmp}/inlean-sync.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
fail=0
say() { echo "inlean-sync: FAIL — $*"; fail=1; }

python3 -I scripts/inlean-sync.py generate "$tmp/a" || { say "generate failed"; exit 1; }
python3 -I scripts/inlean-sync.py generate "$tmp/b" || { say "generate failed"; exit 1; }
diff -r "$tmp/a" "$tmp/b" > /dev/null || say "two runs of generate differ"

src=$(cd InLean && find . -name '*.lean' | sort)
out=$(cd "$tmp/a" && find . -type f | sort)
[ "$src" = "$out" ] || say "generated files are not exactly InLean's .lean files"

head_ok=$(printf '/-\nCopyright (c) ')
for f in $out; do
  g="$tmp/a/$f"
  [ "$(head -c ${#head_ok} "$g")" = "$head_ok" ] || say "$f: no copyright block"
  grep -q -x 'prelude' "$g" || say "$f: no prelude"
  [ "$(sed -n 6p "$g")" = "module" ] || say "$f: line 6 is not \`module\`"
done

bad=$(grep -n -E '^\s*(public |meta |private )*import\s+(all\s+)?(ConLeche|InLean)(\.|\b)' -r "$tmp/a" || true)
[ -z "$bad" ] || say "con-leche or unrenamed InLean imports:
$bad"
bad=$(grep -n -E '^\s*(namespace|end|open)\s+InLean\b' -r "$tmp/a" || true)
[ -z "$bad" ] || say "an unrenamed InLean namespace:
$bad"

for p in $(grep -h -o -E 'include_str "pins/[^"]*"' -r "$tmp/a" | sed -E 's/include_str "pins\/(.*)"/\1/'); do
  [ -f "pins/$p" ] || say "pin dump pins/$p not found"
done

bad=$(grep -n -E '(ConLeche|InLeanProof|InLean)/|`(scripts|tests)/|#[0-9]{3}\b' -r "$tmp/a" | grep -v 'include_str' || true)
[ -z "$bad" ] || say "repository paths or task numbers in the copy:
$bad"

[ $fail = 0 ] && echo "inlean-sync: OK ($(echo "$out" | wc -l) files)"
exit $fail
