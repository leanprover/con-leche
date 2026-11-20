#!/usr/bin/env bash
# scripts/mk_iota_read_fixtures.sh — the ι-reading fixtures of the e2e gate (task #622).
#
# Compiles tests/e2e/src/iota_read_annotated.lean with the repository toolchain's `lean`, exports
# the names its `--#export` line lists with the toolchain's `leanexport` into
# tests/e2e/iota_read_annotated.ndjson, and derives tests/e2e/iota_read_field_differs.ndjson:
# `S.rec`'s minor premise's first field domain `Nat` replaced by `(fun α : Type => α) Nat`.
set -euo pipefail
cd "$(dirname "$0")/.."
PREFIX=$(lean --print-prefix)
L4E=$PREFIX/bin/leanexport
[ -x "$L4E" ] || { echo "no leanexport in $PREFIX/bin"; exit 3; }
OUT=_tmp/iota-read-fixtures
mkdir -p "$OUT"
m=iota_read_annotated
roots=$(sed -n 's/^--#export //p' "tests/e2e/src/$m.lean")
timeout 300 lean -o "$OUT/$m.olean" "tests/e2e/src/$m.lean"
LEAN_PATH="$OUT:$PREFIX/lib/lean" timeout 300 "$L4E" "$m" -- $roots > "tests/e2e/$m.ndjson"
python3 -I - "tests/e2e/$m.ndjson" tests/e2e/iota_read_field_differs.ndjson <<'PY'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
recs = [json.loads(l) for l in open(src).read().splitlines()]
names = {r["in"]: r for r in recs if "in" in r}
exprs = {r["ie"]: r for r in recs if "ie" in r}
levels = {r["il"]: r for r in recs if "il" in r}
def name_of(i):
    if i == 0: return ""
    r = names[i]
    s = r.get("str") or r.get("num")
    p = name_of(s["pre"])
    v = s.get("str", s.get("i"))
    return f"{p}.{v}" if p else str(v)
def name_idx(n):
    return next(i for i in names if name_of(i) == n)
def level_idx(pred):
    return next(i for i, r in levels.items() if pred(r))
nat = next(i for i, e in exprs.items() if "const" in e and name_of(e["const"]["name"]) == "Nat")
# fresh indices for `(fun α : Type => α) Nat`: definitionally `Nat`, syntactically not
ie = max(exprs) + 1
il1 = level_idx(lambda r: r.get("succ") == 0)
bv0 = next(i for i, e in exprs.items() if e.get("bvar") == 0)
new = [{"ie": ie, "sort": il1},
       {"ie": ie + 1, "lam": {"binderInfo": "default", "body": bv0, "name": 0, "type": ie}},
       {"ie": ie + 2, "app": {"fn": ie + 1, "arg": nat}}]
idv = ie + 2
def rebuild(i, path):
    """Copy the expression `i` along `path` (binder bodies 'b' / domains 't'), the end replaced."""
    global ie
    if not path:
        return idv
    e = json.loads(json.dumps(exprs[i]))
    f = e["forallE"]
    if path[0] == "t": f["type"] = rebuild(f["type"], path[1:])
    else: f["body"] = rebuild(f["body"], path[1:])
    ie_new = max(max(exprs), max(r["ie"] for r in new if "ie" in r)) + 1
    e["ie"] = ie_new
    exprs[ie_new] = e
    new.append(e)
    return ie_new
out = []
for r in recs:
    if "inductive" in r:
        for rec in r["inductive"]["recs"]:
            if name_of(rec["name"]) == "S.rec":
                # S.rec : (motive : S → Sort u) → (mk : (x : Nat) → … ) → (t : S) → motive t
                rec["type"] = rebuild(rec["type"], ["b", "t", "t"])
                out.extend(json.dumps(x) for x in new)
    out.append(json.dumps(r))
open(dst, "w").write("\n".join(out) + "\n")
PY
echo "$m: $(wc -l < "tests/e2e/$m.ndjson") lines"
