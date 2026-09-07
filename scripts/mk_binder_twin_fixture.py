#!/usr/bin/env python3
"""Clone the right-hand side of a theorem's `Eq` statement under fresh
binder names and binder infos: a pair of terms that differ ONLY in
display data.

    scripts/mk_binder_twin_fixture.py [--proj] <in.ndjson> <out.ndjson> THM

THM's type must be `∀ (x : T), @Eq A L L` with both sides the SAME
expression-table node (lean4export interns α-equivalent terms as one
node, so a source spelling `... = ...` with two spellings of a binder
name exports that way).  The right-hand side is deep-copied into fresh
table entries — every `lam`/`forallE` on the copy gets a fresh binder
name (`tw_k`) and the binder info `implicit`, every `letE` a fresh
name — and the theorem's type is re-pointed at `∀ (x : T), @Eq A L L'`
with `L'` the copy.  The value is untouched, so the checker compares
the value's inferred `L = L` against the declared `L = L'`.

With `--proj`, the side `L` must be `Prod.snd A B s` (the projection
FUNCTION, which is how the elaborator exports `p.2`), and that table
node is rewritten IN PLACE to the kernel projection `.proj Prod 1 s`
before cloning — so the value's `rfl` (which references the same node)
and both sides of the statement are `.proj`-headed.  Two `Prod.snd`
applications meet the lazy-delta same-head spine congruence and never
whnf their struct; two `.proj` nodes that are not `==` go through
`whnfCore`'s projection clause, which whnf's the struct in full (the
divergence audit's D5) — the shape of the task #201 residual.

What it is for (task #203): the official kernel's equality and hash
ignore binder names and infos, so this pair is decided by its
structural walk; a checker whose `==` reads the display data misses
its fast path here and, with the difference sitting inside a
`.proj`-headed struct's argument, whnf's the struct in full (the task
#201 residual).  `tests/e2e/binder_name_proj.ndjson` is
`tests/e2e/src/binder_name_proj.lean`'s raw export through this
script with `--proj` and THM = `w2`.

The result must be checked RAW (`CON_LECHE_INDUCTIVE_MODELS=/nonexistent`,
a `raw` line in `tests/e2e-expected.txt`): the preprocessor
(`con-leche-preprocess`, lean-inductive-models) re-exports the stream
through `Lean.Expr`, whose hash-consing is α-equivalence, so a piped
run collapses the clone back into the original node and the pair never
reaches the checker.
"""
import json
import sys


def main() -> int:
    args = sys.argv[1:]
    proj = False
    if args and args[0] == "--proj":
        proj = True
        args = args[1:]
    if len(args) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    src, out, thm = args

    lines = [ln.rstrip("\n") for ln in open(src, encoding="utf-8")]
    names: dict[int, str] = {0: ""}
    exprs: dict[int, dict] = {}
    max_in = 0
    max_ie = 0
    thm_line = None
    for k, ln in enumerate(lines):
        o = json.loads(ln)
        if "in" in o:
            i = o["in"]
            max_in = max(max_in, i)
            if "str" in o:
                pre = names[o["str"]["pre"]]
                names[i] = (pre + "." if pre else "") + o["str"]["str"]
            else:
                pre = names[o["num"]["pre"]]
                names[i] = (pre + "." if pre else "") + str(o["num"]["i"])
        elif "ie" in o:
            max_ie = max(max_ie, o["ie"])
            exprs[o["ie"]] = o
        elif "thm" in o and names.get(o["thm"]["name"]) == thm:
            thm_line = k
    if thm_line is None:
        print(f"theorem {thm} not found", file=sys.stderr)
        return 1

    rec = json.loads(lines[thm_line])
    ty = exprs[rec["thm"]["type"]]
    if "forallE" not in ty:
        print("type is not a ∀", file=sys.stderr)
        return 1
    body = exprs[ty["forallE"]["body"]]
    # body = app (app (app (const Eq) A) L) R
    if "app" not in body:
        print("∀-body is not an application", file=sys.stderr)
        return 1
    lhs_app = exprs[body["app"]["fn"]]
    if "app" not in lhs_app or body["app"]["arg"] != lhs_app["app"]["arg"]:
        print("statement is not `L = L` on one node", file=sys.stderr)
        return 1
    rhs = body["app"]["arg"]

    rewritten: dict[int, str] = {}
    if proj:
        # L = app (app (app (const Prod.snd) A) B) s  ->  proj Prod 1 s
        node = exprs[rhs]
        try:
            a1 = exprs[node["app"]["fn"]]
            a2 = exprs[a1["app"]["fn"]]
            head = exprs[a2["app"]["fn"]]
            hname = head["const"]["name"]
        except (KeyError, TypeError):
            print("--proj: side is not a `Prod.snd A B s` application",
                  file=sys.stderr)
            return 1
        if names.get(hname) != "Prod.snd":
            print(f"--proj: head is {names.get(hname)!r}, not Prod.snd",
                  file=sys.stderr)
            return 1
        prod = next((i for i, n in names.items() if n == "Prod"), None)
        if prod is None:
            print("--proj: no name-table entry for Prod", file=sys.stderr)
            return 1
        newnode = {"ie": rhs,
                   "proj": {"idx": 1, "struct": node["app"]["arg"],
                            "typeName": prod}}
        exprs[rhs] = newnode
        rewritten[rhs] = json.dumps(newnode, separators=(",", ":"),
                                    sort_keys=True)

    new_lines: list[str] = []
    fresh = {"in": max_in, "ie": max_ie, "tw": 0}

    def fresh_name() -> int:
        fresh["in"] += 1
        fresh["tw"] += 1
        new_lines.append(json.dumps(
            {"in": fresh["in"], "str": {"pre": 0, "str": f"tw_{fresh['tw']}"}},
            separators=(",", ":")))
        return fresh["in"]

    memo: dict[int, int] = {}

    def clone(i: int) -> int:
        if i in memo:
            return memo[i]
        o = exprs[i]
        kind = next(k for k in o if k != "ie")
        if kind not in ("app", "lam", "forallE", "letE", "proj"):
            # bvar / sort / const / natVal / strVal: shared as is
            memo[i] = i
            return i
        v = dict(o[kind])
        if kind == "app":
            v["fn"] = clone(v["fn"])
            v["arg"] = clone(v["arg"])
        elif kind in ("lam", "forallE"):
            v["name"] = fresh_name()
            v["binderInfo"] = "implicit"
            v["type"] = clone(v["type"])
            v["body"] = clone(v["body"])
        elif kind == "letE":
            v["name"] = fresh_name()
            v["type"] = clone(v["type"])
            v["value"] = clone(v["value"])
            v["body"] = clone(v["body"])
        else:  # proj
            v["struct"] = clone(v["struct"])
        fresh["ie"] += 1
        j = fresh["ie"]
        n = {kind: v, "ie": j}
        new_lines.append(json.dumps(n, separators=(",", ":"), sort_keys=True))
        memo[i] = j
        return j

    rhs2 = clone(rhs)
    if rhs2 == rhs:
        print("right-hand side has no binder to rename", file=sys.stderr)
        return 1
    fresh["ie"] += 1
    body2 = fresh["ie"]
    new_lines.append(json.dumps(
        {"app": {"arg": rhs2, "fn": body["app"]["fn"]}, "ie": body2},
        separators=(",", ":"), sort_keys=True))
    fresh["ie"] += 1
    ty2 = fresh["ie"]
    fa = dict(ty["forallE"])
    fa["body"] = body2
    new_lines.append(json.dumps({"forallE": fa, "ie": ty2},
                                separators=(",", ":"), sort_keys=True))
    rec["thm"]["type"] = ty2

    with open(out, "w", encoding="utf-8") as f:
        for ln in lines[:thm_line]:
            o = json.loads(ln)
            if "ie" in o and o["ie"] in rewritten:
                ln = rewritten[o["ie"]]
            f.write(ln + "\n")
        for ln in new_lines:
            f.write(ln + "\n")
        f.write(json.dumps(rec, separators=(",", ":"), sort_keys=True) + "\n")
        for ln in lines[thm_line + 1:]:
            f.write(ln + "\n")
    print(f"{out}: cloned {len(memo)} nodes, {fresh['tw']} binders renamed",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
