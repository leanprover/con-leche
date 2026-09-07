#!/usr/bin/env python3
"""Build the `nested_pin_names` e2e fixture: binder-name drift in a
nested-auxiliary iota theorem's stored-pin lambdas.

Takes a stream that carries a `_model` family (historically:
tests/e2e/src/nested_pin_names.lean → lean4export 3.x →
lean-inductive-models, before task #207 dropped the tool; the
committed fixture is that output and stays valid — the in-process
modeller's dump, `CON_LECHE_INMODEL_DUMP`, is the way to produce a new
one) and, for the given iota theorems, renames the binder of every
lambda whose body is headed by
the given constant (the dependent pin `fun _ => PTree._model α`) to a
fresh name.  The export format permits exactly this drift — arenas
intern expressions name-insensitively, so a re-rendered statement can
spell a shared lambda under another binder name (the shape that
declined Mathlib at `Lean.PrefixTreeNode.rec_3`).  The checker must
still accept: binder names are display-only.

The rewrite clones every node on a path to an affected lambda under
fresh `ie` ids (appended immediately before the theorem's record) and
repoints the theorem's `type`; all other records are untouched.

Usage:
  mk_nested_pin_fixture.py <in.ndjson> <out.ndjson> <pin-body-head-const> <thm-name>...
"""
import json
import sys


def main() -> None:
    inp, out = sys.argv[1], sys.argv[2]
    pin_head = sys.argv[3]
    targets = set(sys.argv[4:])

    lines = open(inp).read().splitlines()
    names: dict[int, str] = {0: ""}
    exprs: dict[int, dict] = {}
    max_in = 0
    max_ie = 0
    for line in lines:
        r = json.loads(line)
        if "in" in r:
            i = r["in"]
            max_in = max(max_in, i)
            if "str" in r:
                p = names[r["str"]["pre"]]
                names[i] = (p + "." if p else "") + r["str"]["str"]
            else:
                names[i] = names[r["num"]["pre"]] + "." + str(r["num"]["i"])
        elif "ie" in r:
            max_ie = max(max_ie, r["ie"])
            exprs[r["ie"]] = r

    # resolve the pin head constant's name id
    head_id = None
    for i, n in names.items():
        if n == pin_head:
            head_id = i
    assert head_id is not None, f"constant {pin_head} not in stream"

    def body_head(i: int) -> int | None:
        e = exprs[i]
        while "app" in e:
            e = exprs[e["app"]["fn"]]
        if "const" in e:
            return e["const"]["name"]
        return None

    out_lines: list[str] = []
    fresh_name_emitted = False
    drift_name_id = max_in + 1
    next_ie = max_ie + 1
    rewritten = 0

    for line in lines:
        r = json.loads(line)
        if "thm" in r and names.get(r["thm"]["name"]) in targets:
            new_records: list[dict] = []
            memo: dict[int, int] = {}

            def rewrite(i: int) -> int:
                nonlocal next_ie
                if i in memo:
                    return memo[i]
                e = exprs[i]
                new_id = i
                if "lam" in e and body_head(e["lam"]["body"]) == head_id:
                    b = dict(e["lam"])
                    b["name"] = drift_name_id
                    b["body"] = rewrite(b["body"])
                    b["type"] = rewrite(b["type"])
                    new_id = next_ie
                    next_ie += 1
                    new_records.append({"ie": new_id, "lam": b})
                elif "app" in e:
                    f2, a2 = rewrite(e["app"]["fn"]), rewrite(e["app"]["arg"])
                    if (f2, a2) != (e["app"]["fn"], e["app"]["arg"]):
                        new_id = next_ie
                        next_ie += 1
                        new_records.append(
                            {"ie": new_id, "app": {"fn": f2, "arg": a2}})
                elif "forallE" in e or "lam" in e:
                    k = "forallE" if "forallE" in e else "lam"
                    b = dict(e[k])
                    t2, b2 = rewrite(b["type"]), rewrite(b["body"])
                    if (t2, b2) != (b["type"], b["body"]):
                        b["type"], b["body"] = t2, b2
                        new_id = next_ie
                        next_ie += 1
                        new_records.append({"ie": new_id, k: b})
                memo[i] = new_id
                return new_id

            new_ty = rewrite(r["thm"]["type"])
            if new_ty != r["thm"]["type"]:
                rewritten += 1
                if not fresh_name_emitted:
                    out_lines.append(json.dumps(
                        {"in": drift_name_id,
                         "str": {"pre": 0, "str": "x!pin_drift"}},
                        separators=(",", ":")))
                    fresh_name_emitted = True
                for rec in new_records:
                    exprs[rec["ie"]] = rec
                    out_lines.append(json.dumps(rec, separators=(",", ":")))
                r["thm"]["type"] = new_ty
                out_lines.append(json.dumps(r, separators=(",", ":")))
                continue
        out_lines.append(line)

    assert rewritten == len(targets), \
        f"rewrote {rewritten} of {len(targets)} target theorems"
    with open(out, "w") as f:
        f.write("\n".join(out_lines) + "\n")
    print(f"perturbed {rewritten} theorems; wrote {out}")


if __name__ == "__main__":
    main()
