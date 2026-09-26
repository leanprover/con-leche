#!/usr/bin/env python3
"""Corner case D3 of charter item 8 (lanes CHECKDEL/CHECKDEL2): a container
instantiation whose parameters are well-typed only because two SPELLINGS
of one family class are defeq.  Official rejects; we accept (sound).

  corner_checkdel_d_anc_bad   `corner_checkdel_d_anc.ndjson` with the
      phantom parameter value `fun _ : List R => 0` rewritten to
      `fun _ : List ((fun x => x) R) => 0` at its one hash-consed node
      (every occurrence, the recursors included).  Official rejects:
      `replace_all_nested` compares nested occurrences STRUCTURALLY
      (`inductive.cpp` v4.33.0 :991), so the two spellings become two
      auxiliary types and the auxiliary constructor
      `mk : F (List_1 → Nat) (fun _ : List_3 => 0) R → C_aux` is
      ill-typed ("(kernel) application type mismatch", measured at
      v4.29.1 and v4.33.0 from the source).  TARGET 0 (official 1): ruling
      (D), which rejected it, is withdrawn.

  corner_checkdel_d_anc_nocall_bad   the same forgery of
      `corner_checkdel_d_anc_nocall.ndjson`, whose container field reading
      the parameter (`y : F α a Nat`) is NOT recursive: no recursive call
      types it.  Official 1 for the same reason.  TARGET 0.

Usage: scripts/mk_checkdel_d_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def forge(base):
    src = os.path.join(ROOT, "tests/e2e/%s.ndjson" % base)
    recs = [json.loads(l) for l in open(src).read().splitlines()]
    names = {0: ""}
    for r in recs:
        if "in" in r:
            k = "str" if "str" in r else "num"
            pre = names[r[k]["pre"]]
            names[r["in"]] = (pre + "." if pre else "") + str(r[k].get(k, r[k].get("i")))
    exprs = {r["ie"]: r for r in recs if "ie" in r}

    def is_const(i, n):
        e = exprs[i]
        return "const" in e and names[e["const"]["name"]] == n

    def head_is(i, n):
        while "app" in exprs[i]:
            i = exprs[i]["app"]["fn"]
        return is_const(i, n)

    def is_list_r(i):
        e = exprs[i]
        return "app" in e and is_const(e["app"]["fn"], "List") and is_const(e["app"]["arg"], "R")

    lams = [i for i, e in exprs.items() if "lam" in e and is_list_r(e["lam"]["type"])
            and head_is(e["lam"]["body"], "OfNat.ofNat")]
    assert len(lams) == 1, lams
    lam = lams[0]  # `fun _ : List R => 0`
    list_r = exprs[exprs[lam]["lam"]["type"]]["app"]
    one = next(r["il"] for r in recs if "il" in r and r.get("succ") == 0)  # level 1
    typ = next(i for i, e in exprs.items() if "sort" in e and e["sort"] == one)  # Type
    bv0 = next(i for i, e in exprs.items() if e.get("bvar") == 0)
    nxt = max(exprs) + 1
    xname = exprs[lam]["lam"]["name"]
    new = [
        {"ie": nxt, "lam": {"binderInfo": "default", "body": bv0, "name": xname, "type": typ}},
        {"app": {"arg": list_r["arg"], "fn": nxt}, "ie": nxt + 1},
        {"app": {"arg": nxt + 1, "fn": list_r["fn"]}, "ie": nxt + 2},
    ]
    out = []
    for r in recs:
        if r.get("ie") == lam:
            out += new
            r = dict(r, lam=dict(r["lam"], type=nxt + 2))
        out.append(r)
    dst = os.path.join(ROOT, "tests/e2e/%s_bad.ndjson" % base)
    with open(dst, "w") as f:
        for r in out:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s_bad.ndjson: %d lines (λ node %d)" % (base, len(out), lam))


def main():
    forge("corner_checkdel_d_anc")
    forge("corner_checkdel_d_anc_nocall")


if __name__ == "__main__":
    main()
