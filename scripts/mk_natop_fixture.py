#!/usr/bin/env python3
"""Build small e2e fixtures for the pin-certified Nat operations from a
lean4export 3.x ndjson stream, by *dependency-closure slicing*: keep
only the declarations transitively needed to install the operation
(with the pin/certificate ground constants, whose names are supplied
via a roots json produced from the generated pins), plus

* accept fixture: a literal `Eq.refl`-style theorem
  `opFact : op a [b] = r` exercising the certified literal fast path;
* decline fixture (--perturb): the operation's defining value replaced
  by a type-correct but semantically different body (`fun x y => x`,
  resp. `fun x => x`), which the pin gate must positively decline
  (exit 2).

Usage:
  mk_natop_fixture.py <stream> <roots.json> <op> <out.ndjson> a [b] r
  mk_natop_fixture.py <stream> <roots.json> <op> <out.ndjson> --perturb
      (--perturb rewrites the op to `fun x y => x`; every pin-certified
       operation is binary)

Since task #113 the certificate proofs are self-contained (closed over
the op's own dependency cone), so the roots json only needs the
guard-required ground operations per op (`natOpDeps` + `Bool`):
`scripts/natop_cone_roots.json` builds the pure-cone acceptance
fixture `tests/e2e/nat_land_cone.ndjson`, which deliberately excludes
the historical cert-proof extras (funext, Eq.subst,
of_decide_eq_true, ...).
"""
import json
import sys


def main() -> None:
    stream, rootsj, opname, out = sys.argv[1:5]
    perturb = sys.argv[5] == "--perturb"
    args = [] if perturb else [int(x) for x in sys.argv[5:-1]]
    result = None if perturb else int(sys.argv[-1])

    all_pin_roots = json.load(open(rootsj))
    pin_roots = all_pin_roots.get(opname, [])

    names = {0: ""}
    name_idx: dict[str, int] = {"": 0}
    name_parent: dict[int, int] = {}
    max_name = max_ie = max_il = 0
    succ_zero_il = None

    lines: list[str] = []          # raw lines
    recs: list[dict] = []          # parsed records, parallel
    # expr graph
    e_children: dict[int, list[int]] = {}
    e_names: dict[int, list[int]] = {}
    e_levels: dict[int, list[int]] = {}
    l_children: dict[int, list[int]] = {}
    l_names: dict[int, list[int]] = {}
    # per-line kind info
    decl_lines: list[int] = []     # indices into lines of decl records
    decl_names: dict[int, list[str]] = {}   # line idx -> declared names
    decl_refs: dict[int, tuple[list[int], list[int]]] = {}  # exprs, name idxs
    name_line: dict[int, int] = {}  # name intern idx -> line idx
    ie_line: dict[int, int] = {}
    il_line: dict[int, int] = {}
    declmap: dict[str, int] = {}    # declared name -> line idx

    def walk_expr(o, es, ns, ls):
        # collect referenced expr idxs, name idxs, level idxs from a record body
        if isinstance(o, dict):
            for k, v in o.items():
                if k in ("fn", "arg", "body", "type", "value", "rhs",
                          "struct"):
                    if isinstance(v, int):
                        es.append(v)
                elif k in ("name", "typeName", "ctor", "induct"):
                    if isinstance(v, int):
                        ns.append(v)
                elif k == "sort":
                    if isinstance(v, int):
                        ls.append(v)
                elif k == "us":
                    for u in v:
                        if isinstance(u, int):
                            ls.append(u)
                elif k in ("levelParams", "all"):
                    for u in v:
                        if isinstance(u, int):
                            ns.append(u)
                elif k == "hints":
                    pass
                else:
                    walk_expr(v, es, ns, ls)
        elif isinstance(o, list):
            for v in o:
                walk_expr(v, es, ns, ls)

    opline = None
    with open(stream) as f:
        for line in f:
            r = json.loads(line)
            li = len(lines)
            lines.append(line.rstrip("\n"))
            recs.append(r)
            if "meta" in r:
                continue
            if "in" in r:
                i = r["in"]
                if "str" in r:
                    p = names[r["str"]["pre"]]
                    names[i] = (p + "." if p else "") + r["str"]["str"]
                    name_parent[i] = r["str"]["pre"]
                else:
                    p = names[r["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(r["num"]["i"])
                    name_parent[i] = r["num"]["pre"]
                name_idx[names[i]] = i
                name_line[i] = li
                max_name = max(max_name, i)
                continue
            if "il" in r:
                i = r["il"]
                il_line[i] = li
                max_il = max(max_il, i)
                kids = []
                for k in ("succ",):
                    if k in r and isinstance(r[k], int):
                        kids.append(r[k])
                for k in ("max", "imax"):
                    if k in r and isinstance(r[k], list):
                        kids.extend(v for v in r[k] if isinstance(v, int))
                l_children[i] = kids
                if r.get("succ") == 0 and succ_zero_il is None:
                    succ_zero_il = i
                if "param" in r and isinstance(r["param"], int):
                    l_names[i] = [r["param"]]
                continue
            if "ie" in r:
                i = r["ie"]
                ie_line[i] = li
                max_ie = max(max_ie, i)
                es: list[int] = []
                ns: list[int] = []
                ls: list[int] = []
                body = {k: v for k, v in r.items() if k != "ie"}
                walk_expr(body, es, ns, ls)
                e_children[i] = es
                e_names[i] = ns
                e_levels[i] = ls
                continue
            # declaration record
            new: list[str] = []
            es: list[int] = []
            ns: list[int] = []
            ls: list[int] = []
            if any(k in r for k in ("def", "thm", "opaque", "axiom")):
                kind = next(k for k in ("def", "thm", "opaque", "axiom") if k in r)
                b = r[kind]
                new.append(names[b["name"]])
                walk_expr(b, es, ns, ls)
            elif "inductive" in r:
                b = r["inductive"]
                for t in b.get("types", []):
                    new.append(names[t["name"]])
                for c in b.get("ctors", []):
                    new.append(names[c["name"]])
                for rec in b.get("recs", []):
                    new.append(names[rec["name"]])
                walk_expr(b, es, ns, ls)
            elif "quot" in r:
                new.append(names[r["quot"]["name"]])
                walk_expr(r["quot"], es, ns, ls)
            else:
                continue
            decl_lines.append(li)
            decl_names[li] = new
            decl_refs[li] = (es, ns)
            for n in new:
                declmap.setdefault(n, li)
            if opname in new and opline is None:
                opline = li
                break

    if opline is None:
        sys.exit(f"{opname} not found in {stream}")

    # ---- name refs of a declaration: expand its exprs (memoized)
    expr_names_memo: dict[int, set[int]] = {}

    def expr_names(i: int) -> set[int]:
        if i in expr_names_memo:
            return expr_names_memo[i]
        seen: set[int] = set()
        out_ns: set[int] = set()
        stack = [i]
        while stack:
            j = stack.pop()
            if j in seen:
                continue
            seen.add(j)
            out_ns.update(e_names.get(j, []))
            stack.extend(e_children.get(j, []))
        expr_names_memo[i] = out_ns
        return out_ns

    def decl_ref_names(li: int) -> set[str]:
        es, ns = decl_refs[li]
        out: set[str] = set()
        for n in ns:
            out.add(names[n])
        for e in es:
            for n in expr_names(e):
                out.add(names[n])
        return out

    # ---- closure
    roots = set(pin_roots) | {opname, "Nat", "Eq", "Eq.refl"}
    included: set[int] = set()
    work = [r for r in roots if r in declmap]
    seen_names: set[str] = set(work)
    pinops_done: set[str] = set()
    while work:
        n = work.pop()
        li = declmap[n]
        # a pin-certified operation's install additionally requires its
        # own pin/certificate ground constants
        for dn in decl_names[li]:
            if dn in all_pin_roots and dn not in pinops_done:
                pinops_done.add(dn)
                for extra in all_pin_roots[dn]:
                    if extra in declmap and extra not in seen_names:
                        seen_names.add(extra)
                        work.append(extra)
        if li in included:
            continue
        included.add(li)
        dep = decl_ref_names(li)
        for d in dep:
            if d in declmap and d not in seen_names:
                seen_names.add(d)
                work.append(d)

    # ---- needed intern records
    need_e: set[int] = set()
    need_n: set[int] = set()
    need_l: set[int] = set()
    for li in sorted(included):
        es, ns = decl_refs[li]
        stack = list(es)
        seen_e: set[int] = set()
        while stack:
            j = stack.pop()
            if j in seen_e or j in need_e:
                continue
            seen_e.add(j)
            need_e.add(j)
            stack.extend(e_children.get(j, []))
            need_n.update(e_names.get(j, []))
            need_l.update(e_levels.get(j, []))
        need_n.update(ns)
        # declared names themselves
        r = recs[li]

    # level closure
    lstack = list(need_l)
    while lstack:
        j = lstack.pop()
        for k in l_children.get(j, []):
            if k not in need_l:
                need_l.add(k)
                lstack.append(k)
    for j in need_l:
        need_n.update(l_names.get(j, []))
    # name refs from decl records (declared names + level params)
    for li in sorted(included):
        r = recs[li]
        ns2: list[int] = []
        walk_names = []
        def collect_name_ints(o):
            if isinstance(o, dict):
                for k, v in o.items():
                    if k in ("name", "structName", "ctor", "all") or k == "levelParams":
                        if isinstance(v, int):
                            ns2.append(v)
                        elif isinstance(v, list):
                            ns2.extend(x for x in v if isinstance(x, int))
                    else:
                        collect_name_ints(v)
            elif isinstance(o, list):
                for v in o:
                    collect_name_ints(v)
        collect_name_ints(r)
        need_n.update(ns2)
    # name parent closure
    nstack = list(need_n)
    while nstack:
        j = nstack.pop()
        p = name_parent.get(j)
        if p is not None and p not in need_n and p != 0:
            need_n.add(p)
            nstack.append(p)

    # ---- emit
    out_lines: list[str] = []
    keep_lines: set[int] = set(included)
    keep_lines.update(name_line[i] for i in need_n if i in name_line)
    keep_lines.update(ie_line[i] for i in need_e if i in ie_line)
    keep_lines.update(il_line[i] for i in need_l if i in il_line)
    # keep the meta line
    for li, r in enumerate(recs):
        if "meta" in r:
            keep_lines.add(li)
    for li in sorted(keep_lines):
        out_lines.append(lines[li])

    def fresh_ie():
        nonlocal max_ie
        max_ie += 1
        return max_ie

    def emit(obj):
        out_lines.append(json.dumps(obj, separators=(",", ":")))

    if perturb:
        # replace the op's value with fun x y => x (resp. fun x => x)
        r = json.loads(lines[opline])
        e_nat = fresh_ie()
        pre = [json.dumps({"const": {"name": name_idx["Nat"], "us": []},
                           "ie": e_nat}, separators=(",", ":"))]
        e_b1 = fresh_ie()
        pre.append(json.dumps({"ie": e_b1, "bvar": 1}, separators=(",", ":")))
        e_lam1 = fresh_ie()
        pre.append(json.dumps({"ie": e_lam1, "lam": {"binderInfo": "default",
            "body": e_b1, "name": 0, "type": e_nat}}, separators=(",", ":")))
        e_lam2 = fresh_ie()
        pre.append(json.dumps({"ie": e_lam2, "lam": {"binderInfo": "default",
            "body": e_lam1, "name": 0, "type": e_nat}}, separators=(",", ":")))
        r["def"]["value"] = e_lam2
        # replace the op decl line in out_lines
        opl = lines[opline]
        idx = out_lines.index(opl)
        out_lines[idx:idx + 1] = pre + [json.dumps(r, separators=(",", ":"))]
        with open(out, "w") as f:
            f.write("\n".join(out_lines) + "\n")
        print(f"wrote {out} (perturbed {opname}, {len(out_lines)} lines)")
        return

    if succ_zero_il is None:
        max_il += 1
        succ_zero_il = max_il
        emit({"il": succ_zero_il, "succ": 0})
    e_nat = fresh_ie(); emit({"const": {"name": name_idx["Nat"], "us": []}, "ie": e_nat})
    e_eq = fresh_ie(); emit({"const": {"name": name_idx["Eq"], "us": [succ_zero_il]}, "ie": e_eq})
    e_refl = fresh_ie(); emit({"const": {"name": name_idx["Eq.refl"], "us": [succ_zero_il]}, "ie": e_refl})
    e_args = []
    for a in args:
        e = fresh_ie(); emit({"ie": e, "natVal": str(a)})
        e_args.append(e)
    e_r = fresh_ie(); emit({"ie": e_r, "natVal": str(result)})
    e_op = fresh_ie(); emit({"const": {"name": name_idx[opname], "us": []}, "ie": e_op})
    lhs = e_op
    for e in e_args:
        e2 = fresh_ie(); emit({"app": {"fn": lhs, "arg": e}, "ie": e2})
        lhs = e2
    t1 = fresh_ie(); emit({"app": {"fn": e_eq, "arg": e_nat}, "ie": t1})
    t2 = fresh_ie(); emit({"app": {"fn": t1, "arg": lhs}, "ie": t2})
    t3 = fresh_ie(); emit({"app": {"fn": t2, "arg": e_r}, "ie": t3})
    v1 = fresh_ie(); emit({"app": {"fn": e_refl, "arg": e_nat}, "ie": v1})
    v2 = fresh_ie(); emit({"app": {"fn": v1, "arg": e_r}, "ie": v2})
    max_name += 1
    nfact = max_name
    fact_str = opname.split(".")[-1] + "Fact"
    emit({"in": nfact, "str": {"pre": 0, "str": fact_str}})
    emit({"thm": {"all": [nfact], "levelParams": [], "name": nfact,
                  "type": t3, "value": v2}})
    with open(out, "w") as f:
        f.write("\n".join(out_lines) + "\n")
    print(f"wrote {out} ({opname} {args} = {result}, {len(out_lines)} lines)")


if __name__ == "__main__":
    main()
