#!/usr/bin/env python3
"""Build e2e fixtures for the compiler-trust axiom family (task #95)
from a lean4export 3.x ndjson stream, by dependency-closure slicing
(same approach as mk_natop_fixture.py): keep the declarations
transitively needed to install `Lean.trustCompiler`, `Lean.reduceNat`,
`Lean.ofReduceNat`, `Lean.reduceBool` and `Lean.ofReduceBool`
plus

* accept fixture: a theorem *using* `Lean.ofReduceNat`'s type
  vacuously (`useOfReduceNat := Lean.ofReduceNat`) — the installed
  axiom must be consumable;
* reject fixture (--bad): additionally a theorem
  `badNative : Lean.reduceBool Bool.true = Bool.true := Eq.refl _`,
  the kernel-visible shape of a genuinely native-evaluated
  `ofReduceBool` use.  `Lean.reduceBool` is opaque, so the `rfl` proof
  is stuck and the declaration must reject (exit 1) — that hypothesis
  only ever comes from untrusted native evaluation.

Usage:
  mk_trust_fixture.py <stream> <out.ndjson> [--bad]
"""
import json
import sys


def main() -> None:
    stream, out = sys.argv[1:3]
    bad = len(sys.argv) > 3 and sys.argv[3] == "--bad"

    opname = "Lean.ofReduceBool"

    names = {0: ""}
    name_idx: dict[str, int] = {"": 0}
    name_parent: dict[int, int] = {}
    max_name = max_ie = max_il = 0
    succ_zero_il = None

    lines: list[str] = []
    recs: list[dict] = []
    e_children: dict[int, list[int]] = {}
    e_names: dict[int, list[int]] = {}
    e_levels: dict[int, list[int]] = {}
    l_children: dict[int, list[int]] = {}
    l_names: dict[int, list[int]] = {}
    decl_lines: list[int] = []
    decl_names: dict[int, list[str]] = {}
    decl_refs: dict[int, tuple[list[int], list[int]]] = {}
    name_line: dict[int, int] = {}
    ie_line: dict[int, int] = {}
    il_line: dict[int, int] = {}
    declmap: dict[str, int] = {}

    def walk_expr(o, es, ns, ls):
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

    roots = {"Lean.trustCompiler", "Lean.reduceNat", "Lean.ofReduceNat",
             "Lean.reduceBool", "Lean.ofReduceBool",
             "Nat", "Bool", "True", "Eq", "Eq.refl"}
    included: set[int] = set()
    work = [r for r in roots if r in declmap]
    seen_names: set[str] = set(work)
    while work:
        n = work.pop()
        li = declmap[n]
        if li in included:
            continue
        included.add(li)
        dep = decl_ref_names(li)
        for d in dep:
            if d in declmap and d not in seen_names:
                seen_names.add(d)
                work.append(d)

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

    lstack = list(need_l)
    while lstack:
        j = lstack.pop()
        for k in l_children.get(j, []):
            if k not in need_l:
                need_l.add(k)
                lstack.append(k)
    for j in need_l:
        need_n.update(l_names.get(j, []))
    for li in sorted(included):
        r = recs[li]
        ns2: list[int] = []

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
    nstack = list(need_n)
    while nstack:
        j = nstack.pop()
        p = name_parent.get(j)
        if p is not None and p not in need_n and p != 0:
            need_n.add(p)
            nstack.append(p)

    out_lines: list[str] = []
    keep_lines: set[int] = set(included)
    keep_lines.update(name_line[i] for i in need_n if i in name_line)
    keep_lines.update(ie_line[i] for i in need_e if i in ie_line)
    keep_lines.update(il_line[i] for i in need_l if i in il_line)
    for li, r in enumerate(recs):
        if "meta" in r:
            keep_lines.add(li)
    for li in sorted(keep_lines):
        out_lines.append(lines[li])

    def fresh_ie():
        nonlocal max_ie
        max_ie += 1
        return max_ie

    def fresh_name(s: str) -> int:
        nonlocal max_name
        max_name += 1
        out_lines.append(json.dumps(
            {"in": max_name, "str": {"pre": 0, "str": s}},
            separators=(",", ":")))
        return max_name

    def emit(obj):
        out_lines.append(json.dumps(obj, separators=(",", ":")))

    # accept: a theorem using ofReduceNat's type vacuously
    ofrn_line = recs[declmap["Lean.ofReduceNat"]]
    ofrn_ty = ofrn_line["axiom"]["type"]
    use_n = fresh_name("useOfReduceNat")
    v = fresh_ie()
    emit({"ie": v, "const": {"name": name_idx["Lean.ofReduceNat"], "us": []}})
    emit({"thm": {"all": [use_n], "levelParams": [], "name": use_n,
                  "type": ofrn_ty, "value": v}})

    if bad:
        # badNative : Lean.reduceBool Bool.true = Bool.true := Eq.refl _
        assert succ_zero_il is not None
        eq_i = name_idx["Eq"]
        eqrefl_i = name_idx["Eq.refl"]
        bool_i = name_idx["Bool"]
        booltrue_i = name_idx["Bool.true"]
        rbool_i = name_idx["Lean.reduceBool"]
        boolC = fresh_ie()
        emit({"ie": boolC, "const": {"name": bool_i, "us": []}})
        btC = fresh_ie()
        emit({"ie": btC, "const": {"name": booltrue_i, "us": []}})
        rbC = fresh_ie()
        emit({"ie": rbC, "const": {"name": rbool_i, "us": []}})
        rbt = fresh_ie()
        emit({"ie": rbt, "app": {"fn": rbC, "arg": btC}})
        eqC = fresh_ie()
        emit({"ie": eqC, "const": {"name": eq_i, "us": [succ_zero_il]}})
        e1 = fresh_ie()
        emit({"ie": e1, "app": {"fn": eqC, "arg": boolC}})
        e2 = fresh_ie()
        emit({"ie": e2, "app": {"fn": e1, "arg": rbt}})
        ty = fresh_ie()
        emit({"ie": ty, "app": {"fn": e2, "arg": btC}})
        reflC = fresh_ie()
        emit({"ie": reflC, "const": {"name": eqrefl_i, "us": [succ_zero_il]}})
        r1 = fresh_ie()
        emit({"ie": r1, "app": {"fn": reflC, "arg": boolC}})
        pf = fresh_ie()
        emit({"ie": pf, "app": {"fn": r1, "arg": btC}})
        bad_n = fresh_name("badNative")
        emit({"thm": {"all": [bad_n], "levelParams": [], "name": bad_n,
                      "type": ty, "value": pf}})

    with open(out, "w") as f:
        f.write("\n".join(out_lines) + "\n")
    print(f"{out}: {len(out_lines)} lines "
          f"({len(included)} declarations sliced)")


if __name__ == "__main__":
    main()
