#!/usr/bin/env python3
"""Reorder a lean4export ndjson stream: HOIST the dependency closure of
the named declarations to the front of the declaration records.

    scripts/mk_reorder_fixture.py <in.ndjson> <out.ndjson> NAME...

The output keeps every name/level/expression table line (`in`/`il`/
`ie`) in its original position relative to the other table lines and
emits them all first — table entries reference only earlier table
entries, never declarations — then, for each NAME in turn, the
declaration records of its transitive type/value closure not emitted
yet (in their original relative order, so each closure stays
dependency-ordered), then every other declaration record in its
original order.  The result is a valid stream: every declaration still
follows everything it references — and the NAMEs come out in the order
given (each after its own ground).

What it is for (task #191, the built-in prelude): the pin-certified
`Nat` operations were sensitive to the stream's installation order —
`Nat.shiftLeft`'s certificate statements are spelled over `Nat.ble`,
`Nat.sub`, `Eq` and the `Bool` values, none of which its own closure
reaches, so a stream that declares the operation (with its ground
`Nat.ble`/`Nat.sub`) BEFORE the `Eq` block declined at the install.
`tests/e2e/natop_before_eq.ndjson` is exactly that: the raw export of
`tests/e2e/src/natop_order.lean` with the closures of
`Nat.ble Nat.sub Nat.shiftLeft` (in that order: the operation after
its structural ground) hoisted ahead of `Eq`.
`tests/e2e/natop_before_ble.ndjson` hoists `Nat.shiftLeft` FIRST — the
operation ahead of `Nat.ble`/`Nat.sub`, the order-sensitivity the
prelude cannot remove (those are stream-certified operations; see
DESIGN.md, task #191) — and stays a decline.
"""
import json
import sys


def main() -> int:
    if len(sys.argv) < 4:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    src, out, roots = sys.argv[1], sys.argv[2], sys.argv[3:]

    names = {0: ""}
    e_children: dict[int, list[int]] = {}
    e_names: dict[int, list[int]] = {}
    table_lines: list[str] = []
    meta_lines: list[str] = []
    decls: list[tuple[str, list[str], list[int], list[int]]] = []
    declmap: dict[str, int] = {}

    def walk(o, es, ns):
        if isinstance(o, dict):
            for k, v in o.items():
                if k in ("fn", "arg", "body", "type", "value", "rhs", "struct"):
                    if isinstance(v, int):
                        es.append(v)
                elif k in ("name", "typeName", "ctor", "induct"):
                    if isinstance(v, int):
                        ns.append(v)
                elif k in ("sort", "us", "levelParams", "all", "hints"):
                    pass
                else:
                    walk(v, es, ns)
        elif isinstance(o, list):
            for v in o:
                walk(v, es, ns)

    with open(src) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.strip():
                continue
            r = json.loads(line)
            if "meta" in r:
                meta_lines.append(line)
                continue
            if "in" in r:
                i = r["in"]
                if "str" in r:
                    p = names[r["str"]["pre"]]
                    names[i] = (p + "." if p else "") + r["str"]["str"]
                else:
                    p = names[r["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(r["num"]["i"])
                table_lines.append(line)
                continue
            if "il" in r:
                table_lines.append(line)
                continue
            if "ie" in r:
                es: list[int] = []
                ns: list[int] = []
                walk({k: v for k, v in r.items() if k != "ie"}, es, ns)
                e_children[r["ie"]] = es
                e_names[r["ie"]] = ns
                table_lines.append(line)
                continue
            new: list[str] = []
            es = []
            ns = []
            if any(k in r for k in ("def", "thm", "opaque", "axiom")):
                kind = next(k for k in ("def", "thm", "opaque", "axiom") if k in r)
                new.append(names[r[kind]["name"]])
                walk(r[kind], es, ns)
            elif "inductive" in r:
                b = r["inductive"]
                for key in ("types", "ctors", "recs"):
                    for t in b.get(key, []):
                        new.append(names[t["name"]])
                walk(b, es, ns)
            elif "quot" in r:
                new.append(names[r["quot"]["name"]])
                walk(r["quot"], es, ns)
            else:
                print(f"unrecognized record: {line[:80]}", file=sys.stderr)
                return 3
            di = len(decls)
            decls.append((line, new, ns, es))
            for n in new:
                declmap.setdefault(n, di)

    memo: dict[int, set[int]] = {}

    def expr_names(i: int) -> set[int]:
        if i in memo:
            return memo[i]
        seen: set[int] = set()
        outn: set[int] = set()
        stack = [i]
        while stack:
            j = stack.pop()
            if j in seen:
                continue
            seen.add(j)
            outn.update(e_names.get(j, []))
            stack.extend(e_children.get(j, []))
        memo[i] = outn
        return outn

    def refs(di: int) -> set[str]:
        _, _, ns, es = decls[di]
        r = {names[n] for n in ns}
        for e in es:
            r |= {names[n] for n in expr_names(e)}
        return r

    # the `quot` package is one unit for the checker (four records folded
    # into one basis block): hoist all four together with `Quot`
    emitted: set[int] = set()
    hoisted: list[int] = []
    for root in roots:
        if root not in declmap:
            print(f"{root} is not declared in {src}", file=sys.stderr)
            return 3
        closure: set[int] = set()
        work = [declmap[root]]
        while work:
            di = work.pop()
            if di in closure or di in emitted:
                continue
            closure.add(di)
            for n in refs(di):
                if n in declmap and declmap[n] not in closure:
                    work.append(declmap[n])
                if n.startswith("Quot"):
                    for q in ("Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"):
                        if q in declmap and declmap[q] not in closure:
                            work.append(declmap[q])
        for di in sorted(closure):
            hoisted.append(di)
        emitted |= closure

    with open(out, "w") as f:
        for line in meta_lines:
            f.write(line + "\n")
        for line in table_lines:
            f.write(line + "\n")
        for di in hoisted:
            f.write(decls[di][0] + "\n")
        for di in range(len(decls)):
            if di not in emitted:
                f.write(decls[di][0] + "\n")
    print(f"{out}: hoisted {len(hoisted)} of {len(decls)} declaration records "
          f"({', '.join(roots)} and their closures, in that order)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
