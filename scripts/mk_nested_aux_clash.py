#!/usr/bin/env python3
"""scripts/mk_nested_aux_clash.py — the auxiliary-name clash fixture (task #279).

    scripts/mk_nested_aux_clash.py            # writes tests/e2e/nested_aux_clash.ndjson

`tests/e2e/nested_p03.ndjson` is the chain probe `P3.mk : Array (List
P3) → P3`; the nested elimination mints three copies for it,
`_nested.Array_1`, `_nested.List_2` and `_nested.List_3`, whose
constructors and recursors carry those prefixes.  This script takes that
stream and inserts, before the block, one ordinary definition NAMED
`_nested.List_2.cons` — the name the second copy's `cons` constructor is
about to get.

No exporter can produce such a stream from a source: the official kernel
mints `_nested.List_2` for the copy (the TYPE name is free — only the
constructor name is taken), and then `declare_inductive_types`' own
`check_name` throws "already declared" on the constructor, so the
declaration never enters an environment and never reaches an export.
The stream is therefore FORGED, as the arena forges its two nested tests
with `debug.skipKernelTC` — and official's verdict for it is REJECT.

What it pins here: `copiesFresh`, the nested route's check that every
name the elimination mints is free in the PRE-BLOCK environment.  Without
it the scratch environment's cons would SHADOW the definition, and
nothing else in the route looks at the generated names.  The reserved-
prefix guard (`check_no_nested_aux`) does not catch this: it rejects a
block whose declared types MENTION a `_nested` constant, not a
declaration NAMED one.
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "tests", "e2e", "nested_p03.ndjson")
OUT = os.path.join(ROOT, "tests", "e2e", "nested_aux_clash.ndjson")

recs = [json.loads(line) for line in open(SRC)]

names = {}
for d in recs:
    if "in" in d:
        if "str" in d:
            names[d["in"]] = (d["str"]["pre"], d["str"]["str"])


def full(i):
    if i == 0:
        return ""
    pre, s = names[i]
    f = full(pre)
    return (f + "." + s) if f else s


# the block the clash is aimed at, and the two expressions the inserted
# definition reuses: `List`'s own type and the constant `List.{u}`
block_idx = None
list_type = None
list_const = None
list_lps = None
for idx, d in enumerate(recs):
    if "inductive" in d:
        types = d["inductive"]["types"]
        head = full(types[0]["name"])
        if head == "List":
            list_type = types[0]["type"]
            list_lps = types[0]["levelParams"]
        elif head == "P3":
            block_idx = idx
    if list_const is None and "const" in d and full(d["const"]["name"]) == "List":
        list_const = d["ie"]

if block_idx is None or list_type is None or list_const is None:
    sys.exit("nested_p03.ndjson does not have the expected shape")

next_name = max(d["in"] for d in recs if "in" in d) + 1
n_nested = next_name
n_list2 = next_name + 1
n_cons = next_name + 2

inserted = [
    {"in": n_nested, "str": {"pre": 0, "str": "_nested"}},
    {"in": n_list2, "str": {"pre": n_nested, "str": "List_2"}},
    {"in": n_cons, "str": {"pre": n_list2, "str": "cons"}},
    {"def": {"all": [n_cons], "hints": "abbrev", "levelParams": list_lps,
             "name": n_cons, "safety": "safe",
             "type": list_type, "value": list_const}},
]

out = recs[:block_idx] + inserted + recs[block_idx:]
with open(OUT, "w") as f:
    for d in out:
        f.write(json.dumps(d, sort_keys=True) + "\n")
print("wrote %s (%d records, the clash at name %d)" % (OUT, len(out), n_cons))
