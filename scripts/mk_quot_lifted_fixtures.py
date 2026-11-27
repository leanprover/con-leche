#!/usr/bin/env python3
"""Variants of `tests/e2e/quot_lifted.ndjson` (the lifted `Quot` of lean4#15023), task #630.

  quot_lifted_rfl_bad         — `squash_sound : s = Squash.mk True.intro` proved by
                                `squash_self`'s value `fun s => rfl`: a quotient of a proposition
                                is a type, so proof irrelevance does not apply (official: reject).
  quot_lifted_mixed_sound_bad — `Quot.sound`'s equation at `Eq.{u}` (the released form) beside the
                                lifted `Quot`: ill-typed, official rejects.
  quot_other_sort_bad         — `Quot` (and `Squash`) at `Sort (u+1)`: a quotient record that is
                                neither form of the pin, declined as before.
  quot_lifted_no_sound        — without the `Quot.sound` record and `squash_sound`, its one use:
                                the quotient package as an export that never uses the axiom has
                                it; the built-in prelude supplies no quotient record (official: 0).
  quot_lifted_no_sound_rfl_bad — quot_lifted_no_sound with `squash_sound` proved by `rfl`
                                (`squash_self`'s value): no proof irrelevance at a lifted
                                quotient, whatever `Quot.sound` (official: reject).

Each edit is located by the record it changes and checked to apply once.

Usage: scripts/mk_quot_lifted_fixtures.py
"""
import json
import sys

SRC = "tests/e2e/quot_lifted.ndjson"


def load():
    with open(SRC) as f:
        return [json.loads(l) for l in f if l.strip()]


def emit(path, rows):
    with open(path, "w") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(f"{path}: {len(rows)} lines", file=sys.stderr)


def name_id(rows, s, pre=0):
    hits = [r["in"] for r in rows if "in" in r and r.get("str") == {"pre": pre, "str": s}]
    assert len(hits) == 1, (s, hits)
    return hits[0]


def level_ids(rows):
    param = {r["param"]: r["il"] for r in rows if "il" in r and "param" in r}
    return param


def thm(rows, nid):
    hits = [r for r in rows if "thm" in r and r["thm"]["name"] == nid]
    assert len(hits) == 1, nid
    return hits[0]


rows = load()
quot = name_id(rows, "Quot")
u_name = [r["levelParams"][0] for r in (x["quot"] for x in rows if "quot" in x)
          if r["kind"] == "type"][0]
u = level_ids(rows)[u_name]
lifted = [r for r in rows if "il" in r and r.get("max") is not None
          and rows[[i for i, x in enumerate(rows) if x.get("il") == r["max"][1]][0]].get("param") == u_name]
assert len(lifted) == 1, lifted
lifted = lifted[0]["il"]

# quot_lifted_rfl_bad
v = json.loads(json.dumps(rows))
self_v = thm(v, name_id(v, "squash_self"))["thm"]["value"]
thm(v, name_id(v, "squash_sound"))["thm"]["value"] = self_v
emit("tests/e2e/quot_lifted_rfl_bad.ndjson", v)

# quot_lifted_mixed_sound_bad
v = json.loads(json.dumps(rows))
eq = name_id(v, "Eq")
hits = [r for r in v if "const" in r and r["const"] == {"name": eq, "us": [lifted]}]
assert len(hits) == 1, hits
hits[0]["const"]["us"] = [u]
emit("tests/e2e/quot_lifted_mixed_sound_bad.ndjson", v)

# quot_other_sort_bad
v = json.loads(json.dumps(rows))
hits = [r for r in v if r.get("il") == lifted]
assert len(hits) == 1
hits[0].pop("max")
hits[0]["succ"] = u
emit("tests/e2e/quot_other_sort_bad.ndjson", v)

# quot_lifted_no_sound
v = json.loads(json.dumps(rows))
sound = name_id(v, "sound", quot)
ax = [i for i, r in enumerate(v) if "axiom" in r and r["axiom"]["name"] == sound]
assert len(ax) == 1
sq = [i for i, r in enumerate(v) if "thm" in r and r["thm"]["name"] == name_id(v, "squash_sound")]
assert len(sq) == 1
emit("tests/e2e/quot_lifted_no_sound.ndjson", [r for i, r in enumerate(v) if i not in ax + sq])

# quot_lifted_no_sound_rfl_bad
v = json.loads(json.dumps(rows))
thm(v, name_id(v, "squash_sound"))["thm"]["value"] = thm(v, name_id(v, "squash_self"))["thm"]["value"]
emit("tests/e2e/quot_lifted_no_sound_rfl_bad.ndjson",
     [r for i, r in enumerate(v) if i not in ax])
