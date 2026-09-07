#!/usr/bin/env python3
"""The two task-#213 tree-size-budget fixtures.

  tests/e2e/budget_model.ndjson.gz — tests/e2e/dag_tower.ndjson with its
      2^28-node definition renamed `DagTower._model`.  Before task #213
      the frontend budgeted every `_model`-named record and DECLINED
      this stream; the audit lifted that class (the in-process modeller
      pushes identical records unbudgeted, and the external
      preprocessor is being retired), so it now ACCEPTS like its
      unrenamed twin.

  tests/e2e/budget_block.ndjson — a one-field structure block whose
      field type carries a ~2^12-node DAG tower (defeq to the numeral
      it replaces: `(fun a b => a) T T`).  It accepts at the default
      budget and DECLINES, naming the block, under
      CON_LECHE_TREE_BUDGET=1000 — an inductive block is still walked
      as a tree (the basis-pin `canon` match, and the install's
      `renameConsts`/`openPisAtFvars`).

Usage: scripts/mk_budget_fixtures.py
"""
import gzip
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def mk_model():
    src = os.path.join(ROOT, "tests/e2e/dag_tower.ndjson.gz")
    out = os.path.join(ROOT, "tests/e2e/budget_model.ndjson.gz")
    lines = gzip.open(src, "rt").read().splitlines()
    res = []
    for l in lines:
        r = json.loads(l)
        if "in" in r and r.get("str", {}).get("str") == "dagTower":
            # `DagTower._model`: name index 78 becomes the `_model`
            # component over a fresh `DagTower` prefix (index 79 is free
            # — 78 is the last name in the stream)
            res.append(json.dumps({"in": 79, "str": {"pre": 0, "str": "DagTower"}}))
            res.append(json.dumps({"in": 78, "str": {"pre": 79, "str": "_model"}}))
        else:
            res.append(l)
    with gzip.open(out, "wt") as f:
        f.write("\n".join(res) + "\n")
    print(f"{out}: {len(res)} lines")


def mk_block(levels=12):
    """`inductive Big : Type where | mk : (h : @Eq Nat T T) → Big`, hand
    written over the built-in prelude's `Eq` and `Nat` (task #191: both
    are installed first and unconditionally, so the stream declares
    neither).  `T` is the doubling tower over `Nat.zero`."""
    out = os.path.join(ROOT, "tests/e2e/budget_block.ndjson")
    L = []
    L.append(json.dumps({"meta": {"exporter": {"name": "mk_budget_fixtures.py",
                                               "version": "1"}}}))
    # names
    N = {}
    def name(full, pre, last):
        i = len(N) + 1
        N[full] = i
        L.append(json.dumps({"in": i, "str": {"pre": pre, "str": last}}))
        return i
    nEq = name("Eq", 0, "Eq")
    nNat = name("Nat", 0, "Nat")
    nZero = name("Nat.zero", nNat, "zero")
    nBig = name("Big", 0, "Big")
    nMk = name("Big.mk", nBig, "mk")
    nRec = name("Big.rec", nBig, "rec")
    nU = name("u", 0, "u")
    nAnon = 0
    # levels
    L.append(json.dumps({"il": 1, "param": nU}))
    lU, lZero = 1, 0
    L.append(json.dumps({"il": 2, "succ": 0}))
    lOne = 2                              # Sort 1 = Type
    # expressions
    E = []
    def ex(obj):
        i = len(E) + 1
        E.append(i)
        L.append(json.dumps(dict(obj, ie=i)))
        return i
    eProp = ex({"sort": lZero})
    eType = ex({"sort": lOne})
    eSortU = ex({"sort": lU})
    eNat = ex({"const": {"name": nNat, "us": []}})
    eZero = ex({"const": {"name": nZero, "us": []}})
    eEq = ex({"const": {"name": nEq, "us": [lOne]}})   # @Eq.{1} : Type → …
    # K := fun (a : Nat) => fun (b : Nat) => a  (Nat → Nat → Nat)
    eB1 = ex({"bvar": 1})
    eK = ex({"lam": {"binderInfo": "default", "name": nAnon, "type": eNat,
                     "body": ex({"lam": {"binderInfo": "default", "name": nAnon,
                                         "type": eNat, "body": eB1}})}})
    # the tower: T_0 = Nat.zero, T_{k+1} = (K T_k) T_k  (defeq to T_k)
    t = eZero
    for _ in range(levels):
        t = ex({"app": {"fn": ex({"app": {"fn": eK, "arg": t}}), "arg": t}})
    eFieldTy = ex({"app": {"fn": ex({"app": {"fn": ex({"app": {"fn": eEq,
                                                               "arg": eNat}}),
                                             "arg": t}}), "arg": t}})
    eBig = ex({"const": {"name": nBig, "us": []}})
    # Big.mk : (h : eFieldTy) → Big
    eMkTy = ex({"forallE": {"binderInfo": "default", "name": nAnon,
                            "type": eFieldTy, "body": eBig}})
    # Big.rec.{u} : {motive : Big → Sort u} →
    #   ((h : eFieldTy) → motive (Big.mk h)) → (t : Big) → motive t
    eB0 = ex({"bvar": 0})
    eMotiveTy = ex({"forallE": {"binderInfo": "default", "name": nAnon,
                                "type": eBig, "body": eSortU}})
    eMkC = ex({"const": {"name": nMk, "us": []}})
    eMinor = ex({"forallE": {"binderInfo": "default", "name": nAnon,
                             "type": eFieldTy,
                             "body": ex({"app": {"fn": ex({"bvar": 1}),
                                                 "arg": ex({"app": {"fn": eMkC,
                                                                    "arg": eB0}})}})}})
    eRecTy = ex({"forallE": {"binderInfo": "implicit", "name": nAnon,
                             "type": eMotiveTy,
                             "body": ex({"forallE": {"binderInfo": "default",
                                                     "name": nAnon, "type": eMinor,
                             "body": ex({"forallE": {"binderInfo": "default",
                                                     "name": nAnon, "type": eBig,
                             "body": ex({"app": {"fn": ex({"bvar": 2}),
                                                 "arg": eB0}})}})}})}})
    # the rule: Big.rec motive minor (Big.mk h) ↦ minor h
    eRhs = ex({"lam": {"binderInfo": "implicit", "name": nAnon, "type": eMotiveTy,
               "body": ex({"lam": {"binderInfo": "default", "name": nAnon,
                                   "type": eMinor,
               "body": ex({"lam": {"binderInfo": "default", "name": nAnon,
                                   "type": eFieldTy,
                                   "body": ex({"app": {"fn": ex({"bvar": 1}),
                                                       "arg": eB0}})}})}})}})
    L.append(json.dumps({"inductive": {
        "types": [{"name": nBig, "levelParams": [], "type": eType, "numParams": 0,
                   "numIndices": 0, "numNested": 0, "ctors": [nMk],
                   "isRec": False, "isUnsafe": False, "isReflexive": False,
                   "all": [nBig]}],
        "ctors": [{"name": nMk, "levelParams": [], "type": eMkTy, "numParams": 0,
                   "numFields": 1, "cidx": 0, "induct": nBig, "isUnsafe": False}],
        "recs": [{"name": nRec, "levelParams": [nU], "type": eRecTy,
                  "numParams": 0, "numMotives": 1, "numMinors": 1,
                  "numIndices": 0, "k": False, "isUnsafe": False,
                  "all": [nBig], "rules": [{"ctor": nMk, "nfields": 1, "rhs": eRhs}]}],
        "isUnsafe": False, "all": [nBig]}}))
    open(out, "w").write("\n".join(L) + "\n")
    print(f"{out}: {len(L)} lines")


mk_model()
mk_block()
