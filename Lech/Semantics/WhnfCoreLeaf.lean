import Lech.Verify.Knot

/-!
# `SetBase/WhnfCoreLeaf` — the six shapes `whnfCore` returns unchanged

Six `rfl` lemmas re-based out of `SetR/Bridge/WhnfCore.lean` at THE
SEPARATION's S2 (task #161).  S1 deferred them here by name: they are
statements about a *kernel function* with no model in sight, and both
lanes' `whnfCore` walks simp with them.

They came down with the two-edit sever's second edit — the graded
lane's `Step2/WhnfP` was reading them through the 2U module
`Step2/Whnf`, whose import the sever removes.

Statements verbatim.  (The design census would rather see them in
`Lech/Verify/*`, which is where proofs about kernel functions belong;
that is a rename, not a move, so it was not that batch's business —
the base directory is the boundary that matters.)

**KEPT at the SetR removal's Stage C** (2026-09-05), which deleted the
relation family and the whole derivation bridge above it.  This module
then carried the `Lech.SetR` namespace and a `whnfCoreR_*` name
prefix, and it was neither: six `rfl` facts about the *kernel's*
`whnfCore`, with a live consumer in the graded lane
(`SetP/Step2/WhnfP.lean`).  It is the clearest case in the tree of the
rule the batch ran on — *classify a module by what its statements
mention, not by the namespace it sits in.*  The cleanup pass of
2026-09-06 gave them their honest names: `whnfCore_leaf_*` (the
section title below), in `Lech.Semantics`.
-/

namespace Lech.Semantics

variable {mode : CheckMode} {env : Env} {fuel d : Nat}

/-! ## The leaf clauses

Six shapes `whnfCoreBody` returns unchanged; each unfolding is `rfl`
(the clause is `pure e`, and `pure` at `Except` is `.ok`).  On this lane
each is `Red.refl` — R1, the rule that also covers every stuck fallback,
every `iotaRec = none`, and every uncertified redex. -/

@[simp] theorem whnfCore_leaf_sort (u : Level) :
    whnfCore mode env (fuel + 1) d (.sort u) = .ok (.sort u) := rfl

@[simp] theorem whnfCore_leaf_fvar (idx : Nat) (n : Name) (ty : Expr) :
    whnfCore mode env (fuel + 1) d (.fvar idx n ty) = .ok (.fvar idx n ty) :=
  rfl

@[simp] theorem whnfCore_leaf_forallE (n : Name) (ty body : Expr)
    (bi : BinderMeta) :
    whnfCore mode env (fuel + 1) d (.forallE n ty body bi) =
      .ok (.forallE n ty body bi) := rfl

@[simp] theorem whnfCore_leaf_lam (n : Name) (ty body : Expr) (mb : BinderMeta) :
    whnfCore mode env (fuel + 1) d (.lam n ty body mb) =
      .ok (.lam n ty body mb) := rfl

@[simp] theorem whnfCore_leaf_const (n : Name) (us : List Level) :
    whnfCore mode env (fuel + 1) d (.const n us) = .ok (.const n us) := rfl

@[simp] theorem whnfCore_leaf_lit (l : Literal) :
    whnfCore mode env (fuel + 1) d (.lit l) = .ok (.lit l) := rfl

end Lech.Semantics
