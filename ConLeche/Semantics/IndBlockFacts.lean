module

import ConLeche.Semantics.DeclEta


import ConLeche.Verify.Denote.Rename

public import ConLeche.Verify.Extend.Recs

import ConLeche.Semantics.DeclRun
import ConLeche.Kernel.Checker
import ConLeche.Verify.Abstract
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst

@[expose] public section
/-!
# The inductive block's recursor-swap side condition

`SwapNResS`, the reserved-name side condition of the block's recursor
swap (consumed by `Model/Inductives/BlockStageRec.lean`).
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The reserved-name side condition of the group swap: a genuinely
swapped entry never sits at a pinned basis name. -/
def SwapNResS (env₀ env₃ : Env) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env₀.find? n = some (.recInfo cv mI rP []) →
    env₃.find? n = some (.recInfo cv mI rP rules) →
    rules = [] ∨ reservedBasisNames.contains n = false

end ConLeche.Semantics
