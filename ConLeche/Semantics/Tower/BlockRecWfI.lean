module

public import ConLeche.Semantics.Tower.BlockRecKitI
public import ConLeche.SetModel.WfRec
@[expose] public section

/-!
# Regime WF: the class kit is F5's `WfRecKit` (task #315, M5 model half)

DESIGN "DESIGN DOCUMENT 2, v2" §3.2.  At `¬allProp ∧ w ≠ 0` the
recursion is **well-founded recursion on the global subterm relation**
`x ⊏ y := x ∈ tc y` over the tagged union of the majors' ORDINARY
carriers — lane F5's `WfRecKit` (`ConLeche/SetModel/WfRec.lean`), which
asks nothing of the carriers: no fixed-point structure, no
`PredsFrom`, no simultaneous accessibility.

`WfRecKit.toC` is that kit as a `UnionRecKitC`, so the whole regime is
`BlockRecKitI`'s arm at `toC`: `wfData` below builds the family's data
and `wfCand_hCand` is `famCand_hCand`.  Nothing in the arm knows about
`tc`, which is why regime SQ (`BlockRecSqI.lean`) reuses it unchanged
at a different predecessor.

**What the Model tier owes** is unchanged by the repackaging:
everything that mentions the STORED forms — that a rule's spine fits
the recursor's type, that the conclusion reads to the kit's motive,
and that the kit's step reads to the residue at the ih values.  The
kit's own two obligations (`hB`, `hst`) are F5's shape and the Model
tier's content: `hst` is G1, the residue's certified typing at the
constructors' environment (`ResidueOk`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

section Wf

variable {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl : Nat → AnnotTerm} {ρ : Nat → V}

/-- **The WF regime's data**: `RecFamData` at F5's `WfRecKit`, whose
predecessors are the ∈-smaller elements of the tagged union (`tcPred`)
and whose accessibility is regularity (`tcAcc_all`).  The two readings
are stated at the `WfRecKit`'s own `B`, which `toC` keeps. -/
noncomputable def wfData (Is Cr : List V → Nat → V) (tupOf : Nat → List V → V)
    (kitW : ∀ xs : List V, WfRecKit ℓ K (Is xs) (Cr xs))
    (hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      tupOf c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupOf c (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (kitW (prefOf (rP c) ys)).B (tagged c (tupOf c (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c)) :
    RecFamData V ℓ K rP rds concl ρ where
  Is := Is
  Cr := Cr
  tupOf := tupOf
  kit := fun xs => (kitW xs).toC
  hsplit := hsplit
  hconcl := hconcl

end Wf

end ConLeche.Semantics
