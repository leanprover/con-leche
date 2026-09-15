module

public import ConLeche.Semantics.Tower.FixLeafI
public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# The native leaf is the one-member block (task #315)

The ONE fixpoint route's type-former leaf is `fixFamI = lfpFamSet w I
fixFunVI` (`FixLeafI.lean`).  The uniform route's datum is a block of
`k` families as one least pre-fixed TUPLE (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`); at `k = 1` the two agree
with no hypothesis (`lfpTuple_one`), so every native block already IS
a one-member block of the uniform datum — the statement the route
keeps while it generalises the installer to `k` members.
-/

namespace ConLeche.Semantics
open ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- **The native leaf is the `k = 1` tuple lfp.** -/
theorem fixFamI_eq_lfpTuple (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    fixFamI u w ρp Ids nIdx rss tlss Eiss Fss Ess
      = lfpTuple w 1 (fun _ => idxSet u ρp Ids)
          (oneTuple (fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess)) 0 := by
  unfold fixFamI
  rw [lfpTuple_one]

end ConLeche.Semantics
