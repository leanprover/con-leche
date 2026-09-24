module

public import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Semantics.Tower.SumWire

@[expose] public section

/-!
# The recursive recursor leaf's closedness (task #188)

`nativeRecAVI` — the selected fixed point of the one-step
unfolding — is a closed term: the recursor type is a Π-tower over
closed binder data, the body's case split with inductive hypotheses
sits one below the K-frame, and an inductive-hypothesis argument
mentions the unfolded function, the block's variables, the field's
index expressions (moved to the payload's projections) and the
payload's projection only.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify

/-! ## The inductive-hypothesis arguments -/

/-! ## The squash regime's body (task #202 A2) -/

/-! ## The leaf -/

/-- A Π-tower over bounded binder data with a bounded conclusion is
bounded. -/
theorem mkPisAV_below_of {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow k ds →
      Term.bvarsBelow (k + ds.length) C.erase → Term.bvarsBelow k (mkPisAV ds C).erase
  | [], _, _, hC => hC
  | d :: ds, k, hd, hC => by
    refine ⟨hd.1, mkPisAV_below_of hd.2 ?_⟩
    rwa [show k + 1 + ds.length = k + (d :: ds).length from by simp; omega]

end ConLeche.Semantics
