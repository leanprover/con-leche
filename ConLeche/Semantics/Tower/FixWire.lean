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

theorem domsBelow_mono : ∀ {ds : List (Nat × Nat × AnnotTerm)} {k k' : Nat}, k ≤ k' →
    DomsBelow k ds → DomsBelow k' ds
  | [], _, _, _, _ => trivial
  | _ :: ds, k, k', hk, h => ⟨Term.bvarsBelow.mono hk h.1, domsBelow_mono (ds := ds) (by omega) h.2⟩

/-! ## The squash regime's body (task #202 A2) -/

/-- A moved index expression: `ihIdxAtM` lifts by `nF - i + l` and
then by `o`. -/
theorem ihIdxAtM_below {nF o i l m K : Nat} {E : AnnotTerm} (hE : Term.bvarsBelow K E.erase) :
    Term.bvarsBelow (K + (nF - i + l) + o) (ihIdxAtM nF o i l m E).erase := by
  unfold ihIdxAtM
  rw [AnnotTerm.erase_liftN, AnnotTerm.erase_liftN]
  exact VExprAux.bvarsBelow_liftN o _ _ _ (VExprAux.bvarsBelow_liftN (nF - i + l) _ _ _ hE)

/-- A telescope moved to the ih frame is bounded there. -/
theorem ihTeleAtGo_below {nF o i l K : Nat} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow (K + k) tl →
      DomsBelow (K + (nF - i + l) + o + k) (ihTeleAtGo nF o i l k tl)
  | [], _, _ => trivial
  | d :: tl, k, h => by
    refine ⟨?_, ?_⟩
    · have := ihIdxAtM_below (nF := nF) (o := o) (i := i) (l := l) (m := k) h.1
      rwa [show K + k + (nF - i + l) + o = K + (nF - i + l) + o + k from by omega] at this
    · have := ihTeleAtGo_below (nF := nF) (o := o) (i := i) (l := l) (K := K) (tl := tl) (k := k + 1)
        (by rw [show K + (k + 1) = K + k + 1 from by omega]; exact h.2)
      rwa [show K + (nF - i + l) + o + (k + 1) = K + (nF - i + l) + o + k + 1 from by omega] at this

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
