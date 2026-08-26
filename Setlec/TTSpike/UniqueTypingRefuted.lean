import Setlec.TT.Semantics.Consistency
import Setlec.TT.Deq

/-!
# REFUTATION: unique typing (up to `Deq`), closed-term witness

The infer-only app case must relate the `pi` type that `Typable`'s
inversion supplies for the function to the `pi` type that `InferOnly`
computes for it — i.e. it needs some form of **unique typing up to
`Deq`**.  That is refuted here, by a *closed* term in the *empty*
context:

> `uT := (Nat → Empty.{1}) → Nat` is derivably typed at **both**
> `Sort 1` and `Sort 0`, and `Deq [] (Sort 1) (Sort 0)` is unsound.

The mechanism: under the binder `x : Nat → Empty.{1}` the context is
*syntactically explosive* — `x 0 : Empty.{1}`, and `Empty.rec` at an
equation-valued motive proves any equation, in particular
`Sort 1 = Sort 0`; `conv` then types `Nat : Sort 0` there, and the
`pi` rule's `imax 1 0 = 0` puts the whole (perfectly harmless) type in
`Prop`.  Nothing exotic entered: every step is a rule of the layer.

Consequences for the design:

* "`InferOnly`'s answer is `Deq` to every actual type" is false (here
  infer-only would answer `Sort 1`; `Sort 0` is an actual type).
* any induction that reconciles two typings of one subterm must
  survive explosive extended contexts, where sorts (and everything
  else) collapse derivably while the *outer* context stays empty and
  satisfiable.
-/

namespace Setlec.TT
namespace Spike

open VExpr SetTheory

/-- `Nat → Empty.{1}` — an uninhabited `Sort 1` type. -/
def NE : VExpr := .pi natT (emptyT 1)

/-- The witness type: `(Nat → Empty.{1}) → Nat`. -/
def uT : VExpr := .pi NE natT

theorem NE_sort1 : HasType [] NE (.sort 1) :=
  .pi (u := 1) (v := 1) .const .const

/-- In context `[NE]` there is an inhabitant of `Empty.{1}`. -/
theorem empty_inhab :
    HasType [NE] (.app (.bvar 0) natZeroT) (emptyT 1) :=
  .app (A := natT) (B := emptyT 1) (.bvar (A := NE) rfl) .const

/-- …so `Empty.rec` proves the equation `Sort 1 = Sort 0` there. -/
theorem sorts_collapse :
    HasType [NE]
      (.app (.app (.const .emptyRec [1, 0])
          (.lam (emptyT 1) (.eqE (.sort 2) (.sort 1) (.sort 0))))
        (.app (.bvar 0) natZeroT))
      (.eqE (.sort 2) (.sort 1) (.sort 0)) := by
  have hM : HasType [NE] (.lam (emptyT 1) (.eqE (.sort 2) (.sort 1) (.sort 0)))
      (.pi (emptyT 1) (.sort 0)) :=
    .lam .eqType
  have h1 := HasType.app (Γ := [NE]) (.const (c := .emptyRec) (us := [1, 0])) hM
  have h2 := HasType.app h1 empty_inhab
  exact .conv h2
    (.beta (T := .sort 2) (A := emptyT 1) empty_inhab)

/-- `Nat : Sort 0` — under the explosive binder. -/
theorem nat_prop_in_ctx : HasType [NE] natT (.sort 0) :=
  .conv .const sorts_collapse

/-- **First typing**: `uT : Sort 1`, the structural one (the one
infer-only computes). -/
theorem uT_sort1 : HasType [] uT (.sort 1) :=
  .pi (u := 1) (v := 1) NE_sort1 .const

/-- **Second typing**: `uT : Sort 0`, via the collapse —
`imax 1 0 = 0`. -/
theorem uT_sort0 : HasType [] uT (.sort 0) :=
  .pi (u := 1) (v := 0) NE_sort1 nat_prop_in_ctx

/-- `Deq [] (Sort 1) (Sort 0)` is unsound: it would put `ω` in
`univ 0`, whose members are truth values. -/
theorem not_deq_sort1_sort0 (V : Type w) [SetTheory V] :
    ¬ Deq [] (.sort 1) (.sort 0) := by
  intro hd
  have hs := (hd.toHasType (.sort 2)).sound V (rho0 V) (Sat_nil V _)
  rw [interp_eqE] at hs
  have huniv : (univ 1 : V) = univ 0 := mem_eqv hs
  have hsub : (omega : V) ⊆ˢ unitSet :=
    mem_univZero.mp (univ_zero (V := V) ▸ huniv ▸ omega_mem_univ)
  have h0 : (natzero : V) = pt := mem_unitSet (hsub _ natzero_mem)
  refine pt_ne_empty (V := V) (h0 ▸ ?_)
  unfold natzero
  rfl

/-- **The refutation, assembled**: one closed term, two derivable
types, underivably related. -/
theorem unique_typing_refuted (V : Type w) [SetTheory V] :
    HasType [] uT (.sort 1) ∧ HasType [] uT (.sort 0) ∧
      ¬ Deq [] (.sort 1) (.sort 0) :=
  ⟨uT_sort1, uT_sort0, not_deq_sort1_sort0 V⟩

end Spike
end Setlec.TT
