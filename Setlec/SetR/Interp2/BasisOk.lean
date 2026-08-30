import Setlec.SetR.Interp2.BasisType
import Setlec.SetR.Interp2.Interp

/-!
# `bval2_mem_type` — every built-in inhabits its annotated type

Step 2's second entry item, and the skeleton's `const` row's remaining
supplier: `Setlec/TT/Semantics/ConstOk.lean`'s capstone ported onto
`piR`/`lamR` and `BConst.type2`.

## The port pattern

Each case is three moves, and the first two are mechanical:

1. `show` the value at its own tower (`bval2` is a `match`, so this is
   definitional);
2. `simp only` with `BConst.type2`, the smart constructors it mentions,
   and the `interp2` clause equations — this reduces
   `interp2 ρ (type2 c us)` to the tower's *own space*, which is the
   whole point of having read the numeral convention off `Value.lean`
   rather than choosing one;
3. apply the tower's membership argument — `lamR_mem` down the
   binders, then the constant's own semantic fact.

Where v1 needed a universe side condition (`app_mem`'s codomain
premise, `pi_mem_univ`'s levels) the port needs none: `lamR_mem` has no
premise beyond the fibres and `app_mem_piR_pos` none at all.  Where v1
needed `pt_mem_piC_iff` because the collapse made a value `pt`, the
port often does not: `Empty.rec` is a *graph* here
(`emptyRecV2 = lamR v … (lamR v ∅ …)`), so its case is two `lamR_mem`s
over a vacuous domain rather than a proof-point argument.

## The `Nat.succ` wrinkle, inherited verbatim

`type2`'s step premise mentions `Nat.succ`'s *value*
(`natSuccT2 (.bvar 1)` interprets to `app (natSuccV2 V) n`) while
`natStepSpace2` is written with the operator `natsucc`.  They agree on
`ω`, which is what the outer product quantifies over — v1's
`natStepSpace_eq`, restated here as `natStepSpace2_eq`.
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.TT (BConst lv)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat` -/

theorem bval2_mem_nat (us : List Nat) (ρ : Nat → V) :
    bval2 V .nat us ∈ˢ interp2 V ρ (BConst.type2 .nat us) := by
  show (omega : V) ∈ˢ _
  simp only [BConst.type2, interp2_sort]
  exact omega_mem_univ_succ 0

theorem bval2_mem_natZero (us : List Nat) (ρ : Nat → V) :
    bval2 V .natZero us ∈ˢ interp2 V ρ (BConst.type2 .natZero us) := by
  show natzero ∈ˢ _
  simp only [BConst.type2, natT2, interp2_const, bval2]
  exact natzero_mem

theorem bval2_mem_natSucc (us : List Nat) (ρ : Nat → V) :
    bval2 V .natSucc us ∈ˢ interp2 V ρ (BConst.type2 .natSucc us) := by
  show natSuccV2 V ∈ˢ _
  simp only [BConst.type2, arrowA, natT2, interp2_pi, interp2_const,
    AVExpr.liftN, bval2]
  exact natSuccV2_mem V

/-- The step space as `interp2` produces it (with `Nat.succ`'s *value*
applied) is the one the tower is written with (`natsucc`): they agree
on `ω`.  v1's `natStepSpace_eq`. -/
theorem natStepSpace2_eq {u : Nat} (M : V) :
    (piR u (omega : V) fun n =>
        piR u (app M n) fun _ => app M (app (natSuccV2 V) n))
      = natStepSpace2 V u M :=
  piR_congr fun n hn => by rw [natSuccV2_app V hn]

/-- `Nat.rec`'s type, as `interp2` produces it. -/
theorem interp2_type_natRec (us : List Nat) (ρ : Nat → V) :
    interp2 V ρ (BConst.type2 .natRec us) =
      piR (lv us 0) (natMotiveSpace V (lv us 0)) fun M =>
        piR (lv us 0) (app M natzero) fun _ =>
          piR (lv us 0) (natStepSpace2 V (lv us 0) M) fun _ =>
            piR (lv us 0) omega fun n => app M n := by
  simp only [BConst.type2, arrowA, natT2, natZeroT2, natSuccT2,
    interp2_pi, interp2_const, interp2_app, interp2_bvar, interp2_sort,
    AVExpr.liftN, cons_zero, cons_succ, bval2, natMotiveSpace]
  refine piR_congr fun M _ => piR_congr fun z _ => ?_
  rw [natStepSpace2_eq]

theorem bval2_mem_natRec (us : List Nat) (ρ : Nat → V) :
    bval2 V .natRec us ∈ˢ interp2 V ρ (BConst.type2 .natRec us) := by
  rw [interp2_type_natRec]
  show natRecV2 V (lv us 0) ∈ˢ _
  refine lamR_mem fun M hM => lamR_mem fun z hz =>
    lamR_mem fun s hs => ?_
  refine lamR_mem fun n hn => ?_
  exact natRecV2_mem_fibre V hM hz hs hn

/-! ## `PUnit` -/

theorem bval2_mem_punit (us : List Nat) (ρ : Nat → V) :
    bval2 V .punit us ∈ˢ interp2 V ρ (BConst.type2 .punit us) := by
  show (unitSet : V) ∈ˢ _
  simp only [BConst.type2, interp2_sort]
  exact unitSet_mem_univ _

theorem bval2_mem_punitUnit (us : List Nat) (ρ : Nat → V) :
    bval2 V .punitUnit us
      ∈ˢ interp2 V ρ (BConst.type2 .punitUnit us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.type2, punitT2, interp2_const, bval2]
  exact pt_mem_unitSet

theorem bval2_mem_punitRec (us : List Nat) (ρ : Nat → V) :
    bval2 V .punitRec us
      ∈ˢ interp2 V ρ (BConst.type2 .punitRec us) := by
  show punitRecV2 V (lv us 1) ∈ˢ _
  simp only [BConst.type2, arrowA, punitT2, punitUnitT2, interp2_pi,
    interp2_const, interp2_app, interp2_bvar, interp2_sort,
    AVExpr.liftN, cons_zero, cons_succ, bval2]
  refine lamR_mem fun M hM => lamR_mem fun m hm =>
    lamR_mem fun t ht => ?_
  rw [mem_unitSet ht]
  exact hm

/-! ## `Empty` -/

theorem bval2_mem_empty (us : List Nat) (ρ : Nat → V) :
    bval2 V .empty us ∈ˢ interp2 V ρ (BConst.type2 .empty us) := by
  show (empty : V) ∈ˢ _
  simp only [BConst.type2, interp2_sort]
  exact empty_mem_univ _

theorem bval2_mem_emptyRec (us : List Nat) (ρ : Nat → V) :
    bval2 V .emptyRec us
      ∈ˢ interp2 V ρ (BConst.type2 .emptyRec us) := by
  show emptyRecV2 V (lv us 1) ∈ˢ _
  simp only [BConst.type2, arrowA, emptyT2, interp2_pi, interp2_const,
    interp2_app, interp2_bvar, interp2_sort, AVExpr.liftN, cons_zero,
    cons_succ, bval2]
  refine lamR_mem fun M _ => lamR_mem fun t ht => ?_
  exact absurd ht (not_mem_empty t)

/-! ## `PSigma'` -/

theorem bval2_mem_psigma (us : List Nat) (ρ : Nat → V) :
    bval2 V .psigma us ∈ˢ interp2 V ρ (BConst.type2 .psigma us) := by
  show psigmaV2 V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.type2, arrowA, interp2_pi, interp2_bvar,
    interp2_sort, AVExpr.liftN, cons_zero, psigmaV2,
    psigmaFibreSpace]
  exact lamR_mem fun A hA => lamR_mem fun B hB =>
    sigma_mem_univ hA fun x hx =>
      app_mem_piR_pos (Nat.succ_ne_zero _) hB hx

/-! ## `Quot` -/

theorem bval2_mem_quot (us : List Nat) (ρ : Nat → V) :
    bval2 V .quot us ∈ˢ interp2 V ρ (BConst.type2 .quot us) := by
  show quotV2 V (lv us 0) ∈ˢ _
  simp only [BConst.type2, relT2, interp2_pi, interp2_bvar,
    interp2_sort, AVExpr.liftN, cons_zero, quotV2, relSpace2]
  exact lamR_mem fun A hA => lamR_mem fun R _ => quotSet_mem_univ hA

theorem bval2_mem_quotMk (us : List Nat) (ρ : Nat → V) :
    bval2 V .quotMk us ∈ˢ interp2 V ρ (BConst.type2 .quotMk us) := by
  show quotMkV2 V (lv us 0) ∈ˢ _
  simp only [BConst.type2, relT2, quotT2, interp2_pi, interp2_bvar,
    interp2_sort, interp2_app, interp2_const, AVExpr.liftN,
    AVExpr.mkAppN, cons_zero, cons_succ, quotMkV2, relSpace2, bval2,
    lv, List.getD_cons_zero]
  refine lamR_mem fun A hA => lamR_mem fun R hR =>
    lamR_mem fun a ha => ?_
  rw [quotV2_app V hA hR]
  exact quotClass_mem ha

/-! ## `Classical.choice` -/

theorem bval2_mem_choice (us : List Nat) (ρ : Nat → V) :
    bval2 V .choice us ∈ˢ interp2 V ρ (BConst.type2 .choice us) := by
  show choiceV2 V (lv us 0) ∈ˢ _
  simp only [BConst.type2, negT2, arrowA, emptyT2, interp2_pi,
    interp2_bvar, interp2_sort, interp2_const, AVExpr.liftN, cons_zero,
    cons_succ, choiceV2, dnegSpace2, bval2]
  refine lamR_mem fun A hA => lamR_mem fun h hh => ?_
  obtain ⟨x, hx⟩ := exists_mem_of_dneg2 V hh
  exact schoice_mem hx

end Setlec.SetR.Interp2
