import Setlec.Semantics.BasisType
import Setlec.Semantics.Interp

/-!
# `bval2_mem_type` — every built-in inhabits its annotated type

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but base, and the graded lane needs it.
Path and module name changed; namespaces, statements and proofs
verbatim.)*


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

/-- **`PSigma'.mk`** — the case the port pattern does not reach.  v1's
four pointwise `lamC_mem`s work because `psigmaMkV`'s *body* carries an
explicit `if max u v = 0 then pt` tag; `psigmaMkV2` dropped it (the
annotation squashes the tower instead), so the innermost pointwise
obligation would be `spair a b ∈ˢ sigmaSet 0 A B'` — **false**, since a
kind-`0` `sigmaSet` is a truth value and `spair a b ≠ pt`.  The kind-`0`
argument therefore moves from the leaf to the root: split first, then
exhibit the tower's *inhabitation* with `pt_mem_piR_zero`. -/
theorem bval2_mem_psigmaMk (us : List Nat) (ρ : Nat → V) :
    bval2 V .psigmaMk us
      ∈ˢ interp2 V ρ (BConst.type2 .psigmaMk us) := by
  show psigmaMkV2 V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.type2, arrowA, psigmaT2, interp2_pi, interp2_bvar,
    interp2_sort, interp2_app, interp2_const, AVExpr.liftN,
    AVExpr.mkAppN, cons_zero, cons_succ, bval2, lv,
    List.getD_cons_zero, List.getD_cons_succ]
  by_cases hw : Nat.max (us.getD 0 0) (us.getD 1 0) = 0
  · -- the whole tower is the canonical proof; exhibit inhabitation
    rw [psigmaMkV2, hw, lamR_zero]
    refine pt_mem_piR_zero fun A hA => ⟨pt, pt_mem_piR_zero
      fun B hB => ⟨pt, pt_mem_piR_zero fun a ha => ⟨pt,
        pt_mem_piR_zero fun b hb => ⟨pt, ?_⟩⟩⟩⟩
    rw [psigmaV2_app V hA hB, hw]
    exact pt_mem_sigma ha hb
  · refine lamR_mem fun A hA => lamR_mem fun B hB =>
      lamR_mem fun a ha => lamR_mem fun b hb => ?_
    rw [psigmaV2_app V hA hB]
    exact spair_mem hw ha hb

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

/-- **`Quot.lift`** — six binders, five of them `lamR_mem`, and the
tail is `quotLiftR_mem`.  Its kind-`0` fibre premise comes from the
third binder (`B ∈ˢ univ v`, and `univ 0 = univZero`), so nothing new
is needed. -/
theorem bval2_mem_quotLift (us : List Nat) (ρ : Nat → V) :
    bval2 V .quotLift us
      ∈ˢ interp2 V ρ (BConst.type2 .quotLift us) := by
  show quotLiftV2 V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.type2, relT2, quotT2, interp2_pi, interp2_bvar,
    interp2_sort, interp2_app, interp2_const, interp2_eqE,
    AVExpr.liftN, AVExpr.mkAppN, cons_zero, cons_succ, quotLiftV2,
    relSpace2, quotInvSpace2, bval2, lv, List.getD_cons_zero]
  refine lamR_mem fun A hA => lamR_mem fun R hR =>
    lamR_mem fun B hB => lamR_mem fun f hf =>
      lamR_mem fun h hh => ?_
  rw [quotV2_app V hA hR]
  exact quotLiftR_mem V hf fun h0 => by
    rw [← univ_zero]; exact h0 ▸ hB

/-! ## The `pt`-valued propositions

`Quot.ind`, `Quot.sound` and `propext` have `bval2 = pt`, so their
cases are *inhabitation* arguments rather than typings: every binder is
`piR 0`, and `pt_mem_piR_zero_of` replaces the collapse lane's
`pt_mem_piC_iff.mpr` line for line. -/

theorem bval2_mem_quotInd (us : List Nat) (ρ : Nat → V) :
    bval2 V .quotInd us ∈ˢ interp2 V ρ (BConst.type2 .quotInd us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.type2, relT2, quotT2, quotMkT2, interp2_pi,
    interp2_bvar, interp2_sort, interp2_app, interp2_const,
    AVExpr.liftN, AVExpr.mkAppN, cons_zero, cons_succ,
    bval2, lv, List.getD_cons_zero]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun R hR => ?_
  refine pt_mem_piR_zero_of fun M hM => ?_
  refine pt_mem_piR_zero_of fun mi hmi => ?_
  refine pt_mem_piR_zero_of fun q hq => ?_
  have hMq : app M q ∈ˢ (univ 0 : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM hq
  rw [quotV2_app V hA hR] at hq
  obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
  have h1 := app_mem_piR hmi ha fun _ x hx => by
      rw [quotMkV2_app V hA hR hx, ← univ_zero]
      exact app_mem_piR_pos Nat.one_ne_zero hM
        (by rw [quotV2_app V hA hR]; exact quotClass_mem hx)
  rw [quotMkV2_app V hA hR ha] at h1
  exact mem_univ_zero hMq h1 ▸ h1

theorem bval2_mem_quotSound (us : List Nat) (ρ : Nat → V) :
    bval2 V .quotSound us
      ∈ˢ interp2 V ρ (BConst.type2 .quotSound us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.type2, relT2, quotT2, quotMkT2, interp2_pi,
    interp2_bvar, interp2_sort, interp2_app, interp2_const,
    interp2_eqE, AVExpr.liftN, AVExpr.mkAppN, cons_zero, cons_succ,
    bval2, lv, List.getD_cons_zero]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun R hR => ?_
  refine pt_mem_piR_zero_of fun a ha => ?_
  refine pt_mem_piR_zero_of fun b hb => ?_
  refine pt_mem_piR_zero_of fun _wv hwv => ?_
  rw [quotMkV2_app V hA hR ha, quotMkV2_app V hA hR hb,
    SetTheory.quotSound ha hb hwv]
  exact pt_mem_eqv_self _

theorem bval2_mem_propext (us : List Nat) (ρ : Nat → V) :
    bval2 V .propext us ∈ˢ interp2 V ρ (BConst.type2 .propext us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.type2, interp2_pi, interp2_bvar, interp2_sort,
    interp2_eqE, cons_zero, cons_succ]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun B hB => ?_
  refine pt_mem_piR_zero_of fun f hf => ?_
  refine pt_mem_piR_zero_of fun g hg => ?_
  have hAB : A = B := by
    refine prop_ext hA hB (fun hp => ?_) (fun hp => ?_)
    · have h1 : app f pt ∈ˢ B :=
        app_mem_piR hf hp fun _ _ _ => by rw [← univ_zero]; exact hB
      exact mem_univ_zero hB h1 ▸ h1
    · have h1 : app g pt ∈ˢ A :=
        app_mem_piR hg hp fun _ _ _ => by rw [← univ_zero]; exact hA
      exact mem_univ_zero hA h1 ▸ h1
  rw [hAB]
  exact pt_mem_eqv_self _

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

/-! ## The capstone

`ConstOk.lean`'s `bval_mem_type`, over `interp2` and `BConst.type2`.
This is what the skeleton's `const` row waits on, and with it
deliverable (2) stands at ten formers of ten. -/

/-- **Every built-in constant inhabits its annotated type.** -/
theorem bval2_mem_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    bval2 V c us ∈ˢ interp2 V ρ (BConst.type2 c us) := by
  cases c with
  | nat => exact bval2_mem_nat V us ρ
  | natZero => exact bval2_mem_natZero V us ρ
  | natSucc => exact bval2_mem_natSucc V us ρ
  | natRec => exact bval2_mem_natRec V us ρ
  | punit => exact bval2_mem_punit V us ρ
  | punitUnit => exact bval2_mem_punitUnit V us ρ
  | punitRec => exact bval2_mem_punitRec V us ρ
  | psigma => exact bval2_mem_psigma V us ρ
  | psigmaMk => exact bval2_mem_psigmaMk V us ρ
  | empty => exact bval2_mem_empty V us ρ
  | emptyRec => exact bval2_mem_emptyRec V us ρ
  | quot => exact bval2_mem_quot V us ρ
  | quotMk => exact bval2_mem_quotMk V us ρ
  | quotLift => exact bval2_mem_quotLift V us ρ
  | quotInd => exact bval2_mem_quotInd V us ρ
  | quotSound => exact bval2_mem_quotSound V us ρ
  | propext => exact bval2_mem_propext V us ρ
  | choice => exact bval2_mem_choice V us ρ

end Setlec.SetR.Interp2
