module

public import ConLeche.Model.Claims
import ConLeche.Semantics.BasisType
public import ConLeche.Model.BitAgree

public section

/-!
# `WellDenotedV` at every built-in type (task #161, ENDGAME E)

Every pinned type's annotated type reading is truthful and bit-valid
(`WellDenotedV_bconst_type`).

## Why this is two lemmas and not one

* `WellDenoted`'s `.app` clause carries a **numeral** and a fibre
  obligation (`∃ v A B, f ∈ˢ piR v A B ∧ a ∈ˢ A ∧ (v = 0 → …)`).
  The numeral is not free: it is
  whichever one `bval_mem_type` supplies, because that membership is
  the only source of the `piR` fact;
* there is a **second predicate**.  `AnnotValid` is bit validity, and
  its one numeral-reading clause is `pi`'s `v = 0 → the codomain reads
  into `univZero``.  `BConst.typeAV`'s convention (every codomain slot
  carries the tower's *result* sort) is what makes those discharge: a
  `pi` slot is zero exactly when the tower's result is a proposition,
  and then every suffix of the tower is one too.

## How the two computations close

`AnnotValid_bconst_type` is one `cases c` plus one **contextual**
`simp only` (the `v = 0` antecedents have to be usable on their own
consequents, which is exactly what `+contextual` buys) with three
closers folded into the simp set — impredicativity
(`piR_zero_mem_univZero`), the truth set (`eqv_mem_univZero`), and the
unsatisfiability of the `n + 1 = 0` premises.  That leaves **fifteen
residual goals in nine cases**, and every one is the clause's own
`v = 0` premise plus one argument membership:

1. `natRec` ×2, `punitRec`, `emptyRec`, `quotInd` ×2, `psigmaMk`,
   `quotMk` — `motive_app_univZero` below, with the argument supplied
   by `natSuccV_mem`, `quotClass_mem`, `sigma_mem_univ`, … one per
   goal;
2. `quotLift` ×2, `propext` ×2, `choice` ×3 — `univ 0 = univZero` at a
   binder already known to land in `univ v`.

`WellDenoted_bconst_type` is the same `cases c` + `simp only`, and its
residue is uniformly the `.app` clause's `∃ v A B, f ∈ˢ piR v A B ∧
a ∈ˢ A ∧ (v = 0 → …)`.  **The numeral is never chosen**: at a bound
motive it is the binder's own hypothesis, and at a basis constant's
head it is the codomain slot of `BConst.typeAV`'s own binder —
`bconst_app_data`/`_dataAV`/`_data3` read the `piR` fact off
`bval_mem_type` and the fibre obligation off `AnnotValid_bconst_type`
at the *same* binder, so both halves come from the pin.  The two
bespoke suppliers are `rel_app_data` (a relation applied once is still
a graph, numeral `1`, because `Prop` as a type is `Sort 1`) and
`quotMk_mem_quot`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **A motive at a zero level lands in `univZero`.**  The one
non-structural move the bit-validity computation needs: every basis
recursor's type binds a motive in `piR (v + 1) A (fun _ => univ v)`,
and the `pi` clause's premise is exactly `v = 0`.  The `+ 1` is what
keeps the motive space in the graph regime whatever `v` is — a motive
is a *function into a universe*, never a proposition, which is the
`v'`-for-a-`Sort` trap of `Semantics/BasisType.lean`'s docstring showing
up on the validity side. -/
theorem motive_app_univZero {u : Nat} {A M a : V} (hu : u = 0)
    (hM : M ∈ˢ piR (u + 1) A (fun _ => (univ u : V))) (ha : a ∈ˢ A) :
    SetTheory.app M a ∈ˢ (univZero : V) := by
  have h := app_mem_piR_pos (Nat.succ_ne_zero u) hM ha
  rw [hu, univ_zero] at h
  exact h

/-! ## The two grading predicates at every built-in type -/

variable (V)

/-! ## `lfpTuple k`'s two towers

The block carrier's constant is the one whose type is a *tower*, so its
two grading facts are not the `simp` battery's: bit validity is
hereditary and needs no membership at all (`ndTowerAV_annotValid`),
while the grading of the family tower needs the ambient variable to be
an index-set tuple — which is exactly what the outer `Π`'s own clause
hands it. -/

/-- **The non-dependent tower is bit-valid**: hereditarily from its
components', with no membership fact anywhere (the `pi` clause's own
component is discharged by the tower's `r + 1` fibre annotation). -/
theorem ndTowerAV_annotValid {r : Nat} {G : Nat → AnnotTerm} {ρ : Nat → V} :
    ∀ (n s d : Nat) (σ : Nat → V), shiftE d 0 σ = ρ →
      (∀ m, m < s + n → AnnotValid V ρ (G m)) →
      AnnotValid V σ (ndTowerAV r G s d n)
  | 0, _, _, _, _, _ => by simp [ndTowerAV]
  | n + 1, s, d, σ, hσ, hok => by
    have hCok : AnnotValid V σ ((G s).liftN d 0) := by
      rw [AnnotValid_liftN, hσ]; exact hok s (by omega)
    show AnnotValid V σ (.app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
      (.lam (r + 1) ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n)))
    rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
    exact ⟨⟨trivial, hCok⟩, hCok, fun x _ =>
      ndTowerAV_annotValid n (s + 1) (d + 1) (cons x σ)
        (by rw [shiftE_succ_cons]; exact hσ) (fun m hm => hok m (by omega))⟩

theorem tupleSortsAV_annotValid (k : Nat) (us : List Nat) (ρ : Nat → V) :
    AnnotValid V ρ (tupleSortsAV k us) :=
  ndTowerAV_annotValid V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) (fun _ _ => trivial)

theorem tupleFamsAV_annotValid (k : Nat) (us : List Nat) (j : Nat) (ρ : Nat → V) :
    AnnotValid V ρ (tupleFamsAV k us j) :=
  ndTowerAV_annotValid V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) fun m _ => by
    rw [AnnotValid_pi]
    exact ⟨projAV_validV (i := m) trivial, fun _ _ => trivial,
      fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩

/-- **`lfpTuple k`'s type is bit-valid**: every binder's result slot is
the family tuple's own sort, which is never `0`. -/
theorem AnnotValid_lfpTuple (k : Nat) (us : List Nat) (ρ : Nat → V) :
    AnnotValid V ρ (BConst.typeAV (.lfpTuple k) us) := by
  show AnnotValid V ρ (.pi _ _ (tupleSortsAV k us)
    (.pi _ _ (.pi _ _ (tupleFamsAV k us 0) (tupleFamsAV k us 1)) (tupleFamsAV k us 1)))
  have hR : ConLeche.Term.tupleFamSort k us ≠ 0 := tupleFamSort_ne_zero k us
  rw [AnnotValid_pi]
  refine ⟨tupleSortsAV_annotValid V k us ρ, fun Is _ => ?_, fun h0 => absurd h0 hR⟩
  rw [AnnotValid_pi]
  refine ⟨?_, fun F _ => tupleFamsAV_annotValid V k us 1 _, fun h0 => absurd h0 hR⟩
  rw [AnnotValid_pi]
  exact ⟨tupleFamsAV_annotValid V k us 0 _, fun x _ => tupleFamsAV_annotValid V k us 1 _,
    fun h0 => absurd h0 hR⟩

/-- **`lfpTuple k`'s type is graded**: the family tower's projections
are graded because the outer `Π`'s clause hands them an index-set
tuple. -/
theorem WellDenoted_lfpTuple (k : Nat) (us : List Nat) (ρ : Nat → V) :
    WellDenoted V ρ (BConst.typeAV (.lfpTuple k) us) := by
  show WellDenoted V ρ (.pi _ _ (tupleSortsAV k us)
    (.pi _ _ (.pi _ _ (tupleFamsAV k us 0) (tupleFamsAV k us 1)) (tupleFamsAV k us 1)))
  rw [WellDenoted_pi]
  refine ⟨(tupleSortsAV_facts V k us ρ).2, fun Is hIs => ?_⟩
  rw [(tupleSortsAV_facts V k us ρ).1] at hIs
  have h0 : WellDenoted V (cons Is ρ) (tupleFamsAV k us 0) :=
    (tupleFamsAV_facts V (j := 0) (ρ := cons Is ρ) hIs).2
  have h1 : ∀ x : V, WellDenoted V (cons x (cons Is ρ)) (tupleFamsAV k us 1) :=
    fun x => (tupleFamsAV_facts V (j := 1) (ρ := cons x (cons Is ρ)) hIs).2
  rw [WellDenoted_pi]
  refine ⟨?_, fun F _ => h1 F⟩
  rw [WellDenoted_pi]
  exact ⟨h0, fun x _ => h1 x⟩

set_option maxHeartbeats 4000000 in
theorem AnnotValid_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    AnnotValid V ρ (BConst.typeAV c us) := by
  cases c
  case lfpTuple k => exact AnnotValid_lfpTuple V k us ρ
  all_goals
    simp +contextual +decide only [BConst.typeAV, arrowA, relAV, negTyAV,
      natTyAV, natZeroAV, natSuccAV, punitAV, punitUnitAV, emptyAV,
      psigmaAV, quotAV, quotMkAV, AnnotTerm.mkAppN, AnnotTerm.lift,
      AnnotTerm.liftN, AnnotValid_pi, AnnotValid_app, AnnotValid_eqE,
      AnnotValid_bvar, AnnotValid_sort, AnnotValid_const,
      interp_pi, interp_app, interp_eqE, interp_sort,
      interp_const, interp_bvar, cons_zero, cons_succ,
      piR_zero_mem_univZero, eqv_mem_univZero, Nat.succ_ne_zero,
      Nat.max_eq_zero_iff, Nat.max_self, true_and, and_true, and_self,
      implies_true, false_implies, forall_const, and_false, ite_false]
  case natRec =>
    refine fun M hM z _ => ⟨fun n hn hu _ _ => ?_,
      fun _s _ hu n hn => motive_app_univZero hu hM hn⟩
    exact motive_app_univZero hu hM
      (app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) hn)
  case punitRec =>
    exact fun _M hM _m _ hu _t ht => motive_app_univZero hu hM ht
  case emptyRec =>
    exact fun _M hM hu _t ht => motive_app_univZero hu hM ht
  case psigmaMk =>
    intro A hA B hB a _ h b _
    obtain ⟨hu, hv⟩ := h
    rw [hu] at hA
    rw [hv] at hB
    have hmem := sigma_mem_univ (u := 0) (v := 0) hA
      (fun x hx => psigmaFibre_apply V hB hx)
    rw [show Nat.max 0 0 = 0 from rfl, univ_zero] at hmem
    show app (app (psigmaV V 0 0) A) B ∈ˢ _
    rw [psigmaV_app V hA hB]
    exact hmem
  case quotMk =>
    intro A hA R hR hu a _
    rw [hu] at hA hR
    have h := quotSet_mem_univ (u := 0) (A := A) (R := R) hA
    rw [univ_zero] at h
    show app (app (quotV V 0) A) R ∈ˢ _
    rw [quotV_app V hA hR]
    exact h
  case quotLift =>
    intro A hA R hR B hB
    have hB0 : lv us 1 = 0 → B ∈ˢ (univZero : V) := by
      intro hv; rw [hv, univ_zero] at hB; exact hB
    exact ⟨fun hv _ _ => hB0 hv, fun _f _ _h _ hv _q _ => hB0 hv⟩
  case quotInd =>
    intro A hA R hR M hM
    refine ⟨fun a ha => motive_app_univZero (u := 0) rfl hM ?_,
      fun _mi _ q hq => motive_app_univZero (u := 0) rfl hM hq⟩
    show app (app (app (quotMkV V (lv us 0)) A) R) a
      ∈ˢ app (app (quotV V (lv us 0)) A) R
    rw [quotMkV_app V hA hR ha, quotV_app V hA hR]
    exact quotClass_mem ha
  case propext =>
    exact fun _A hA _B hB => ⟨fun _ _ => univ_zero (V := V) ▸ hB,
      fun _ _ _ _ => univ_zero (V := V) ▸ hA⟩
  case choice =>
    intro A hA
    refine ⟨⟨fun _ _ => univ_zero (V := V) ▸ empty_mem_univ 0,
      fun _ _ => univ_zero (V := V) ▸ empty_mem_univ 0⟩, fun hu _ _ => ?_⟩
    rw [hu, univ_zero] at hA
    exact hA


/-- **The `.app` clause's witness at a basis constant's head.**  The
numeral is not chosen: it is the codomain slot of `typeAV`'s own outer
binder, the `piR` fact is `bval_mem_type` at that binder, and the
fibre obligation is `AnnotValid_bconst_type`'s `pi` clause verbatim. -/
theorem bconst_app_data (c : BConst) (us : List Nat) (ρ : Nat → V)
    {u v : Nat} {A B : AnnotTerm} (h : BConst.typeAV c us = .pi u v A B)
    {a : V} (ha : a ∈ˢ interp V ρ A) :
    ∃ (w : Nat) (S : V) (F : V → V), bval V c us ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) := by
  refine ⟨v, interp V ρ A, fun x => interp V (cons x ρ) B, ?_, ha, ?_⟩
  · have hm := bval_mem_type V c us ρ
    rw [h, interp_pi] at hm; exact hm
  · have hv := AnnotValid_bconst_type V c us ρ
    rw [h, AnnotValid_pi] at hv; exact hv.2.2

/-- The same one binder in: a basis constant applied to its first
argument.  `app_mem_piR`'s fibre premise is again the outer binder's
own `AnnotValid` clause, so nothing is chosen here either. -/
theorem bconst_app_dataAV (c : BConst) (us : List Nat) (ρ : Nat → V)
    {u v u2 v2 : Nat} {A A2 B2 : AnnotTerm}
    (h : BConst.typeAV c us = .pi u v A (.pi u2 v2 A2 B2))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a : V} (ha : a ∈ˢ interp V (cons a1 ρ) A2) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (bval V c us) a1 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) := by
  have hv := AnnotValid_bconst_type V c us ρ
  rw [h, AnnotValid_pi] at hv
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piR hm ha1 hv.2.2
  rw [interp_pi] at h1
  refine ⟨v2, interp V (cons a1 ρ) A2,
    fun x => interp V (cons x (cons a1 ρ)) B2, h1, ha, ?_⟩
  have h2 := hv.2.1 a1 ha1
  rw [AnnotValid_pi] at h2
  exact h2.2.2

/-- A membership at a zero level lands in `univZero`. -/
theorem mem_univZero_of_zero {u : Nat} {X : V} (hu : u = 0)
    (h : X ∈ˢ (univ u : V)) : X ∈ˢ (univZero : V) := by
  rw [hu, univ_zero] at h; exact h

/-- Two binders in: the constant applied to its first two arguments. -/
theorem bconst_app_data3 (c : BConst) (us : List Nat) (ρ : Nat → V)
    {u v u2 v2 u3 v3 : Nat} {A A2 A3 B3 : AnnotTerm}
    (h : BConst.typeAV c us = .pi u v A (.pi u2 v2 A2 (.pi u3 v3 A3 B3)))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a2 : V} (ha2 : a2 ∈ˢ interp V (cons a1 ρ) A2)
    {a : V} (ha : a ∈ˢ interp V (cons a2 (cons a1 ρ)) A3) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (app (bval V c us) a1) a2 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) := by
  have hv := AnnotValid_bconst_type V c us ρ
  rw [h, AnnotValid_pi] at hv
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piR hm ha1 hv.2.2
  rw [interp_pi] at h1
  have hv2 := hv.2.1 a1 ha1
  rw [AnnotValid_pi] at hv2
  have h2 := app_mem_piR h1 ha2 hv2.2.2
  rw [interp_pi] at h2
  refine ⟨v3, interp V (cons a2 (cons a1 ρ)) A3,
    fun x => interp V (cons x (cons a2 (cons a1 ρ))) B3, h2, ha, ?_⟩
  have hv3 := hv2.2.1 a2 ha2
  rw [AnnotValid_pi] at hv3
  exact hv3.2.2

/-- Three binders in: the constant applied to its first three
arguments.  The basis *recursors*' RHS towers apply their
head four and five deep (`Nat.rec`'s successor rule, `Quot.lift`), and
the numeral is read off `typeAV`'s own binder at every step, exactly as
at `_data`/`_dataAV`/`_data3`. -/
theorem bconst_app_data4 (c : BConst) (us : List Nat) (ρ : Nat → V)
    {u v u2 v2 u3 v3 u4 v4 : Nat} {A A2 A3 A4 B4 : AnnotTerm}
    (h : BConst.typeAV c us
      = .pi u v A (.pi u2 v2 A2 (.pi u3 v3 A3 (.pi u4 v4 A4 B4))))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a2 : V} (ha2 : a2 ∈ˢ interp V (cons a1 ρ) A2)
    {a3 : V} (ha3 : a3 ∈ˢ interp V (cons a2 (cons a1 ρ)) A3)
    {a : V} (ha : a ∈ˢ interp V (cons a3 (cons a2 (cons a1 ρ))) A4) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (app (app (bval V c us) a1) a2) a3 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) := by
  have hv := AnnotValid_bconst_type V c us ρ
  rw [h, AnnotValid_pi] at hv
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piR hm ha1 hv.2.2
  rw [interp_pi] at h1
  have hv2 := hv.2.1 a1 ha1
  rw [AnnotValid_pi] at hv2
  have h2 := app_mem_piR h1 ha2 hv2.2.2
  rw [interp_pi] at h2
  have hv3 := hv2.2.1 a2 ha2
  rw [AnnotValid_pi] at hv3
  have h3 := app_mem_piR h2 ha3 hv3.2.2
  rw [interp_pi] at h3
  refine ⟨v4, interp V (cons a3 (cons a2 (cons a1 ρ))) A4,
    fun x => interp V (cons x (cons a3 (cons a2 (cons a1 ρ)))) B4,
    h3, ha, ?_⟩
  have hv4 := hv3.2.1 a3 ha3
  rw [AnnotValid_pi] at hv4
  exact hv4.2.2

/-- `Quot.mk`'s spine inhabits its quotient — the argument membership
`quotInd`'s and `quotSound`'s motive rows want. -/
theorem quotMk_mem_quot {u : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V u A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u) A) R) a ∈ˢ app (app (quotV V u) A) R := by
  rw [quotMkV_app V hA hR ha, quotV_app V hA hR]
  exact quotClass_mem ha

/-- A relation applied to one argument is still a graph: the `.app`
clause's data at `relAV`'s inner binder, whose numeral is `1` because
`Prop` as a type is `Sort 1`. -/
theorem rel_app_data {u : Nat} {A R a b : V}
    (hR : R ∈ˢ piR (Nat.max u 1) A fun _ => piR 1 A fun _ => (univ 0 : V))
    (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    ∃ (w : Nat) (S : V) (F : V → V), app R a ∈ˢ piR w S F ∧ b ∈ˢ S ∧
      (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) :=
  ⟨1, A, fun _ => univ 0, app_mem_piR_pos (maxOne_ne_zero u) hR ha, hb,
    fun h => absurd h Nat.one_ne_zero⟩

set_option maxHeartbeats 4000000 in
theorem WellDenoted_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    WellDenoted V ρ (BConst.typeAV c us) := by
  cases c
  case lfpTuple k => exact WellDenoted_lfpTuple V k us ρ
  all_goals
    simp +contextual +decide only [BConst.typeAV, arrowA, relAV, negTyAV,
      natTyAV, natZeroAV, natSuccAV, punitAV, punitUnitAV, emptyAV,
      psigmaAV, quotAV, quotMkAV, AnnotTerm.mkAppN, AnnotTerm.lift,
      AnnotTerm.liftN, WellDenoted_pi, WellDenoted_app, WellDenoted_eqE,
      WellDenoted_bvar, WellDenoted_sort, WellDenoted_const,
      interp_pi, interp_app, interp_eqE, interp_sort,
      interp_const, interp_bvar, cons_zero, cons_succ,
      true_and, and_true, and_self, implies_true, ite_false]
  all_goals
    (repeat' first
      | exact ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h (Nat.succ_ne_zero _)⟩
      | exact ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h Nat.one_ne_zero⟩
      | exact ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h (maxOne_ne_zero _)⟩
      | exact ⟨_, _, _, ‹_›, natzero_mem, fun h => absurd h (Nat.succ_ne_zero _)⟩
      | exact ⟨_, _, _, ‹_›, pt_mem_unitSet, fun h => absurd h (Nat.succ_ne_zero _)⟩
      | exact ⟨_, _, _, ‹_›,
          app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) ‹_›,
          fun h => absurd h (Nat.succ_ne_zero _)⟩
      | exact ⟨_, _, _, ‹_›, ‹_›,
          fun hz _ _ => mem_univZero_of_zero V hz ‹_›⟩
      | (apply rel_app_data V <;> assumption)
      | (refine ⟨_, _, _, ‹_›, quotMk_mem_quot V ?_ ?_ ?_,
            fun h => absurd h Nat.one_ne_zero⟩ <;> assumption)
      | (refine bconst_app_data V _ _ ρ rfl ?_; assumption)
      | (refine bconst_app_dataAV V _ _ ρ rfl ?_ ?_ <;> assumption)
      | (refine bconst_app_data3 V _ _ ρ rfl ?_ ?_ ?_ <;> assumption)
      | apply And.intro
      | intro _
      | trivial)

/-- **Every built-in constant's annotated type is `WellDenotedV`**:
truthfulness and bit validity together.  This is the grading half of the twenty-two basis
type readings — the other half is `AnnotTerm.BitAgree` (`BitAgree.lean`),
which carries this across to whatever `denoteMeta` actually emits. -/
theorem WellDenotedV_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (BConst.typeAV c us) :=
  ⟨WellDenoted_bconst_type V c us ρ, AnnotValid_bconst_type V c us ρ⟩

end ConLeche.Model
