module

import ConLeche.Semantics.Tower.BlockRecWfI
import ConLeche.Semantics.Tower.BlockRecIndI
import ConLeche.Semantics.Univ

/-!
# The recursor family's leaf, INSTANTIATED (falsifier, task #315, M5 model half)

The generic theorems of `BlockRecI`/`BlockRecKitI`/`BlockRecWfI`/
`BlockRecIndI` are worth nothing if their premises cannot be met
together.  This file meets them, end to end, at three shapes:

* **`FalsWf` — `K = 1`, regime WF** (`ℓ ≠ 0`): one class, no prefix,
  no indices, the carrier a one-element set, one constructor with no
  fields.  A real `WfRecKit` is built and the ι law comes out.
* **`FalsTwo` — ONE MEMBER, TWO RECURSORS** (`ℓ ≠ 0`, regime WF): the
  shape the maintainer's naming ruling admits — a member may carry any
  number of recursors, each assigned to it by its MAJOR and each with
  its OWN rule prefix.  The two classes here have the same carrier
  (the same member) but DIFFERENT conclusions (`PUnit` and
  `PUnit → PUnit`, at the same level `ℓ`, as D-d requires) and
  DIFFERENT rule prefixes (`0` and `1`).  This is what exercises the
  per-class `rP` and the chain's arithmetic at once: both classes'
  equations read the chain at `bvar 1`, and it denotes a different
  component in each because the rules bind different numbers of
  binders.
* **`FalsInd` — `K = 2`, regime IND** (`ℓ = 0`): two `Prop`-valued
  recursor types, one rule each.

All three end at `blockRecAV_facts`/`blockRecAV_iota`: the leaves are
typed, graded, and satisfy every rule's ι equation.  The point is that
the PREMISES compose, not that these particular families are
interesting.

**Module-local on purpose.**  Unlike the rest of `Semantics/*` this
file opens no `@[expose] public section`: nothing above reasons about
a falsifier, it exists to be BUILT.  Keeping its declarations
module-local is also what keeps `scripts/pub-import-plan.py` honest —
a leaf whose public interface nothing needs has no justified
`public import`, and the gate says so.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The one-element type, as a reading -/

/-- `PUnit.{0}` (`punitAV 0`, `Semantics/BasisType.lean`) — the
falsifiers' carrier, domain and conclusion. -/
abbrev punit0 : AnnotTerm := punitAV 0

theorem interp_punit0 (ρ : Nat → V) : interp V ρ punit0 = (unitSet : V) := rfl

theorem wd_punit0 (ρ : Nat → V) : WellDenoted V ρ punit0 := trivial

theorem interp_prfAV (ρ : Nat → V) : interp V ρ (.prf) = (pt : V) := rfl

theorem unitSet_mem_univZero : (unitSet : V) ∈ˢ (univZero : V) := by
  rw [← univ_zero]; exact unitSet_mem_univ 0

/-- Two tagged indices of different classes differ — the falsifiers'
class discriminator (no decoder needed: the carriers are singletons). -/
theorem tagged_ne_zero {c : Nat} (hc : c ≠ 0) (i x : V) :
    tagged c i x ≠ tagged 0 (pt : V) pt := fun h => absurd (tagged_inj h).1 hc

/-- `PUnit → PUnit` at level `ℓ`, and its reading. -/
theorem interp_punitArrow (ℓ : Nat) (ρ : Nat → V) :
    interp V ρ (.pi ℓ ℓ punit0 punit0) = piR ℓ (unitSet : V) fun _ => unitSet := rfl

theorem punitArrow_mem_univ (ℓ : Nat) (hℓ : ℓ ≠ 0) :
    (piR ℓ (unitSet : V) fun _ => unitSet) ∈ˢ (univ ℓ : V) := by
  have := piR_mem_univ (V := V) (u := ℓ) (v := ℓ) (A := unitSet) (B := fun _ => unitSet)
    (unitSet_mem_univ ℓ) fun _ _ => unitSet_mem_univ ℓ
  rwa [if_neg hℓ, natMax_self] at this

/-- Both falsifiers' ι equations for a one-rule, field-free family:
one class per `c < K`, one rule each, the constructed major and the
residue the terms given. -/
def falsEqs (K : Nat) (pdoms : Nat → List AnnotTerm) (Rb : Nat → Nat → AnnotTerm) :
    List AnnotTerm :=
  iotaEqsAV K (fun _ => 1) pdoms (fun _ _ => []) (fun _ _ => [])
    (fun _ _ => .prf) (fun _ _ => []) Rb

/-! ## Falsifier 1 — `K = 1`, regime WF -/

namespace FalsWf

variable (V)

/-- The class's index set: the one-element set (no indices, so the
index TUPLE is the point). -/
noncomputable def Is (_ : List V) (_ : Nat) : V := unitSet

/-- The class's ordinary carrier: constantly the one-element set. -/
noncomputable def Cr (_ : List V) (_ : Nat) : V := graph (fun _ => (unitSet : V)) unitSet

variable {V}

theorem app_Cr (xs : List V) (c : Nat) {i : V} (hi : i ∈ˢ (unitSet : V)) :
    app (Cr V xs c) i = (unitSet : V) := app_graph hi

/-- The kit: the motive is the one-element set at every tagged index,
the step is the point.  Both obligations are immediate — which is the
point: the kit asks nothing of the carriers. -/
noncomputable def kit (ℓ : Nat) (xs : List V) : WfRecKit ℓ 1 (Is V xs) (Cr V xs) where
  B := fun _ => unitSet
  st := fun _ _ => pt
  hB := fun _ _ => unitSet_mem_univ ℓ
  hst := fun _ _ _ _ => pt_mem_unitSet

/-- The recursor's binder data: one binder, the major, at bit `ℓ`. -/
def rds (ℓ : Nat) (_ : Nat) : List (Nat × Nat × AnnotTerm) := [(ℓ, ℓ, punit0)]

/-- The regime's data. -/
noncomputable def data (ℓ : Nat) (ρ : Nat → V) :
    RecFamData V ℓ 1 (fun _ => 0) (rds ℓ) (fun _ => punit0) ρ :=
  wfData (Is V) (Cr V) (fun _ _ => pt) (kit ℓ)
    (by
      intro c _ ys hsp
      have hy : ∃ t : V, ys = [t] ∧ t ∈ˢ (unitSet : V) := by
        match ys, hsp with
        | [t], h => exact ⟨t, rfl, h.1⟩
      obtain ⟨t, rfl, ht⟩ := hy
      refine ⟨rfl, rfl, pt_mem_unitSet, ?_⟩
      show majOf [t] ∈ˢ app (Cr V _ c) pt
      rw [app_Cr _ _ pt_mem_unitSet]
      show ([t] : List V).reverse.headD pt ∈ˢ (unitSet : V)
      simpa using ht)
    (by intro c _ ys _; rfl)

/-- The recursor's type at this family. -/
def recTy (ℓ : Nat) (c : Nat) : AnnotTerm := mkPisAV (rds ℓ c) punit0

theorem interp_recTy (ℓ : Nat) (ρ : Nat → V) (c : Nat) :
    interp V ρ (recTy ℓ c) = piR ℓ (unitSet : V) fun _ => unitSet := rfl

/-- **The falsifier's premise**, complete: the types are formed at
`univ ℓ`, the ι equations are graded, and the WF regime supplies the
candidate. -/
theorem pre (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    BlockRecPre V ℓ 1 (recTy ℓ) (falsEqs 1 (fun _ => []) (fun _ _ => .prf)) ρ where
  hTy := by
    intro c _
    exact ⟨by rw [interp_recTy]; exact punitArrow_mem_univ ℓ hℓ,
      by show WellDenoted V ρ (.pi ℓ ℓ punit0 punit0)
         rw [WellDenoted_pi]
         exact ⟨trivial, fun _ _ => trivial⟩⟩
  hEq := by
    refine hEq_iotaEqsAV_of fun rs hlen hmem c hc j _ => ⟨trivial, fun ys hsp => ?_⟩
    have hys : ys = [] := by
      have h : ys.length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
      exact List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hys
    have hc0 : c = 0 := by omega
    subst hc0
    refine ⟨?_, trivial⟩
    show WellDenoted V (consList rs ρ) (.app (.bvar 0) .prf)
    refine WellDenoted_app_of V (u := ℓ) (v := ℓ) (Aa := punit0) (Ba := punit0) trivial trivial
      ?_ pt_mem_unitSet (fun h0 => absurd h0 hℓ)
    show consList rs ρ 0 ∈ˢ interp V (consList rs ρ) (recTy ℓ 0)
    rw [consList_getD_of_lt _ _ _ (by omega), hlen]
    exact hmem 0 (by omega)
  hCand := by
    refine famCand_hCand (data ℓ ρ) hℓ (fun c _ => rfl) (fun c _ d hd => ?_) (fun _ _ => rfl)
      (fun c _ j _ xs fs _ hsp => ?_) (fun c _ j _ xs fs _ _ => rfl)
    · rw [show d = (ℓ, ℓ, punit0) from by simpa [rds] using hd]
    · have h : (xs ++ fs).length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
      simp only [List.length_append, List.length_nil, Nat.add_zero] at h
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hf : fs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hx; subst hf
      exact ⟨pt_mem_unitSet, trivial⟩

/-- **THE FALSIFIER**: at `K = 1`, regime WF, the leaf is typed, graded
and satisfies its rule's ι law. -/
theorem facts (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 1 → a c ∈ˢ interp V ρ (recTy ℓ c) ∧
        interp V ρ (blockRecAV ℓ 1 (recTy ℓ) (falsEqs 1 (fun _ => []) (fun _ _ => .prf)) c)
          = a c ∧
        WellDenoted V ρ
          (blockRecAV ℓ 1 (recTy ℓ) (falsEqs 1 (fun _ => []) (fun _ _ => .prf)) c)) ∧
      ∀ c, c < 1 → SetTheory.app (a c) pt = (pt : V) := by
  obtain ⟨a, ha, hiota⟩ := blockRecAV_iota (pre ℓ hℓ ρ)
  refine ⟨a, ha, fun c hc => ?_⟩
  have h := hiota c hc 0 (by omega) [] [] rfl trivial
  simpa using h

end FalsWf

/-! ## Falsifier 2 — ONE member, TWO recursors -/

namespace FalsTwo

variable (V)

/-- Both recursors' index set and carrier: they are recursors of the
SAME member, so the carrier is the same. -/
noncomputable def Is (_ : List V) (_ : Nat) : V := unitSet

noncomputable def Cr (_ : List V) (_ : Nat) : V := graph (fun _ => (unitSet : V)) unitSet

variable {V}

theorem app_Cr (xs : List V) (c : Nat) {i : V} (hi : i ∈ˢ (unitSet : V)) :
    app (Cr V xs c) i = (unitSet : V) := app_graph hi

/-- DIFFERENT conclusions at the SAME level (D-d): `PUnit` for the
first recursor, `PUnit → PUnit` for the second. -/
def concl (ℓ c : Nat) : AnnotTerm := if c = 0 then punit0 else .pi ℓ ℓ punit0 punit0

/-- DIFFERENT rule prefixes on the same member: the first recursor has
none, the second has one binder (what official would fill with a
motive or a minor — the route never looks inside). -/
def rP (c : Nat) : Nat := if c = 0 then 0 else 1

/-- The binder data: prefix, then the major. -/
def rds (ℓ c : Nat) : List (Nat × Nat × AnnotTerm) :=
  if c = 0 then [(ℓ, ℓ, punit0)] else [(ℓ, ℓ, punit0), (ℓ, ℓ, punit0)]

/-- The rules' λ-prefix domains, per class. -/
def pdoms (c : Nat) : List AnnotTerm := if c = 0 then [] else [punit0]

/-- The residues: the point for the first recursor, the constant
function for the second — each in its own conclusion. -/
def Rb (ℓ c : Nat) (_ : Nat) : AnnotTerm := if c = 0 then .prf else .lam ℓ punit0 .prf

@[simp] theorem concl_zero (ℓ : Nat) : concl ℓ 0 = punit0 := if_pos rfl
@[simp] theorem concl_one (ℓ : Nat) : concl ℓ 1 = .pi ℓ ℓ punit0 punit0 := if_neg (by omega)
@[simp] theorem rP_zero : rP 0 = 0 := if_pos rfl
@[simp] theorem rP_one : rP 1 = 1 := if_neg (by omega)
@[simp] theorem rds_zero (ℓ : Nat) : rds ℓ 0 = [(ℓ, ℓ, punit0)] := if_pos rfl
@[simp] theorem rds_one (ℓ : Nat) :
    rds ℓ 1 = [(ℓ, ℓ, punit0), (ℓ, ℓ, punit0)] := if_neg (by omega)
@[simp] theorem pdoms_zero : pdoms 0 = [] := if_pos rfl
@[simp] theorem pdoms_one : pdoms 1 = [punit0] := if_neg (by omega)
@[simp] theorem Rb_zero (ℓ j : Nat) : Rb ℓ 0 j = .prf := if_pos rfl
@[simp] theorem Rb_one (ℓ j : Nat) : Rb ℓ 1 j = .lam ℓ punit0 .prf := if_neg (by omega)

/-- The motive, by CLASS: the two recursors' conclusions.  The
carriers are singletons, so class `0`'s only tagged index is
`tagged 0 pt pt` and the test needs no decoder. -/
noncomputable def B (ℓ : Nat) (u : V) : V :=
  open Classical in
  if u = tagged 0 (pt : V) pt then unitSet else piR ℓ (unitSet : V) fun _ => unitSet

/-- The step, by class. -/
noncomputable def st (ℓ : Nat) (u : V) (_ : V) : V :=
  open Classical in
  if u = tagged 0 (pt : V) pt then pt else lamR ℓ (unitSet : V) fun _ => pt

noncomputable def kit (ℓ : Nat) (hℓ : ℓ ≠ 0) (xs : List V) :
    WfRecKit ℓ 2 (Is V xs) (Cr V xs) where
  B := B ℓ
  st := st ℓ
  hB := by
    intro u _
    by_cases h : u = tagged 0 (pt : V) pt
    · rw [B, if_pos h]; exact unitSet_mem_univ ℓ
    · rw [B, if_neg h]; exact punitArrow_mem_univ ℓ hℓ
  hst := by
    intro u _ g _
    by_cases h : u = tagged 0 (pt : V) pt
    · rw [B, st, if_pos h, if_pos h]; exact pt_mem_unitSet
    · rw [B, st, if_neg h, if_neg h]
      exact lamR_mem fun _ _ => pt_mem_unitSet

/-- The regime's data. -/
noncomputable def data (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    RecFamData V ℓ 2 rP (rds ℓ) (concl ℓ) ρ :=
  wfData (Is V) (Cr V) (fun _ _ => pt) (kit ℓ hℓ)
    (by
      intro c hc ys hsp
      match c, hc with
      | 0, _ =>
        rw [rds_zero] at hsp
        have hy : ∃ t : V, ys = [t] ∧ t ∈ˢ (unitSet : V) := by
          match ys, hsp with
          | [t], h => exact ⟨t, rfl, h.1⟩
        obtain ⟨t, rfl, ht⟩ := hy
        rw [rP_zero]
        refine ⟨rfl, rfl, pt_mem_unitSet, ?_⟩
        show majOf [t] ∈ˢ app (Cr V _ 0) pt
        rw [app_Cr _ _ pt_mem_unitSet]
        show ([t] : List V).reverse.headD pt ∈ˢ (unitSet : V)
        simpa using ht
      | 1, _ =>
        rw [rds_one] at hsp
        have hy : ∃ p t : V, ys = [p, t] ∧ p ∈ˢ (unitSet : V) ∧ t ∈ˢ (unitSet : V) := by
          match ys, hsp with
          | [p, t], h => exact ⟨p, t, rfl, h.1, h.2.1⟩
        obtain ⟨p, t, rfl, -, ht⟩ := hy
        rw [rP_one]
        refine ⟨rfl, rfl, pt_mem_unitSet, ?_⟩
        show majOf [p, t] ∈ˢ app (Cr V _ 1) pt
        rw [app_Cr _ _ pt_mem_unitSet]
        show ([p, t] : List V).reverse.headD pt ∈ˢ (unitSet : V)
        simpa using ht)
    (by
      intro c hc ys hsp
      match c, hc with
      | 0, _ =>
        rw [rds_zero] at hsp
        have hy : ∃ t : V, ys = [t] ∧ t = (pt : V) := by
          match ys, hsp with
          | [t], h => exact ⟨t, rfl, mem_unitSet_iff.mp h.1⟩
        obtain ⟨t, rfl, rfl⟩ := hy
        show B ℓ (tagged 0 (pt : V) (majOf [(pt : V)])) = _
        have hm : majOf [(pt : V)] = (pt : V) := by simp [majOf]
        rw [hm, B, if_pos rfl, concl_zero]
        rfl
      | 1, _ =>
        show B ℓ (tagged 1 (pt : V) _) = _
        rw [B, if_neg (tagged_ne_zero (by omega) _ _), concl_one]
        rfl)

/-- The data's step, by class. -/
theorem data_st (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) (xs : List V) (c : Nat) (g : V) :
    ((data ℓ hℓ ρ).kit xs).st (tagged c (pt : V) pt) g
      = if c = 0 then (pt : V) else lamR ℓ (unitSet : V) fun _ => pt := by
  show st ℓ (tagged c (pt : V) pt) g = _
  rw [st]
  by_cases hc : c = 0
  · subst hc; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (tagged_ne_zero hc _ _), if_neg hc]

/-- The recursors' types. -/
def recTy (ℓ : Nat) (c : Nat) : AnnotTerm := mkPisAV (rds ℓ c) (concl ℓ c)

theorem interp_recTy_zero (ℓ : Nat) (ρ : Nat → V) :
    interp V ρ (recTy ℓ 0) = piR ℓ (unitSet : V) fun _ => unitSet := by
  show interp V ρ (mkPisAV (rds ℓ 0) (concl ℓ 0)) = _
  rw [rds_zero, concl_zero]
  simp only [mkPisAV]
  rfl

theorem interp_recTy_one (ℓ : Nat) (ρ : Nat → V) :
    interp V ρ (recTy ℓ 1)
      = piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V)
          fun _ => unitSet := by
  show interp V ρ (mkPisAV (rds ℓ 1) (concl ℓ 1)) = _
  rw [rds_one, concl_one]
  simp only [mkPisAV]
  rfl

theorem wd_recTy (ℓ : Nat) (ρ : Nat → V) (c : Nat) (hc : c < 2) :
    WellDenoted V ρ (recTy ℓ c) := by
  match c, hc with
  | 0, _ =>
    show WellDenoted V ρ (mkPisAV (rds ℓ 0) (concl ℓ 0))
    rw [rds_zero, concl_zero]
    simp only [mkPisAV]
    rw [WellDenoted_pi]
    exact ⟨trivial, fun _ _ => trivial⟩
  | 1, _ =>
    show WellDenoted V ρ (mkPisAV (rds ℓ 1) (concl ℓ 1))
    rw [rds_one, concl_one]
    simp only [mkPisAV]
    rw [WellDenoted_pi]
    refine ⟨trivial, fun x _ => ?_⟩
    rw [WellDenoted_pi]
    refine ⟨trivial, fun y _ => ?_⟩
    rw [WellDenoted_pi]
    exact ⟨trivial, fun _ _ => trivial⟩

/-- **The falsifier's premise**, complete at ONE member with TWO
recursors. -/
theorem pre (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    BlockRecPre V ℓ 2 (recTy ℓ) (falsEqs 2 pdoms (Rb ℓ)) ρ where
  hTy := by
    intro c hc
    refine ⟨?_, wd_recTy ℓ ρ c hc⟩
    match c, hc with
    | 0, _ => rw [interp_recTy_zero]; exact punitArrow_mem_univ ℓ hℓ
    | 1, _ =>
      rw [interp_recTy_one]
      have h2 : (piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V) fun _ => unitSet)
          ∈ˢ (univ ℓ : V) := by
        have := piR_mem_univ (V := V) (u := ℓ) (v := ℓ) (A := unitSet)
          (B := fun _ => piR ℓ (unitSet : V) fun _ => unitSet)
          (unitSet_mem_univ ℓ) fun _ _ => punitArrow_mem_univ ℓ hℓ
        rwa [if_neg hℓ, natMax_self] at this
      have := piR_mem_univ (V := V) (u := ℓ) (v := ℓ) (A := unitSet)
        (B := fun _ => piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V) fun _ => unitSet)
        (unitSet_mem_univ ℓ) fun _ _ => h2
      rwa [if_neg hℓ, natMax_self] at this
  hEq := by
    refine hEq_iotaEqsAV_of fun rs hlen hmem c hc j _ => ?_
    match c, hc with
    | 0, _ =>
      refine ⟨by rw [pdoms_zero]; trivial, fun ys hsp => ?_⟩
      rw [pdoms_zero] at hsp ⊢
      have hys : ys = [] := by
        have h : ys.length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
        exact List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hys
      refine ⟨?_, by rw [Rb_zero]; trivial⟩
      show WellDenoted V (consList rs ρ) (.app (.bvar 1) .prf)
      refine WellDenoted_app_of V (u := ℓ) (v := ℓ) (Aa := punit0) (Ba := punit0) trivial trivial
        ?_ pt_mem_unitSet (fun h0 => absurd h0 hℓ)
      have h0 := hmem 0 (by omega)
      rw [interp_recTy_zero] at h0
      show consList rs ρ 1 ∈ˢ (piR ℓ (unitSet : V) fun _ => unitSet)
      rw [consList_getD_of_lt _ _ _ (by omega), hlen]
      exact h0
    | 1, _ =>
      refine ⟨by rw [pdoms_one]; exact ⟨trivial, fun h => absurd rfl h, fun _ _ => trivial⟩,
        fun ys hsp => ?_⟩
      rw [pdoms_one] at hsp ⊢
      have hys : ∃ p : V, ys = [p] ∧ p ∈ˢ (unitSet : V) := by
        match ys, hsp with
        | [p], h => exact ⟨p, rfl, h.1⟩
      obtain ⟨p, rfl, hp⟩ := hys
      have hmem1 : consList rs ρ 0
          ∈ˢ (piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V) fun _ => piR ℓ (unitSet : V)
              fun _ => unitSet) := by
        have h1 := hmem 1 (by omega)
        rw [interp_recTy_one] at h1
        rw [consList_getD_of_lt _ _ _ (by omega), hlen]
        exact h1
      have hinner : interp V (consList [p] (consList rs ρ)) (.bvar 1)
          ∈ˢ interp V (consList [p] (consList rs ρ))
            (.pi ℓ ℓ punit0 (.pi ℓ ℓ punit0 (.pi ℓ ℓ punit0 punit0))) := hmem1
      have hp' : interp V (consList [p] (consList rs ρ)) (.bvar 0) ∈ˢ (unitSet : V) := hp
      refine ⟨?_, ?_⟩
      · show WellDenoted V (consList [p] (consList rs ρ)) (.app (.app (.bvar 1) (.bvar 0)) .prf)
        refine WellDenoted_app_of V (u := ℓ) (v := ℓ) (Aa := punit0)
          (Ba := .pi ℓ ℓ punit0 punit0)
          (WellDenoted_app_of V (u := ℓ) (v := ℓ) (Aa := punit0)
            (Ba := .pi ℓ ℓ punit0 (.pi ℓ ℓ punit0 punit0))
            trivial trivial hinner hp' (fun h0 => absurd h0 hℓ))
          trivial ?_ pt_mem_unitSet (fun h0 => absurd h0 hℓ)
        exact app_mem_piR_pos hℓ hinner hp'
      · rw [Rb_one]
        show WellDenoted V (consList [p] (consList rs ρ)) (.lam ℓ punit0 .prf)
        rw [WellDenoted_lam]
        exact ⟨trivial, fun _ _ => trivial, fun _ => unitSet, fun _ _ => pt_mem_unitSet,
          fun h0 => absurd h0 hℓ⟩
  hCand := by
    refine famCand_hCand (data ℓ hℓ ρ) hℓ (fun c _ => rfl) (fun c hc d hd => ?_)
      (fun c hc => ?_) (fun c hc j _ xs fs hxl hsp => ?_) (fun c hc j _ xs fs hxl hsp => ?_)
    · match c, hc with
      | 0, _ =>
        rw [rds_zero] at hd
        rw [show d = (ℓ, ℓ, punit0) from by simpa using hd]
      | 1, _ =>
        rw [rds_one] at hd
        rw [show d = (ℓ, ℓ, punit0) from by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with h | h <;> exact h]
    · match c, hc with
      | 0, _ => rw [pdoms_zero, rP_zero]; rfl
      | 1, _ => rw [pdoms_one, rP_one]; rfl
    · match c, hc with
      | 0, _ =>
        rw [pdoms_zero] at hsp hxl
        have h : (xs ++ fs).length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
        simp only [List.length_append, List.length_nil, Nat.add_zero] at h
        have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hf : fs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hx; subst hf
        rw [rds_zero]
        exact ⟨pt_mem_unitSet, trivial⟩
      | 1, _ =>
        rw [pdoms_one] at hsp hxl
        have hxf : ∃ p : V, xs = [p] ∧ fs = [] ∧ p ∈ˢ (unitSet : V) := by
          match xs, fs, hsp, hxl with
          | [p], [], hs, _ => exact ⟨p, rfl, rfl, hs.1⟩
        obtain ⟨p, rfl, rfl, hp⟩ := hxf
        rw [rds_one]
        exact ⟨hp, pt_mem_unitSet, trivial⟩
    · match c, hc with
      | 0, _ =>
        show ((data ℓ hℓ ρ).kit xs).st (tagged 0 (pt : V) pt) _ = _
        rw [data_st, if_pos rfl, Rb_zero]
        rfl
      | 1, _ =>
        show ((data ℓ hℓ ρ).kit xs).st (tagged 1 (pt : V) pt) _ = _
        rw [data_st, if_neg (by omega), Rb_one]
        rfl

/-- **THE FALSIFIER** at one member with two recursors: both leaves are
typed and graded, and each rule's ι law holds at its OWN prefix. -/
theorem facts (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 2 → a c ∈ˢ interp V ρ (recTy ℓ c) ∧
        interp V ρ (blockRecAV ℓ 2 (recTy ℓ) (falsEqs 2 pdoms (Rb ℓ)) c) = a c ∧
        WellDenoted V ρ (blockRecAV ℓ 2 (recTy ℓ) (falsEqs 2 pdoms (Rb ℓ)) c)) ∧
      SetTheory.app (a 0) pt = (pt : V) ∧
      ∀ p : V, p ∈ˢ (unitSet : V) →
        SetTheory.app (SetTheory.app (a 1) p) pt = lamR ℓ (unitSet : V) fun _ => pt := by
  obtain ⟨a, ha, hiota⟩ := blockRecAV_iota (pre ℓ hℓ ρ)
  refine ⟨a, ha, ?_, fun p hp => ?_⟩
  · have h := hiota 0 (by omega) 0 (by omega) [] []
      (by rw [pdoms_zero]; rfl) (by rw [pdoms_zero]; trivial)
    simpa [interp_punit0] using h
  · have h := hiota 1 (by omega) 0 (by omega) [p] [] (by rw [pdoms_one]; rfl)
      (by rw [pdoms_one]; exact ⟨hp, trivial⟩)
    simpa [interp_punit0] using h

end FalsTwo

/-! ## Falsifier 3 — `K = 2`, regime IND -/

namespace FalsInd

/-- Both classes' recursor type: `PUnit → PUnit` at `Prop`. -/
def recTy (_ : Nat) : AnnotTerm := mkPisAV [(0, 0, punit0)] punit0

theorem interp_recTy (ρ : Nat → V) (c : Nat) :
    interp V ρ (recTy c) = piR 0 (unitSet : V) fun _ => unitSet := rfl

theorem pt_mem_recTy (ρ : Nat → V) (c : Nat) : (pt : V) ∈ˢ interp V ρ (recTy c) := by
  rw [interp_recTy]
  exact pt_mem_piR_zero_of fun _ _ => pt_mem_unitSet

/-- **The falsifier's `hCand`** at the MUTUAL shape: the IND regime
delivers the constant-point candidate, and the chain's two components
are read at `bvar 1` and `bvar 0`. -/
theorem hCand (ρ : Nat → V) :
    ∃ a : Nat → V, (∀ c, c < 2 → a c ∈ˢ interp V ρ (recTy c)) ∧
      ∀ e ∈ falsEqs 2 (fun _ => []) (fun _ _ => .prf),
        (pt : V) ∈ˢ interp V (chainFrame 2 a ρ) e :=
  indCand_hCand (fun c _ => pt_mem_recTy ρ c)
    fun _ _ _ _ _ _ _ _ => ⟨unitSet, unitSet_mem_univZero, pt_mem_unitSet⟩

/-- **The falsifier's premise**, complete at the MUTUAL shape. -/
theorem pre (ρ : Nat → V) :
    BlockRecPre V 0 2 recTy (falsEqs 2 (fun _ => []) (fun _ _ => .prf)) ρ where
  hTy := by
    intro c _
    refine ⟨?_, ?_⟩
    · rw [interp_recTy]
      have := piR_mem_univ (V := V) (u := 0) (v := 0) (A := unitSet) (B := fun _ => unitSet)
        (unitSet_mem_univ 0) fun _ _ => unitSet_mem_univ 0
      rwa [if_pos rfl] at this
    · show WellDenoted V ρ (.pi 0 0 punit0 punit0)
      rw [WellDenoted_pi]
      exact ⟨trivial, fun _ _ => trivial⟩
  hEq := by
    refine hEq_iotaEqsAV_of fun rs hlen hmem c hc j _ => ⟨trivial, fun ys hsp => ?_⟩
    have hys : ys = [] := by
      have h : ys.length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
      exact List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hys
    refine ⟨?_, trivial⟩
    show WellDenoted V (consList rs ρ) (.app (.bvar (0 + 0 + (2 - 1 - c))) .prf)
    refine WellDenoted_app_of V (u := 0) (v := 0) (Aa := punit0) (Ba := punit0) trivial trivial
      ?_ pt_mem_unitSet (fun _ _ _ => unitSet_mem_univZero)
    show consList rs ρ (0 + 0 + (2 - 1 - c)) ∈ˢ interp V (consList rs ρ) (recTy c)
    rw [show 0 + 0 + (2 - 1 - c) = 2 - 1 - c from by omega,
      consList_getD_of_lt _ _ _ (by omega), hlen,
      show 2 - 1 - (2 - 1 - c) = c from by omega]
    exact hmem c hc
  hCand := hCand ρ

/-- **THE FALSIFIER** at `K = 2`: both leaves are typed, graded, and
both ι laws hold. -/
theorem facts (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 2 → a c ∈ˢ interp V ρ (recTy c) ∧
        interp V ρ (blockRecAV 0 2 recTy (falsEqs 2 (fun _ => []) (fun _ _ => .prf)) c) = a c ∧
        WellDenoted V ρ
          (blockRecAV 0 2 recTy (falsEqs 2 (fun _ => []) (fun _ _ => .prf)) c)) ∧
      ∀ c, c < 2 → SetTheory.app (a c) pt = (pt : V) := by
  obtain ⟨a, ha, hiota⟩ := blockRecAV_iota (pre ρ)
  refine ⟨a, ha, fun c hc => ?_⟩
  have h := hiota c hc 0 (by omega) [] [] rfl trivial
  simpa using h

end FalsInd

end ConLeche.Semantics
