module

public import ConLeche.Semantics.Tower.BlockRecWfI
import ConLeche.Semantics.Tower.BlockRecIndI
import ConLeche.Semantics.Univ
@[expose] public section

/-!
# The recursor family's leaf, INSTANTIATED (falsifier, task #315, M5 model half)

The two generic theorems of `BlockRecI`/`BlockRecWfI`/`BlockRecIndI`
are worth nothing if their premises cannot be met together.  This file
meets them, end to end, at the two shapes the design cares about:

* **`K = 1`, regime WF** (`ℓ ≠ 0`): one class, no prefix, no indices,
  the carrier a one-element set, one constructor with no fields — the
  `Nat`-like skeleton with the recursion stripped to its smallest
  instance.  A real `WfRecKit` is built (`hB`/`hst` discharged), and
  the ι law comes out as `app (rec) t = <the residue>`.
* **`K = 2`, regime IND** (`ℓ = 0`): two classes, a `Prop`-valued
  recursor type each, one rule each — the MUTUAL shape, which is what
  exercises the chain's arithmetic (class `c`'s component is
  `bvar (K-1-c)`, so `c = 0` and `c = 1` read different binders).

Both end at `blockRecAV_facts`/`blockRecAV_iota`: the leaf is typed,
graded, and satisfies every rule's ι equation.  The point of the
exercise is that the PREMISES compose — `WfRecData`'s two readings
with the kit's two obligations in WF, the induction principle with
G1's typing in IND — not that these particular families are
interesting.
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

/-- Both falsifiers' ι equations: one class per `c < K`, one rule
each, no prefix, no fields, no indices, the constructed major and the
residue both the proof point. -/
def falsEqs (K : Nat) : List AnnotTerm :=
  iotaEqsAV K (fun _ => 1) (fun _ => []) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ => .prf) (fun _ _ => []) (fun _ _ => .prf)

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
    WfRecData V ℓ 1 0 (rds ℓ) (fun _ => punit0) ρ where
  Is := Is V
  Cr := Cr V
  tupOf := fun _ _ => pt
  kit := kit ℓ
  hsplit := by
    intro c _ ys hsp
    have : ∃ t : V, ys = [t] ∧ t ∈ˢ (unitSet : V) := by
      match ys, hsp with
      | [t], h => exact ⟨t, rfl, h.1⟩
    obtain ⟨t, rfl, ht⟩ := this
    refine ⟨rfl, rfl, pt_mem_unitSet, ?_⟩
    show majOf [t] ∈ˢ app (Cr V _ c) pt
    rw [app_Cr _ _ pt_mem_unitSet]
    show ([t] : List V).reverse.headD pt ∈ˢ (unitSet : V)
    simpa using ht
  hconcl := by
    intro c _ ys _
    rfl

/-- **The falsifier's `hCand`**: the WF regime delivers the candidate
at this family. -/
theorem hCand (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 1 → a c ∈ˢ interp V ρ (mkPisAV (rds ℓ c) punit0)) ∧
      ∀ e ∈ falsEqs 1, (pt : V) ∈ˢ interp V (chainFrame 1 a ρ) e := by
  refine wfCand_hCand (data ℓ ρ) hℓ (fun c _ => rfl) (fun c _ d hd => ?_) (fun _ _ => rfl)
    (fun c _ j _ xs fs _ hsp => ?_) (fun c _ j _ xs fs _ _ => rfl)
  · rw [show d = (ℓ, ℓ, punit0) from by simpa [rds] using hd]
  · have h : (xs ++ fs).length = ([] ++ [] : List AnnotTerm).length := hsp.length_eq
    simp only [List.length_append, List.length_nil, Nat.add_zero] at h
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hf : fs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx; subst hf
    exact ⟨pt_mem_unitSet, trivial⟩

/-- The recursor's type at this family. -/
def recTy (ℓ : Nat) (c : Nat) : AnnotTerm := mkPisAV (rds ℓ c) punit0

theorem interp_recTy (ℓ : Nat) (ρ : Nat → V) (c : Nat) :
    interp V ρ (recTy ℓ c) = piR ℓ (unitSet : V) fun _ => unitSet := rfl

/-- **The falsifier's premise**, complete: the types are formed at
`univ ℓ`, the ι equations are graded, and the WF regime supplies the
candidate. -/
theorem pre (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    BlockRecPre V ℓ 1 (recTy ℓ) (falsEqs 1) ρ where
  hTy := by
    intro c _
    refine ⟨?_, ?_⟩
    · rw [interp_recTy]
      have := piR_mem_univ (V := V) (u := ℓ) (v := ℓ) (A := unitSet) (B := fun _ => unitSet)
        (unitSet_mem_univ ℓ) fun _ _ => unitSet_mem_univ ℓ
      rwa [if_neg hℓ, natMax_self] at this
    · show WellDenoted V ρ (.pi ℓ ℓ punit0 punit0)
      rw [WellDenoted_pi]
      exact ⟨trivial, fun _ _ => trivial⟩
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
  hCand := hCand ℓ hℓ ρ

/-- **THE FALSIFIER**: at `K = 1`, regime WF, the leaf is typed, graded
and satisfies its rule's ι law — `app (rec) pt = pt` at this family. -/
theorem facts (ℓ : Nat) (hℓ : ℓ ≠ 0) (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 1 → a c ∈ˢ interp V ρ (recTy ℓ c) ∧
        interp V ρ (blockRecAV ℓ 1 (recTy ℓ) (falsEqs 1) c) = a c ∧
        WellDenoted V ρ (blockRecAV ℓ 1 (recTy ℓ) (falsEqs 1) c)) ∧
      ∀ c, c < 1 → SetTheory.app (a c) pt = (pt : V) := by
  obtain ⟨a, ha, hiota⟩ := blockRecAV_iota (pre ℓ hℓ ρ)
  refine ⟨a, ha, fun c hc => ?_⟩
  have h := hiota c hc 0 (by omega) [] [] rfl trivial
  simpa using h

end FalsWf

/-! ## Falsifier 2 — `K = 2`, regime IND -/

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
      ∀ e ∈ falsEqs 2, (pt : V) ∈ˢ interp V (chainFrame 2 a ρ) e :=
  indCand_hCand (fun c _ => pt_mem_recTy ρ c)
    fun _ _ _ _ _ _ _ _ => ⟨unitSet, unitSet_mem_univZero, pt_mem_unitSet⟩

/-- **The falsifier's premise**, complete at the MUTUAL shape. -/
theorem pre (ρ : Nat → V) :
    BlockRecPre V 0 2 recTy (falsEqs 2) ρ where
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
both ι laws hold — `app (rec_c) pt = pt`, with the two classes read at
`bvar 1` and `bvar 0`. -/
theorem facts (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ c, c < 2 → a c ∈ˢ interp V ρ (recTy c) ∧
        interp V ρ (blockRecAV 0 2 recTy (falsEqs 2) c) = a c ∧
        WellDenoted V ρ (blockRecAV 0 2 recTy (falsEqs 2) c)) ∧
      ∀ c, c < 2 → SetTheory.app (a c) pt = (pt : V) := by
  obtain ⟨a, ha, hiota⟩ := blockRecAV_iota (pre ρ)
  refine ⟨a, ha, fun c hc => ?_⟩
  have h := hiota c hc 0 (by omega) [] [] rfl trivial
  simpa using h

end FalsInd

end ConLeche.Semantics
