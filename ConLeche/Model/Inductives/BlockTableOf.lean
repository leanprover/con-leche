module

public import ConLeche.Model.Inductives.BlockTableMember
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockRecKit
import ConLeche.Model.Inductives.StructStageCtor
public section

/-!
# The table bundle's set-level content, from the datum (task #315, M4 s5)

At a STRUCTURE-LIKE member (one constructor, no index) the flat table
bundle's three set-level clauses (`TableMember.fold`, `.fib`, `.ctor`)
are the datum's own clauses read at the empty index tuple: the
carrier is the member's `lfpTuple` component there (`tableCarrier`),
its members decode by `BlockRep.fibre` at the tuple's own value
(`carrier_app_eq`) into the one constructor's injections of fitting
spines (`spineFit_of_fitsFrom`), and the injection is the tagged tower
at the constructor's global position (`MutualTableFacts.inj`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **A member's carrier at a parameter frame**, at the empty index
tuple (the structure-like member's only one). -/
@[expose] noncomputable def BlockRepData.tableCarrier (d : BlockRepData V) (mm : Nat)
    (ψ : Name → Nat) (ρ' : Nat → V) : V :=
  SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρ') (d.Φ ψ ρ') mm) (d.tup ψ mm [])

namespace BlockRep

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockRepData V} {mm : Nat}
  (h : BlockRep m T cvT cvR mI rP rules d mm)
include h

/-- At an index-free member the empty tuple is an index tuple. -/
theorem tup_nil_mem (hnI : d.nIdxAt mm = 0) (ψ : Name → Nat) (ρ' : Nat → V) :
    d.tup ψ mm [] ∈ˢ d.idx ψ ρ' mm := by
  have hnil : d.IdsM mm ψ = [] :=
    List.eq_nil_of_length_eq_zero (by rw [h.IdsM_length, hnI])
  show tupW _ [] ∈ˢ idxSet _ ρ' (d.IdsM mm ψ)
  rw [hnil]
  exact tupW_mem trivial

/-- **The bundle's `fold`**: the member at a fitting spine of its own
parameter telescope is the carrier at the spine's frame. -/
theorem table_fold (hreps : BlockReps m d)
    (hframe : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM mm ψ).take d.nP).map (·.2.2)).reverse ρ ↔ Sat V (d.params ψ).reverse ρ)
    (hnI : d.nIdxAt mm = 0) (ψ : Name → Nat) (ρ : Nat → V) (ts : List V)
    (hsp : SpineFit ρ ((d.ppsM mm ψ).map (·.2.2)) ts) :
    ts.foldl SetTheory.app (interp V ρ (m.acval T ψ)) = d.tableCarrier mm ψ (consList ts ρ) := by
  have hlen : (d.ppsM mm ψ).length = d.nP := by rw [h.ppsM_length, hnI, Nat.add_zero]
  have htake : (d.ppsM mm ψ).take d.nP = d.ppsM mm ψ := List.take_of_length_le (Nat.le_of_eq hlen)
  have hk : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le _) h.memberLt
  have hspP : SpineFit ρ (d.params ψ) ts := by
    refine (spineFit_iff_of_sat_iff ?_ (fun ρ' => ?_) ρ ts ?_).mp hsp
    · rw [List.length_map, hlen, hreps.params_length hk]
    · have hf := hframe ψ ρ'
      rw [htake] at hf
      exact hf
    · rw [hsp.length_eq, List.length_map]
  have hnil : d.IdsM mm ψ = [] :=
    List.eq_nil_of_length_eq_zero (by rw [h.IdsM_length, hnI])
  have := h.leaf ψ ρ ts [] hspP (by rw [hnil]; trivial)
  rw [List.append_nil] at this
  exact this

/-- **The bundle's `ctor`**: the one constructor at fitting parameters
and fields is the tagged tower injection. -/
theorem table_ctor (hreps : BlockReps m d) {cA : ConstantVal × Nat} (hone : d.ctorsM mm = [cA])
    {ψ : Name → Nat} {J : Nat}
    (hinj : ∀ fs : List V, d.inj ψ mm 0 fs = injW (d.w ψ) J (mkTower (fs ++ [pt])))
    (ρ : Nat → V) (as fs : List V)
    (hspP : SpineFit ρ (((d.dsF mm 0 ψ).take d.nP).map (·.2.2)) as)
    (hspF : SpineFit (consList as ρ) (((d.dsF mm 0 ψ).drop d.nP).map (·.2.2)) fs) :
    (as ++ fs).foldl SetTheory.app (interp V ρ (m.acval cA.1.name ψ))
      = injW (d.w ψ) J (mkTower (fs ++ [pt])) := by
  have hj : (d.ctorsM mm)[0]? = some cA := by rw [hone]; rfl
  have hk : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le _) h.memberLt
  have hlen₁ : (((d.dsF mm 0 ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, (h.ctorData hj).len]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hspP' : SpineFit ρ (d.params ψ) as :=
    (spineFit_iff_of_sat_iff (by rw [hlen₁, hreps.params_length hk])
      (fun ρ' => (h.paramsIff mm 0 cA h.memberLt hj ψ ρ').symm) ρ as
      (by rw [hspP.length_eq, hlen₁])).mp hspP
  rw [← hinj]
  exact h.ctor mm 0 cA h.memberLt hj ψ ρ as fs hspP' (by rw [BlockRep.Fss_getD hj]; exact hspF)

end BlockRep

/-- **The bundle's `fib`**: at a structure-like member the carrier's
members are the one constructor's injections of fitting field spines
— the datum's `fibre` at the tuple's own value, decoded by
`spineFit_of_fitsFrom` — and the injection is the tagged tower. -/
theorem BlockReps.table_fibreAt {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {mm : Nat} (hmm : mm < d.k)
    {cA : ConstantVal × Nat} (hone : d.ctorsM mm = [cA]) (hnI : d.nIdxAt mm = 0) {J : Nat}
    (hinj : ∀ fs : List V, d.inj ψ mm 0 fs = injW (d.w ψ) J (mkTower (fs ++ [pt])))
    {ρ' : Nat → V} (hρ' : Sat V (((d.dsF mm 0 ψ).take d.nP).map (·.2.2)).reverse ρ') :
    FibreAt (d.w ψ) J (((d.dsF mm 0 ψ).drop d.nP).map (·.2.2)) ρ' (d.tableCarrier mm ψ ρ') := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mm hmm
  have hj : (d.ctorsM mm)[0]? = some cA := by rw [hone]; rfl
  have hρp : Sat V (d.params ψ).reverse ρ' := (h.paramsIff mm 0 cA hmm hj ψ ρ').mpr hρ'
  have ht := h.tup_nil_mem hnI ψ ρ'
  have key : ∀ x : V, x ∈ˢ d.tableCarrier mm ψ ρ' →
      ∃ fs : List V, SpineFit ρ' (((d.dsF mm 0 ψ).drop d.nP).map (·.2.2)) fs ∧
        x = d.inj ψ mm 0 fs := by
    intro x hx
    unfold BlockRepData.tableCarrier at hx
    rw [← h.carrier_app_eq hρp hmm ht] at hx
    obtain ⟨j, fs, hjlt, hfit, rfl⟩ :=
      (h.fibre ψ ρ' hρp _ (lfpTuple_mem _ _ _ _) mm hmm _ ht _).mp hx
    have hj0 : j = 0 := by
      rw [hone, List.length_singleton] at hjlt
      exact Nat.lt_one_iff.mp hjlt
    subst hj0
    refine ⟨fs, ?_, rfl⟩
    have := hreps.spineFit_of_fitsFrom hfT hmm hj hρp (TupleLe.refl _ _ _) hfit.1
    rwa [BlockRep.Fss_getD hj] at this
  refine ⟨fun hw x hx => ?_, fun hw x hx => ?_⟩
  · obtain ⟨fs, hsp, rfl⟩ := key x hx
    exact ⟨fs, by rw [hinj, injW_pos hw], hsp⟩
  · obtain ⟨fs, hsp, rfl⟩ := key x hx
    exact ⟨h.mkZero ψ hw mm 0 fs, fs, hsp⟩

end ConLeche.Model
