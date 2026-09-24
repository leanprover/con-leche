module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Semantics.Kit
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Semantics.Tower.BlockRecI
public section

/-!
# The block's lfp clause IN HOLE FORM, from the representation (lane HOLE2)

Charter item 2: every stored `I p⃗` is the least fixed point of its
right-hand-side operator — the interpretation of its constructor types
with holes at the block's members.  The clause the environment records
(`Model/Annot/BlockLfp.lean`) says so through `LfpClause.holes`: the fit
relation of the operator's fibre IS the telescope fit of the
constructors' fields with holes (`BlockData.absF`, `BlockRep.lean`) at
the hole frame (`LfpDatum.frame`: the parameter frame with each member's
hole holding the tuple's family, curried).

This file proves it for a uniform block from its representation
(`BlockModelAt`) and what the stages record of its constructors
(`BlockHoleFacts`: their reading facts, the stored field shape facts
`StoredFieldShapes`, and the telescopes' lengths): the holes occur only
applied to the parameters (`blockHolesApplied`, M3 — the flat shape's
`FlatShape.holeApp`), and the clause (`BlockModelAt.toLfp`) takes
`functor`, `fibre`, `leaf`, `mkZero`, `mkInj` from the representation
and `ctor` at the stored fit the hole fit at the carrier is.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames (moved from `BlockRecPreRun.lean`) -/

/-- **A frame's `k`-th entry, as a bvar.** -/
theorem interp_bvarAt {L : List V} {ρ : Nat → V} {k : Nat} (hk : k < L.length) :
    interp V (consList L ρ) (.bvar (L.length - 1 - k)) = L.getD k pt := by
  rw [interp_bvar, consList_getD_of_lt L ρ _ (by omega),
    show L.length - 1 - (L.length - 1 - k) = k from by omega]

/-- A prefix of a list, as its first entries. -/
theorem take_eq_map_getD : ∀ (L : List V) (n : Nat), n ≤ L.length →
    L.take n = (List.range n).map fun k => L.getD k pt := by
  intro L n hn
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  have hi : i < n := by
    have := h1
    simp only [List.length_take] at this
    omega
  rw [List.getElem_take, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- The parameter bvars read the frame's first `nP` entries. -/
theorem map_bvarAt_take {L : List V} {ρ : Nat → V} {nP D : Nat} (hD : D = L.length)
    (hnP : nP ≤ L.length) :
    (paramBvarsAt nP D).map (interp V (consList L ρ)) = L.take nP := by
  subst hD
  rw [take_eq_map_getD L nP hnP, paramBvarsAt, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  exact interp_bvarAt (by simpa using Nat.lt_of_lt_of_le (List.mem_range.mp hk) hnP)

/-! ## Reading below the holes -/

/-- **A term lifted over variables inserted below a spine** reads at the
frame with them as the term at the frame without. -/
theorem interp_liftN_consList2 (e : AnnotTerm) (bs hs : List V) (ρ : Nat → V) :
    interp V (consList bs (consList hs ρ)) (e.liftN hs.length bs.length)
      = interp V (consList bs ρ) e := by
  rw [interp_liftN, ConLeche.Semantics.shiftE_consList_len, shiftE_consList]

namespace BlockData

variable (d : BlockData V)

/-- The member holes' values at `(ψ, ρp, X)`: the hole frame is the
parameter frame with these above it. -/
@[expose] noncomputable def holeList (ψ : Name → Nat) (ρp X : Nat → V) : List V :=
  (List.range d.k).map (d.toLfp.holeVal ψ ρp X)

theorem toLfp_frame (ψ : Name → Nat) (ρp X : Nat → V) :
    d.toLfp.frame ψ ρp X = consList (d.holeList ψ ρp X) ρp := rfl

variable {d}

theorem holeList_length {ψ : Name → Nat} {ρp X : Nat → V} : (d.holeList ψ ρp X).length = d.k := by
  simp [holeList]

/-- **A member's hole, read above a spine**: the bvar at the hole's
position is the member's hole value. -/
theorem interp_hole_bvar {ψ : Name → Nat} {ρp X : Nat → V} {t : Nat} (ht : t < d.k) (L : List V) :
    interp V (consList L (consList (d.holeList ψ ρp X) ρp)) (.bvar (L.length + (d.k - 1 - t)))
      = d.toLfp.holeVal ψ ρp X t := by
  rw [interp_bvar, show L.length + (d.k - 1 - t) = (d.k - 1 - t) + L.length by omega,
    consList_apply_add, consList_getD_of_lt _ _ _ (by rw [holeList_length]; omega),
    holeList_length, show d.k - 1 - (d.k - 1 - t) = t by omega]
  simp [holeList, List.getD_eq_getElem?_getD, ht]

/-- **The parameter variables above the holes** read the parameter frame's
own values. -/
theorem map_paramBvars_holes {ψ : Name → Nat} {ρp X : Nat → V} (L : List V) :
    (paramBvarsAt d.nP (d.nP + d.k + L.length)).map
        (interp V (consList L (consList (d.holeList ψ ρp X) ρp)))
      = frameIdx d.nP ρp := by
  unfold paramBvarsAt frameIdx
  rw [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have := List.mem_range.mp hp
  simp only [Function.comp_def, interp_bvar]
  rw [show d.nP + d.k + L.length - 1 - p = (d.nP - 1 - p + d.k) + L.length by omega,
    consList_apply_add,
    show d.nP - 1 - p + d.k = (d.nP - 1 - p) + (d.holeList ψ ρp X).length by
      rw [holeList_length],
    consList_apply_add]

end BlockData

/-! ## The fit relation IS the hole fit -/

theorem take_succ_getD {α : Type} {Fs : List α} {i : Nat} (d : α) (hi : i < Fs.length) :
    Fs.take (i + 1) = Fs.take i ++ [Fs.getD i d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

/-! ## `ReadsHoles` and the clause -/

section Clause

variable {env : Env} {m : EnvModel V env} {names : List Name} {d : BlockData V} {lps : List Name}

/-- **What the clause's production reads off the stages** beside the
representation: every constructor's reading facts, the stored field
shape facts, and the lengths of the parameter telescope and of the
result index readings. -/
structure BlockHoleFacts (m : EnvModel V env) (d : BlockData V) (lps : List Name) : Prop where
  facts : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA → BlockCtorRead m d lps c j cA
  /-- the stored field shape facts: the fields with holes against the
  stored field readings, the members' leaves at the model (the ONE
  interface every reading of the fields' shape goes through) -/
  shapes : ∀ ψ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
    StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => m.acval (d.memberName t) ψ)
      (d.absF ψ c j) ((d.Fss c ψ).getD j [])
  lenP : ∀ ψ, (d.params ψ).length = d.nP
  /-- every member's own parameter telescope: `nP` long, satisfied where
  the block's is -/
  parsLen : ∀ ψ m, m < d.k → (d.toLfp.pars m ψ).length = d.nP
  parsSat : ∀ ψ m, m < d.k → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
    Sat V (d.toLfp.pars m ψ).reverse ρ
  parsSatInv : ∀ ψ m, m < d.k → ∀ ρ : Nat → V, Sat V (d.toLfp.pars m ψ).reverse ρ →
    Sat V (d.params ψ).reverse ρ
  lenE : ∀ ψ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
    ((d.Ess c ψ).getD j []).length = (d.IdsM c ψ).length

/-- A constructor's field readings number its fields. -/
theorem BlockCtorRead.nF {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hD : BlockCtorRead m d lps c j cA) (ψ : Name → Nat) :
    ((d.Fss c ψ).getD j []).length = cA.2 := by
  unfold BlockCtorRead at hD
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
  omega

/-! ## The holes occur only applied to the parameters (lane CONTSEM, M3) -/

/-- **A uniform block's fields with holes apply each hole to the
parameters** — the flat shape of the stored field shape facts
(`FlatShape.holeApp`). -/
theorem blockHolesApplied (hH : BlockHoleFacts m d lps) (ψ : Name → Nat) {c : Nat} (hc : c < d.N)
    {j : Nat} (hj : j < (d.ctorsM c).length) : d.toLfp.HolesApplied ψ c j := by
  have hS := hH.shapes ψ c hc j hj
  obtain ⟨rec, hrec⟩ := hS.flat
  refine ⟨fun l F hl => ?_, fun e he => ?_⟩
  · show HoleApp d.k (d.params ψ).length l F
    rw [hH.lenP ψ]
    exact hrec.holeApp l F hl
  · show HoleApp d.k (d.params ψ).length (d.absF ψ c j).length e
    obtain ⟨E, -, rfl⟩ := List.mem_map.mp he
    rw [hS.len]
    exact holeApp_liftN _ _ E _

/-- **The representation's lfp clause, in hole form** — `functor`,
`fibre`, `leaf`, `mkZero`, `mkInj` verbatim; `ctor` is the
representation's `ctor` at the stored fit the hole fit at the carrier is
(`BlockModelAt.carrier`). -/
theorem BlockModelAt.toLfp (hM : BlockModelAt m names d) (hH : BlockHoleFacts m d lps) :
    LfpClause m.acval d.toLfp where
  kN := Nat.le_add_right _ _
  functor := hM.functor
  fibre := hM.fibre
  fitsMono := hM.fitsMono
  leaf := hM.leaf
  mkZero := hM.mkZero
  mkInj := fun ψ hw c hc j fs j' fs' hj hj' hl hl' h =>
    hM.mkInj ψ hw c hc j fs j' fs' hj hj'
      (by rw [hl]; simp [BlockData.toLfp, BlockData.absF])
      (by rw [hl']; simp [BlockData.toLfp, BlockData.absF]) h
  ctor := fun c hc j ψ ρ as fs t hsa ht hf => by
    have hsat := d.satOfSpine hsa
    obtain ⟨hj, hsp, -⟩ := (hM.carrier ψ (consList as ρ) hsat c hc t ht j fs).mp hf
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    show (as ++ fs).foldl app (interp V ρ (m.acval ((d.ctorsM c).getD j default).1.name ψ))
      = d.inj ψ c j fs
    rw [List.getD_eq_getElem?_getD, hcj]
    exact hM.ctor c hc j _ hcj ψ ρ as fs hsa hsp
  parsLen := fun mm hmm ψ => (hH.parsLen ψ mm hmm).trans (hH.lenP ψ).symm
  parsSat := fun mm hmm ψ ρ hs => hH.parsSat ψ mm hmm ρ hs
  parsSatInv := fun mm hmm ψ ρ hs => hH.parsSatInv ψ mm hmm ρ hs
  holeApp := fun ψ c hc j hj => blockHolesApplied hH ψ hc hj

end Clause

end ConLeche.Model
