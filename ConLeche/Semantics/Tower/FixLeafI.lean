module

import ConLeche.Semantics.Tower.SumLeaf
public import ConLeche.Semantics.Tower.SumMk
import ConLeche.Semantics.NoBVar
import ConLeche.SetModel.Iter
public import ConLeche.SetModel.TowerMono
import ConLeche.Semantics.Univ

@[expose] public section

/-!
# The type-former leaf of a direct recursive FAMILY (task #188, indexed)

The carrier of a directly installed recursive inductive family
`T : Π p⃗ ı⃗, Sort w` is the least pre-fixed family (`lfpFam`,
`ConLeche/SetTheory/Derive/LfpFam.lean`) of its constructor-tower functor
on families over the **index-tuple set** `I = ⟦Σ' ı⃗⟧` (the tower over
the index telescope, `idxTyAV`; a tuple is `tupW u ı⃗` — the point at
index level `0`):

    λ p⃗ ı⃗. lfpFam.{u,w} I (λ (X : I → Sort w) (t : I). Σ_j tower_j(X, t)) ⟨ı⃗⟩

Constructor `j`'s tower at `(X, t)` is spelled over its **X-chain**
(`chainXI`): an ordinary field domain is lifted past the two binders
`X, t`; a recursive field `T p⃗ e⃗_i(f_prev)` reads `X ⟨e⃗_i⟩` — the family
applied to the tuple of its index expressions, the tuple built by the
**index tupler** `tuplerAV` (a λ over the index telescope returning the
tuple, applied to the expressions — no substitution is ever performed);
the terminator is the index equation of the sum route (`idxEqAV`) with
the constructor's index expressions equated to the PROJECTIONS of the
tuple `t`.  At `nIdx = 0` this is the non-indexed route with the unit
tuple; the non-recursive class is the constant functor.

This module: the spelled pieces, their readings and gradings, and the
former leaf's three laws (`nativeTyAVI_mem/_ok2/_fold`) under one
hereditary premise (`ParamsOkXI`).  The functor's semantic laws
(monotonicity, the ω-iterate as a closed family, the fixed point, the
identification with the real chains) are in `FixFamI.lean`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The index tuple -/

/-- The index tuple's value: the point at index level `0`, the tuple
tower above. -/
noncomputable def tupW (u : Nat) (is : List V) : V := if u = 0 then pt else mkTower is

theorem tupW_zero (is : List V) : tupW 0 is = (pt : V) := if_pos rfl
theorem tupW_pos {u : Nat} (hu : u ≠ 0) (is : List V) : tupW u is = mkTower is := if_neg hu

/-- The index-tuple set at a parameter frame. -/
noncomputable def idxSet (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : V :=
  towerSet u (teleOfFields ρp Ids)

/-- The index tuple type, spelled at the parameter frame. -/
def idxTyAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm := towerBodyAV u Ids

/-- The index tupler: the λ-tower over the index telescope returning
the tuple (bit `u`: the tuple's type is `I : Sort u`). -/
def tuplerAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  mkLamsC u (Ids.map fun F => (u, u, F)) (mkTowerGo u Ids)

/-- The index telescope's grading, with the bound in both regimes (the
index domains' sorts are at most `u`, so the tuple type is a graph-regime
tower even at `u = 0` where `FieldsOkB` alone asks for no bound). -/
def IdxOk (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : Prop :=
  FieldsOkB u ρp Ids ∧ FieldsBound u ρp Ids

theorem idxTyAV_facts {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (idxTyAV u Ids) = idxSet u ρp Ids ∧
      idxSet u ρp Ids ∈ˢ (univ u : V) ∧ WellDenoted V ρp (idxTyAV u Ids) :=
  ⟨towerBodyAV_interp (fun _ => h.2), towerSet_univ_of_okB (fun _ => h.2), towerBodyAV_wellDenoted h.1⟩

/-- A fitting index spine's tuple is in the tuple set. -/
theorem tupW_mem {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {is : List V}
    (hsp : SpineFit ρp Ids is) : tupW u is ∈ˢ idxSet u ρp Ids := by
  unfold tupW idxSet
  split
  · next hu => exact hu ▸ pt_mem_tower (fitsS_teleOfFields.mpr hsp)
  · next hu => exact mkTower_mem hu (fitsS_teleOfFields.mpr hsp)

/-- The tupler's binder data. -/
abbrev tuplerData (u : Nat) (Ids : List AnnotTerm) : List (Nat × Nat × AnnotTerm) :=
  Ids.map fun F => (u, u, F)

omit [SetTheory V] in
theorem tuplerData_doms (u : Nat) (Ids : List AnnotTerm) :
    (tuplerData u Ids).map (·.2.2) = Ids := by
  simp [tuplerData, Function.comp_def]

/-- The tupler's type: `Π ı⃗, I` (the tuple type lifted under the index
binders). -/
def tuplerTyAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  mkPisAV (tuplerData u Ids) ((idxTyAV u Ids).liftN Ids.length 0)

theorem tuplerAV_under {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    UnderTowerOk u ρp (mkTowerGo u Ids) ((idxTyAV u Ids).liftN Ids.length 0) (tuplerData u Ids) := by
  have := underTowerOk_fields (w := u) (bodyC := (idxTyAV u Ids).liftN Ids.length 0) (ρp := ρp)
    (Fs := Ids) h.1 (fun bs hsp => by
      have hsh : shiftE Ids.length 0 (consList bs ρp) = ρp := by
        rw [← hsp.length_eq]; exact shiftE_consList bs ρp
      rw [interp_liftN, hsh]
      exact (idxTyAV_facts h).1)
    (rest := tuplerData u Ids) (pre := []) (bs := []) (by simp [tuplerData, Function.comp_def])
    trivial
  simpa using this

theorem tuplerAV_mem {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (tuplerAV u Ids) ∈ˢ interp V ρp (tuplerTyAV u Ids) :=
  mkLamsC_mem (fun _ hd => by
    obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
    exact Iff.rfl) (tuplerAV_under h)

theorem tuplerAV_wellDenoted {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    WellDenoted V ρp (tuplerAV u Ids) :=
  mkLamsC_wellDenoted (fun _ hd => by
    obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
    exact Iff.rfl) (tuplerAV_under h)

theorem foldl_app_pt' : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' ts

/-- **The tupler's fold**: along a fitting index spine it computes the
tuple (both regimes). -/
theorem tuplerAV_fold {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) :
    is.foldl SetTheory.app (interp V ρp (tuplerAV u Ids)) = tupW u is := by
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero]
    cases Ids with
    | nil =>
      cases is with
      | nil => rfl
      | cons _ _ => exact hsp.elim
    | cons F Ids =>
      show is.foldl SetTheory.app (interp V ρp (mkLamsAV ((0, F) :: _) _)) = _
      rw [mkLamsAV_zero_head]
      exact foldl_app_pt' is
  · unfold tuplerAV mkLamsC
    rw [mkLamsAV_fold (fun d hd => by
        obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
        exact hu) (by rw [List.map_map]; simpa [tuplerData, Function.comp_def] using hsp)]
    rw [mkTowerGo_interp (fun _ => h.2) hsp, if_neg hu, tupW_pos hu]

/-! ## The family type and the functor -/

/-- `I → Sort w`, spelled. -/
def famTyAV (u w : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  .pi u (w + 1) (idxTyAV u Ids) (.sort w)

theorem famTyAV_facts {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (famTyAV u w Ids) = lfpFamSpace V w (idxSet u ρp Ids) ∧
      lfpFamSpace V w (idxSet u ρp Ids) ∈ˢ (univ (Nat.max u (w + 1)) : V) ∧
      WellDenoted V ρp (famTyAV u w Ids) := by
  obtain ⟨hv, hu, hok⟩ := idxTyAV_facts h
  refine ⟨?_, ?_, ?_⟩
  · unfold famTyAV lfpFamSpace
    rw [interp_pi, hv]
    rfl
  · unfold lfpFamSpace
    have := piR_mem_univ (u := u) (v := w + 1) hu (fun _ _ => univ_mem_univ w)
    rwa [if_neg (Nat.succ_ne_zero w)] at this
  · unfold famTyAV
    rw [WellDenoted_pi]
    exact ⟨hok, fun _ _ => trivial⟩

/-- A recursive field's own telescope (`a⃗ : A⃗` at a reflexive field,
task #202; empty at a finitary one) lifted past the two binders `X, t`
at position `i`: binder `k` sits under `k` earlier telescope binders. -/
def liftTele2 (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  (List.range tl.length).map fun k =>
    let d := tl.getD k default
    (d.1, d.2.1, d.2.2.liftN 2 (i + k))

omit [SetTheory V] in
theorem liftTele2_length (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    (liftTele2 i tl).length = tl.length := by simp [liftTele2]

/-- The variables of an `m`-binder telescope, innermost last. -/
def teleVarsAV (m : Nat) : List AnnotTerm := (List.range m).map fun k => .bvar (m - 1 - k)

omit [SetTheory V] in

/-- The index equations at the chain's end: the constructor's index
expressions against the projections of the tuple `t` (at `bvar nF`). -/
def eqsXI (nIdx nF : Nat) (Es : List AnnotTerm) : List (AnnotTerm × AnnotTerm) :=
  (List.range nIdx).map fun l => ((Es.getD l default).liftN 2 nF, projAV l (.bvar nF))

/-! ## The leaf -/

omit [SetTheory V] in
theorem frameIdx_succ (n : Nat) (ρ : Nat → V) : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := by
  unfold frameIdx
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  show ρ (n + 1 - 1 - 0) :: _ = _
  rw [show n + 1 - 1 - 0 = n from rfl]
  congr 1
  apply List.map_congr_left
  intro l _
  show ρ (n + 1 - 1 - (l + 1)) = ρ (n - 1 - l)
  rw [show n + 1 - 1 - (l + 1) = n - 1 - l from by omega]

omit [SetTheory V] in
/-- The index tuple of a consed spine. -/
theorem frameIdx_consList' : ∀ (is : List V) (ρ : Nat → V),
    frameIdx is.length (consList is ρ) = is
  | [], _ => rfl
  | a :: as, ρ => by
    rw [consList_cons, List.length_cons, frameIdx_succ, frameIdx_consList' as (cons a ρ)]
    congr 1
    have := consList_apply_add as (cons a ρ) 0
    rw [Nat.zero_add] at this
    exact this

omit [SetTheory V] in
/-- A frame is its index tuple over its shift. -/
theorem consList_frameIdx : ∀ (n : Nat) (ρ : Nat → V),
    consList (frameIdx n ρ) (shiftE n 0 ρ) = ρ
  | 0, ρ => by
    show consList [] (shiftE 0 0 ρ) = ρ
    rw [consList_nil, shiftE_zero_zero]
  | n + 1, ρ => by
    have hfr : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := frameIdx_succ n ρ
    have hsh : cons (ρ n) (shiftE (n + 1) 0 ρ) = shiftE n 0 ρ := by
      funext i
      cases i with
      | zero => show ρ n = ρ (0 + n); rw [Nat.zero_add]
      | succ i =>
        show ρ (i + (n + 1)) = ρ (i + 1 + n)
        rw [show i + (n + 1) = i + 1 + n from by omega]
    rw [hfr, consList_cons, hsh]
    exact consList_frameIdx n ρ

end ConLeche.Semantics
