module

public import ConLeche.Model.Inductives.BlockComposed
public import ConLeche.Model.Inductives.BlockRecKit
public import ConLeche.Semantics.Tower.InstAll
public section

/-!
# The instantiation law at the pins — `hfit` (task #315, M6 s5)

`ofNested_pin_block_of_fit` (`BlockComposed.lean`) reduced `pinLeaf`'s
set equality to ONE hypothesis, `hfit`: a field spine fits the COPY's
constructor `offs (k + q₀ + i) + j` of the auxiliary block at the
joined tuple `segJoin (k + q₀) kJ L⁺ Y` iff it is the CONTAINER's
`ChainFit` at `Y` for its member `i`'s constructor `j` — at the pin's
frame `ρJ = consList ⟦Ds⟧ ρp`.  This module proves `hfit` from the
INSTANTIATION IDENTITIES of the copy's readings (DESIGN §U.17):

* `fitsFrom_iff_frames`: `FitsFrom` across TWO frames is a congruence
  of the per-field ENTRY SETS at every fitting prefix;
* `CopyCtorInst`: per constructor, the copy's readings are the
  container's with the pin's components substituted at the field's
  depth (`AnnotTerm.instAll`, `Semantics/Tower/InstAll.lean`): a
  container-recursive field is copy-recursive at the copy of its
  target with the telescope and index expressions instantiated
  (`recF`); a container-ordinary field is either copy-ordinary with its
  domain instantiated, or copy-recursive at a MEMBER or a pin OUTSIDE
  the group — the elimination's rewrite of an occurrence inside the
  components — whose entry at the auxiliary carrier is the container's
  domain read at the pin's frame (`ordF`, the members' `leaf` and the
  other pins' `pinLeaf`, the assembly's induction); the index telescope
  and the result's index readings instantiated (`idxTele`, `es`);
* `copyCtorInst_fit_iff` = `hfit` at one constructor; `hfit_of_inst`
  = `hfit` verbatim; **`ofNested_pin_block_of_inst`** and
  **`ofNested_pinLeaf_of`**: `pinLeaf` for `ofNested` at a pin group
  whose container is PIN-FREE, from the identities, the universe facts
  and the container's block model.

The universe facts: the block's sort EQUALS the container's at the
pin's level assignment (`hw`, `mutualCrossChecks`' `isEquiv` at the
copy's sort); the index universes agree on `= 0` (`hu`, the tower
regimes) — see DESIGN §U.17 (g) for the second's status.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `FitsFrom` across two frames -/

/-- **`FitsFrom` congruence across two frames**: along two domain lists
of one length, whenever at every position and every prefix fitting
BOTH chains the two ENTRY sets agree (the slot at the recursive
positions, the domain's reading otherwise, each at its own frame), the
fits agree. -/
theorem fitsFrom_iff_frames {rs rs' : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ ρ' : Nat → V} {Fs Fs' : List AnnotTerm} {fs : List V},
      Fs.length = Fs'.length →
      (∀ l, l < Fs.length → ∀ fs₁ : List V, fs₁.length = l →
        FitsFrom rs slot i ρ (Fs.take l) fs₁ → FitsFrom rs' slot' i ρ' (Fs'.take l) fs₁ →
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
          else interp V (consList fs₁ ρ) (Fs.getD l default))
        = (if rs'.getD (i + l) false then slot' (i + l) (consList fs₁ ρ')
          else interp V (consList fs₁ ρ') (Fs'.getD l default))) →
      (FitsFrom rs slot i ρ Fs fs ↔ FitsFrom rs' slot' i ρ' Fs' fs)
  | _, _, _, [], [], [], _, _ => Iff.rfl
  | _, _, _, [], [], _ :: _, _, _ => Iff.rfl
  | _, _, _, [], _ :: _, _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, [], _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, _ :: _, [], _, _ => Iff.rfl
  | i, ρ, ρ', F :: Fs, F' :: Fs', a :: fs, hlen, hent => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs fs) ↔
      (a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
        FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs)
    have h0 := hent 0 (by simp) [] rfl trivial trivial
    simp only [Nat.add_zero, consList_nil, List.getD_cons_zero] at h0
    have hmem : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ↔
        a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') := by rw [h0]
    have htail : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) →
        (FitsFrom rs slot (i + 1) (cons a ρ) Fs fs ↔ FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs) := by
      intro ha
      refine fitsFrom_iff_frames (by simpa using hlen) fun l hl fs₁ hl₁ hf hf' => ?_
      have := hent (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁])
        (by
          show a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
            FitsFrom rs slot (i + 1) (cons a ρ) (Fs.take l) fs₁
          exact ⟨ha, hf⟩)
        (by
          show a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
            FitsFrom rs' slot' (i + 1) (cons a ρ') (Fs'.take l) fs₁
          exact ⟨hmem.mp ha, hf'⟩)
      simpa only [consList_cons, List.getD_cons_succ, show i + (l + 1) = i + 1 + l from by omega]
        using this
    exact ⟨fun ⟨ha, hf⟩ => ⟨hmem.mp ha, (htail ha).mp hf⟩,
      fun ⟨ha', hf'⟩ => ⟨hmem.mpr ha', (htail (hmem.mpr ha')).mpr hf'⟩⟩

/-! ## The slot and the index set under instantiation -/

/-- `tupW` reads its universe only through `= 0`. -/
theorem tupW_zero_agree {u u' : Nat} (hz : u = 0 ↔ u' = 0) (is : List V) :
    tupW u is = tupW u' is := by
  by_cases hu : u = 0
  · rw [hu, hz.mp hu]
  · rw [tupW_pos hu, tupW_pos fun h => hu (hz.mpr h)]

/-- **The slot under instantiation**: a recursive slot whose telescope
and index expressions are the container's instantiated at the fields'
depth, read at the fields' frame over the block's frame, is the
container's slot at the fields' frame over the pin's frame — at the
same family, when the two sorts and the two index universes agree on
`= 0`. -/
theorem slotSet_instTele {w w' u u' : Nat} (hw : w = 0 ↔ w' = 0) (hu : u = 0 ↔ u' = 0)
    (ds : List AnnotTerm) (ρ : Nat → V) (fs : List V) {tlC tlJ : List (Nat × Nat × AnnotTerm)}
    (htl : tlC.map (·.2.2) = instTele ds fs.length (tlJ.map (·.2.2))) (Eis : List AnnotTerm)
    (X : V) :
    slotSet w u (consList fs ρ) tlC (Eis.map (AnnotTerm.instAll ds (fs.length + tlJ.length))) X
      = slotSet w' u' (consList fs (consList (ds.map (interp V ρ)) ρ)) tlJ Eis X := by
  unfold slotSet
  rw [htl]
  refine piTele_instTele hw ds ρ (tlJ.map (·.2.2)) fs [] fun bs hbs => ?_
  simp only [List.nil_append, List.map_map]
  rw [tupW_zero_agree hu]
  congr 2
  refine List.map_congr_left fun E _ => ?_
  show interp V (consList bs (consList fs ρ)) (AnnotTerm.instAll ds (fs.length + tlJ.length) E)
    = interp V (consList bs (consList fs (consList (ds.map (interp V ρ)) ρ))) E
  have hlen : fs.length + tlJ.length = (fs ++ bs).length := by
    rw [List.length_append, hbs.length_eq, List.length_map]
  rw [← consList_append fs bs ρ, ← consList_append fs bs (consList (ds.map (interp V ρ)) ρ), hlen,
    interp_instAll]

/-- The index-tuple set under instantiation. -/
theorem idxSet_instTele {u u' : Nat} (hu : u = 0 ↔ u' = 0) (ds : List AnnotTerm) (ρ : Nat → V)
    (Ids : List AnnotTerm) :
    idxSet u ρ (instTele ds 0 Ids) = idxSet u' (consList (ds.map (interp V ρ)) ρ) Ids := by
  unfold idxSet
  have := towerSet_instTele hu ds ρ Ids []
  simpa only [consList_nil, List.length_nil] using this

/-! ## The instantiation identities of a copy's constructor -/

section Inst

variable {nP k : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env} {memberNames : List Name}
  {nIdxs : List Nat} {ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {W : (Name → Nat) → Nat} {ctorsM : Nat → List (ConstantVal × Nat)} {idxF : Nat → Nat → List Expr}
  {dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → Nat → List (Option Nat)}
  {ksF : Nat → Nat → List RecFieldKind} {tgts : Nat → Nat → Nat → Nat}
  {fvsPF xFvsF : Nat → Nat → List Expr} {xrestF : Nat → Nat → Expr}
  {eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {pins : List PinSyn} {offs : Nat → Nat}
  {mems nFs : List Nat} {tgtsG : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

local notation "D" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins offs mems nFs
  tgtsG rss tlss Eiss₀ Fss₀ Ess₀)

local notation "ΨA" => nestedΨ (V := V) nP k pins.length resSort ppsA W offs mems nFs tgtsG rss tlss
  Eiss₀ Fss₀ Ess₀

variable {ψ : Name → Nat} {ρp : Nat → V}

-- The auxiliary least tuple at the frame (the members' carriers and
-- the pins' carriers at once), spelled without the block model so that
-- the identities below mention only the lists (`(D).w ψ`, `(D).idx ψ ρp`
-- are these by `rfl`).
local notation "L⁺" => lfpTuple (resSort.eval ψ) (k + pins.length) (nestedIs nP ppsA W ψ ρp)
  (ΨA ψ ρp)

/-- **The instantiation identities of one copy's constructor**: the
container `dJ`'s member `i`, constructor `j`, copied at the pin group
`[q₀, q₀ + kJ)` whose components read as `Ds` (at the block's
parameter frame `ρp`) and whose level assignment is `ψJ`; the copy is
the auxiliary block's constructor `offs (k + q₀ + i) + j`.  Each field
of the container's reads in the copy as its instantiation at the
field's depth (`AnnotTerm.instAll`), with the container's targets
moved to the group's copies; a container-ordinary field the
elimination rewrote (an occurrence of a member or of another pin's
container INSIDE the components) is copy-recursive at a target OUTSIDE
the group and its entry at the auxiliary carrier is the container's
domain read at the pin's frame (the members' `leaf` and the other
pins' `pinLeaf` — the assembly's induction).  `Y` is the group's tuple
the fits are taken at. -/
structure CopyCtorInst (dJ : BlockModel V) (ψJ : Name → Nat) (Ds : List AnnotTerm) (q₀ kJ : Nat)
    (Y : Nat → V) (i j : Nat) : Prop where
  /-- the copy has the container's field count -/
  len : ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []).length = ((dJ.Fss i ψJ).getD j []).length
  /-- a container-recursive field: copy-recursive at the group's copy
  of its target, telescope and index expressions instantiated -/
  recF : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
    ((dJ.rss i).getD j []).getD l false = true →
    (rss.getD (offs (k + q₀ + i) + j) []).getD l false = true ∧
    (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 = k + q₀ + dJ.tgts i j l ∧
    ((((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD l []).map (·.2.2))
      = instTele Ds l ((((dJ.tlss i ψJ).getD j []).getD l []).map (·.2.2)) ∧
    (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l [])
      = (((dJ.Eiss i ψJ).getD j []).getD l []).map
          (AnnotTerm.instAll Ds (l + (((dJ.tlss i ψJ).getD j []).getD l []).length))
  /-- a container-ordinary field: copy-ordinary with the domain
  instantiated, or copy-recursive outside the group with the entry
  identity at the auxiliary carrier -/
  ordF : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
    ((dJ.rss i).getD j []).getD l false = false →
    ((rss.getD (offs (k + q₀ + i) + j) []).getD l false = false ∧
      ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default
        = AnnotTerm.instAll Ds l (((dJ.Fss i ψJ).getD j []).getD l default)) ∨
    ((rss.getD (offs (k + q₀ + i) + j) []).getD l false = true ∧
      ¬ (k + q₀ ≤ (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 ∧
        (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 < k + q₀ + kJ) ∧
      ∀ fs₁ : List V, fs₁.length = l →
        FitsFrom (rss.getD (offs (k + q₀ + i) + j) [])
          (fun i' ρ => slotSet (resSort.eval ψ) (W ψ) ρ
            (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (segJoin (k + q₀) kJ L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
          0 ρp (((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []).take l) fs₁ →
        interp V (consList fs₁ (consList (Ds.map (interp V ρp)) ρp))
            (((dJ.Fss i ψJ).getD j []).getD l default)
          = slotSet (resSort.eval ψ) (W ψ) (consList fs₁ ρp)
              (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD l [])
              (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l [])
              (L⁺ ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)))
  /-- the result's index readings instantiated under the fields -/
  es : ∀ l, l < (dJ.IdsM i ψJ).length →
    ((Ess₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default
      = AnnotTerm.instAll Ds ((dJ.Fss i ψJ).getD j []).length
          (((dJ.Ess i ψJ).getD j []).getD l default)

/-- **`hfit` at one constructor**: the copy's fit at the joined tuple
is the container's `ChainFit` at `Y` — from the identities, at a
pin-free container of the group's size whose sort is the block's and
whose index universes agree with the block's on `= 0`. -/
theorem CopyCtorInst.fit_iff {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {q₀ kJ : Nat} {Y : Nat → V} {i j : Nat}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hI : IsBlockModel m T cvT cvR mI rP rules dJ i) (hnp : dJ.pins = []) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ) (hu : ∀ i', i' < kJ → (W ψ = 0 ↔ dJ.uM i' ψJ = 0))
    (hidx : blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (h : CopyCtorInst (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
      dJ ψJ Ds q₀ kJ Y i j)
    (t : V) (fs : List V) :
    (FitsFrom (rss.getD (offs (k + q₀ + i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ) (W ψ) ρ
        (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
        (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
        (segJoin (k + q₀) kJ L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
      0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) fs ∧
      (∀ l, l < (blockIds nP ppsA ψ (k + q₀ + i)).length →
        interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default)
          = projS l t))
    ↔ dJ.ChainFit ψJ (consList (Ds.map (interp V ρp)) ρp) Y t i j fs := by
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hI.Fss_length hj ψJ]
  have htgt : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → dJ.tgts i j l < kJ := fun l hl =>
    hkJ ▸ hI.tgt_lt hjl (hks ▸ hl) hnp
  -- the fits
  have hfits : FitsFrom (rss.getD (offs (k + q₀ + i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ) (W ψ) ρ
        (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
        (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
        (segJoin (k + q₀) kJ L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
      0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) fs ↔
      FitsFrom ((dJ.rss i).getD j []) (dJ.slotAt ψJ Y i j) 0 (consList (Ds.map (interp V ρp)) ρp)
        ((dJ.Fss i ψJ).getD j []) fs := by
    refine fitsFrom_iff_frames h.len fun l hl fs₁ hl₁ hf _ => ?_
    subst hl₁
    rw [h.len] at hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · obtain ⟨hrC, htg, htl, hEis⟩ := h.recF _ hl hr
      rw [if_pos hrC, if_pos hr, htg, segJoin_add _ _ (htgt _ hl),
        dJ.slotAt_of_mem (hkJ ▸ htgt _ hl), hEis, hw]
      exact slotSet_instTele Iff.rfl (hu _ (htgt _ hl)) Ds ρp fs₁ htl _ _
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, hent⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true),
          if_neg (by rw [hr']; exact Bool.false_ne_true), hF, interp_instAll]
      · rw [if_pos hrC, if_neg (by rw [hr']; exact Bool.false_ne_true), segJoin_out _ _ hout]
        exact (hent fs₁ rfl hf).symm
  -- the index equations
  refine Iff.trans (and_congr hfits (Iff.rfl)) ?_
  unfold BlockModel.ChainFit
  refine and_congr_right fun hf => ?_
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hf.length_eq
  rw [hidx, instTele_length]
  refine forall_congr' fun l => imp_congr_right fun hl => ?_
  rw [h.es l hl, ← hlen, interp_instAll]

/-- **`hfit` verbatim** (`ofNested_pin_block_of_fit`'s hypothesis) from
the identities at every constructor of the group, with the grouping of
the auxiliary block's constructor list (the copy's constructors are
the container member's, in order). -/
theorem hfit_of_inst {env : Env} {m : EnvModel V env} {dJ : BlockModel V} {ψJ : Name → Nat}
    {Ds : List AnnotTerm} {q₀ kJ : Nat}
    (hreps : IsBlockModels m dJ) (hnp : dJ.pins = []) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ) (hu : ∀ i', i' < kJ → (W ψ = 0 ↔ dJ.uM i' ψJ = 0))
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hinst : ∀ Y, InTupleSpace (resSort.eval ψ) kJ (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) Y →
      ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyCtorInst (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ kJ Y i j) :
    ∀ Y, InTupleSpace (resSort.eval ψ) kJ (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) Y →
      ∀ i, i < kJ → ∀ t, t ∈ˢ dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp) i → ∀ j fs,
      (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
        mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i ∧
        FitsFrom (rss.getD (offs (k + q₀ + i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ) (W ψ) ρ
            (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (segJoin (k + q₀) kJ L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (k + q₀ + i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsM i).length ∧
          dJ.ChainFit ψJ (consList (Ds.map (interp V ρp)) ρp) Y t i j fs) := by
  intro Y hY i hi t _ j fs
  by_cases hj : j < (dJ.ctorsM i).length
  · obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i (hkJ ▸ hi)
    have hj' : (dJ.ctorsM i)[j]? = some ((dJ.ctorsM i).getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hfit := CopyCtorInst.fit_iff hI hnp hkJ hw hu (hidx i hi) hj' (hinst Y hY i hi j hj) t fs
    obtain ⟨h1, h2⟩ := (hgrp i hi j).mpr hj
    constructor
    · rintro ⟨-, -, h3, h4⟩
      exact ⟨hj, hfit.mp ⟨h3, h4⟩⟩
    · rintro ⟨-, hC⟩
      obtain ⟨h3, h4⟩ := hfit.mpr hC
      exact ⟨h1, h2, h3, h4⟩
  · constructor
    · rintro ⟨h1, h2, -, -⟩
      exact absurd ((hgrp i hi j).mp ⟨h1, h2⟩) hj
    · rintro ⟨h', -⟩
      exact absurd h' hj

/-- **The `Tree`/`List` shape**: one pin, one-member container (`List`'s
`ofNative` block model) — `hfit_of_inst` at `kJ = 1`, the check the
session brief asked for first; the general statement subsumes it. -/
theorem hfit_of_inst_one {env : Env} {m : EnvModel V env} {dJ : BlockModel V} {ψJ : Name → Nat}
    {Ds : List AnnotTerm} {q₀ : Nat}
    (hreps : IsBlockModels m dJ) (hnp : dJ.pins = []) (hkJ : dJ.k = 1)
    (hw : dJ.w ψJ = resSort.eval ψ) (hu : W ψ = 0 ↔ dJ.uM 0 ψJ = 0)
    (hidx : blockIds nP ppsA ψ (k + q₀ + 0) = instTele Ds 0 (dJ.IdsM 0 ψJ))
    (hgrp : ∀ j, (offs (k + q₀ + 0) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + 0) + j) 0 = k + q₀ + 0) ↔ j < (dJ.ctorsM 0).length)
    (hinst : ∀ Y, InTupleSpace (resSort.eval ψ) 1 (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) Y →
      ∀ j, j < (dJ.ctorsM 0).length →
      CopyCtorInst (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ 1 Y 0 j) :
    ∀ Y, InTupleSpace (resSort.eval ψ) 1 (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) Y →
      ∀ t, t ∈ˢ dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp) 0 → ∀ j fs,
      (offs (k + q₀ + 0) + j < (Fss₀ ψ).length ∧
        mems.getD (offs (k + q₀ + 0) + j) 0 = k + q₀ + 0 ∧
        FitsFrom (rss.getD (offs (k + q₀ + 0) + j) []) (fun i' ρ => slotSet (resSort.eval ψ) (W ψ) ρ
            (((tlss ψ).getD (offs (k + q₀ + 0) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (k + q₀ + 0) + j) []).getD i' [])
            (segJoin (k + q₀) 1 L⁺ Y ((tgtsG.getD (offs (k + q₀ + 0) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + 0) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (k + q₀ + 0)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q₀ + 0) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsM 0).length ∧
          dJ.ChainFit ψJ (consList (Ds.map (interp V ρp)) ρp) Y t 0 j fs) :=
  fun Y hY t ht j fs =>
    hfit_of_inst hreps hnp hkJ hw (fun i' hi' => by rw [Nat.lt_one_iff.mp hi']; exact hu)
      (fun i' hi' => by rw [Nat.lt_one_iff.mp hi']; exact hidx)
      (fun i' hi' => by rw [Nat.lt_one_iff.mp hi']; exact hgrp)
      (fun Y hY i' hi' => by rw [Nat.lt_one_iff.mp hi']; exact hinst Y hY)
      Y hY 0 Nat.zero_lt_one t ht j fs

/-- **A pin's carrier at the block's carrier is its PIN-FREE
container's least tuple**, from the instantiation identities
(`ofNested_pin_block_of_fit` at the container's block model: the fibre
by its `fibre` clause, the tag shape `EnvBlockModels`', the fits by
`hfit_of_inst`). -/
theorem ofNested_pin_block_of_inst {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {q₀ kJ : Nat}
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)
    (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss (Eiss₀ ψ) (Fss₀ ψ)
      (Ess₀ ψ))
    (hseg : q₀ + kJ ≤ pins.length)
    (hreps : IsBlockModels m dJ) (hnp : dJ.pins = []) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ) (hu : ∀ i', i' < kJ → (W ψ = 0 ↔ dJ.uM i' ψJ = 0))
    (hinj : ∀ (mm' j : Nat) (fs : List V), dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt])))
    (hρJ : Sat V (dJ.params ψJ).reverse (consList (Ds.map (interp V ρp)) ρp))
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hinst : ∀ Y, InTupleSpace (resSort.eval ψ) kJ (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) Y →
      ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyCtorInst (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ kJ Y i j)
    {i : Nat} (hi : i < kJ) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp))
          (dJ.Φ ψJ (consList (Ds.map (interp V ρp)) ρp)) i := by
  have hkJ' : kJ = dJ.k := hkJ.symm
  subst hkJ'
  have hw' : (D).w ψ = dJ.w ψJ := hw.symm
  refine (ofNested_pin_block_of_fit h hS hseg (IsJ := dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp))
    (ΦJ := dJ.Φ ψJ (consList (Ds.map (interp V ρp)) ρp)) ?_ ?_ (injJ := dJ.inj ψJ) ?_
    (nCJ := fun i => (dJ.ctorsM i).length)
    (FitJ := fun Y t i j fs => dJ.ChainFit ψJ (consList (Ds.map (interp V ρp)) ρp) Y t i j fs)
    ?_ ?_ hi).trans (by rw [hw'])
  · -- MapsTuple
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
    rw [hw']
    exact (hI.functor ψJ _ hρJ).2.1
  · -- hIs
    intro i' hi'
    show idxSet (W ψ) ρp (blockIds nP ppsA ψ (k + q₀ + i')) = _
    rw [hidx i' hi']
    exact idxSet_instTele (hu i' hi') Ds ρp _
  · -- hinj
    intro i' j fs
    rw [hinj, hw']
  · -- hfibJ
    intro Y hY i' hi' t ht x
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i' hi'
    rw [hw'] at hY
    exact hI.fibre ψJ _ hρJ Y hY i' hi' t ht x
  · -- hfit
    intro Y hY i' hi' t ht j fs
    exact hfit_of_inst hreps hnp rfl hw hu hidx hgrp hinst Y hY i' hi' t ht j fs

/-- **`pinLeaf` for `ofNested` at a pin of a PIN-FREE container**: the
container at the pin's components and fitting indices is the pin's
carrier at the block's carrier — the container's `leaf` at the pin's
frame through `ofNested_pin_block_of_inst`.  The pin's record is the
container's (`hpJ`/`hpψ`/`hpDs`/`hpu`/`hpIds`); the components fit the
container's parameter telescope at the block's frame (`hDsFit`, the
post-check `nestedPinsOk` read through `PinsTyped`). -/
theorem ofNested_pinLeaf_of {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {i : Nat}
    (hI : IsBlockModel m T cvT cvR mI rP rules dJ i)
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {q₀ kJ : Nat} {ρ : Nat → V} {as is : List V}
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ (consList as ρ))
    (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss (Eiss₀ ψ) (Fss₀ ψ)
      (Ess₀ ψ))
    (hseg : q₀ + kJ ≤ pins.length) (hi : i < kJ)
    (hreps : IsBlockModels m dJ) (hnp : dJ.pins = []) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ) (hu : ∀ i', i' < kJ → (W ψ = 0 ↔ dJ.uM i' ψJ = 0))
    (hinj : ∀ (mm' j : Nat) (fs : List V), dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt])))
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hinst : ∀ Y, InTupleSpace (resSort.eval ψ) kJ
        (dJ.idx ψJ (consList (Ds.map (interp V (consList as ρ))) (consList as ρ))) Y →
      ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyCtorInst (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := consList as ρ)
        dJ ψJ Ds q₀ kJ Y i j)
    (hpJ : ((D).pinAt (q₀ + i)).J = T) (hpψ : ((D).pinAt (q₀ + i)).ψJ ψ = ψJ)
    (hpDs : ((D).pinAt (q₀ + i)).Ds ψ = Ds) (hpu : ((D).pinAt (q₀ + i)).u ψ = W ψ)
    (hpIds : ((D).pinAt (q₀ + i)).Ids ψ = dJ.IdsM i ψJ)
    (hDsFit : SpineFit (consList as ρ) (dJ.params ψJ) (Ds.map (interp V (consList as ρ))))
    (hisFit : SpineFit ((D).pinFrame (q₀ + i) ψ (consList as ρ)) (((D).pinAt (q₀ + i)).Ids ψ) is) :
    ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)) ++ is).foldl SetTheory.app
        (interp V ρ (m.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ)))
      = SetTheory.app ((D).pinCar ψ (consList as ρ)
            (lfpTuple ((D).w ψ) k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) (q₀ + i))
          (tupW (((D).pinAt (q₀ + i)).u ψ) is) := by
  unfold BlockModel.pinFrame at hisFit
  rw [hpDs, hpIds] at hisFit
  rw [hpDs, hpJ, hpψ, hpu, interp_closed (V := V) (m.cval_closedL T ψJ) ρ (consList as ρ),
    hI.leaf ψJ (consList as ρ) _ is hDsFit hisFit,
    ofNested_pin_block_of_inst h hS hseg hreps hnp hkJ hw hu hinj (dJ.satOfSpine hDsFit) hidx hgrp
      hinst hi]
  unfold BlockModel.tup
  rw [tupW_zero_agree (hu i hi)]

end Inst

end ConLeche.Model
