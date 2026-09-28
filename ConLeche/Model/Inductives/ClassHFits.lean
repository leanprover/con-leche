module

public import ConLeche.Model.Inductives.ClassBody
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Inductives.HoleKit

public section

/-!
# A crest's fit IS its container's recorded fit (P2d, DESIGN CLASSCHECK / P2D4)

`classCrest_spineFit_recorded` (the fields) and `classCrest_result_frame`
(the result) together: at a locally coherent valuation whose group holes
hold the container's hole values at `Y`, a spine fits a container class's
crest — its fields at the valuation, its result's index readings the
index tuple's components (`CrestFitAt`) — exactly when it fits the
container's recorded constructor at the key's frame (`HFits`)
(`classCrest_hfits_iff`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **A crest's fit at `τ`**: the spine fits the crest's fields, and the
crest's result is a variable applied to arguments reading, under the
spine, as the index tuple's components. -/
@[expose] def CrestFitAt (τ : Nat → V) (ab : List (Nat × Nat × AnnotTerm)) (r : AnnotTerm) (t : V)
    (fs : List V) : Prop :=
  SpineFit τ (ab.map (·.2.2)) fs ∧ ∃ i vs, r = AnnotTerm.mkAppN (.bvar i) vs ∧
    ∀ l, l < vs.length → interp V (consList fs τ) (vs.getD l default) = projS l t

set_option maxHeartbeats 6400000 in
/-- **The crest's fit is the recorded fit** (see the module docstring). -/
theorem classCrest_hfits_iff {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (mp.base2.acval n ψ).liftN 1 k = mp.base2.acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk mp.base2.acval env φ cls H) {isF isG : Expr → Bool}
    (hkf : KeysFOk mp.base2.acval env φ cls (fun h => isF h || isG h) H)
    (hFc : FClosed cls (fun h => isF h || isG h))
    {al : List ConLeche.ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta mp.base2.acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, (isF a.hole || isG a.hole) = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V mp.base2.acval env φ cls (fun h => isF h || isG h) H τ)
    (hsem : AliasKeySem V mp.base2.acval env φ cls al H Good)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) (hk : D.names.length = D.k)
    {c : ClassInfo} {cv : ConLeche.ConstantVal} {e0 A : Expr} {n : Nat} (hPis : IsPisN n e0)
    (heq : Expr.SemEq ((classAbsF cls (fun h => isF h || isG h) e0).replaceFVars
        (ConLeche.classGL cls D.names c H (c.dsA.map (classAbsF cls isF))))
      ((A.instantiateLevelParams cv.levelParams c.key.lvls).replaceFVars
        (ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF)))))
    {pF : List AnnotTerm} (hlp : c.dsA.length = c.nPc) (hlpF : pF.length = c.nPc)
    (hpF : ∀ i, i < c.nPc → Expr.fvarsBelow H ((c.dsA.map (classAbsF cls isF)).getD i default) ∧
      ((c.dsA.map (classAbsF cls isF)).getD i default).looseBVarsBounded 0 = true ∧
      denoteMeta mp.base2.acval env φ H ((c.dsA.map (classAbsF cls isF)).getD i default)
        = some (pF.getD i default))
    (hL : Expr.fvarsBelow H (classAbsF cls (fun h => isF h || isG h) e0))
    (hA : Expr.fvarsBelow (c.nPc + D.k) A)
    {abC abL ab : List (Nat × Nat × AnnotTerm)} {rC rL r : AnnotTerm}
    (hCr : denoteMeta mp.base2.acval env φ H (ConLeche.classAliasAbs al (ConLeche.classAbs cls e0))
      = some (mkPisAV abC rC))
    (hLr : denoteMeta mp.base2.acval env φ H (classAbsF cls (fun h => isF h || isG h) e0)
      = some (mkPisAV abL rL))
    (hAr : denoteMeta mp.base2.acval env (Level.substFn φ cv.levelParams c.key.lvls) (c.nPc + D.k) A
      = some (mkPisAV ab r))
    (hlC : abC.length = n) (hlL : abL.length = n) (hlA : ab.length = n)
    {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env (Level.substFn φ cv.levelParams c.key.lvls) 0 cvm.type
        = some (Tys.getD mm default))
    {c' j' : Nat} (hc' : c' < D.k) (hj' : j' < D.nctors c')
    (hEq : FieldsEqOn V (D.params (Level.substFn φ cv.levelParams c.key.lvls) ++ Tys).reverse
      (ab.map (·.2.2)) (D.fields (Level.substFn φ cv.levelParams c.key.lvls) c' j'))
    (hr : r = AnnotTerm.mkAppN (.bvar (n + (D.k - 1 - c')))
      ((List.range c.nPc).map (fun i => AnnotTerm.bvar (c.nPc + D.k + n - 1 - i)) ++
        D.resIdx (Level.substFn φ cv.levelParams c.key.lvls) c' j'))
    (hresLen : (D.resIdx (Level.substFn φ cv.levelParams c.key.lvls) c' j').length
      = (D.ids c' (Level.substFn φ cv.levelParams c.key.lvls)).length)
    {τ : Nat → V} (hτ : Good τ)
    (hSat : Sat V (D.params (Level.substFn φ cv.levelParams c.key.lvls)).reverse
      (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default) else τ (j - c.nPc + H)))
    {Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn φ cv.levelParams c.key.lvls)) D.N
      (D.idx (Level.substFn φ cv.levelParams c.key.lvls)
        (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
          else τ (j - c.nPc + H))) Y)
    (hgrp : ∀ i mm, i < H → ConLeche.classGrpOf cls D.names c i = some mm →
      τ (H - 1 - i) = (pF.map (interp V τ)).foldl SetTheory.app
        (D.holeVal (Level.substFn φ cv.levelParams c.key.lvls)
          (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
            else τ (j - c.nPc + H)) Y mm))
    {hg : Nat} {hty : Expr} {idx : List Expr}
    (hfB : ConLeche.classAliasAbs al (ConLeche.classAbs cls (bodyN n e0))
      = Expr.mkAppN (.fvar hg hty) (idx.map fun a => ConLeche.classAliasAbs al (ConLeche.classAbs cls a)))
    (hgB : classAbsF cls (fun h => isF h || isG h) (bodyN n e0)
      = Expr.mkAppN (.fvar hg hty) (idx.map (classAbsF cls (fun h => isF h || isG h))))
    (hhg : hg < H) {mm : Nat} (hmm : ConLeche.classGrpOf cls D.names c hg = some mm)
    (t : V) (fs : List V) :
    CrestFitAt τ abC rC t fs ↔
      D.HFits (Level.substFn φ cv.levelParams c.key.lvls)
        (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
          else τ (j - c.nPc + H)) Y t c' j' fs := by
  generalize hψ : Level.substFn φ cv.levelParams c.key.lvls = ψ at *
  generalize hρ : (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
    else τ (j - c.nPc + H)) = ρP at *
  -- the fields
  have hfields := classCrest_spineFit_recorded (φ := φ) mp hacl hwf hhk hkf hFc hawf hden hF hG hsem
    hD hk hPis heq hlp hlpF hpF hL hA hCr hLr (by rw [hψ]; exact hAr) hlC hlL hlA hlT
    (by rw [hψ]; exact hTys) (by rw [hψ]; exact hEq) hτ (by rw [hψ, hρ]; exact hSat)
    (by rw [hψ, hρ]; exact hY) (by rw [hψ, hρ]; exact hgrp) fs
  rw [hψ, hρ] at hfields
  -- the result
  have hAr' : denoteMeta mp.base2.acval env φ (c.nPc + D.names.length)
      (A.instantiateLevelParams cv.levelParams c.key.lvls) = some (mkPisAV ab r) := by
    rw [denotePInstLevels mp.base2 φ cv.levelParams c.key.lvls, hk, hψ]; exact hAr
  have hA' : Expr.fvarsBelow (c.nPc + D.names.length)
      (A.instantiateLevelParams cv.levelParams c.key.lvls) := by
    rw [hk]; exact fvarsBelow_instLevelsC cv.levelParams c.key.lvls hA
  obtain ⟨hmmc, vsC, rfl, hlvC, hles, hper⟩ := classCrest_result_frame (φ := φ) mp.base2 hacl hwf hhk
    hkf hFc hawf hden hF hG hsem hPis heq hlp hlpF hpF hL hA' hCr hLr hAr' hlC hlL hlA
    (hv := (List.range D.k).map (D.holeVal ψ ρP Y)) (by simp [hk]) hτ
    (fun i mm hi hg' => by
      rw [hgrp i mm hi hg', List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by rw [← hk]; exact classGrpOf_lt hg')]
      rfl)
    hfB hgB hhg hmm (c' := c') (by rw [hk]; exact hc') (es := D.resIdx ψ c' j')
    (by rw [hr, hk])
  rw [hρ] at hper
  have hfr : D.frame ψ ρP Y = consList ((List.range D.k).map (D.holeVal ψ ρP Y)) ρP := rfl
  rw [← hfr] at hper
  unfold CrestFitAt LfpDatum.HFits
  rw [hfields]
  constructor
  · rintro ⟨hsp, i, vs, hvs, hres⟩
    obtain ⟨-, rfl⟩ := mkAppN_bvar_inj hvs
    have hfsl : fs.length = n := by
      have := (hfields.mpr hsp).length_eq; simpa [hlC] using this
    refine ⟨hj', hsp, fun l hl => ?_⟩
    have hlr : l < (D.resIdx ψ c' j').length := by rw [hresLen]; exact hl
    have hlv : l < vsC.length := by omega
    refine ⟨(D.resIdx ψ c' j')[l], List.getElem?_eq_getElem hlr, ?_⟩
    have := hper fs hfsl l (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlr,
      List.getElem?_eq_getElem hlv, Option.getD_some] at this
    rw [← this]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlv] using hres l hlv
  · rintro ⟨-, hsp, hres⟩
    have hsp' := hfields.mpr hsp
    refine ⟨hsp, _, vsC, rfl, fun l hl => ?_⟩
    have hfsl : fs.length = n := by
      have := hsp'.length_eq; simpa [hlC] using this
    have hli : l < (D.ids c' ψ).length := by rw [← hresLen]; omega
    obtain ⟨e, he, hev⟩ := hres l hli
    rw [hper fs hfsl l (by omega), List.getD_eq_getElem?_getD, he, Option.getD_some]
    exact hev

end ConLeche.Model
