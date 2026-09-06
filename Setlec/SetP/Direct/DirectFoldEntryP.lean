import Setlec.SetP.Direct.DirectStageEntryP
import Setlec.SetP.Direct.DirectEntryFreeP
import Setlec.Semantics.Bridge.ProjRed
import Setlec.Verify.Direct.DirectPartsInv

/-!
# The projection-slot fold (task #175 W4c, P3 module 7, part 8)

`foldEntriesP`: the P carrier survives the direct install's projection
fold (`DirectProjFoldR`).  The invariant at slot `k` carries the
block's data at the accumulator (the former's and the constructor's
readings and leaves), the stored lookups, the earlier installed slots
(each a tower entry), and the later slots' freshness with their
`NoProjEnv` (no stored piece mentions a not-yet-installed slot).  A
skipped slot is the identity; an installed slot is `stageEntry`, with
the slot decision's monotonicity (`directProjSlots_prefix`) supplying
the earlier entries and the field-sort run supplying the guard's
levelwise content.
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The fold invariant at slot `k`. -/
structure FoldInvP (V : Type w) [SetTheory V] (μ : CheckMode) (p : DirectParts)
    (cvTa cvCa : ConstantVal) (sorts : List Level)
    (pps ds : (Name → Nat) → List (Nat × Nat × AVExpr))
    (k : Nat) (env : Env) : Prop where
  carrier : ∃ mp : EnvS2PM V μ env,
    FormerData mp.base2 cvTa p.nP p.resSort pps ∧
    CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds ∧
    (∀ ψ, mp.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2))) ∧
    (∀ ψ, mp.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
  findT : env.find? p.cvT.name = some (.indInfo cvTa (Setlec.directCaps p))
  findC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF)
  /-- an earlier admitted slot holds a tower entry (an unadmitted one
  holds the inert entry, which nothing reads — task #175 W4c P3
  module 7) -/
  prev : ∀ j, j < k → (Setlec.directProjSlots p).getD j false = true →
    Setlec.directSlotAdmit p.resSort p.cvT.levelParams cvCa.type p.nP
      (Setlec.directProjGuards cvCa.type p.nP p.nF sorts) j = true →
    ∃ entry, env.findProj? p.cvT.name j = some entry ∧ entry.tower = true
  fresh : ∀ j, k ≤ j → j < p.nF → env.find? (projFnName p.cvT.name j) = none
  noProj : ∀ j, k ≤ j → j < p.nF → NoProjEnv env p.cvT.name j
  wf : Setlec.EnvWF env

/-- **One slot of the fold.** -/
theorem foldStepP (hμ : μ.verified = true) {F : Nat} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {sorts : List Level} {envS : Env} {xFvs : List Expr}
    (hsorts : Setlec.checkDirectFieldSorts (Setlec.fueledOps μ F) envS p.isProp p.large
      p.resSort p.nP xFvs p.nF = .ok sorts)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hCshape : p.cvC.name.isProjFnShape = false)
    (hresT : Setlec.reservedBasisNames.contains p.cvT.name = false)
    (hresR : Setlec.reservedBasisNames.contains (p.cvT.name.str "rec") = false)
    (hresC : Setlec.reservedBasisNames.contains p.cvC.name = false)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false →
          FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (∀ j, j < p.nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
          interp2 V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)))
    {k : Nat} (hk : k < p.nF) {env env' : Env}
    (hstep : Setlec.checkDirectProj (m := Setlec.CheckM) (Setlec.fueledOps μ F)
      p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF p.resSort
      (Setlec.directProjSlots p) (Setlec.directProjGuards cvCa.type p.nP p.nF sorts)
      cvTa cvCa env k = .ok env')
    (hinv : FoldInvP V μ p cvTa cvCa sorts pps ds k env) :
    FoldInvP V μ p cvTa cvCa sorts pps ds (k + 1) env' := by
  obtain ⟨hlenS, hsortsAll⟩ := Setlec.checkDirectFieldSorts_inv hsorts
  have hwf' : Setlec.EnvWF env' := Setlec.direct_proj_wf hinv.wf hstep
  rcases Setlec.checkDirectProj_run hstep with ⟨hoff, rfl⟩ | ⟨hon, hadm, pty, -, hEntry⟩ |
    ⟨hon, hadm, hfreshI, rfl⟩
  · -- a skipped slot
    refine ⟨hinv.carrier, hinv.findT, hinv.findC, ?_, fun j hj hjF => hinv.fresh j (by omega) hjF,
      fun j hj hjF => hinv.noProj j (by omega) hjF, hinv.wf⟩
    intro j hj hon hadm
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact hinv.prev j hjk hon hadm
    · obtain rfl : j = k := by omega
      rw [hoff] at hon
      exact nomatch hon
  · -- an installed slot
    obtain ⟨mp, hFD, hCD, hleafT, hleafC⟩ := hinv.carrier
    -- the guard's content: the official join over the used earlier slots
    have hguardEq : (Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero
        = (List.range k).foldl
            (fun acc j => if Setlec.directUsedLater cvCa.type p.nP j then
              Level.max acc (sorts.getD j .zero) else acc)
            (sorts.getD k .zero) := Setlec.directProjGuards_getD _ _ _ _ hk
    have hguardSem : ∀ ψ : Name → Nat,
        ((Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 →
        (sorts.getD k .zero).eval ψ = 0 ∧
        ∀ j, j < k → Setlec.directUsedLater cvCa.type p.nP j = true →
          (sorts.getD j .zero).eval ψ = 0 := by
      intro ψ h0
      rw [hguardEq, eval_foldl_max_if_zero_iff ψ (Setlec.directUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)] at h0
      exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
    have hguardOf : ∀ ψ : Name → Nat, (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
        ((Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 := by
      intro ψ hall
      rw [hguardEq, eval_foldl_max_if_zero_iff ψ (Setlec.directUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)]
      exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
    have hsortD : ∀ j, j < p.nF → ∃ u, sorts.getD j .zero = u ∧
        (p.isProp = false → Level.leq u p.resSort = some true) := by
      intro j hj
      obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hsortsAll j hj
      exact ⟨u, by rw [List.getD_eq_getElem?_getD, hu]; rfl, hleq⟩
    have hO5 : (Level.isEquiv p.resSort .zero == some true) = false →
        ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 →
        ((Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 := by
      intro hne ψ h0
      refine hguardOf ψ fun j hj => ?_
      obtain ⟨u, hu, hleq⟩ := hsortD j (by omega)
      rw [hu]
      have := Level.leq_sound (hleq (by rw [hProp]; exact hne)) ψ
      omega
    -- the unused earlier fields are free in the projected field's type
    have hCf : cvCa.type.hasFvar = false := (hinv.wf _ (Setlec.Semantics.Env.find?_mem hinv.findC)).1
    obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + p.nF) 0 hstripC
    have hlenA : fvsA.length = p.nP + p.nF := openPisAtFvars_length _ hopAll
    have hfree : ∀ (ψ : Name → Nat) (j : Nat), j < k →
        Setlec.directUsedLater cvCa.type p.nP j = false →
        ∃ X : AVExpr, (((ds ψ).drop p.nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
      intro ψ j hj hun
      have hsome : (cvCa.type.stripPis (p.nP + j + 1)).isSome = true :=
        Setlec.Semantics.stripPis_le (by omega) hstripC
      obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
      have hrest : rest.hasLooseBVar 0 = false := by
        unfold Setlec.directUsedLater at hun
        rw [hst] at hun
        exact hun
      obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (p.nP + p.nF) (p.nP + j) hopAll (by omega)
        hst hrest (by
          intro l hl
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
          exact absurd hl List.not_mem_nil)
      obtain ⟨pps, b, hstA, -, -, hbind⟩ := denoteP_openPis (p.nP + p.nF) hopAll (hCD.read ψ)
      have hppsEq : pps = ds ψ := by
        have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ)
        rw [hCD.len ψ] at h2
        exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
      obtain ⟨x, hx⟩ : ∃ x, fvsA[p.nP + k]? = some x :=
        ⟨fvsA[p.nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
      obtain ⟨q, hq, -, hqread⟩ := hbind (p.nP + k) x hx
      rw [hppsEq] at hq
      have hW : Expr.WScoped (0 + (p.nP + k)) (Expr.fvarTypeD x) :=
        openPisAtFvars_typeWScoped (p.nP + p.nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
      have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ p.nP + j := by
        intro l hl
        have hsub : l ∈ x.fvarLeaves := by
          cases x with
          | fvar idx nm ty =>
            simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
            exact List.mem_cons_of_mem _ hl
          | _ => exact hl
        have := hleavesK (p.nP + k) (by omega) x hx l hsub
        simpa using this
      obtain ⟨X, hX⟩ := denoteP_liftN_of_leaf_free mp.base2 (0 + (p.nP + k)) (Expr.fvarTypeD x) hW
        (q := p.nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
      refine ⟨X, ?_⟩
      have hFk : (((ds ψ).drop p.nP).map (·.2.2)).getD k default = q.2.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
        rfl
      rw [hFk, hX, show 0 + (p.nP + k) - 1 - (p.nP + j) = k - 1 - j from by omega]
    have hprev : ∀ j, j < k →
        ∃ entry, env.findProj? p.cvT.name j = some entry ∧ entry.tower = true :=
      fun j hj => hinv.prev j hj (Setlec.directProjSlots_prefix hj hk hon)
        (Setlec.directSlotAdmit_prefix (Nat.le_of_lt hj) hadm)
    have hfreshK := hinv.fresh k (Nat.le_refl _) hk
    -- the entry's shape, for the extension's bookkeeping
    obtain ⟨hnf, -, ptyA, hann, -, hcr, -, -, -, -, -, -, henv'⟩ :=
      Setlec.checkDirectProjEntry_shape hEntry
    obtain ⟨A, mp', hac⟩ := stageEntry hμ mp hEntry hwf' hinv.findT hlpsT hinv.findC hlpsC hstripC
      hProp hTshape hCshape hresT hresR hresC hk hguardSem hO5
      (hinv.noProj k (Nat.le_refl _) hk) hprev hfree hFD hCD hleafT hleafC hiff hfields
    subst henv'
    let entry : ProjEntry := ⟨p.cvT.name, k, p.cvT.levelParams, p.nP, p.cvC.name,
      p.nF, ptyA, (Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero, p.resSort,
      true, false, true⟩
    -- the new invariant
    have hneT : p.cvT.name ≠ projFnName p.cvT.name k := by
      intro h
      have := projFnName_isProjFnShape p.cvT.name k
      rw [← h, hTshape] at this
      exact nomatch this
    have hneC : p.cvC.name ≠ projFnName p.cvT.name k := by
      intro h
      have := projFnName_isProjFnShape p.cvT.name k
      rw [← h, hCshape] at this
      exact nomatch this
    have hnpK := hinv.noProj k (Nat.le_refl _) hk
    have hcrossT : ConsCrossAt (.projInfo entry) cvTa.type := by
      intro e' he' _
      cases he'
      exact hnpK.type _ (Setlec.Semantics.Env.find?_mem hinv.findT)
    have hcrossC : ConsCrossAt (.projInfo entry) cvCa.type := by
      intro e' he' _
      cases he'
      exact hnpK.type _ (Setlec.Semantics.Env.find?_mem hinv.findC)
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (hinv.wf _ (Setlec.Semantics.Env.find?_mem hinv.findT)).2.2.1
    have hcbC : ConstsBound env cvCa.type :=
      constsBound_of_constsResolve _ (hinv.wf _ (Setlec.Semantics.Env.find?_mem hinv.findC)).2.2.1
    have hfreshE : env.find? (ConstantInfo.projInfo entry).name = none := hfreshK
    refine ⟨⟨mp', hFD.cross (c₀ := .projInfo entry) hfreshE hcrossT hcbT mp'.base2 hac,
      hCD.cross (c₀ := .projInfo entry) hfreshE hneT hcrossC hcbC mp'.base2 hac, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name k) A p.cvT.name ψ = _
      rw [acvalWith_ne hneT]
      exact hleafT ψ
    · intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name k) A p.cvC.name ψ = _
      rw [acvalWith_ne hneC]
      exact hleafC ψ
    · rw [Setlec.Env.find?_cons, if_neg (fun h => hneT h.symm)]
      exact hinv.findT
    · rw [Setlec.Env.find?_cons, if_neg (fun h => hneC h.symm)]
      exact hinv.findC
    · intro j hj hon' hadm'
      rcases Nat.lt_or_ge j k with hjk | hjk
      · obtain ⟨entry, hfe, htw⟩ := hinv.prev j hjk hon' hadm'
        refine ⟨entry, ?_, htw⟩
        unfold Setlec.Env.findProj? at hfe ⊢
        rw [Setlec.Env.find?_cons, if_neg (fun h => by
          have := (Setlec.projFnName_inj h).2; dsimp only at this; omega)]
        exact hfe
      · rw [show j = k from by omega]
        refine ⟨entry, ?_, rfl⟩
        unfold Setlec.Env.findProj?
        rw [Setlec.Env.find?_cons,
          if_pos (show (ConstantInfo.projInfo entry).name = projFnName p.cvT.name k from rfl)]
    · intro j hj hjF
      rw [Setlec.Env.find?_cons, if_neg (fun h => by
        have := (Setlec.projFnName_inj h).2; dsimp only at this; omega)]
      exact hinv.fresh j (by omega) hjF
    · intro j hj hjF
      refine NoProjEnv.cons (hinv.noProj j (by omega) hjF) ?_
      refine NoProjHead.ofType ?_ (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h)
      show Expr.NoProjAt p.cvT.name j ptyA
      exact Setlec.annotateCore_noProjAt μ hann
        (by rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hnf)
        (hinv.fresh j (by omega) hjF)
  · -- an unadmitted slot: the inert entry (task #175 W4c P3 module 7)
    obtain ⟨mp, hFD, hCD, hleafT, hleafC⟩ := hinv.carrier
    let entry : ProjEntry := Setlec.directInertEntry p.cvT.name k p.cvT.levelParams p.nP
      p.cvC.name p.nF ((Setlec.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero) p.resSort
    have hneT : p.cvT.name ≠ projFnName p.cvT.name k := by
      intro h
      have := projFnName_isProjFnShape p.cvT.name k
      rw [← h, hTshape] at this
      exact nomatch this
    have hneC : p.cvC.name ≠ projFnName p.cvT.name k := by
      intro h
      have := projFnName_isProjFnShape p.cvT.name k
      rw [← h, hCshape] at this
      exact nomatch this
    have hnres : Setlec.reservedBasisNames.contains (projFnName p.cvT.name k) = false := by
      cases h : Setlec.reservedBasisNames.contains (projFnName p.cvT.name k)
      · rfl
      · exact absurd rfl (Setlec.projFnName_ne_reserved h)
    have hnpK := hinv.noProj k (Nat.le_refl _) hk
    have hcrossT : ConsCrossAt (.projInfo entry) cvTa.type := by
      intro e' he' _
      cases he'
      exact hnpK.type _ (Setlec.Semantics.Env.find?_mem hinv.findT)
    have hcrossC : ConsCrossAt (.projInfo entry) cvCa.type := by
      intro e' he' _
      cases he'
      exact hnpK.type _ (Setlec.Semantics.Env.find?_mem hinv.findC)
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (hinv.wf _ (Setlec.Semantics.Env.find?_mem hinv.findT)).2.2.1
    have hcbC : ConstsBound env cvCa.type :=
      constsBound_of_constsResolve _ (hinv.wf _ (Setlec.Semantics.Env.find?_mem hinv.findC)).2.2.1
    have hfreshE : env.find? (ConstantInfo.projInfo entry).name = none := hfreshI
    obtain ⟨mp', hac⟩ := declStepPM_of_inert_cons mp (entry := entry) hfreshE hnres rfl rfl
      rfl hwf'
    refine ⟨⟨mp', hFD.cross (c₀ := .projInfo entry) hfreshE hcrossT hcbT mp'.base2 hac,
      hCD.cross (c₀ := .projInfo entry) hfreshE hneT hcrossC hcbC mp'.base2 hac, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name k) _ p.cvT.name ψ = _
      rw [acvalWith_ne hneT]
      exact hleafT ψ
    · intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name k) _ p.cvC.name ψ = _
      rw [acvalWith_ne hneC]
      exact hleafC ψ
    · rw [Setlec.Env.find?_cons, if_neg (fun h => hneT h.symm)]
      exact hinv.findT
    · rw [Setlec.Env.find?_cons, if_neg (fun h => hneC h.symm)]
      exact hinv.findC
    · intro j hj hon' hadm'
      rcases Nat.lt_or_ge j k with hjk | hjk
      · obtain ⟨entry, hfe, htw⟩ := hinv.prev j hjk hon' hadm'
        refine ⟨entry, ?_, htw⟩
        unfold Setlec.Env.findProj? at hfe ⊢
        rw [Setlec.Env.find?_cons, if_neg (fun h => by
          have := (Setlec.projFnName_inj h).2; simp only [Setlec.directInertEntry] at this; omega)]
        exact hfe
      · obtain rfl : j = k := by omega
        rw [hadm] at hadm'
        exact nomatch hadm'
    · intro j hj hjF
      rw [Setlec.Env.find?_cons, if_neg (fun h => by
        have := (Setlec.projFnName_inj h).2; simp only [Setlec.directInertEntry] at this; omega)]
      exact hinv.fresh j (by omega) hjF
    · intro j hj hjF
      refine NoProjEnv.cons (hinv.noProj j (by omega) hjF) ?_
      refine NoProjHead.ofType ?_ (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h)
      show Expr.NoProjAt p.cvT.name j (.sort (.succ .zero))
      unfold Expr.NoProjAt
      trivial

/-- **The fold**: from the invariant at slot `k`, the run over the
remaining slots lands a carrier. -/
theorem foldEntriesP (hμ : μ.verified = true) {F : Nat} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {sorts : List Level} {envS : Env} {xFvs : List Expr}
    (hsorts : Setlec.checkDirectFieldSorts (Setlec.fueledOps μ F) envS p.isProp p.large
      p.resSort p.nP xFvs p.nF = .ok sorts)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hCshape : p.cvC.name.isProjFnShape = false)
    (hresT : Setlec.reservedBasisNames.contains p.cvT.name = false)
    (hresR : Setlec.reservedBasisNames.contains (p.cvT.name.str "rec") = false)
    (hresC : Setlec.reservedBasisNames.contains p.cvC.name = false)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false →
          FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (∀ j, j < p.nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
          interp2 V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))) :
    ∀ (l : List Nat) (k : Nat), l = (List.range p.nF).drop k →
      ∀ {env env₂ : Env},
      Setlec.Semantics.DirectProjFoldR μ F p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
        p.resSort (Setlec.directProjSlots p)
        (Setlec.directProjGuards cvCa.type p.nP p.nF sorts) cvTa cvCa env l env₂ →
      FoldInvP V μ p cvTa cvCa sorts pps ds k env →
      Nonempty (EnvS2PM V μ env₂)
  | [], _, _, env, env₂, hfold, hinv => by
    obtain rfl : env₂ = env := hfold
    obtain ⟨mp, -⟩ := hinv.carrier
    exact ⟨mp⟩
  | i :: rest, k, hl, env, env₂, hfold, hinv => by
    obtain ⟨env', hstep, hrest⟩ := hfold
    have hk : k < p.nF := by
      rcases Nat.lt_or_ge k p.nF with h | h
      · exact h
      · exfalso
        rw [List.drop_eq_nil_of_le (by simp; omega)] at hl
        exact nomatch hl
    have hik : i = k ∧ rest = (List.range p.nF).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hk), List.getElem_range] at hl
      exact ⟨(List.cons.inj hl).1, (List.cons.inj hl).2⟩
    obtain ⟨rfl, hrest'⟩ := hik
    exact foldEntriesP hμ hsorts hlpsT hlpsC hstripC hProp hTshape hCshape hresT hresR hresC
      hiff hfields rest (i + 1) hrest' hrest
      (foldStepP hμ hsorts hlpsT hlpsC hstripC hProp hTshape hCshape hresT hresR hresC
        hiff hfields hk hstep hinv)

end Setlec.Semantics
