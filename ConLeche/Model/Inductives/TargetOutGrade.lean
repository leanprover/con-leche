module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.IndDomGrade
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Semantics.Tower.TowerWire

public section

/-!
# The instantiated constructor is GRADED at an outside class (lane NESTIND, session 7)

An outside class's rule certificates (`BlockRuleCerts`) grade the rule's
frame: the prefix, then the fields of the container's constructor at the
major's instantiation `C.{us} ds`.  No recorded clause fact grades a
constructor's fields; the grading comes from the constructor's STORED
type, whose reading is graded (`type_wellDenotedV`), peeled along the
parameters' readings — which fit the constructor's own parameter binders
by finding F9 (`LfpCtorReads`: the constructor's parameters are the
block's) at the key frame the major's parameters satisfy (`tgtOutSat`).

* `peelPis_mkPisAV_split` — a successful peel exhibits the tower;
* `wdV_mkPisAV_dom`/`wdV_mkPisAV_body` — a graded tower's domains and
  body are graded along fitting spines;
* **`tgtOutCrestWd`** — the instantiated constructor's reading at the
  rule prefix is graded at every prefix spine fitting the rule's prefix
  domains.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Towers -/

/-- A graded Π-tower's domains are graded along fitting spines. -/
theorem wdV_mkPisAV_dom :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {σ : Nat → V},
      WellDenotedV V σ (mkPisAV ds b) → ∀ l, l < ds.length → ∀ ys : List V,
      SpineFit σ ((ds.map (·.2.2)).take l) ys →
      WellDenotedV V (consList ys σ) ((ds.map (·.2.2)).getD l default)
  | [], _, _, _, l, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | d :: ds, b, σ, h, 0, _, ys, hys => by
    have hy : ys = [] := by
      have := hys.length_eq; simpa using this
    subst hy
    exact WellDenotedV_pi_dom h
  | d :: ds, b, σ, h, l + 1, hl, ys, hys => by
    match ys, hys with
    | y :: ys', hys =>
      simp only [List.map_cons, List.take_succ_cons] at hys
      obtain ⟨hy, hys'⟩ := hys
      have hb := WellDenotedV_pi_body h hy
      have := wdV_mkPisAV_dom hb l (by simpa using hl) ys' hys'
      simpa [consList_cons] using this

/-- A graded Π-tower's body is graded along fitting spines. -/
theorem wdV_mkPisAV_body :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {σ : Nat → V},
      WellDenotedV V σ (mkPisAV ds b) → ∀ ys : List V,
      SpineFit σ (ds.map (·.2.2)) ys → WellDenotedV V (consList ys σ) b
  | [], _, _, h, ys, hys => by
    have hy : ys = [] := by
      have := hys.length_eq; simpa using this
    subst hy
    exact h
  | d :: ds, b, σ, h, ys, hys => by
    match ys, hys with
    | y :: ys', hys =>
      simp only [List.map_cons] at hys
      obtain ⟨hy, hys'⟩ := hys
      have := wdV_mkPisAV_body (WellDenotedV_pi_body h hy) ys' hys'
      simpa [consList_cons] using this

/-! ## The instantiated constructor, graded -/

section Crest

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {outside nested : Bool} {block : List ConstantInfo}

set_option maxHeartbeats 2000000 in
/-- **The instantiated constructor, as a fit of the stored type** at an
outside class: the constructor's stored type reads (at the instantiation's
levels) as a closed, graded Π-tower with the container's parameter count
of outer binders, and at a prefix spine fitting the rule's prefix domains
the parameters' readings FIT it (F9 at the key frame, `tgtOutSat`), the
residual being the instantiated constructor's reading (`tgtCrest`). -/
theorem tgtOutCtorFit (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs)
 :
    ∃ (T0 : AnnotTerm) (pps : List (Nat × Nat × AnnotTerm)) (b0 : AnnotTerm),
      ConstantInfo.ctorInfo cA.1 (tgtMajor out j).nPc cA.2 ∈ envC.consts ∧
      cA.1.levelParams = cvI.levelParams ∧
      denoteMeta mpC.base2.acval envC (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) 0
        cA.1.type = some T0 ∧
      T0 = mkPisAV pps b0 ∧ pps.length = (tgtMajor out j).nPc ∧
      (∀ σ : Nat → V, WellDenotedV V σ T0) ∧ Term.bvarsBelow 0 T0.erase ∧
      ∀ C : AnnotTerm,
        denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j) (tgtCrest out j i) = some C →
        TeleFitPA V (consList xs ρ) T0 (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j) C := by
  have hacl := mpC.base2.acval_closed
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatW⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨hsatK, hdsaW⟩ := hsatW ρ xs hpref
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, -, hQcr, -, -, -, -⟩ := targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨-, -, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -, hpars, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  rw [hlpsI] at hul hlenP hsatK
  have hcons := List.mem_of_find?_eq_some hfc0
  have hwfC := mpC.base2.wf _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  -- the stored type's reading at the instantiation's levels, graded
  obtain ⟨T0, hT0⟩ := mpC.type_reads _ hcons
    (Level.substFn ψ cA.1.levelParams (tgtMajor out j).lvls)
  change denoteMeta mpC.base2.acval envC (Level.substFn ψ cA.1.levelParams (tgtMajor out j).lvls)
    0 cA.1.type = some T0 at hT0
  have hT0wd := mpC.type_wellDenotedV _ hcons _ T0 hT0
  have hT0cl : Term.bvarsBelow 0 T0.erase :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hCf) hCb hT0
  -- its outer parameter binders (F8's syntactic telescope)
  obtain ⟨cv8, nPc8, nF8, hf8, bs, args, hstrip, -⟩ :=
    (hcov.own D hcl.hD).ctorConcl mm hcl.hmm i hiD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv8 ∧ (tgtMajor out j).nPc = nPc8 ∧ cA.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  obtain ⟨fvsA, oA, hopA⟩ := openPisAtFvars_of_stripPis_isSome ((tgtMajor out j).nPc + cA.2)
    (e := cA.1.type) 0 (by rw [hstrip]; rfl)
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix (tgtMajor out j).nPc
    ((tgtMajor out j).nPc + cA.2) _ 0 (Nat.le_add_right _ _) hopA
  obtain ⟨pps, b0, hst, -, hplen, -⟩ := denoteMeta_openPis (tgtMajor out j).nPc hopP hT0
  obtain ⟨hT0E, -⟩ := stripPisAV_eq_mkPis hst
  -- F9: the parameters' readings fit the constructor's parameter binders
  have hsatC := hpars _ pps b0 (by rw [← hT0E]; exact hT0) (Nat.le_of_eq hplen.symm) _ hsatK
  rw [List.take_of_length_le (Nat.le_of_eq hplen)] at hsatC
  have hdl : dsa.length = (tgtMajor out j).nPc := by
    rw [← DenoteMetaSpine.length_eq hdsa, hdsLen]
  have hspK := spineFit_of_sat_consList' (Ds := pps.map fun p : Nat × Nat × AnnotTerm => p.2.2)
    (as := dsa.map (interp V (consList xs ρ))) (by rw [List.length_map, List.length_map, hdl, hplen])
    (by simpa only [keyFrame] using hsatC)
  rw [hT0E] at hT0cl
  have hbnd : ∀ l, l < (pps.map fun p : Nat × Nat × AnnotTerm => p.2.2).length →
      Term.bvarsBelow l (((pps.map fun p : Nat × Nat × AnnotTerm => p.2.2).getD l
        default).erase) := by
    intro l hl
    rw [List.length_map] at hl
    have := (bvarsBelow_mkPisAV_inv hT0cl).1.getD_below l hl
    rw [Nat.zero_add] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at this
    exact this
  have hsp := spineFit_frame_of_bounded (σ' := consList xs ρ) hbnd hspK
  obtain ⟨rest, hTF⟩ := teleFitPA_mkPisAV_of_spineFit (pds := pps) (b := b0) (ws := dsa)
    (by rw [hdl, hplen]) hsp
  -- the crest's reading IS the peel's residual
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h0 := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h0
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinst, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hTy : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j)
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some T0 := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mpC.base2) ψ]
    exact denoteMeta_depth_of_closed hacl hCf
      (fun k => denoteMeta_closed mpC.base2.acval_erase mpC.base2.cval_closed hCf hCb hT0 1 k)
      hT0 _
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denoteMeta_instPisAt_peel hacl (acval_inst_self mpC.base2)
    _ hinst (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
    hds hTy hdsa
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  have hpe := hTF.peelPis
  rw [← hT0E, hpeel] at hpe
  obtain rfl := Option.some.inj hpe
  refine ⟨T0, pps, b0, hcons, hlpsI.symm, by rw [hlpsI]; exact hT0, hT0E, hplen, hT0wd, ?_,
    fun C hC => ?_⟩
  · rw [hT0E]; exact hT0cl
  · rw [← hQcr, hrest] at hC
    obtain rfl := Option.some.inj hC
    rw [← hdsaE, hT0E]; exact hTF

set_option maxHeartbeats 1000000 in
/-- **The instantiated constructor is graded at an outside class**: at a
prefix spine fitting the rule's prefix domains, the reading of the
container's constructor at the major's levels and parameters
(`tgtCrest`) is graded — the stored type's graded reading peeled along
the parameters' readings (`tgtOutCtorFit`), which are graded
(`tgtOutSatW`). -/
theorem tgtOutCrestWd (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs)
    {C : AnnotTerm}
    (hC : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j) (tgtCrest out j i) = some C) :
    WellDenotedV V (consList xs ρ) C := by
  obtain ⟨T0, -, -, -, -, -, -, -, hT0wd, -, hfit⟩ :=
    tgtOutCtorFit hμ hcov h R hr hcA hrhs hMo hcl ψ ρ hpref
  obtain ⟨dsa, hdsa, -, -, -, hsatW⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨-, hdsaW⟩ := hsatW ρ xs hpref
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  exact teleFitPA_wellDenotedV (hfit C hC) (hT0wd _) hdsaW

end Crest

end ConLeche.Model
