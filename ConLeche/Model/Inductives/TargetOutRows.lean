module

public import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Semantics.Tower.TowerIntro
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Verify.EnvBound
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Semantics.Tower.FixLeafI

public section

/-!
# The rule rows at an OUTSIDE class, at the base frame (lane NESTIND, session 5)

`tgtOutDec_core` (`TargetOutRow.lean`) is the decoding row at an outside
class under the class's reading premises; `tgtOutSat`
(`TargetOutSat.lean`) discharges them from the run.  This file fixes the
class's parameter readings as a FUNCTION of the level valuation
(`tgtOutDsa`, the unique reading of the major's parameters at the rule
prefix), factors the rule's opening of the instantiated constructor
(`tgtOutOpen`), and states the rows the graph producer reads at an
outside class, at the base frame and at a prefix spine fitting the
rule's prefix domains (the class's index set is guarded by that fit,
as a member class's is, `blockRecIs`):

* `tgtOutSpF` — `hspF`: a hole fit of the recorded constructor at the
  carrier of the key frame fits the rule's field domains;
* `tgtOutDec` — `hdec`: a spine fitting the rule's prefix and field
  domains hole-fits the constructor at the tuple of the class's index
  expressions, and the fired spine reads to the injection.
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

/-- **An outside major's parameters, read at the rule prefix** — a
function of the level valuation (the reading is unique,
`denoteMetaSpine_eq_map`). -/
@[expose] def tgtOutDsa (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (j : Nat) :
    List AnnotTerm :=
  (tgtMajor out j).ds.map fun x => (denoteMeta acval envC ψ (tgtRP p j) x).getD default

/-- A read spine is the list of its arguments' readings. -/
theorem denoteMetaSpine_eq_map {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      vs = as.map fun x => (denoteMeta acval env φ d x).getD default
  | [], _, .nil => rfl
  | _ :: _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, ← denoteMetaSpine_eq_map hs]

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {p : BlockShape}
  {outside nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **The rule's opening of the instantiated container constructor**
(the setup `tgtOutDec_core` performs, factored): at the `(j, i)`-th rule
of an outside class, at the class's reading, the fired constructor is
`D`'s `(mm, i)`, its level parameters the inductive's, and the rule's
field domains are the recorded fields substituted by `instTau`. -/
theorem tgtOutOpen
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    (hul : (tgtMajor out j).lvls.length = cvI.levelParams.length)
    (hds : ∀ x ∈ (tgtMajor out j).ds, Expr.WScoped (tgtRP p j) x ∧ x.looseBVarsBounded 0 = true)
    (ψ : Name → Nat) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP p j) (tgtMajor out j).ds dsa)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
      = (tgtMajor out j).ds.length) :
    i < D.nctors mm ∧ cA.1.levelParams = cvI.levelParams ∧
      (∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = cvI.levelParams) ∧
      ∃ (ab : List (Nat × Nat × AnnotTerm)) (Tys : List AnnotTerm), Tys.length = D.k ∧
        (∀ mm', mm' < D.k → ∃ cvm caps, envC.find? (D.member mm') = some (.indInfo cvm caps) ∧
          denoteMeta mpC.base2.acval envC
              (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) 0 cvm.type
            = some (Tys.getD mm' default)) ∧
        FieldsEqOn V (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
            ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i) ∧
        ab.length = cA.2 ∧
        tgtFdomsAV p out mpC.base2.acval envC ψ j i
          = (AnnotTerm.substTele (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP p j)
              (tgtMajor out j).ds) 0 ab).map (·.2.2) := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, _, _, hFld, _, _, _⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hnd := hcl.hnd
  obtain ⟨-, -, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  have hlps : ∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = cvI.levelParams := by
    rw [hlpsI]; exact hlpsC
  refine ⟨hiD, hlpsI.symm, hlps, ?_⟩
  rw [hlpsI] at hnd hul hlenP ⊢
  rw [hlpsI] at hlps
  have hfc : envC.find? (D.ctorName mm i)
      = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hdsLen]; exact hfc0
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h
  have hRP : tgtRP p j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP p j) = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  obtain ⟨-, ab, ⟨Tys, hlT, hTys, hEq⟩, hlab, hrdF, -, -⟩ :=
    instCtor_open mpC hcl.hD hcl.hnN hcl.hkN hlps hnd hul hds hdsa hlenP hcl.hmm hiD hfc hcr hfld
  refine ⟨ab, Tys, hlT, hTys, hEq, hlab, ?_⟩
  rw [tgtFdomsAV, ← hFld, hrdF]

/-- **Row `hspF` at an outside class**: at a prefix spine fitting the
rule's prefix domains, a hole fit of `D`'s constructor `(mm, i)` at the
carrier of the key frame fits the rule's field domains. -/
theorem tgtOutSpF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
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
    {t : V} {fs : List V}
    (hf : D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ))
      (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))) t mm i fs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) (xs ++ fs) := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hs := hsatF ρ xs hpref
  obtain ⟨hiD, -, hlps, ab, Tys, hlT, hTys, hEq, hlab, hfd⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  obtain ⟨hF, -⟩ := instCtor_fit mpC hcl.hD hcl.hnN hcl.hkN hlps hcl.hnd hul hds hdsa hlenP
    hcl.hmm hiD hlT hTys hEq hlab hs
  refine SpineFit.append hpref ?_
  rw [hfd]
  exact (hF fs).mpr hf.2.1

/-- **Row `hdec` at an outside class**: a spine fitting the rule's
prefix and field domains hole-fits `D`'s constructor `(mm, i)` at the
carrier of the key frame, at the tuple of the class's index expressions
(`tgtOutEs`), and the fired spine reads to the injection. -/
theorem tgtOutDec (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
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
    {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length)
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) (xs ++ fs)) :
    D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
            (tgtRP pp.toBlockShape j) (consList xs ρ)))
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          ((tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i).map
            (interp V (consList (xs ++ fs) ρ))))
        mm i fs ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i)
        = D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs ∧
      SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        ((tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i).map
          (interp V (consList (xs ++ fs) ρ))) := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨as₁, as₂, heq, hp, hf⟩ := spineFit_append_inv hfit
  have hl₁ : as₁.length = xs.length := by rw [hp.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  exact tgtOutDec_core R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
    (by rw [hxl, hlenPd]; rfl) (hsatF ρ _ hp) hf

/-- **`targetOutsideInst`, inverted**: the major's inductive is stored,
its type instantiated at the levels and parameters is a telescope ending
in a sort, and the index count is that telescope's. -/
theorem targetOutsideInst_inv {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {r : Nat × Level}
    (h : ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe I us ds = .ok r) :
    ∃ cvI caps ty s, fe.find? I = some (.indInfo cvI caps) ∧
      ConLeche.instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us) = some ty ∧
      ty.piBinders.2 = .sort s ∧ r = (ty.piBinders.1.length, s) := by
  unfold ConLeche.targetOutsideInst at h
  split at h
  · next cvI caps hf =>
    split at h
    · next ty hty =>
      simp only [pure, Except.pure] at h
      split at h
      · next s hs =>
        refine ⟨cvI, caps, ty, s, hf, hty, ?_, ?_⟩
        · rw [← hs]
        · exact (Except.ok.inj h).symm
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- **An outside class's index count is the kernel's** (`M.nIdx`, the
target check's count at the instantiation): the recorded index telescope
of the major's inductive, at the instantiation's levels, has `M.nIdx`
entries (`instPis_count_of_read`). -/
theorem tgtOutIdx_len
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
      = (tgtMajor out j).ds.length) :
    (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
      = (tgtMajor out j).nIdx := by
  obtain ⟨rc, u, -, ⟨E⟩⟩ := targetEntryAt R hr
  obtain ⟨sI, -, -, -, -, -, -, -, -, hinst, -⟩ := E.outside_of hMo
  obtain ⟨cvI', caps', ty, s, hf', hty, hs, hr'⟩ := targetOutsideInst_inv hinst
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [mkFEnv_find?, hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
  obtain ⟨hC, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
  rw [hcl.hmem, hfI] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  generalize hψ : Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls = ψ' at hlenP ⊢
  obtain ⟨ab, hta, hmap, -⟩ := hab ψ'
  have hc := instPis_count_of_read hta cvI.levelParams (tgtMajor out j).lvls hty hs
  have hpl := hC.parsLen mm hcl.hmm ψ'
  have habl : ab.length = (D.pars mm ψ').length + (D.ids mm ψ').length := by
    have := congrArg List.length hmap
    simpa using this
  have hn : (tgtMajor out j).nIdx = ty.piBinders.1.length := congrArg Prod.fst hr'
  omega

set_option maxHeartbeats 1000000 in
/-- **Row `hsplit` at an outside class**: a spine fitting the `j`-th
recursor type's binder data splits into the prefix (fitting the rule's
prefix domains), the index values (fitting the container's index
telescope at the key frame, so their tuple lies in the index set) and
the major, which lies in the container's carrier at that tuple
(`keyLeaf`: the major's domain `I.{us} D⃗ i⃗` is the clause's leaf). -/
theorem tgtOutSplit (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ ys : List V,
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
        (·.2.2)) ys →
      (prefOf (tgtRP pp.toBlockShape j) ys).length = tgtRP pp.toBlockShape j ∧
      ys = prefOf (tgtRP pp.toBlockShape j) ys
        ++ (idxOf (tgtRP pp.toBlockShape j) ys ++ [majOf ys]) ∧
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
        (prefOf (tgtRP pp.toBlockShape j) ys) ∧
      SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList (prefOf (tgtRP pp.toBlockShape j) ys) ρ))
        (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        (idxOf (tgtRP pp.toBlockShape j) ys) ∧
      tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          (idxOf (tgtRP pp.toBlockShape j) ys)
        ∈ˢ D.idx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
            (tgtRP pp.toBlockShape j) (consList (prefOf (tgtRP pp.toBlockShape j) ys) ρ)) mm ∧
      majOf ys ∈ˢ app (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
            (tgtRP pp.toBlockShape j) (consList (prefOf (tgtRP pp.toBlockShape j) ys) ρ)) mm)
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          (idxOf (tgtRP pp.toBlockShape j) ys)) := by
  intro ys hfit
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hlenI0 := tgtOutIdx_len R hr hMo hcl ψ hlenP
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨sI, -, hfn, -, -, -, hdsE, hdsLen, -, -, -⟩ := E.outside_of hMo
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hop' hlenRds
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans E.hopen))
  generalize hRds : blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j = rds
    at hfit hTyE hlenRds hdomsR
  have hmI := E.hmI
  -- the three parts of the spine
  have hDsLen : (rds.map (·.2.2)).length = rc.rP + (tgtMajor out j).nIdx + 1 := by
    rw [List.length_map, hlenRds, hmI]
  obtain ⟨xs, is, mj, rfl, hxl, hisl, h1, h3, h4⟩ := spineFit_split_three hDsLen hfit
  rw [hRP, prefOf_split hxl, idxOf_split hxl, majOf_split]
  have hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      = (rds.map (·.2.2)).take rc.rP := by
    rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some, hRds, List.map_take]
  refine ⟨hxl, rfl, by rw [hPd]; exact h1, ?_⟩
  -- the major's domain, at the opener's depth
  have hmajD : (rds.map (·.2.2)).getD rc.mI default = ((rds.map (·.2.2)).drop rc.rP).getD
      (tgtMajor out j).nIdx default := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, hmI]
  obtain ⟨pd, hpd, -, hrdM⟩ := hdomsR rc.mI E.maj E.hmaj
  have hDM : (rds.map (·.2.2)).getD rc.mI default = pd.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  -- the major's type is the instantiation at the parameters and the index openers
  have hsplitM : E.maj.fvarTypeD
      = Expr.mkAppN (.const (D.member mm) (tgtMajor out j).lvls)
          ((tgtMajor out j).ds ++ (E.fvs.drop rc.rP).take (rc.mI - rc.rP)) := by
    rw [hcl.hmem, ← hfn, hdsE, ← E.hmajIdx, List.take_append_drop, Expr.mkAppN_getApp]
  rw [hsplitM] at hrdM
  obtain ⟨caps, hfI⟩ := hcl.hfind
  have hisLen : ((E.fvs.drop rc.rP).take (rc.mI - rc.rP)).length = (tgtMajor out j).nIdx := by
    have hl := ConLeche.Verify.openPisAtFvars_length _ E.hopen
    rw [List.length_take, List.length_drop, hl]; omega
  obtain ⟨-, isa, hisa, hleaf⟩ := keyLeaf mpC hcl.hD hcl.hmm (by rw [hcl.hmem]; exact hfI)
    (show rc.rP ≤ rc.mI from E.hle) hrdM hlenP.symm
    (by rw [hisLen, hlenI0]) (fun x hx => by rw [← hRP]; exact (hds x hx).1)
    (by rw [← hRP]; exact hdsa)
  -- the index openers read as the index values
  have hisaE : isa = (List.range (tgtMajor out j).nIdx).map
      fun k => AnnotTerm.bvar (rc.mI - 1 - (rc.rP + k)) := by
    have hF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ) rc.mI
      ((E.fvs.drop rc.rP).take (rc.mI - rc.rP)) rc.rP (fun k x hx => by
        rw [List.getElem?_take, List.getElem?_drop] at hx
        split at hx
        · exact ConLeche.openPisAtFvars_index _ _ _ E.hopen _ x hx |>.imp fun _ h => by
            rw [h]; congr 1; omega
        · exact nomatch hx)
    rw [hisLen] at hF
    exact DenoteMetaSpine.unique hisa hF
  have hvals : isa.map (interp V (consList (xs ++ is) ρ)) = is := by
    rw [hisaE, show rc.mI = rc.rP + (tgtMajor out j).nIdx from hmI]
    exact map_fieldBvars hxl hisl
  -- the domain is graded at the prefix and index values
  have hwd : WellDenotedV V (consList (xs ++ is) ρ) pd.2.2 := by
    have htk : rds.take (rc.mI + 1) = rds := List.take_of_length_le (by omega)
    have hfitPI : SpineFit ρ (((rds.take (rc.mI + 1)).map (·.2.2)).take rc.mI) (xs ++ is) := by
      rw [htk, show rc.mI = rc.rP + (tgtMajor out j).nIdx from hmI, List.take_add]
      exact SpineFit.append h1 h3
    have := prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ j) (rds := rds) (rP := rc.mI + 1) (by omega) (fun ρ' => by
          rw [← hTyE]; exact hwdTy ρ') (Nat.lt_succ_self _) hfitPI
    rwa [htk, hDM] at this
  obtain ⟨-, hidsF, hmemE⟩ := hleaf _ hwd
  have hdrop : dropV (rc.mI - rc.rP) (consList (xs ++ is) ρ) = consList xs ρ := by
    funext k
    rw [dropV, consList_append, show rc.mI - rc.rP = is.length by rw [hisl]; omega,
      consList_apply_add]
  rw [hdrop, hvals] at hidsF hmemE
  refine ⟨hidsF, tupW_mem hidsF, ?_⟩
  have h4' : mj ∈ˢ interp V (consList (xs ++ is) ρ) pd.2.2 := by
    rw [consList_append, ← hDM, hmajD]; exact h4
  rw [hmemE] at h4'
  exact h4'

/-- **Row `hconcl` at an outside class**: the motive at the tagged index
tuple and major IS the conclusion's reading at the fitting spine — the
index values come back out of their tuple at the container's own index
telescope (`isOfW_tupW`, the clause's `idxOk` at the key frame, which
satisfies the parameter telescope by `tgtOutSat`), read at the
container's universe and the kernel's index count (`tgtOutIdx_len`). -/
theorem tgtOutConcl (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {K : Nat} {concl : Nat → AnnotTerm} {uX nIdxX : Nat → Nat} (hc : j < K)
    (huX : uX j = D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
    (hnX : nIdxX j = (tgtMajor out j).nIdx) :
    ∀ ys : List V,
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
        (·.2.2)) ys →
      blockRecMot K concl uX nIdxX ρ (prefOf (tgtRP pp.toBlockShape j) ys)
          (tagged j (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
            (idxOf (tgtRP pp.toBlockShape j) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl j) := by
  intro ys hfit
  obtain ⟨-, hdec, hpref, hidsF, -, -⟩ := tgtOutSplit hμ hcov h R hr hMo hcl ψ ρ ys hfit
  obtain ⟨dsa, hdsa, -, -, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hlenI := tgtOutIdx_len R hr hMo hcl ψ hlenP
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  have hIdx := hC.idxOk _ _ (hsatF ρ _ hpref) mm (Nat.lt_of_lt_of_le hcl.hmm hC.kN)
  have hret : isOfW (uX j) (nIdxX j)
      (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        (idxOf (tgtRP pp.toBlockShape j) ys)) = idxOf (tgtRP pp.toBlockShape j) ys := by
    rw [huX, hnX, ← hlenI]
    exact isOfW_tupW hIdx hidsF
  rw [blockRecMot_tagged hc, hret, ← hdec]

end Rows

end ConLeche.Model
