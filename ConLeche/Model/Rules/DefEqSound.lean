module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of the definitional-equality rules (task #305, lanes
S-defeq / S-caps)

One lemma per constructor of `DefEq`.  Lane S-defeq owns `refl` …
`proofIrrel` (the structural rules, the recursive-structure rule, η,
the two proof-irrelevance arms); lane S-caps owns `unitLike`,
`structEta`, `structUnit` (the capability rows of
`Model/Steps/CapsRows.lean` and `Irrel.lean`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem DefEq.refl_sound {d : Nat} {a : Expr} : DefEqSem m φ d a a := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  rw [haa] at hba
  cases hba
  rfl

theorem DefEq.symm_sound {d : Nat} {a b : Expr} (h : DefEqSem m φ d a b) :
    DefEqSem m φ d b a := by
  intro hfb hfa Δa ba aa hCb hCa hba haa hgb hga ρ hρ
  exact (h hfa hfb hCa hCb haa hba hga hgb ρ hρ).symm

/-- **The recursive-structure rule is sound**: the reduct reads, is
graded and framed (`RedSem`), so the continuation's motive applies at
it (`dq_whnfCore_package`'s content, `Steps/DefEq.lean:460`). -/
theorem DefEq.redL_sound {d : Nat} {a a' b : Expr}
    (ha : RedSem m φ d a a') (hb : DefEqSem m φ d a' b) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨hfa', hsub, aa', haa', hga', heq⟩ := ha hfa hCa haa hga
  rw [heq ρ hρ]
  exact hb hfa' hfb (hCa.of_subset hsub) hCb haa' hba hga' hgb ρ hρ

/-- `defeqStuck_claim`'s sort arm (`Steps/DefEq.lean:873`). -/
theorem DefEq.sort_sound {d : Nat} {u v : Level}
    (h : Level.isEquiv u v = some true) :
    DefEqSem m φ d (.sort u) (.sort v) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  rw [denoteMeta_sort] at haa hba
  obtain rfl : aa = AnnotTerm.sort (u.eval φ) := (Option.some.inj haa).symm
  obtain rfl : ba = AnnotTerm.sort (v.eval φ) := (Option.some.inj hba).symm
  rw [Level.isEquiv_sound h φ]

/-- The `fvar` arm: the reading ignores the annotation. -/
theorem DefEq.fvar_sound {d i : Nat} {ty₁ ty₂ : Expr} :
    DefEqSem m φ d (.fvar i ty₁) (.fvar i ty₂) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  rw [denoteMeta_fvar] at haa hba
  obtain rfl : aa = AnnotTerm.bvar (d - 1 - i) := (Option.some.inj haa).symm
  obtain rfl : ba = AnnotTerm.bvar (d - 1 - i) := (Option.some.inj hba).symm
  rfl

/-- `acval_const_congr` (`Steps/DefEq.lean:844`) with `AcvalParams`
(`Model/Annot/EnvModel.lean:164`, `acvalParams m`). -/
theorem DefEq.const_sound {d : Nat} {n : Name} {us us' : List Level}
    (h : Level.isEquivList us us' = some true) :
    DefEqSem m φ d (.const n us) (.const n us') := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  obtain rfl : aa = ba := acval_const_congr' (acvalParams m) h haa hba
  rfl

/-- `denoteMeta_natZeroConst` (`Steps/DefEq.lean:99`). -/
theorem DefEq.natZero_sound {d : Nat} :
    DefEqSem m φ d (.lit (.natVal 0)) (.const natZeroName []) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv haa
  rw [denoteMeta_natZeroConst hg] at hba
  obtain rfl : ba = m.acval ConLeche.natZeroName (Level.substFn φ [] []) :=
    (Option.some.inj hba).symm
  rfl

/-- `denoteMeta_natSuccConst` (`Steps/DefEq.lean:119`): the packed
successor reads as `succ` applied to the packed predecessor. -/
theorem DefEq.natSucc_sound {d : Nat} {k : Nat} {x : Expr}
    (h : DefEqSem m φ d (.lit (.natVal k)) x) :
    DefEqSem m φ d (.lit (.natVal (k + 1))) (.app (.const natSuccName []) x) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv haa
  obtain ⟨fa, xa, hfa', hxa, rfl⟩ := denoteMeta_app_inv hba
  rw [denoteMeta_natSuccConst hg] at hfa'
  obtain rfl : fa = m.acval ConLeche.natSuccName (Level.substFn φ [] []) :=
    (Option.some.inj hfa').symm
  refine deqStep_appCong rfl (h (Frame.of_not_hasFvar rfl rfl) hfb.app_arg
    (CtxOk.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
    hCb.app_arg (denoteMeta_natLit hg) hxa ?_ (Graded.app hgb).2 ρ hρ)
  exact (Graded.app (by simpa only [natLitAV] using hga)).2

/-- `binder_congr` (`Steps/DefEq.lean:756`): equal domains, equal
bodies opened at the right domain, equal bits (`piR_zero_agree`). -/
theorem DefEq.forallE_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSem m φ d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_forallE_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_forallE_inv hba
  obtain ⟨hoT₁, hoB₁⟩ := Graded.pi hga
  obtain ⟨hoT₂, hoB₂⟩ := Graded.pi hgb
  have hdom : ∀ σ : Nat → V, Sat V Δa σ → interp V σ ta₁ = interp V σ ta₂ :=
    fun σ hσ => hty hfa.forallE_ty hfb.forallE_ty hCa.forallE_ty
      hCb.forallE_ty hta₁ hta₂ hoT₁ hoT₂ σ hσ
  rw [hpw]
  refine deqStep_piCong (hdom ρ hρ) (fun x hx => ?_)
  exact hbody (hfa.forallE_open hfb.forallE_ty) (hfb.forallE_open hfb.forallE_ty)
    (CtxOk.openCongC hCa.forallE_body hCb.forallE_ty hta₂ hoT₂ hdom)
    (CtxOk.openCongC hCb.forallE_body hCb.forallE_ty hta₂ hoT₂ hdom)
    (denoteMeta_open_rename hva₁) hva₂ hoB₁ (Graded.head_congr hdom hoB₂)
    (cons x ρ) (Sat_cons V hρ hx)

/-- `binder_congr`, the λ half. -/
theorem DefEq.lam_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSem m φ d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_lam_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_lam_inv hba
  obtain ⟨hoT₁, hoB₁⟩ := Graded.lam hga
  obtain ⟨hoT₂, hoB₂⟩ := Graded.lam hgb
  have hdom : ∀ σ : Nat → V, Sat V Δa σ → interp V σ ta₁ = interp V σ ta₂ :=
    fun σ hσ => hty hfa.lam_ty hfb.lam_ty hCa.lam_ty
      hCb.lam_ty hta₁ hta₂ hoT₁ hoT₂ σ hσ
  rw [hpw]
  refine deqStep_lamCong (hdom ρ hρ) (fun x hx => ?_)
  exact hbody (hfa.lam_open hfb.lam_ty) (hfb.lam_open hfb.lam_ty)
    (CtxOk.openCongC hCa.lam_body hCb.lam_ty hta₂ hoT₂ hdom)
    (CtxOk.openCongC hCb.lam_body hCb.lam_ty hta₂ hoT₂ hdom)
    (denoteMeta_open_rename hva₁) hva₂ hoB₁ (Graded.head_congr hdom hoB₂)
    (cons x ρ) (Sat_cons V hρ hx)

/-- Per-node congruence (`spine_congr`'s one step, `Steps/Stuck.lean:270`). -/
theorem DefEq.app_sound {d : Nat} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ d f₁ f₂) (ha : DefEqSem m φ d a₁ a₂) :
    DefEqSem m φ d (.app f₁ a₁) (.app f₂ a₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨fa₁, xa₁, hf₁, hx₁, rfl⟩ := denoteMeta_app_inv haa
  obtain ⟨fa₂, xa₂, hf₂, hx₂, rfl⟩ := denoteMeta_app_inv hba
  exact deqStep_appCong
    (hf hfa.app_fn hfb.app_fn hCa.app_fn hCb.app_fn hf₁ hf₂
      (Graded.app hga).1 (Graded.app hgb).1 ρ hρ)
    (ha hfa.app_arg hfb.app_arg hCa.app_arg hCb.app_arg hx₁ hx₂
      (Graded.app hga).2 (Graded.app hgb).2 ρ hρ)

/-- `interp_projAV_congr` (`Steps/ProjAVKit.lean:85`). -/
theorem DefEq.proj_sound {d : Nat} {s : Name} {i : Nat} {e₁ e₂ : Expr}
    (h : DefEqSem m φ d e₁ e₂) :
    DefEqSem m φ d (.proj s i e₁) (.proj s i e₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨ia₁, he₁, hrd₁⟩ := denoteMeta_proj_inv haa
  obtain ⟨ia₂, he₂, hrd₂⟩ := denoteMeta_proj_inv hba
  rcases hrd₁ with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec₁⟩
  · rcases hrd₂ with ⟨entry', hfe', rfl⟩ | ⟨hnt', -⟩
    · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
      exact interp_projAV_congr' (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
        hCb.proj_arg he₁ he₂ (Graded.projAV hga) (Graded.projAV hgb) ρ hρ)
    · rw [hnt'] at hfe; exact nomatch hfe
  · rcases hrd₂ with ⟨entry', hfe', -⟩ | ⟨-, hdec₂⟩
    · rw [hnt] at hfe'; exact nomatch hfe'
    · rcases AnnotTerm.projPair?_cases₂ hdec₁ hdec₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact deqStep_fstCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ (Graded.fst hga) (Graded.fst hgb) ρ hρ)
      · exact deqStep_sndCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ (Graded.snd hga) (Graded.snd hgb) ρ hρ)

/-- η (`etaCertStep_of_claims`, `Steps/Stuck.lean:576`: `lamR_eta`,
regime-uniform). -/
theorem DefEq.eta_sound (_hin : RulesInputs V m φ) {d : Nat}
    {ty₁ body₁ b tb ty₂ B : Expr} {m₁ m₂ : BinderMeta}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb (.forallE ty₂ B m₂))
    (hty : DefEqSem m φ d ty₂ ty₁)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSem m φ d (.lam ty₁ body₁ m₁) b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb hokA hokB ρ hρ
  obtain ⟨hwa, hba, hLa⟩ := hfa
  obtain ⟨hwb, hbb, hLb⟩ := hfb
  simp only [Expr.WScoped] at hwa
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba
  have hLty : Expr.LeavesBounded ty₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hLbd : Expr.LeavesBounded body₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hfty : Frame d ty₁ := ⟨hwa.1, hba.1, hLty⟩
  have hCty : CtxOk m φ d Δa ty₁ := hCa.lam_ty
  have hCbd : CtxOk m φ d Δa body₁ := hCa.lam_body
  -- the λ's own reading, and its two gradings
  obtain ⟨ta, bda, hta, hbda, rfl⟩ := denoteMeta_lam_inv hda
  obtain ⟨hokTa, hokBda⟩ := Graded.lam hokA
  -- `b`'s inferred type, its reduct, and both readings
  obtain ⟨hftb, hsubtb, tba, htba, hokTb, hmemB⟩ :=
    htb ⟨hwb, hbb, hLb⟩ hCb hdb hokB
  have hCtb : CtxOk m φ d Δa tb := hCb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hokW, heqW⟩ := hwtb hftb hCtb htba hokTb
  have hCwr : CtxOk m φ d Δa (Expr.forallE ty₂ B m₂) := hCtb.of_subset hsubW
  obtain ⟨ta₂, ba₂, hta₂, -, rfl⟩ := denoteMeta_forallE_inv hwtba
  obtain ⟨hokTa₂, -⟩ := Graded.pi hokW
  -- premise one: the two domains agree
  have hdom : ∀ σ : Nat → V, Sat V Δa σ → interp V σ ta₂ = interp V σ ta :=
    fun σ hσ => hty hfW.forallE_ty hfty hCwr.forallE_ty hCty hta₂ hta
      hokTa₂ hokTa σ hσ
  -- premise two: `b` inhabits the product the ∀-type names
  have hmem : ∀ σ : Nat → V, Sat V Δa σ →
      interp V σ ba ∈ˢ piR (pwBit φ m₂.pw) (interp V σ ta₂)
        (fun x => interp V (cons x σ) ba₂) := by
    intro σ hσ
    have hm := hmemB σ hσ
    rw [heqW σ hσ, interp_pi] at hm
    exact hm
  -- premise three: the two bits are equal (the rule's own `pw` premise)
  have hbit : pwBit φ m₁.pw = pwBit φ m₂.pw := by rw [hpw]
  -- premise four: the λ's fibre is `app ⟦b⟧`
  have hdbUp : denoteMeta m.acval env φ (d + 1) b = some ba.lift := by
    rw [denoteMeta_weaken_top m.acval_closed hwb, hdb]; rfl
  have hdapp : denoteMeta m.acval env φ (d + 1) (.app b (.fvar d ty₁))
      = some (.app ba.lift (.bvar 0)) := by
    rw [denoteMeta, hdbUp, denoteMeta_fvar]
    simp
  have hCfvar : CtxOk m φ (d + 1) (ta :: Δa) (.fvar d ty₁) := by
    have := CtxOk.openS (body := Expr.bvar 0) hCty
      (CtxOk.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves])) hta
      hokTa
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOk m φ (d + 1) (ta :: Δa) (.app b (.fvar d ty₁)) :=
    CtxOk.app (CtxOk.weakenTop hCb) hCfvar
  have hokApp : Graded V (ta :: Δa) (.app ba.lift (.bvar 0)) := by
    intro σ hσ
    have hσ' : Sat V Δa (fun j => σ (j + 1)) := Sat_tail hσ
    have hx : σ 0 ∈ˢ interp V (fun j => σ (j + 1)) ta := hσ 0 ta rfl
    have hok0 := WellDenotedV.hoist_lift (X := ta) hokB σ hσ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨hok0.1, by simp, pwBit φ m₂.pw,
        interp V (fun j => σ (j + 1)) ta₂,
        (fun x => interp V (cons x (fun j => σ (j + 1))) ba₂), ?_, ?_,
        ?_⟩
      · rw [interp_lift]; exact hmem _ hσ'
      · show σ 0 ∈ˢ _
        rw [hdom _ hσ']; exact hx
      · exact ((AnnotValid_pi V _ 0 (pwBit φ m₂.pw) ta₂ ba₂)
          ▸ (hokW _ hσ').2).2.2
    · rw [AnnotValid_app]
      exact ⟨hok0.2, by simp⟩
  have hfopen : Frame (d + 1) (body₁.instantiate1 (.fvar d ty₁)) :=
    Frame.open_body hfty hwa.2 hba.2 hLbd
  have hfapp : Frame (d + 1) (.app b (.fvar d ty₁)) := by
    refine ⟨?_, by simp [Expr.looseBVarsBounded, hbb], fun l hl => ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨Expr.WScoped.mono (by omega) hwb, by omega,
        Expr.WScoped.mono (by omega) hwa.1⟩
    · rw [ConLeche.Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h2 | h2
      · exact hLb l h2
      · rw [ConLeche.Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hba.1
        · exact hLty l h3
  have hbodyEq : ∀ σ : Nat → V, Sat V (ta :: Δa) σ →
      interp V σ bda = interp V σ (.app ba.lift (.bvar 0)) :=
    fun σ hσ => hbody hfopen hfapp (CtxOk.open hCbd hCty hta hokTa) hCapp
      hbda hdapp hokBda hokApp σ hσ
  -- η: `lamR_eta`, regime-uniform
  have hpt : ∀ x, x ∈ˢ interp V ρ ta →
      interp V (cons x ρ) bda = SetTheory.app (interp V ρ ba) x := by
    intro x hx
    rw [hbodyEq _ (Sat_cons V hρ hx), interp_app, interp_lift_cons,
      interp_bvar]
    rfl
  rw [interp_lam, lamR_congr hpt, hbit]
  exact lamR_eta (by rw [← hdom ρ hρ]; exact hmem ρ hρ)

/-- `prf_of_isProofFast` twice (`Steps/IrrelFast.lean:303`). -/
theorem DefEq.proofFast_sound (hin : RulesInputs V m φ) {d : Nat} {a b : Expr}
    (ha : ConLeche.isProofFast env.find? a = true)
    (hb : ConLeche.isProofFast env.find? b = true) :
    DefEqSem m φ d a b := by
  intro _ _ Δa aa ba hCa hCb haa hba _ _ ρ hρ
  rw [prf_of_isProofFast hin.const_ty ha hCa haa ρ hρ,
    prf_of_isProofFast hin.const_ty hb hCb hba ρ hρ]

/-- `prop_side_pt` twice (`Steps/Irrel.lean:71`): a term whose type's
sort is zero-equivalent interprets to the point. -/
theorem DefEq.proofIrrel_sound (_hin : RulesInputs V m φ) {d : Nat}
    {a ta tta b tb ttb : Expr} {u v : Level}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSem m φ d tta (.sort u)) (hu0 : Level.isEquiv u .zero = some true)
    (htb : InferSemIO m φ d b tb) (httb : InferSemIO m φ d tb ttb)
    (hv : RedSem m φ d ttb (.sort v)) (hv0 : Level.isEquiv v .zero = some true) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  rw [prop_side_pt' hta htta hu hu0 hfa hCa haa hga ρ hρ,
    prop_side_pt' htb httb hv hv0 hfb hCb hba hgb ρ hρ]

/-- `unit_side_pt` twice (`unitIrrelPQ_of_claims`, `Steps/Irrel.lean:179`). -/
theorem DefEq.unitLike_sound (_hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb wtb : Expr}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hua : ConLeche.isUnitLikeTy env wta = true)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hub : ConLeche.isUnitLikeTy env wtb = true) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  rw [unit_side_pt' hta hwta hua hfa hCa haa hga ρ hρ,
    unit_side_pt' htb hwtb hub hfb hCb hba hgb ρ hρ]

/-- Structure η (`structEtaCertWithFueled_step`, `Steps/CapsRows.lean:501`,
and `structEtaIrrel_of_claims`, `:897`): the stored η law at the
certified type application. -/
theorem DefEq.structEta_sound (hin : RulesInputs V m φ) {d : Nat}
    {a b tb wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us' : List Level} {cvT : ConstantVal}
    {caps : IndCaps}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hhead : a.getAppFn = .const c us)
    (hctor : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : a.getAppArgs.length = cnP + cnF)
    (hthead : wtb.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hetaCtor : caps.etaCtor = c)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresc : ConLeche.reservedBasisNames.contains c = false)
    (htlen : wtb.getAppArgs.length = caps.etaParams)
    (hlv : us'.length = cvT.levelParams.length)
    (hlps : cvc.levelParams = cvT.levelParams)
    (hslots : (ConLeche.towerSlotsAll env T caps.etaFields ||
      ConLeche.recSlotsAll env T caps.etaFields) = true)
    (hus : Level.isEquivList us us' = some true)
    (hcerts : CertsSem m φ d false
      (cvT.type.instantiateLevelParams cvT.levelParams us') wtb.getAppArgs)
    (hproj : ConLeche.towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsSem m φ d T us' wtb.getAppArgs b cvT.levelParams
        (List.range caps.etaFields))
    (hparams : DefEqListSem m φ d (a.getAppArgs.take caps.etaParams)
      wtb.getAppArgs)
    (hfields : DefEqListSem m φ d (a.getAppArgs.drop caps.etaParams)
      (ConLeche.etaProjs env T us' wtb.getAppArgs b caps.etaFields)) :
    DefEqSem m φ d a b := by
  sorry

/-- Unit-like structure (`structUnitIrrel_of_claims`, `Steps/CapsRows.lean:944`). -/
theorem DefEq.structUnit_sound (hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb wtb : Expr} {T : Name} {us' : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hthead : wta.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (htlen : wta.getAppArgs.length = caps.unitParams)
    (hlv : us'.length = cvT.levelParams.length)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hd : DefEqSem m φ d wta wtb)
    (hcerts : CertsSem m φ d false
      (cvT.type.instantiateLevelParams cvT.levelParams us') wta.getAppArgs) :
    DefEqSem m φ d a b := by
  sorry

end ConLeche.Model.Rules
