import Setlec.Model.Core.Claims

/-!
# Checker-core soundness: PairEta

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A successful pair-eta certification identifies the constructor
application's interpretation with the stuck side's: both are the pair
of the stuck side's components (or the proof point at the Prop
collapse). -/
theorem pairEta_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : pairEtaCertP env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    mIr, rPr, r, rfl, hfindM, htb, hwtb, hfindI, hfr, hrc, hrf, hmirp,
    hgres, hlev, hd1, hd2⟩ := pairEtaCert_inv h
  -- identify the structure through the pinned recursor, then the
  -- constructor through the recursor's rule
  obtain ⟨hpr, -⟩ := m.ind_ok.right.right.right.left _ _ hfr rfl hgres
  have hcn' : c' = psigmaName := by
    rcases pinnedInfo_recInfo_cases hpr.symm
      with hc' | hc' | hc' | hc' | hc' | hc' | hc'
    · rw [hc'] at hpr
      rw [show pinnedInfo (eqName.str "rec") = eqRecA from rfl] at hpr
      have h1 := congrArg ConstantInfo.recNi hpr
      rw [hmirp] at h1
      simp [eqRecA, ConstantInfo.recNi] at h1
    · rw [hc'] at hpr
      exact nomatch
        (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
    · injection hc'
    · rw [hc'] at hpr
      have hr : r.nfields = 0 :=
        congrArg (fun ci =>
          ((ConstantInfo.recRules ci).getD 0 default).nfields) hpr
      rw [hrf] at hr
      exact nomatch hr
    · rw [hc'] at hpr
      exact nomatch
        (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
    · exact absurd hc' (by simp [quotLiftName, quotName])
    · exact absurd hc' (by simp [quotIndName, quotName])
  subst hcn'
  have hcn : c = psigmaMkName := by
    have hr : r.ctor = psigmaMkName :=
      congrArg (fun ci =>
        ((ConstantInfo.recRules ci).getD 0 default).ctor) hpr
    rw [← hrc]
    exact hr
  subst hcn
  -- b's type reduces to the pair type; extract the sigma facts
  obtain ⟨⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ := ihi htb hwb hbb hLbb hokb hab
  have hvbeq : vb' = vb := by
    rw [hvb] at hbi
    exact (Option.some.inj hbi).symm
  rw [hvbeq] at hmemb
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiw, haPi⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hPii : interpExpr V m.val env φ d ρ
      (.app (.app (.const psigmaName us') A) B) = some vtb := by
    rw [hiw]; exact htbi
  try simp only [AnnotOk] at haPi
  obtain ⟨haCA, haB, vf₁, vB, vE₁, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁, hfib₁⟩ := haPi
  try simp only [AnnotOk] at haCA
  obtain ⟨hac, haA, vf₀, vA, vE₀, A₀, B₀, hci, hAi, hpi₀, hvA₀, hfib₀⟩ := haCA
  obtain ⟨hlpI, htyf⟩ := m.ind_ok.1 cvi capsi hfindI
  obtain ⟨ψt, hψt⟩ : ∃ ψt, ψt = Level.substFn φ cvi.levelParams us' := ⟨_, rfl⟩
  have hci' := hci
  rw [interpExpr, hfindI] at hci'
  dsimp only [ConstantInfo.toConstantVal] at hci'
  rw [← hψt] at hci'
  by_cases halI : us'.length = cvi.levelParams.length
  case neg => simp only [halI, if_false] at hci'; exact nomatch hci'
  simp only [halI, if_true] at hci'
  have hvalI : interpExpr V m.val env φ d ρ (.const psigmaName us') =
      some (m.val psigmaName ψt) := by
    rw [interpExpr, hfindI]
    dsimp only [ConstantInfo.toConstantVal]
    rw [← hψt]
    simp only [halI, if_true]
  have hvf₀ : vf₀ = m.val psigmaName ψt := (Option.some.inj hci').symm
  have hfacts := htyf ψt
  have hAmem : vA ∈ˢ univ (ψt uN) := hfacts.dom₀ (hvf₀ ▸ hpi₀) hvA₀
  have hf₁ : vf₁ = app (m.val psigmaName ψt) vA := by
    rw [interpExpr, hvalI, hAi] at hf₁i
    dsimp only at hf₁i
    exact (Option.some.inj hf₁i).symm
  have hBmem : vB ∈ˢ pi (ψt vN + 1) vA (fun _ => univ (ψt vN)) :=
    hfacts.dom₁ hAmem (hf₁ ▸ hpi₁) hvB₁
  have hfold : vtb = sigmaSet (Nat.max (ψt uN) (ψt vN)) vA
      (fun x => app vB x) := by
    rw [interpExpr, hf₁i, hBi] at hPii
    dsimp only at hPii
    have := Option.some.inj hPii
    rw [← this, hf₁, hfacts.fold hAmem hBmem]
  have hvbmem : vb ∈ˢ sigmaSet (Nat.max (ψt uN) (ψt vN)) vA
      (fun x => app vB x) := by
    rw [← hfold]
    exact hmemb
  have hfibB : ∀ x, x ∈ˢ vA → app vB x ∈ˢ univ (ψt vN) := fun x hx =>
    app_mem hBmem hx fun _ _ => univ_mem_univ _
  -- decompose the constructor application's annotations
  simp only [AnnotOk] at haa
  obtain ⟨haa3, has₂, vf₃, vs₂, vE₃, A₃, B₃, hf₃i, hs₂i, hpi₃, hvs₂, hfib₃⟩ := haa
  try simp only [AnnotOk] at haa3
  obtain ⟨haa2, has₁, vf₂, vs₁, vE₂, A₂, B₂, hf₂i, hs₁i, hpi₂, hvs₁, hfib₂⟩ := haa3
  try simp only [AnnotOk] at haa2
  obtain ⟨haa1, hapβ, vf₁m, vpβ, vE₁m, A₁m, B₁m, hf₁mi, hpβi, hpi₁m, hvpβ, hfib₁m⟩ := haa2
  try simp only [AnnotOk] at haa1
  obtain ⟨hacm, hapα, vf₀m, vpα, vE₀m, A₀m, B₀m, hcmi, hpαi, hpi₀m, hvpα, hfib₀m⟩ := haa1
  obtain ⟨hnP2, hnF2, hlpM, hmkfAll⟩ := m.ind_ok.right.left cvm 2 2 hfindM
  obtain ⟨ψk, hψk⟩ : ∃ ψk, ψk = Level.substFn φ cvm.levelParams us := ⟨_, rfl⟩
  have hcmi' := hcmi
  rw [interpExpr, hfindM] at hcmi'
  dsimp only [ConstantInfo.toConstantVal] at hcmi'
  rw [← hψk] at hcmi'
  by_cases halM : us.length = cvm.levelParams.length
  case neg => simp only [halM, if_false] at hcmi'; exact nomatch hcmi'
  simp only [halM, if_true] at hcmi'
  have hvf₀m : vf₀m = m.val psigmaMkName ψk := (Option.some.inj hcmi').symm
  have hmkf := hmkfAll ψk
  have hψeq : ψk = ψt := by
    rw [hψk, hψt, hlpM, hlpI]
    exact Level.substFn_congr (Level.isEquivList_sound hlev φ)
  -- the application chain of values
  have hvf₁m : vf₁m = app (m.val psigmaMkName ψk) vpα := by
    rw [interpExpr, hcmi, hpαi] at hf₁mi
    dsimp only at hf₁mi
    rw [hvf₀m] at hf₁mi
    exact (Option.some.inj hf₁mi).symm
  have hvf₂ : vf₂ = app vf₁m vpβ := by
    rw [interpExpr, hf₁mi, hpβi] at hf₂i
    dsimp only at hf₂i
    exact (Option.some.inj hf₂i).symm
  have hvf₃ : vf₃ = app vf₂ vs₁ := by
    rw [interpExpr, hf₂i, hs₁i] at hf₃i
    dsimp only at hf₃i
    exact (Option.some.inj hf₃i).symm
  have hva' : va = app vf₃ vs₂ := by
    rw [interpExpr, hf₃i, hs₂i] at hva
    dsimp only at hva
    exact (Option.some.inj hva).symm
  have hva'' : va = app (app (app (app (m.val psigmaMkName ψk) vpα) vpβ)
      vs₁) vs₂ := by
    rw [hva', hvf₃, hvf₂, hvf₁m]
  -- the components are the stuck side's projections
  have hproj0i : interpExpr V m.val env φ d ρ (.proj psigmaName 0 b) =
      some (sfst vb) := by
    simp only [interpExpr, hvb]
    rfl
  have hproj1i : interpExpr V m.val env φ d ρ (.proj psigmaName 1 b) =
      some (ssnd vb) := by
    simp only [interpExpr, hvb]
    rfl
  have hwp : ∀ i, WScoped d (Expr.proj psigmaName i b) := fun _ => by
    simp only [WScoped]
    exact hwb
  have hbp : ∀ i, (Expr.proj psigmaName i b).looseBVarsBounded 0 = true := by
    intro i
    simpa [looseBVarsBounded] using hbb
  have hLbp : ∀ i, Expr.LeavesBounded (Expr.proj psigmaName i b) := fun i l hl =>
    hLbb l (by simpa [fvarLeaves] using hl)
  have hokp : ∀ i, FvarsOk V m.val env φ d ρ (Expr.proj psigmaName i b) :=
    fun i => FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hokb
  have hap : ∀ i, i < 2 → AnnotOk V m.val env φ d ρ (Expr.proj psigmaName i b) := by
    intro i hi
    simp only [AnnotOk]
    exact ⟨hab, hi, vb, ψt uN, ψt vN, vA, (fun x => app vB x),
      hvb, hvbmem, hAmem, hfibB⟩
  -- hypothesis sets for the components
  simp only [WScoped] at hwa
  obtain ⟨⟨⟨⟨-, hwpα⟩, hwpβ⟩, hws₁⟩, hws₂⟩ := hwa
  simp only [looseBVarsBounded, Bool.and_eq_true] at hba
  obtain ⟨⟨⟨⟨-, hbpα⟩, hbpβ⟩, hbs₁⟩, hbs₂⟩ := hba
  have hLbs₁ : Expr.LeavesBounded s₁ := fun l hl =>
    hLba l (by simp [fvarLeaves, hl])
  have hLbs₂ : Expr.LeavesBounded s₂ := fun l hl =>
    hLba l (by simp [fvarLeaves, hl])
  have hoks₁ : FvarsOk V m.val env φ d ρ s₁ :=
    FvarsOk.of_subset (fun l hl => by simp [fvarLeaves, hl]) hoka
  have hoks₂ : FvarsOk V m.val env φ d ρ s₂ :=
    FvarsOk.of_subset (fun l hl => by simp [fvarLeaves, hl]) hoka
  have hs₁eq : vs₁ = sfst vb :=
    ihd hd1 hws₁ (hwp 0) hbs₁ (hbp 0) hLbs₁ (hLbp 0) hoks₁ (hokp 0)
      has₁ (hap 0 (by omega)) hs₁i hproj0i
  have hs₂eq : vs₂ = ssnd vb :=
    ihd hd2 hws₂ (hwp 1) hbs₂ (hbp 1) hLbs₂ (hLbp 1) hoks₂ (hokp 1)
      has₂ (hap 1 (by omega)) hs₂i hproj1i
  by_cases hw : Nat.max (ψk uN) (ψk vN) = 0
  · -- Prop collapse: both sides are the proof point
    rw [hva'', hmkf.zero hw vpα vpβ vs₁ vs₂]
    obtain ⟨a', b', -, -, hpt0, -⟩ := mem_sigma_elim hvbmem
    have hw' : Nat.max (ψt uN) (ψt vN) = 0 := hψeq ▸ hw
    rw [hpt0 hw']
  · -- the pair of the stuck side's components
    have hα : vpα ∈ˢ univ (ψk uN) := hmkf.dom₀ hw (hvf₀m ▸ hpi₀m) hvpα
    have hβ : vpβ ∈ˢ pi (ψk vN + 1) vpα (fun _ => univ (ψk vN)) :=
      hmkf.dom₁ hw hα (hvf₁m ▸ hpi₁m) hvpβ
    have hs₁m : vs₁ ∈ˢ vpα :=
      hmkf.dom₂ hw hα hβ ((hvf₂.trans (by rw [hvf₁m])) ▸ hpi₂) hvs₁
    have hs₂m : vs₂ ∈ˢ app vpβ vs₁ :=
      hmkf.dom₃ hw hα hβ hs₁m
        ((hvf₃.trans (by rw [hvf₂, hvf₁m])) ▸ hpi₃) hvs₂
    rw [hva'', hmkf.fold hα hβ hs₁m hs₂m, if_neg hw, hs₁eq, hs₂eq]
    obtain ⟨a', b', -, -, -, hpair⟩ := mem_sigma_elim hvbmem
    have hw' : ¬ Nat.max (ψt uN) (ψt vN) = 0 := by
      rw [← hψeq]
      exact hw
    rw [hpair hw', sfst_spair, ssnd_spair]

end Claims

end Setlec
