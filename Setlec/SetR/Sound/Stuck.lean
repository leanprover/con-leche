import Setlec.SetR.Sound.Rigidity
import Setlec.Verify.PinnedShapes

/-!
# Soundness cases — the stuck cascade and the rescues (task #148, T4, batch d)

D10 `structEta` / D11 `structUnit` consume the fired capability laws
(`EnvSHyp.caps_ok` — the `structEta_sound`/`structUnit_sound`
re-hangs); D12 `pairEta` is the pinned-pair rigidity elimination
(`mem_psigmaV_app` + `mem_sigma_elim` + `psigmaMkV_app`/`psigmaMkV_zero`
— the `pairEta_sound` re-hang, with the (now deleted) tt-only
`projParamCert`'s role played by off-domain emptiness); R12–R14 (the `majorToCtor` rescues)
take their equalities from their `DefEq` certificate premises and
rebuild the fabrication's truthfulness through `TeleFitV.appN_annot`
(the `majorToCtor_claims` re-hang, split by branch).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ### The rescues (R12–R14) -/

/-- The shared fabrication package: a constructor head applied along a
certified telescope spine is truthful.  Extracted because all three
rescues and the iota reduct use it verbatim. -/
theorem fab_annot (henv : EnvSHyp V env cval φ) {Δ : List VExpr}
    {cvj : ConstantVal} {cnP cnF : Nat} {cj : Name} {ust : List Level}
    {TVj rest : VExpr} {ts : List VExpr} {ρ : Nat → V}
    (hΔ : Sat V Δ ρ)
    (hfc : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hlen : cvj.levelParams.length = ust.length)
    (hden : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (ihT : TeleS V Δ TVj ts rest) :
    AnnotOkV V ρ
      (VExpr.mkAppN (cval cj (Level.substFn φ cvj.levelParams ust)) ts) := by
  obtain ⟨hfit, hargs, -⟩ := ihT ρ hΔ
  obtain ⟨hmem, hok⟩ :=
    henv.mem_type cj _ hfc ust hlen.symm TVj hden ρ
  exact TeleFitV.appN_annot V hfit hok hargs hmem (henv.annot_okV _ _ ρ)

theorem sndRedRescueK (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {m₀ tm TM tf TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (_ : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (_ : (cvj.type.piResult).getAppFn = .const T tus)
    (_ : env.find? T = some (.indInfo cvT caps))
    (_ : caps.ruleK = true) (_ : cnF = 0)
    (h7 : cvj.levelParams.length = ust.length)
    (_ : ust.length = cvT.levelParams.length)
    (_ : cnP ≤ ts.length)
    (_ : (cvj.type.stripPis cnP).isSome = true)
    (_ : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h12 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (_ : VExpr.Closed TVj)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : DefEq μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj (ts.take cnP) rest)
    (_ : Infer μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) tf)
    (_ : DefEq μ env cval φ Δ TM tf)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) m₀)
    (_ : InfS V Δ m₀ tm) (_ : DeqS V Δ tm TM)
    (ih15 : TeleS V Δ TVj (ts.take cnP) rest)
    (_ : InfS V Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) tf)
    (_ : DeqS V Δ TM tf)
    (ih18 : DeqS V Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) m₀) :
    RedS V Δ m₀
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) := by
  intro ρ hΔ
  exact ⟨(ih18 ρ hΔ).symm,
    fun _ => fab_annot henv hΔ h2 h7 h12 ih15⟩

theorem sndRedRescueEta (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (_ : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (_ : (cvj.type.piResult).getAppFn = .const T tus)
    (_ : env.find? T = some (.indInfo cvT caps))
    (_ : caps.eta = true) (h6 : rl.ctor = caps.etaCtor)
    (_ : Name.isProjFnShape recName = false)
    (_ : ts.length = caps.etaParams)
    (_ : ust.length = cvT.levelParams.length)
    (_ : piResultNeverZero cvT.levelParams ust cvT.type = true)
    (h11 : cvj.levelParams.length = ust.length)
    (_ : (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome
      = true)
    (_ : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h14 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (_ : VExpr.Closed TVj)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : DefEq μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj
      (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
        caps.etaFields) rest)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) m₀)
    (_ : InfS V Δ m₀ tm) (_ : DeqS V Δ tm TM)
    (ih17 : TeleS V Δ TVj
      (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
        caps.etaFields) rest)
    (ih18 : DeqS V Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) m₀) :
    RedS V Δ m₀
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) := by
  intro ρ hΔ
  refine ⟨(ih18 ρ hΔ).symm, fun _ => ?_⟩
  have := fab_annot henv hΔ (cj := rl.ctor) h2 h11 h14 ih17
  rwa [h6] at this

theorem sndRedRescueUnit0 (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (_ : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (_ : (cvj.type.piResult).getAppFn = .const T tus)
    (_ : env.find? T = some (.indInfo cvT caps))
    (_ : caps.eta = true) (h6 : rl.ctor = caps.etaCtor)
    (_ : Name.isProjFnShape recName = false)
    (_ : caps.etaFields = 0)
    (_ : ts.length = caps.etaParams)
    (_ : ust.length = cvT.levelParams.length)
    (_ : piResultNeverZero cvT.levelParams ust cvT.type = true)
    (h12 : cvj.levelParams.length = ust.length)
    (_ : (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome
      = true)
    (_ : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h15 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (_ : VExpr.Closed TVj)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : DefEq μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj ts rest)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts) m₀)
    (_ : InfS V Δ m₀ tm) (_ : DeqS V Δ tm TM)
    (ih18 : TeleS V Δ TVj ts rest)
    (ih19 : DeqS V Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts)
      m₀) :
    RedS V Δ m₀
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts) := by
  intro ρ hΔ
  refine ⟨(ih19 ρ hΔ).symm, fun _ => ?_⟩
  have := fab_annot henv hΔ (cj := rl.ctor) h2 h12 h15 ih18
  rwa [h6] at this

/-! ### D10: structural eta -/

theorem sndDeqStructEta (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {b tb TFv restT : VExpr}
    {c T : Name} {cvc cvT : ConstantVal} {caps : IndCaps}
    {cnP cnF : Nat} {us us' : List Level} {as ts : List VExpr}
    {cvp : Nat → ConstantVal} {mIp rPp : Nat → Nat}
    {rulesP : Nat → List RecRule} {TPv restP : Nat → VExpr}
    (h1 : env.find? c = some (.ctorInfo cvc cnP cnF))
    (_ : as.length = cnP + cnF)
    (h3 : env.find? T = some (.indInfo cvT caps))
    (h4 : caps.eta = true) (h5 : caps.etaCtor = c)
    (h6 : caps.etaParams = cnP) (h7 : caps.etaFields = cnF)
    (h8 : reservedBasisNames.contains T = false)
    (h9 : reservedBasisNames.contains c = false)
    (h10 : ts.length = cnP)
    (_ : us'.length = cvT.levelParams.length)
    (h12 : cvc.levelParams = cvT.levelParams)
    (_ : (cvT.type.stripPis cnP).isSome = true)
    (h14 : Level.isEquivList us us' = some true)
    (h15 : denoteClosed cval env φ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv)
    (_ : VExpr.Closed TFv)
    (h16 : ∀ j, j < cnF →
      env.find? (projFnName T j)
        = some (.recInfo (cvp j) (mIp j) (rPp j) (rulesP j)))
    (_ : ∀ j, j < cnF → (cvp j).levelParams = cvT.levelParams)
    (_ : ∀ j, j < cnF → ((cvp j).type.stripPis (cnP + 1)).isSome = true)
    (_ : ∀ j, j < cnF →
      denoteClosed cval env φ
        ((cvp j).type.instantiateLevelParams (cvp j).levelParams us')
        = some (TPv j))
    (_ : ∀ j, j < cnF → VExpr.Closed (TPv j))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : DefEq μ env cval φ Δ tb
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (_ : Tele μ env cval φ Δ TFv ts restT)
    (_ : ∀ j, j < cnF →
      Tele μ env cval φ Δ (TPv j) (ts ++ [b]) (restP j))
    (_ : DefEqL μ env cval φ Δ (as.take cnP) ts)
    (_ : DefEqL μ env cval φ Δ (as.drop cnP)
      (projSpinesV cval T (Level.substFn φ cvT.levelParams us') ts b
        cnF))
    (ihb : InfS V Δ b tb)
    (ihr : DeqS V Δ tb
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (ihT : TeleS V Δ TFv ts restT)
    (_ : ∀ j (_ : j < cnF),
      TeleS V Δ (TPv j) (ts ++ [b]) (restP j))
    (ih24 : DeqLS V Δ (as.take cnP) ts)
    (ih25 : DeqLS V Δ (as.drop cnP)
      (projSpinesV cval T (Level.substFn φ cvT.levelParams us') ts b
        cnF)) :
    DeqS V Δ
      (VExpr.mkAppN (cval c (Level.substFn φ cvc.levelParams us)) as)
      b := by
  intro ρ hΔ
  -- the family is a stored eta family
  have hfam : EtaFamilyStored env T caps := by
    refine ⟨by rw [h5]; exact h9, ⟨cvc, ?_⟩, ?_⟩
    · rw [h5, h6, h7]; exact h1
    · intro j hj
      rw [h7] at hj
      exact ⟨_, _, _, _, h16 j hj⟩
  have hlaw := (henv.caps_ok.1 T cvT caps h3 h4 h8 hfam) φ us' ρ ts TFv
    restT b (by rw [h6]; exact h10) h15 (ihT ρ hΔ).1
  -- the stuck side inhabits the family instance
  have hmem : interp V ρ b ∈ˢ interp V ρ
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts) :=
    (ihr ρ hΔ) ▸ (ihb ρ hΔ).2
  have hb := hlaw hmem
  rw [h5, h7] at hb
  rw [hb]
  -- the two spines interpret equally, argument by argument
  have hψ : Level.substFn φ cvc.levelParams us
      = Level.substFn φ cvT.levelParams us' := by
    rw [h12]
    exact Level.substFn_congr (Level.isEquivList_sound h14 φ)
  rw [interp_mkAppN_map, interp_mkAppN_map, hψ]
  congr 1
  rw [etaFabArgsV, ← List.take_append_drop cnP as, List.map_append,
    List.map_append, ih24 ρ hΔ, ih25 ρ hΔ]

/-! ### D11: unit-likeness -/

theorem sndDeqStructUnit (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {a b ta tb TB TFv rest : VExpr}
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    {us' : List Level} {ts : List VExpr}
    (h1 : env.find? T = some (.indInfo cvT caps))
    (h2 : caps.unitlike = true)
    (h3 : reservedBasisNames.contains T = false)
    (h4 : ts.length = caps.unitParams)
    (_ : us'.length = cvT.levelParams.length)
    (_ : (cvT.type.stripPis caps.unitParams).isSome = true)
    (h7 : denoteClosed cval env φ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv)
    (_ : VExpr.Closed TFv)
    (_ : Infer μ env cval φ Δ a ta)
    (_ : DefEq μ env cval φ Δ ta
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : DefEq μ env cval φ Δ tb TB)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts)
      TB)
    (_ : Tele μ env cval φ Δ TFv ts rest)
    (iha : InfS V Δ a ta)
    (ihra : DeqS V Δ ta
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (ihb : InfS V Δ b tb)
    (ihrb : DeqS V Δ tb TB)
    (ihst : DeqS V Δ
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts)
      TB)
    (ihT : TeleS V Δ TFv ts rest) :
    DeqS V Δ a b := by
  intro ρ hΔ
  have hlaw := (henv.caps_ok.2 T cvT caps h1 h2 h3) φ us' ρ ts TFv rest
    (interp V ρ a) (interp V ρ b) h4 h7 (ihT ρ hΔ).1
  refine hlaw ((ihra ρ hΔ) ▸ (iha ρ hΔ).2) ?_
  have hb : interp V ρ b ∈ˢ interp V ρ TB := (ihrb ρ hΔ) ▸ (ihb ρ hΔ).2
  exact (ihst ρ hΔ).symm ▸ hb

/-! ### D12: pair eta (the pinned-pair rigidity elimination) -/

theorem sndDeqPairEta (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {pα pβ s₁ s₂ b tb A B : VExpr}
    {c c' : Name} {cvm : ConstantVal} {cvi : ConstantVal}
    {caps' : IndCaps} {cvr : ConstantVal} {mI rP : Nat} {rr : RecRule}
    {us us' : List Level}
    (h1 : env.find? c = some (.ctorInfo cvm 2 2))
    (h2 : env.find? c' = some (.indInfo cvi caps'))
    (h3 : env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]))
    (h4 : rr.ctor = c) (h5 : rr.nfields = 2) (h6 : mI = rP)
    (h7 : reservedBasisNames.contains (c'.str "rec") = true)
    (h8 : Level.isEquivList us us' = some true)
    (_ : us.length = cvm.levelParams.length)
    (_ : us'.length = cvi.levelParams.length)
    (_ : Infer μ env cval φ Δ b tb)
    (_ : DefEq μ env cval φ Δ tb
      (.app (.app (cval c' (Level.substFn φ cvi.levelParams us')) A) B))
    (_ : DefEq μ env cval φ Δ pα A) (_ : DefEq μ env cval φ Δ pβ B)
    (_ : DefEq μ env cval φ Δ s₁ (.proj 0 b))
    (_ : DefEq μ env cval φ Δ s₂ (.proj 1 b))
    (ihb : InfS V Δ b tb)
    (ihr : DeqS V Δ tb
      (.app (.app (cval c' (Level.substFn φ cvi.levelParams us')) A) B))
    (ihα : DeqS V Δ pα A) (ihβ : DeqS V Δ pβ B)
    (ih1 : DeqS V Δ s₁ (.proj 0 b)) (ih2 : DeqS V Δ s₂ (.proj 1 b)) :
    DeqS V Δ
      (.app (.app (.app (.app
        (cval c (Level.substFn φ cvm.levelParams us)) pα) pβ) s₁) s₂)
      b := by
  intro ρ hΔ
  -- identify the pinned pair
  obtain ⟨hc', hctor⟩ := pairLike_eq_psigma henv.basis_pinned h3 h5 h6 h7
  subst hc'
  obtain rfl : c = psigmaMkName := by rw [← h4, hctor]
  -- the pinned declarations fix the level-parameter lists
  have hcvm : cvm.levelParams = [uN, vN] := by
    have h := (henv.basis_pinned _ _ h1 (by decide)).1 rfl
    rw [show pinnedInfo psigmaMkName = psigmaMkA from rfl] at h
    unfold psigmaMkA at h
    injection h with h
    rw [h]
    rfl
  have hcvi : cvi.levelParams = [uN, vN] := by
    have h := (henv.basis_pinned _ _ h2 (by decide)).1 rfl
    rw [show pinnedInfo psigmaName = psigmaA from rfl] at h
    unfold psigmaA at h
    injection h with h
    rw [h]
    rfl
  -- the two instantiations agree, named once
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = Level.substFn φ cvi.levelParams us' :=
    ⟨_, rfl⟩
  have hψ : Level.substFn φ cvm.levelParams us = ψ := by
    rw [hψdef, hcvm, hcvi]
    exact Level.substFn_congr (Level.isEquivList_sound h8 φ)
  -- the pinned valuations
  have hvi : cval psigmaName ψ = .const .psigma [ψ uN, ψ vN] :=
    (henv.basis_pinned _ _ h2 (by decide)).2 _ ψ rfl
  have hvm : cval psigmaMkName ψ = .const .psigmaMk [ψ uN, ψ vN] :=
    (henv.basis_pinned _ _ h1 (by decide)).2 _ ψ rfl
  -- the stuck side is a member of the pair space: rigidity fires
  have hmem : interp V ρ b ∈ˢ
      SetTheory.app (SetTheory.app (psigmaV V (ψ uN) (ψ vN))
        (interp V ρ A)) (interp V ρ B) := by
    have h := (ihr ρ hΔ) ▸ (ihb ρ hΔ).2
    rw [← hψdef] at h
    rw [interp_app, interp_app, hvi] at h
    exact h
  obtain ⟨hAu, hBpi, hbsig⟩ := mem_psigmaV_app hmem
  obtain ⟨a', b', ha', hb', hpt0, hpair⟩ := mem_sigma_elim hbsig
  -- both sides, componentwise
  have hs₁ : interp V ρ s₁ = sfst (interp V ρ b) := by
    rw [ih1 ρ hΔ, interp_proj, if_pos rfl]
  have hs₂ : interp V ρ s₂ = ssnd (interp V ρ b) := by
    rw [ih2 ρ hΔ, interp_proj, if_neg (by omega)]
  have hlhs : interp V ρ (.app (.app (.app (.app
      (cval psigmaMkName (Level.substFn φ cvm.levelParams us)) pα) pβ)
        s₁) s₂)
      = SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkV V (ψ uN) (ψ vN)) (interp V ρ A)) (interp V ρ B))
          (sfst (interp V ρ b))) (ssnd (interp V ρ b)) := by
    simp only [interp_app, hψ, hvm, ihα ρ hΔ, ihβ ρ hΔ, hs₁, hs₂]
    rfl
  rw [hlhs]
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · rw [psigmaMkV_zero hw, app_pt, app_pt, app_pt, app_pt, hpt0 hw]
  · have hb : interp V ρ b = spair a' b' := hpair hw
    rw [hb, sfst_spair, ssnd_spair,
      psigmaMkV_app V hAu hBpi ha' hb', if_neg hw]

end Cases

end Setlec.SetR
