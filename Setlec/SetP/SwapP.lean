import Setlec.SetP.IotaRuleNestedP
import Setlec.Verify.Denote.EnvExt

/-!
# The group rule-list swap, P tier (task #161, IND TIER part 10)

`Install/SwapS.lean`'s twin one currency over: `EnvS2PM.swapP`
transports the P invariant across the step that attaches a recursor
group's checked rule lists to its rule-less provisioned entries.

The workhorse is `denoteP_env_ext` — the `denoteP` mirror of
`denote_env_ext` (`Verify/Denote/EnvExt.lean`).  It is an **equation**
with no `ConstsBound` premise, unlike the extension crossing
(`denoteP_envExtend_mono`): a swap changes no stored name, so the
reading's three environment consultations — the `.const` clause's
`find?` (through the stored level parameters only), the two literal
guards, and the string spine's `levelParamsAt` — are all congruent.
That is why every field of the invariant crosses in *both* directions
and the contravariant readings need no determinism trick here.

The three environment-level facts about the *result* — `EnvWF`,
`RecCtorsStored`, `RecRulesP` — are hypotheses, exactly as in v1: they
are what the group install proves (the last through `iotaRulesP`), and
taking them here keeps the transport free of the per-rule content.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading across a level-preserving correspondence -/

/-- **`denoteP` reads the environment only through the stored level
parameters and the two literal guards** — `denote_env_ext`'s twin.  An
equation, so a law's `denoteP` *hypotheses* and *conclusions* both move
across it for free, which is what makes the fired-form fields
transportable at all. -/
theorem denoteP_env_ext {acval : Name → (Name → Nat) → AVExpr}
    {env₁ env₂ : Env} {φ : Name → Nat}
    (henvLev : ∀ n,
      (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : Setlec.natLitSupported env₁ = Setlec.natLitSupported env₂)
    (hstr : Setlec.strLitSupported env₁ = Setlec.strLitSupported env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = env₂.findProj? sn i) :
    ∀ (d : Nat) (e : Expr),
      denoteP acval env₁ φ d e = denoteP acval env₂ φ d e := by
  intro d e
  induction d, e using denoteP.induct (env := env₁) with
  | case1 d u => rw [denoteP, denoteP]
  | case2 d idx nm ty => rw [denoteP, denoteP]
  | case3 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denoteP, hf, denoteP, hf₂]
      dsimp only
      rw [if_pos hlen, if_pos (h ▸ hlen), h]
  | case4 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denoteP, hf, denoteP, hf₂]
      dsimp only
      rw [if_neg hlen, if_neg (fun hh => hlen (h ▸ hh))]
  | case5 d n us hf =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [denoteP, hf, denoteP, hf₂]
    | some ci₂ => rw [hf₂] at h; exact nomatch h
  | case6 d n ty body m ihty ihbody =>
    rw [denoteP, denoteP, ihty, ihbody]
  | case7 d n ty body m ihty ihbody =>
    rw [denoteP, denoteP, ihty, ihbody]
  | case8 d f a ihf iha => rw [denoteP, denoteP, ihf, iha]
  | case9 d n ty val body ihty ihval ihbody =>
    rw [denoteP, denoteP, ihty, ihval, ihbody]
  | case10 d sn i e ihe =>
    rw [denoteP, denoteP, ihe, hproj sn i]
  | case11 d n hsup =>
    rw [denoteP, if_pos hsup, denoteP, if_pos (hnat ▸ hsup)]
  | case12 d n hsup =>
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hnat.trans h))]
  | case13 d s hsup =>
    rw [denoteP, if_pos hsup, denoteP, if_pos (hstr ▸ hsup),
      levelParamsAt_ext (henvLev Setlec.listNilName),
      levelParamsAt_ext (henvLev Setlec.listConsName)]
  | case14 d s hsup =>
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hstr.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat' hstr' =>
    cases x with
    | bvar i => rw [denoteP.eq_def, denoteP.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat' n)
      | strVal s => exact absurd rfl (hstr' s)

/-- The reading crosses a swap congruence. -/
theorem denoteP_swap {acval : Name → (Name → Nat) → AVExpr}
    {env₀ env₃ : Env} (hcg : Setlec.SwapCongr env₀ env₃)
    (φ : Name → Nat) (d : Nat) (e : Expr) :
    denoteP acval env₀ φ d e = denoteP acval env₃ φ d e :=
  denoteP_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq d e

/-! ## The fired modeled-iota contract across the swap -/

/-- **A fired law reads the environment only through `denoteP` and the
constructor's lookup, so it crosses the rule-list swap**
(`RecRuleLawV.swapS`'s twin).  Both carriers have the *same* `acval`;
the statement mentions the environment nowhere else. -/
theorem RecRuleLawP.swapP {env₀ env₃ : Env}
    (hcg : Setlec.SwapCongr env₀ env₃)
    {m₀ : EnvS2Core V env₀} {m₃ : EnvS2Core V env₃}
    (hac : m₃.acval = m₀.acval)
    {φ : Name → Nat} {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rl : RecRule} (h : RecRuleLawP m₀ φ n cv mI rP rl) :
    RecRuleLawP m₃ φ n cv mI rP rl := by
  have hde : ∀ (d : Nat) (e : Expr),
      denoteP m₀.acval env₀ φ d e = denoteP m₀.acval env₃ φ d e :=
    fun d e => denoteP_swap hcg φ d e
  unfold RecRuleLawP at h ⊢
  rw [hac]
  obtain ⟨hle, h⟩ := h
  refine ⟨hle, ?_⟩
  intro us hus
  obtain ⟨Ra, hRa, hokRa, hpins, hlaw⟩ := h us hus
  refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
  · rw [← hde]; exact hRa
  · -- the pins' carried readings and their guarded gradings
    intro lvls pins hfr i hi
    obtain ⟨vpa, hvpa, hgr⟩ := hpins lvls pins hfr i hi
    refine ⟨vpa, by rw [← hde]; exact hvpa, ?_⟩
    intro ρ zs TVa restR hzl hzok hTVa hfit
    rw [← hde] at hTVa
    exact hgr ρ zs TVa restR hzl hzok hTVa hfit
  · intro cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hlev hplain hnested hidx hTVa hTVja hfitR hfitC
    rw [← hde] at hTVa hTVja
    refine hlaw cvj cnP cnF
      (hcg.findDown _ _ hfc (fun _ _ _ _ hcon => nomatch hcon)) usj ρ
      xs ys TVa TVja restR restC hxl hyl hujl hlev hplain ?_ hidx hTVa
      hTVja hfitR hfitC
    intro lvls pins hfr i hi vpa hvpa
    refine hnested lvls pins hfr i hi vpa ?_
    rw [← hde]
    exact hvpa

/-! ## The P invariant across the swap -/

set_option maxHeartbeats 3200000 in
/-- **The group rule-list swap, P tier**: an invariant of the
provisional (rule-less) environment transports to the environment
carrying the checked rule lists, with the *same* annotated
valuation. -/
theorem EnvS2PM.swapP {μ : CheckMode} {env₀ env₃ : Env}
    (mp : EnvS2PM V μ env₀)
    (hsw : Setlec.SwapShList env₀.consts env₃.consts)
    -- the four syntactic environment facts at the swapped
    -- environment (`swapEnvFacts`, `SetBase/IndRecsCoreR.lean`;
    -- task #161 S7, Wall C): taking them rather than rebuilding them
    -- keeps this file free of the rule facts, exactly as taking the
    -- v1 carrier used to
    (hwf₃ : EnvWF env₃) (hctors₃ : Setlec.RecCtorsStored env₃)
    (hbp₃ : BasisPinnedTT env₃ mp.base2.cvalE)
    (hproj₃ : ProjOkT env₃)
    (hrecP : ∀ (m₃ : EnvS2Core V env₃), m₃.acval = mp.base2.acval →
      ∀ φ : Name → Nat, RecRulesP m₃ φ) :
    ∃ mp₃ : EnvS2PM V μ env₃, mp₃.base2.acval = mp.base2.acval ∧
      mp₃.base2.cvalE = mp.base2.cvalE := by
  have hcg : Setlec.SwapCongr env₀ env₃ := Setlec.SwapShList.congr hsw
  have hcorr := Setlec.swapSh_find?_corr hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denoteP mp.base2.acval env₀ ψ d e
        = denoteP mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denoteP_swap hcg ψ d e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  -- the member correspondence, at the level of `toConstantVal`
  have hmemcorr : ∀ c₃ ∈ env₃.consts, ∃ c₀ ∈ env₀.consts,
      c₀.toConstantVal = c₃.toConstantVal ∧ c₀.name = c₃.name := by
    intro c₃ hc₃
    obtain ⟨c₀, hc₀, hpair⟩ := Setlec.swapSh_mem_corr hsw c₃ hc₃
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
    · exact ⟨c₀, hc₀, rfl, rfl⟩
    · exact ⟨_, hc₀, rfl, rfl⟩
  refine ⟨{ base2 :=
              { wf := hwf₃
                acval := mp.base2.acval
                cval_closedL := fun n ψ => mp.base2.cval_closedL n ψ
                basis_pinnedL := hbp₃
                proj_ok := hproj₃
                rec_ctors := hctors₃
                acval_closed := mp.base2.acval_closed
                acval_params := by
                  intro n ci hf ψ₁ ψ₂ hp
                  rcases hcorr n with heq |
                    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
                  · exact mp.base2.acval_params n ci
                      (by rw [← heq]; exact hf) ψ₁ ψ₂ hp
                  · rw [h₃] at hf
                    obtain rfl := Option.some.inj hf
                    exact mp.base2.acval_params n _ h₀ ψ₁ ψ₂ hp
                acval_ok2 := mp.base2.acval_ok2 }
            acval_validV := mp.acval_validV
            type_reads := ?_
            type_okP := ?_
            mem_typeP := ?_
            defn_reads := ?_
            nat_heads := ?_
            nat_ops := ?_
            div_mod := ?_
            eq_lawP := ?_
            caps_ok := ?_
            rec_rules := hrecP _ rfl
            reduce_ops := ?_ },
          rfl, rfl⟩
  · -- `type_reads`
    intro c hc ψ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    obtain ⟨ta, hta⟩ := mp.type_reads c₀ hc₀ ψ
    exact ⟨ta, by rw [← hde, ← hcv]; exact hta⟩
  · -- `type_okP`
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    rw [← hde, ← hcv] at hta
    exact mp.type_okP c₀ hc₀ ψ ta hta ρ
  · -- `mem_typeP`
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hcv, hname⟩ := hmemcorr c hc
    rw [← hde, ← hcv] at hta
    have := mp.mem_typeP c₀ hc₀ ψ ta hta ρ
    rw [hname] at this
    exact this
  · -- `defn_reads`
    intro ψ cv value hmem
    have hmem₀ : (∃ hint : Setlec.ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env₀.consts) ∨
        ConstantInfo.thmInfo cv value ∈ env₀.consts := by
      rcases hmem with ⟨hint, hd⟩ | hd
      · obtain ⟨c₀, hc₀, hpair⟩ := Setlec.swapSh_mem_corr hsw _ hd
        rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
        · exact Or.inl ⟨hint, hc₀⟩
        · exact nomatch heq
      · obtain ⟨c₀, hc₀, hpair⟩ := Setlec.swapSh_mem_corr hsw _ hd
        rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
        · exact Or.inr hc₀
        · exact nomatch heq
    rw [← hde]
    exact mp.defn_reads ψ cv value hmem₀
  · -- `nat_heads`
    intro φ hsup ρ
    exact mp.nat_heads φ (hcg.natEq ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := mp.nat_ops φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL,
      by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hlaw⟩
  · -- `eq_lawP`: `Eq` is stored as an `indInfo`, so it is never swapped
    intro hf
    exact mp.eq_lawP
      ((hsame eqName eqA
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- `caps_ok`
    obtain ⟨he, hu⟩ := mp.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        Setlec.EtaFamilyStored env₃ T caps →
        Setlec.EtaFamilyStored env₀ T caps := by
      intro T caps hst
      obtain ⟨h1, ⟨cvC, hC⟩, h3⟩ := hst
      refine ⟨h1, ⟨cvC, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hC⟩, ?_⟩
      intro j hj
      obtain ⟨cv, mI, rP, rules, hfj⟩ := h3 j hj
      rcases hcorr (Setlec.projFnName T j) with heq |
        ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
      · exact ⟨cv, mI, rP, rules, by rw [← heq]; exact hfj⟩
      · exact ⟨cv2, mI2, rP2, [], h₀⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
        he T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres (hfam T caps hfamS) φ' us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw⟩
    · intro T cvT caps hf hcap hres φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
        hu T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres φ' us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw⟩
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
      hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩

end Setlec.SetR.Interp2
