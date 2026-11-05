module

import ConLeche.Model.Env.CanonCrest
import ConLeche.Verify.Denote.EnvExt
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Tiers
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Kernel.Checker
import ConLeche.Model.IndDomGrade
import ConLeche.Model.IndFrame
public import ConLeche.Model.IndPinGrade
public import ConLeche.Verify.Extend.Recs
import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.IndBlockFacts
public section

/-!
# The group rule-list swap, P tier (task #161, IND TIER part 10)

`EnvModelM.swapP` transports the P invariant across the step that
attaches a recursor group's checked rule lists to its rule-less
provisioned entries.

The workhorse is `denote_env_ext`.  It is an **equation**
with no `ConstsBound` premise, unlike the extension crossing
(`denote_envExtend_mono`): a swap changes no stored name, so the
reading's three environment consultations — the `.const` clause's
`find?` (through the stored level parameters only), the two literal
guards, and the string spine's `levelParamsAt` — are all congruent.
That is why every field of the invariant crosses in *both* directions
and the contravariant readings need no determinism trick here.

The three environment-level facts about the *result* — `EnvWF`,
`RecCtorsStored`, `RecRules` — are hypotheses: they are what the group
install proves, and taking them here keeps the transport free of the
per-rule content.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading across a level-preserving correspondence -/

/-- **`denote` reads the environment only through the stored level
parameters and the two literal guards**.  An equation, so a law's `denote` *hypotheses* and *conclusions* both move
across it for free, which is what makes the fired-form fields
transportable at all. -/
theorem denote_env_ext {acval : Name → (Name → Nat) → Term}
    {env₁ env₂ : Env} {φ : Name → Nat}
    (henvLev : ∀ n,
      (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : ConLeche.natLitSupported env₁ = ConLeche.natLitSupported env₂)
    (hstr : ConLeche.strLitSupported env₁ = ConLeche.strLitSupported env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = env₂.findProj? sn i) :
    ∀ (d : Nat) (e : Expr),
      denote acval env₁ φ d e = denote acval env₂ φ d e := by
  intro d e
  induction d, e using denote.induct (env := env₁) with
  | case1 d u => rw [denote, denote]
  | case2 d idx ty => rw [denote, denote]
  | case3 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denote, hf, denote, hf₂]
      dsimp only
      rw [ite_eq_left hlen, ite_eq_left (h ▸ hlen), h]
  | case4 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denote, hf, denote, hf₂]
      dsimp only
      rw [ite_eq_right hlen, ite_eq_right (fun hh => hlen (h ▸ hh))]
  | case5 d n us hf =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [denote, hf, denote, hf₂]
    | some ci₂ => rw [hf₂] at h; exact nomatch h
  | case6 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case7 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case8 d f a ihf iha => rw [denote, denote, ihf, iha]
  | case9 d ty val body ihty ihv ihbody =>
    rw [denote, denote, ihty, ihv, ihbody]
  | case10 d sn i e ihe =>
    rw [denote, denote, ihe, hproj sn i]
  | case11 d n hsup =>
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hnat ▸ hsup)]
  | case12 d n hsup =>
    rw [denote, ite_eq_right hsup, denote,
      ite_eq_right (fun h => hsup (hnat.trans h))]
  | case13 d s hsup =>
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hstr ▸ hsup),
      levelParamsAt_ext (henvLev ConLeche.listNilName),
      levelParamsAt_ext (henvLev ConLeche.listConsName)]
  | case14 d s hsup =>
    rw [denote, ite_eq_right hsup, denote,
      ite_eq_right (fun h => hsup (hstr.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat' hstr' =>
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat' n)
      | strVal s => exact absurd rfl (hstr' s)

/-- The reading crosses a swap congruence. -/
theorem denote_swap {acval : Name → (Name → Nat) → Term}
    {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    (φ : Name → Nat) (d : Nat) (e : Expr) :
    denote acval env₀ φ d e = denote acval env₃ φ d e :=
  denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq d e

/-! ## The P invariant across the swap -/

set_option maxHeartbeats 3200000 in
/-- **The group rule-list swap, P tier**: an invariant of the
provisional (rule-less) environment transports to the environment
carrying the checked rule lists, with the *same* leaf
valuation. -/
theorem EnvModelM.swapP {env₀ env₃ : Env}
    (mp : EnvModelM V env₀)
    (hsw : ConLeche.SwapShList env₀.consts env₃.consts)
    (htab : env₃.tables = env₀.tables)
    -- the four syntactic environment facts at the swapped
    -- environment: taking them rather than rebuilding them keeps this
    -- file free of the rule facts
    (hwf₃ : EnvWF env₃) (hctors₃ : ConLeche.RecCtorsStored env₃)
    (hbp₃ : BasisPinnedTT env₃ mp.base2.acval)
    (hproj₃ : ProjOkT env₃)
    (hrecP : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval →
      ∀ φ : Name → Nat, RecRules m₃ φ) :
    ∃ mp₃ : EnvModelM V env₃, mp₃.base2.acval = mp.base2.acval ∧
      mp₃.base2.acval = mp.base2.acval := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapShList.congrEnv hsw htab
  have hcorr := ConLeche.swapSh_find?_corrEnv hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env₀ ψ d e
        = denote mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denote_swap hcg ψ d e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  -- a pinned `Nat`-operation type: the stored `Bool` entry keeps its
  -- constant value (a swap changes a recursor's rules only)
  have hpinUp : ∀ {c : Name} {ty : Expr}, ConLeche.natOpTyPinned env₀ c ty = true →
      ConLeche.natOpTyPinned env₃ c ty = true := fun h =>
    ConLeche.Verify.natOpTyPinned_of_find (fun ci hf => by
      rcases hcorr ConLeche.boolName with heq | ⟨cv, mI, rP, isK, rules, h₀, h₃, -⟩
      · exact ⟨ci, by rw [heq]; exact hf, rfl⟩
      · rw [h₀] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, h₃, rfl⟩) h
  -- the member correspondence, at the level of `toConstantVal`
  have hmemcorr : ∀ c₃ ∈ env₃.consts, ∃ c₀ ∈ env₀.consts,
      c₀.toConstantVal = c₃.toConstantVal ∧ c₀.name = c₃.name := by
    intro c₃ hc₃
    obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw c₃ hc₃
    rcases hpair with rfl | ⟨cv, mI, rP, isK, rules, rfl, rfl⟩
    · exact ⟨c₀, hc₀, rfl, rfl⟩
    · exact ⟨_, hc₀, rfl, rfl⟩
  refine ⟨{ base2 :=
              { wf := hwf₃
                acval := mp.base2.acval
                cval_closed := fun n ψ => mp.base2.cval_closed n ψ
                basis_pinned := hbp₃
                proj_ok := hproj₃
                rec_ctors := hctors₃
                acval_params := by
                  intro n ci hf ψ₁ ψ₂ hp
                  rcases hcorr n with heq |
                    ⟨cv, mI, rP, isK, rules, h₀, h₃, -⟩
                  · exact mp.base2.acval_params n ci
                      (by rw [← heq]; exact hf) ψ₁ ψ₂ hp
                  · rw [h₃] at hf
                    obtain rfl := Option.some.inj hf
                    exact mp.base2.acval_params n _ h₀ ψ₁ ψ₂ hp
                acval_wellDenoted := mp.base2.acval_wellDenoted }
            type_reads := ?_
            type_wellDenotedTy := ?_
            mem_type := ?_
            defn_reads := ?_
            nat_heads := ?_
            nat_ops := ?_
            div_mod := ?_
            eq_law := ?_
            caps_ok := ?_
            rec_rules := hrecP _ rfl
            reduce_ops := ?_
            tower_ok := ?_
            -- the formers are never swapped, and keep their readings
            ind_strict := fun I cv caps hf hfl ψ ab n hread =>
              mp.ind_strict I cv caps
                ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hfl
                ψ ab n (by rw [hde]; exact hread)
            -- the recorded lfp clauses: the swap touches recursors only,
            -- and keeps every leaf
            lfpBlocks := mp.lfpBlocks
            lfp_ok := mp.lfp_ok_transport
              (fun n ci hf hnr => (hsame n ci hnr).mpr hf)
              (fun _ _ _ _ => rfl)
              (fun ψ d _ _ _ hta => by rw [← denote_swap hcg ψ d]; exact hta)
              (fun _ => ConstsBound.of_isSome fun n h => by rw [← hcg.isSomeEq]; exact h) },
          rfl, rfl⟩
  · -- `type_reads`
    intro c hc ψ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    obtain ⟨ta, hta⟩ := mp.type_reads c₀ hc₀ ψ
    exact ⟨ta, by rw [← hde, ← hcv]; exact hta⟩
  · -- `type_wellDenotedTy`
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    rw [← hde, ← hcv] at hta
    exact mp.type_wellDenotedTy c₀ hc₀ ψ ta hta ρ
  · -- `mem_type`: the swap touches recursors only, so the tower
    -- exclusion carries over
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw c hc
    have hcv : c₀.toConstantVal = c.toConstantVal := by
      rcases hpair with rfl | ⟨cv, mI, rP, isK, rules, rfl, rfl⟩ <;> rfl
    have hname : c₀.name = c.name := by
      rcases hpair with rfl | ⟨cv, mI, rP, isK, rules, rfl, rfl⟩ <;> rfl
    rw [← hde, ← hcv] at hta
    have := mp.mem_type c₀ hc₀ ψ ta hta ρ
    rw [hname] at this
    exact this
  · -- `defn_reads`
    intro ψ cv value hmem
    have hmem₀ : ∃ hint : ConLeche.ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env₀.consts := by
      obtain ⟨hint, hd⟩ := hmem
      obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw _ hd
      rcases hpair with rfl | ⟨cv2, mI, rP, isK, rules, rfl, heq⟩
      · exact ⟨hint, hc₀⟩
      · exact nomatch heq
    rw [← hde]
    exact mp.defn_reads ψ cv value hmem₀
  · -- `nat_heads`
    intro φ hsup ρ
    exact mp.nat_heads φ (hcg.natEq ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.nat_ops φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL,
      by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, hlaw⟩
  · -- `eq_law`: `Eq` is stored as an `indInfo`, so it is never swapped
    intro ci p hf hp
    exact mp.eq_law ci p ((hsame eqName ci
      (eqCopy_not_rec (hbp₃ eqName ci hf (by decide)).1)).mp hf) hp
  · -- `caps_ok`
    obtain ⟨he, hu⟩ := mp.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        ConLeche.EtaFamilyStored env₃ T caps →
        ConLeche.EtaFamilyStored env₀ T caps := by
      intro T caps hst
      obtain ⟨h1, ⟨cvC, cnP, cnF, hC⟩, h3⟩ := hst
      exact ⟨h1, ⟨cvC, cnP, cnF, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hC⟩, h3⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS φ' us hus
      obtain ⟨hlaw, hcoh⟩ :=
        he T cvT caps ((hsame _ _
          (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres (hfam T caps hfamS) φ' us hus
      refine ⟨hlaw,
        hcoh.transport (fun cvC nPc nFc hf₂ => (hsame _ _
          (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf₂)
        (fun cvC nPc nFc TCa _ hTCa => by rw [← hde]; exact hTCa) rfl
        (fun _ _ _ => rfl)⟩
    · intro T cvT caps hf hcap hres φ' us hus
      exact hu T cvT caps ((hsame _ _
          (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres φ' us hus
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
      hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩
  · -- `tower_ok` (task #175 wiring W5): a table entry, a former and a
    -- constructor are never recursors, so every lookup the law reads
    -- is unchanged by the swap, and the readings are `hde`
    intro φ T i entry hf
    have hfP : env₀.findProj? T i = some entry := by
      rw [hcg.projEq]; exact hf
    obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, cvC, hfC, hlpsC,
      hlaw, hetaL⟩ := mp.tower_ok φ T i entry hfP
    refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hlpsT⟩,
      cvC, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfC, hlpsC,
      fun us hus => ?_, ?_⟩
    · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
      exact ⟨⟨Ta, by rw [← hde]; exact hTa, fun ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ hg =>
          hA ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ (hg.imp_left (TowerGuardAt.mono
            (by rw [hsn, (hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hfT])
            (fun _ _ _ _ h => by rw [← hde]; exact h) fun _ h => by rw [← hde]; exact h))⟩,
        ⟨TCa, by rw [← hde]; exact hTCa, hB⟩⟩
    · -- (C) the η law (task #175 W4c): the former's lookup is unchanged
      -- by the swap, and the reading is `hde`
      intro cvT' capsT' hfT' us hus
      obtain ⟨hlaw', hcoh⟩ := hetaL cvT' capsT' ((hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hfT') us hus
      exact ⟨hlaw', fun he =>
        (hcoh he).transport (fun cvC nPc nFc hf₂ => (hsame _ _
          (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf₂)
        (fun cvC nPc nFc TCa _ hTCa => by rw [← hde]; exact hTCa) rfl
        (fun _ _ _ => rfl)⟩

end ConLeche.Model
