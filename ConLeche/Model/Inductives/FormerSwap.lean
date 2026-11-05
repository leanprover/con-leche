module

public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Verify.Extend.Formers
import ConLeche.Model.Swap
import ConLeche.Model.Env.CanonCrest
import ConLeche.Verify.Denote.Install

public section

/-!
# The invariant across a swap of formers' stored types

`FormerSwap env₀ env₃`: the two environments answer alike but for formers' types.  The leaves
stay, `denote` reads alike (`denote_formerSwap`), and every law but the ones that read a former's
type crosses unchanged.  What does read one is the caller's: the stored types' three facts, the
recursors' and the projections' laws (their case split's premises), the fibres and the records.
-/

namespace ConLeche.Model

open ConLeche ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

universe w
variable {V : Type w} [SetTheory V]

/-- The reading crosses a swap of formers. -/
theorem denote_formerSwap {acval : Name → (Name → Nat) → Term} {env₀ env₃ : Env}
    (h : FormerSwap env₀ env₃) (φ : Name → Nat) (d : Nat) (e : Expr) :
    denote acval env₀ φ d e = denote acval env₃ φ d e :=
  denote_env_ext h.levelsEq h.natEq h.strEq h.projEq d e

set_option maxHeartbeats 3200000 in
/-- **The invariant across a swap of formers**, with the same leaves. -/
theorem EnvModelM.swapFormers {env₀ env₃ : Env} (mp : EnvModelM V env₀)
    (h : FormerSwap env₀ env₃) (hwf₃ : EnvWF env₃) (hctors₃ : ConLeche.RecCtorsStored env₃)
    (hproj₃ : ProjOkT env₃)
    (hrec : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval → ∀ φ, RecRules m₃ φ)
    (htower : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval → ∀ φ, TowerOk m₃ φ)
    (hstrict : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval → IndStrictOk m₃)
    (htyS : ∀ c ∈ env₃.consts, c ∉ env₀.consts →
      (∀ ψ : Name → Nat, ∃ ta : Term,
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, interp V ρ (mp.base2.acval c.name ψ) ∈ˢ interp V ρ ta))
    (L : List (LfpDatum V))
    (hL : ∀ D ∈ L, LfpClause mp.base2.acval D ∧ LfpStored env₃ D ∧
      LfpReads mp.base2.acval env₃ D ∧ LfpCtorReads mp.base2.acval env₃ D ∧ LfpCaps env₃ D) :
    ∃ mp₃ : EnvModelM V env₃, mp₃.base2.acval = mp.base2.acval ∧ mp₃.lfpBlocks = L := by
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env₀ ψ d e = denote mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denote_formerSwap h ψ d e
  have hsame : ∀ (n : Name) (ci : ConstantInfo), (∀ cv caps, ci ≠ .indInfo cv caps) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) := fun n ci hci => h.find_of_ne hci
  have hpinUp : ∀ {c : Name} {ty : Expr}, ConLeche.natOpTyPinned env₀ c ty = true →
      ConLeche.natOpTyPinned env₃ c ty = true := fun hp =>
    ConLeche.Verify.natOpTyPinned_of_find (fun ci hf =>
      ⟨ci, by rw [h.find_guard (n := ConLeche.boolName) (by decide)]; exact hf, rfl⟩) hp
  have hbp₃ : BasisPinnedTT env₃ mp.base2.acval := by
    intro n ci hf hres
    rw [h.find_reserved hres] at hf
    obtain ⟨h1, h2, h3⟩ := mp.base2.basis_pinned n ci hf hres
    exact ⟨h1, h2.mono fun x cvj cnP cnF hx =>
      (hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hx, h3⟩
  refine ⟨{ base2 :=
              { wf := hwf₃
                acval := mp.base2.acval
                cval_closed := fun n ψ => mp.base2.cval_closed n ψ
                basis_pinned := hbp₃
                proj_ok := hproj₃
                rec_ctors := hctors₃
                acval_params := by
                  intro n ci hf ψ₁ ψ₂ hp
                  rcases h.find n with he |
                    ⟨cv, cv', caps, h₀, h₃, -, hlp, -⟩
                  · exact mp.base2.acval_params n ci (by rw [← he]; exact hf) ψ₁ ψ₂ hp
                  · rw [h₃] at hf
                    obtain rfl := Option.some.inj hf
                    exact mp.base2.acval_params n _ h₀ ψ₁ ψ₂
                      (by simpa [ConstantInfo.toConstantVal, hlp] using hp)
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
            rec_rules := hrec _ rfl
            reduce_ops := ?_
            tower_ok := htower _ rfl
            ind_strict := hstrict _ rfl
            lfpBlocks := L
            lfp_ok := hL }, rfl, rfl⟩
  · -- `type_reads`
    intro c hc ψ
    by_cases h₀ : c ∈ env₀.consts
    · obtain ⟨ta, hta⟩ := mp.type_reads c h₀ ψ
      exact ⟨ta, by rw [← hde]; exact hta⟩
    · exact (htyS c hc h₀).1 ψ
  · -- `type_wellDenotedTy`
    intro c hc ψ ta hta ρ
    by_cases h₀ : c ∈ env₀.consts
    · rw [← hde] at hta
      exact mp.type_wellDenotedTy c h₀ ψ ta hta ρ
    · exact (htyS c hc h₀).2.1 ψ ta hta ρ
  · -- `mem_type`
    intro c hc ψ ta hta ρ
    by_cases h₀ : c ∈ env₀.consts
    · rw [← hde] at hta
      exact mp.mem_type c h₀ ψ ta hta ρ
    · exact (htyS c hc h₀).2.2 ψ ta hta ρ
  · -- `defn_reads`
    intro ψ cv value hmem
    have hmem₀ : ∃ hint : ConLeche.ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env₀.consts := by
      obtain ⟨hint, hd⟩ := hmem
      exact ⟨hint, h.mem _ hd fun _ _ he => ConstantInfo.noConfusion he⟩
    rw [← hde]
    exact mp.defn_reads ψ cv value hmem₀
  · -- `nat_heads`
    intro φ hsup ρ
    exact mp.nat_heads φ (h.natEq ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.nat_ops φ c hc cv value hint
      ((hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hf)
    refine ⟨by rw [← h.guardEq]; exact hgu, hpinUp hpin, ?_⟩
    intro eq heq
    obtain ⟨L', R, hL', hR, hval⟩ := hlaw eq heq
    exact ⟨L', R, by rw [← hde]; exact hL', by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hf)
    exact ⟨by rw [← h.guardEq]; exact hgu, hpinUp hpin, hlaw⟩
  · -- `eq_law`: reserved
    intro ci p hf hp
    exact mp.eq_law ci p (by rw [← h.find_reserved (n := eqName) (by decide)]; exact hf) hp
  · -- `caps_ok`: the laws read a family's level parameters alone
    obtain ⟨he, hu⟩ := mp.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        ConLeche.EtaFamilyStored env₃ T caps → ConLeche.EtaFamilyStored env₀ T caps := by
      intro T caps hst
      obtain ⟨h1, ⟨cvC, cnP, cnF, hC⟩, h3⟩ := hst
      exact ⟨h1, ⟨cvC, cnP, cnF, (hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hC⟩, h3⟩
    have hback : ∀ {T : Name} {cvT : ConstantVal} {caps : IndCaps},
        env₃.find? T = some (.indInfo cvT caps) →
        ∃ cv₀, env₀.find? T = some (.indInfo cv₀ caps) ∧ cvT.levelParams = cv₀.levelParams := by
      intro T cvT caps hf
      rcases h.find T with hq | ⟨cv, cv', caps', h₀, h₃, -, hlp, -⟩
      · exact ⟨cvT, by rw [← hq]; exact hf, rfl⟩
      · rw [h₃] at hf
        obtain ⟨rfl, rfl⟩ : cv' = cvT ∧ caps' = caps := by simpa using hf
        exact ⟨cv, h₀, hlp⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS φ' us hus
      obtain ⟨cv₀, hf₀, hlp⟩ := hback hf
      obtain ⟨hlaw, hcoh⟩ := he T cv₀ caps hf₀ hcap hres (hfam T caps hfamS) φ' us (hlp ▸ hus)
      rw [hlp]
      refine ⟨hlaw, hcoh.transport (fun cvC nPc nFc hf₂ =>
        (hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hf₂)
        (fun cvC nPc nFc TCa _ hTCa => by rw [← hde]; exact hTCa) rfl (fun _ _ _ => rfl)⟩
    · intro T cvT caps hf hcap hres φ' us hus
      obtain ⟨cv₀, hf₀, hlp⟩ := hback hf
      rw [hlp]
      exact hu T cv₀ caps hf₀ hcap hres φ' us (hlp ▸ hus)
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ he => ConstantInfo.noConfusion he)).mp hf) hpin
    exact ⟨by rw [← h.isSomeEq]; exact hs, hlaw⟩

end ConLeche.Model
