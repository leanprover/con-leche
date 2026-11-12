module

public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Verify.Denote.ConstsBound
import ConLeche.Verify.Inductives.ReplaceApps
import ConLeche.Model.Reading.Levels

public section

/-!
# The canonical constructor crest (M2)

`LfpCtorReads` (`Model/Env/EnvModelM.lean`) records the readings of a
stored constructor type's canonical abstraction (`nestCanonCrest`: its
whole member applications abstracted at the canonical holes, its
parameters instantiated at the canonical variables): the terms
`CanonOf`.  Every variable they introduce is annotated `Sort 0`, so they
mention only the stored type's constants and projections: they are
prefix-bound wherever the type is (`canonOf_constsBound`) — the fact the
record's transport (`EnvModelM.lfp_ok_transport`'s `hreadC`) needs at
the cons funnel.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo instPisWith)

/-! ## Instantiation along a telescope -/

theorem constsBound_instPisWith {env₀ : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ConstsBound env₀ a) → ConstsBound env₀ e →
      instPisWith as e = some r → ConstsBound env₀ r
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [constsBound_forallE] at he
      exact constsBound_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (ConstsBound.instantiate1 (has a List.mem_cons_self) b 0 he.2) h'

/-! ## The whole-application replacement -/

theorem constsBound_replaceApps {env₀ : Env} {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us e, f c us = some e → ConstsBound env₀ e) :
    ∀ (e : Expr), ConstsBound env₀ e → ConstsBound env₀ (e.replaceApps f b n) := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceApps]
  | fvar i ty ih => intro h; simpa [ConLeche.Expr.replaceApps] using h
  | sort u => intro _; simp [ConLeche.Expr.replaceApps]
  | const c us =>
    intro h
    rw [ConLeche.Expr.replaceApps_const]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · exact h
  | lit l => intro _; simp [ConLeche.Expr.replaceApps]
  | app a x iha ihx =>
    intro h
    rw [ConLeche.Expr.replaceApps_app]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · simp only [constsBound_app] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, constsBound_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, constsBound_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, constsBound_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceApps, constsBound_proj] at h ⊢
    exact ih h

/-! ## The canonical crest -/

theorem mem_canonParams {nP : Nat} {x : Expr} (h : x ∈ canonParams nP) :
    ∃ i, i < nP ∧ x = .fvar i (.sort .zero) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem canonOf_constsBound {env₀ : Env} {ty A : Expr} (he : ConstsBound env₀ ty)
    (hA : CanonOf ty A) : ConstsBound env₀ A := by
  have hp : ∀ n, ∀ x ∈ canonParams n, ConstsBound env₀ x := fun _ x hx => by
    obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp
  obtain ⟨names, us, n, hA⟩ := hA
  unfold ConLeche.nestCanonCrest at hA
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
  refine constsBound_replaceApps (fun c us' r hr => ?_) _ (constsBound_instPisWith (hp _) he ht)
  obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
  simp

theorem canonParams_getElem? {nP i : Nat} {x : Expr} (h : (canonParams nP)[i]? = some x) :
    x = .fvar i (.sort .zero) := by
  have hi : i < nP := by
    have := (List.getElem?_eq_some_iff.mp h).1; simpa [canonParams, ConLeche.nestPhs] using this
  simp [canonParams, ConLeche.nestPhs, List.getElem?_range hi] at h
  exact h.symm

theorem canonParams_length (nP : Nat) : (canonParams nP).length = nP := by
  simp [canonParams, ConLeche.nestPhs]

/-- **The recorded clauses cross an environment extension** that keeps
every stored inductive former and its leaf, and every successful reading
of a stored former's type — the transport every construction site of
the invariant (the cons funnel, the rule-list swap) instantiates. -/
theorem EnvModelM.lfp_ok_transport {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env) {env' : Env}
    {acval' : Name → (Name → Nat) → ConLeche.Term.Term}
    (hfind : ∀ n ci, env.find? n = some ci → (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      env'.find? n = some ci)
    (hag : ∀ n ci, env.find? n = some ci → (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      acval' n = mp.base2.acval n)
    (hread : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr) (ta : ConLeche.Term.Term), ConstsBound env e →
      denote mp.base2.acval env ψ d e = some ta → denote acval' env' ψ d e = some ta) :
    ∀ D ∈ mp.lfpBlocks, LfpClause acval' D ∧ LfpStored env' D ∧ LfpReads acval' env' D ∧
      LfpCtorReads acval' env' D ∧ LfpCaps env' D := by
  intro D hD
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := mp.lfp_ok D hD
  refine ⟨hL.congr (fun mm hmm => ?_) (fun c hc j hj => ?_),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc j hj => ?_⟩,
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact hag _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, a, b, iT, hf⟩ := hstC c hc j hj
    exact hag _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, a, b, iT, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, iT, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, caps, hf, hfl, hval, hw⟩ := hrd mm hmm
    have hcS : ConstsBound env cv.type :=
      (ConLeche.Verify.envWF_constsBound mp.base2.wf _ (ConLeche.Env.find?_mem hf)).1
    refine ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h,
      fun hflat ψ => ?_, fun ψ => ?_, hw⟩
    · obtain ⟨ab, u, hta, hl⟩ := hfl hflat ψ
      exact ⟨ab, u, hread ψ _ _ _ hcS hta, hl⟩
    · obtain ⟨ta, hta, hv⟩ := hval ψ
      exact ⟨ta, hread ψ _ _ _ hcS hta, hv⟩
  · obtain ⟨cv, nPc, nF, iT, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc j hj
    have hcB : ConstsBound env cv.type :=
      (ConLeche.Verify.envWF_constsBound mp.base2.wf _ (ConLeche.Env.find?_mem hf)).1
    refine ⟨cv, nPc, nF, iT, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hcf,
      fun mm hmm => ?_, fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc, fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      exact ⟨cvm, caps, hfind _ _ hfm fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hl⟩
    · -- the new reading is the old one (the old one exists, and crosses)
      obtain ⟨ta, hta⟩ := mp.type_reads _ (List.mem_of_find?_eq_some hf) ψ
      change denote mp.base2.acval env ψ 0 cv.type = some ta at hta
      have hta' := hread ψ 0 _ _ hcB hta
      rw [hrd'] at hta'
      obtain rfl := Option.some.inj hta'
      exact hpars ψ dsC bodyC hta hle
    · obtain ⟨h1, h2, ab, hta, hlab, hab⟩ := hrdA ψ
      exact ⟨h1, h2, ab, hread ψ _ _ _ (canonOf_constsBound hcB ⟨_, _, _, hA⟩) hta,
        hlab, hab⟩
  · obtain ⟨cv, caps, hf, hz⟩ := hcK mm hmm
    exact ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hz⟩
  · obtain ⟨cv, nPc, nF, iT, hf, hsh⟩ := hcC c hc j hj
    exact ⟨cv, nPc, nF, iT, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hsh⟩

open SetTheory ConLeche.Term in
/-- **A recorded block's formers have its telescope's value** (`LfpReads`). -/
theorem EnvModelM.lfpReads {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) : LfpReads mp.base2.acval env D :=
  (mp.lfp_ok D hD).2.2.1

open SetTheory ConLeche.Term in
/-- **A recorded member inhabits its block's telescope** by value, read at any valuation: it
inhabits its stored type, which is closed and has the telescope's value (`LfpReads`). -/
theorem EnvModelM.member_mem_tower {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) (ψ : Name → Nat)
    (ρ σ : Nat → V) :
    interp V ρ (mp.base2.acval (D.member mm) ψ)
      ∈ˢ interp V σ (mkPisAV (D.pars mm ψ ++ D.ids mm ψ) (.sort (D.w ψ))) := by
  obtain ⟨cv, caps, hf, -, hval, -⟩ := mp.lfpReads hD mm hmm
  obtain ⟨ta, hta, hv⟩ := hval ψ
  have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
  have hcl : ConLeche.Term.Term.bvarsBelow 0 ta :=
    ConLeche.Verify.denote_bvarsBelow mp.base2.cval_closed 0 _
      (ConLeche.Expr.WScoped.of_not_hasFvar hwf.1) hwf.2.2.2.1 hta
  have hm := mp.mem_type _ (ConLeche.Env.find?_mem hf) ψ ta hta ρ
  rw [ConLeche.Env.find?_name hf] at hm
  rw [← hv σ, interp_closed V hcl σ ρ]
  exact hm

open SetTheory ConLeche.Term in
/-- **A recorded member's telescope has one value at two level assignments agreeing on the
member's level parameters**: both are its stored type's (`LfpReads`), which reads alike. -/
theorem EnvModelM.tower_congr {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    {ψ₁ ψ₂ : Name → Nat} (hag : ∀ q ∈ cv.levelParams, ψ₁ q = ψ₂ q) (σ : Nat → V) :
    interp V σ (mkPisAV (D.pars mm ψ₁ ++ D.ids mm ψ₁) (.sort (D.w ψ₁)))
      = interp V σ (mkPisAV (D.pars mm ψ₂ ++ D.ids mm ψ₂) (.sort (D.w ψ₂))) := by
  obtain ⟨cv', caps', hf', -, hval, -⟩ := mp.lfpReads hD mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨t₁, h₁, hv₁⟩ := hval ψ₁
  obtain ⟨t₂, h₂, hv₂⟩ := hval ψ₂
  have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
  rw [denote_params_ext mp.base2 hag 0 cv.type hwf.2.1, h₂] at h₁
  obtain rfl := Option.some.inj h₁
  rw [← hv₁, ← hv₂]

end ConLeche.Model
