module

public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Verify.Denote.ConstsBound
import ConLeche.Verify.Inductives.ReplaceApps

public section

/-!
# The canonical constructor crest (M2)

`LfpCtorReads` (`Model/Env/EnvModelM.lean`) records the readings of a
stored constructor type's canonical abstraction (`nestCanonCrest`: its
whole member applications abstracted at the canonical holes, its
parameters instantiated at the canonical variables) and of the members'
hole types (the formers at the canonical parameters): the terms
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
  rcases hA with ⟨names, us, n, hA⟩ | ⟨n, hA⟩
  · unfold ConLeche.nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    refine constsBound_replaceApps (fun c us' r hr => ?_) _ (constsBound_instPisWith (hp _) he ht)
    obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
    simp
  · exact constsBound_instPisWith (hp _) he hA

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
      denote mp.base2.acval env ψ d e = some ta → denote acval' env' ψ d e = some ta)
    (hbound : ∀ e, ConstsBound env e → ConstsBound env' e) :
    ∀ D ∈ mp.lfpBlocks, LfpClause acval' D ∧ LfpStored env' D ∧ LfpReads acval' env' D ∧
      LfpCtorReads acval' env' D ∧ LfpCaps env' D := by
  intro D hD
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := mp.lfp_ok D hD
  refine ⟨hL.congr (fun mm hmm => ?_) (fun c hc j hj => ?_),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc j hj => ?_⟩,
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact hag _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact hag _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, caps, hf, ⟨hfl, hsh⟩, hab⟩ := hrd mm hmm
    have hcS : ConstsBound env cv.type :=
      (ConLeche.Verify.envWF_constsBound mp.base2.wf _ (ConLeche.Env.find?_mem hf)).1
    have hcB : ConstsBound env (D.formerAt mm cv).type := by
      rcases hsh with hn | ⟨f, hs, -, -, -, -, hb, -⟩
      · rw [show D.formerAt mm cv = cv by simp [LfpDatum.formerAt, hn.1]]
        exact hcS
      · rw [show D.formerAt mm cv = f by simp [LfpDatum.formerAt, hs]]
        exact hb
    refine ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, ⟨hfl, ?_⟩,
      fun ψ => ?_⟩
    · refine hsh.imp id fun ⟨f, hs, h1, h2, h3, h4, hb, hdl, hm⟩ =>
        ⟨f, hs, h1, h2, h3, h4, hbound _ hb, hdl, fun ψ => ?_⟩
      obtain ⟨ta, ta₀, hta, hta₀, hmem⟩ := hm ψ
      refine ⟨ta, ta₀, hread ψ _ _ _ hb hta, hread ψ _ _ _ hcS hta₀, fun ρ => ?_⟩
      rw [hag _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h]
      exact hmem ρ
    · obtain ⟨ab, hta, h1⟩ := hab ψ
      exact ⟨ab, hread ψ _ _ _ hcB hta, h1⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc j hj
    have hcB : ConstsBound env cv.type :=
      (ConLeche.Verify.envWF_constsBound mp.base2.wf _ (ConLeche.Env.find?_mem hf)).1
    refine ⟨cv, nPc, nF, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hcf,
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
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, hread ψ _ _ _ (canonOf_constsBound hcB (.inl ⟨_, _, _, hA⟩)) hta,
        hlab, hlT, fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, ty, hfm, hty, hr⟩ := hTys mm hmm
      obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
      rw [hfm] at hf'
      obtain ⟨rfl, rfl⟩ : cvm = cv' ∧ caps = caps' := by simpa using hf'
      have hcB : ConstsBound env (D.formerAt mm cvm).type := by
        rcases hsh with hn | ⟨f, hs, -, -, -, -, hb, -, -⟩
        · rw [show D.formerAt mm cvm = cvm by simp [LfpDatum.formerAt, hn.1]]
          exact (ConLeche.Verify.envWF_constsBound mp.base2.wf _ (ConLeche.Env.find?_mem hfm)).1
        · rw [show D.formerAt mm cvm = f by simp [LfpDatum.formerAt, hs]]
          exact hb
      exact ⟨cvm, caps, ty, hfind _ _ hfm fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hty,
        hread ψ _ _ _ (canonOf_constsBound hcB (.inr ⟨_, hty⟩)) hr⟩
  · obtain ⟨cv, caps, hf, hz⟩ := hcK mm hmm
    exact ⟨cv, caps, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hz⟩
  · obtain ⟨cv, nPc, nF, hf, hsh⟩ := hcC c hc j hj
    exact ⟨cv, nPc, nF, hfind _ _ hf fun _ _ _ _ _ h => ConstantInfo.noConfusion h, hsh⟩

/-- A stored former that shows its telescope is the one read. -/
theorem EnvModelM.formerAt_flat {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    (hflat : ConLeche.formerDefHeaded cv = false) : D.formerAt mm cv = cv := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨hfa, -⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  exact hfa hflat

/-- A recorded member's former, as read: closed and resolving. -/
theorem EnvModelM.formerAt_wf {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps)) :
    (D.formerAt mm cv).type.hasFvar = false ∧ (D.formerAt mm cv).type.looseBVarsBounded 0 = true ∧
      ConstsBound env (D.formerAt mm cv).type ∧ (D.formerAt mm cv).levelParams = cv.levelParams ∧
      (D.formerAt mm cv).type.allLevelParamsDefined cv.levelParams = true := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases hsh with hn | ⟨f, hs, -, h2, h3, h4, hb, hdl, -⟩
  · rw [show D.formerAt mm cv = cv by simp [LfpDatum.formerAt, hn.1]]
    have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
    exact ⟨hwf.1, hwf.2.2.2.1, (ConLeche.Verify.envWF_constsBound mp.base2.wf _
      (ConLeche.Env.find?_mem hf)).1, rfl, hwf.2.1⟩
  · rw [show D.formerAt mm cv = f by simp [LfpDatum.formerAt, hs]]
    exact ⟨h3, h4, hb, h2, h2 ▸ hdl⟩

/-- **What a run reads of a recorded family's telescope is what its block read.** -/
@[expose] def FamilyRead {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env) (F : Nat) :
    Prop :=
  ∀ D ∈ mp.lfpBlocks, ∀ (mm : Nat) (cv : ConstantVal) (caps : ConLeche.IndCaps) (ty : Expr), mm < D.k →
    env.find? (D.member mm) = some (.indInfo cv caps) →
    ConLeche.familyTelescope (ConLeche.fueledOps .verified F) env cv caps = .ok ty →
    ty = (D.formerAt mm cv).type

/-- A recorded member's stored sort datum, where its block's sort is zero. -/
theorem EnvModelM.formerZ_holds {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    (hz : ∀ ψ : Name → Nat, D.w ψ = 0 → (ConLeche.formerZ (D.formerAt mm cv)).holds ψ = true) :
    ∀ ψ : Name → Nat, D.w ψ = 0 → (ConLeche.formerZ cv).holds ψ = true := by
  cases hrs : ConLeche.formerResSort cv.type with
  | none =>
    intro ψ _
    simp [ConLeche.formerZ, hrs, ConLeche.PropWhen.holds]
  | some s =>
    rw [mp.formerAt_flat hD hmm hf (by simp [ConLeche.formerDefHeaded, hrs])] at hz
    exact hz

open SetTheory ConLeche.Term in
/-- **A recorded member inhabits its former as read.** -/
theorem EnvModelM.formerAt_mem {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    {ψ : Name → Nat} {ta : ConLeche.Term.Term}
    (hta : denote mp.base2.acval env ψ 0 (D.formerAt mm cv).type = some ta) (ρ : Nat → V) :
    interp V ρ (mp.base2.acval (D.member mm) ψ) ∈ˢ interp V ρ ta := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases hsh with hn | ⟨f, hs, -, -, -, -, -, -, hm⟩
  · rw [show D.formerAt mm cv = cv by simp [LfpDatum.formerAt, hn.1]] at hta
    have := mp.mem_type _ (ConLeche.Env.find?_mem hf) ψ _ hta ρ
    rwa [ConLeche.Env.find?_name hf] at this
  · rw [show D.formerAt mm cv = f by simp [LfpDatum.formerAt, hs]] at hta
    obtain ⟨ta', _, hta', _, hin⟩ := hm ψ
    rw [hta] at hta'
    obtain rfl := Option.some.inj hta'
    exact (hin ρ).2.1

open SetTheory ConLeche.Term in
/-- **A recorded member's former reads as a type.** -/
theorem EnvModelM.formerAt_wellDenotedTy {V : Type w} [SetTheory V] {env : Env}
    (mp : EnvModelM V env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    {cv : ConstantVal} {caps : ConLeche.IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {ψ : Name → Nat}
    {ta : ConLeche.Term.Term}
    (hta : denote mp.base2.acval env ψ 0 (D.formerAt mm cv).type = some ta) (ρ : Nat → V) :
    WellDenotedTy V ρ ta := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases hsh with hn | ⟨f, hs, -, -, -, -, -, -, hm⟩
  · rw [show D.formerAt mm cv = cv by simp [LfpDatum.formerAt, hn.1]] at hta
    exact mp.type_wellDenotedTy _ (ConLeche.Env.find?_mem hf) ψ _ hta ρ
  · rw [show D.formerAt mm cv = f by simp [LfpDatum.formerAt, hs]] at hta
    obtain ⟨ta', _, hta', _, hin⟩ := hm ψ
    rw [hta] at hta'
    obtain rfl := Option.some.inj hta'
    exact (hin ρ).2.2

open SetTheory ConLeche.Term in
/-- **A stored former and the one its block read have one value.** -/
theorem EnvModelM.formerAt_interp {V : Type w} [SetTheory V] {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    {ψ : Name → Nat} {ta₀ ta : ConLeche.Term.Term}
    (hta₀ : denote mp.base2.acval env ψ 0 cv.type = some ta₀)
    (hta : denote mp.base2.acval env ψ 0 (D.formerAt mm cv).type = some ta) (ρ : Nat → V) :
    interp V ρ ta₀ = interp V ρ ta := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases hsh with hn | ⟨f, hs, -, -, -, -, -, -, hm⟩
  · rw [show D.formerAt mm cv = cv by simp [LfpDatum.formerAt, hn.1], hta₀] at hta
    rw [Option.some.inj hta]
  · rw [show D.formerAt mm cv = f by simp [LfpDatum.formerAt, hs]] at hta
    obtain ⟨ta', ta₀', hta', hta₀', hin⟩ := hm ψ
    rw [hta] at hta'
    obtain rfl := Option.some.inj hta'
    rw [hta₀] at hta₀'
    obtain rfl := Option.some.inj hta₀'
    exact (hin ρ).1

end ConLeche.Model
