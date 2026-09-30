module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Annot.BitConsCross
import ConLeche.Verify.Inductives.ReplaceApps

public section

/-!
# The canonical constructor crest (M2)

`LfpCtorReads` (`Model/Annot/EnvModelM.lean`) records the readings of a
stored constructor type's canonical abstraction (`nestCanonCrest`: its
whole member applications abstracted at the canonical holes, its
parameters instantiated at the canonical variables) and of the members'
hole types (the formers at the canonical parameters): the terms
`CanonOf`.  Every variable they introduce is annotated `Sort 0`, so they
mention only the stored type's constants and projections: they are
prefix-bound wherever the type is (`canonOf_constsBound`) and cross
every cons the type crosses (`canonOf_consCrossAt`) — the two facts the
record's transport (`EnvModelM.lfp_ok_transport`'s `hreadC`) needs at
the cons funnel.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo instPisWith)

/-! ## Constant replacement -/

theorem constsBound_replaceConsts {env₀ : Env} {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → ConstsBound env₀ e) :
    ∀ (e : Expr), ConstsBound env₀ e → ConstsBound env₀ (e.replaceConsts f) := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceConsts]
  | fvar i ty ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_fvar] at h ⊢
    exact ih h
  | sort u => intro _; simp [ConLeche.Expr.replaceConsts]
  | const c us =>
    intro h
    simp only [ConLeche.Expr.replaceConsts]
    cases hc : f c us with
    | none => exact h
    | some e => exact hf c us e hc
  | lit l => intro _; simp [ConLeche.Expr.replaceConsts]
  | app a b iha ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_app] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_proj] at h ⊢
    exact ih h

theorem noProjAt_replaceConsts {T : Name} {q : Nat} {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → ConLeche.Expr.NoProjAt T q e) :
    ∀ (e : Expr), ConLeche.Expr.NoProjAt T q e →
      ConLeche.Expr.NoProjAt T q (e.replaceConsts f) := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceConsts]
  | fvar i ty ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_fvar] at h ⊢
    exact ih h
  | sort u => intro _; simp [ConLeche.Expr.replaceConsts]
  | const c us =>
    intro h
    simp only [ConLeche.Expr.replaceConsts]
    cases hc : f c us with
    | none => exact h
    | some e => exact hf c us e hc
  | lit l => intro _; simp [ConLeche.Expr.replaceConsts]
  | app a b iha ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_app] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_proj] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-! ## Instantiation along a telescope -/

theorem constsBound_instPisWith {env₀ : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ConstsBound env₀ a) → ConstsBound env₀ e →
      instPisWith as e = some r → ConstsBound env₀ r
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [constsBound_forallE] at he
      exact constsBound_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (ConstsBound.instantiate1 (has a List.mem_cons_self) b 0 he.2) h'

theorem noProjAt_instPisWith {T : Name} {q : Nat} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ConLeche.Expr.NoProjAt T q a) →
      ConLeche.Expr.NoProjAt T q e → instPisWith as e = some r → ConLeche.Expr.NoProjAt T q r
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [ConLeche.Expr.noProjAt_forallE] at he
      exact noProjAt_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (ConLeche.Expr.NoProjAt.instantiate1 (has a List.mem_cons_self) b 0 he.2) h'

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
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, constsBound_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
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

theorem noProjAt_replaceApps {T : Name} {q : Nat} {f : Name → List Level → Option Expr}
    {b n : Nat} (hf : ∀ c us e, f c us = some e → ConLeche.Expr.NoProjAt T q e) :
    ∀ (e : Expr), ConLeche.Expr.NoProjAt T q e →
      ConLeche.Expr.NoProjAt T q (e.replaceApps f b n) := by
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
    · simp only [ConLeche.Expr.noProjAt_app] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.noProjAt_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.noProjAt_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.noProjAt_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.noProjAt_proj] at h ⊢
    exact ⟨h.1, ih h.2⟩

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

theorem canonOf_noProjAt {T : Name} {q : Nat} {ty A : Expr}
    (he : ConLeche.Expr.NoProjAt T q ty) (hA : CanonOf ty A) : ConLeche.Expr.NoProjAt T q A := by
  have hp : ∀ n, ∀ x ∈ canonParams n, ConLeche.Expr.NoProjAt T q x := fun _ x hx => by
    obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp
  rcases hA with ⟨names, us, n, hA⟩ | ⟨n, hA⟩
  · unfold ConLeche.nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    refine noProjAt_replaceApps (fun c us' r hr => ?_) _ (noProjAt_instPisWith (hp _) he ht)
    obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
    simp
  · exact noProjAt_instPisWith (hp _) he hA

theorem canonOf_consCrossAt {c₀ : ConstantInfo} {ty A : Expr} (he : ConsCrossAt c₀ ty)
    (hA : CanonOf ty A) : ConsCrossAt c₀ A :=
  fun tbl heq q => canonOf_noProjAt (he tbl heq q) hA

theorem canonParams_getElem? {nP i : Nat} {x : Expr} (h : (canonParams nP)[i]? = some x) :
    x = .fvar i (.sort .zero) := by
  have hi : i < nP := by
    have := (List.getElem?_eq_some_iff.mp h).1; simpa [canonParams, ConLeche.nestPhs] using this
  simp [canonParams, ConLeche.nestPhs, List.getElem?_range hi] at h
  exact h.symm

theorem canonParams_length (nP : Nat) : (canonParams nP).length = nP := by
  simp [canonParams, ConLeche.nestPhs]

end ConLeche.Model
