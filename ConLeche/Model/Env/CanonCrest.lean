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

/-! ## The same, for resolution -/

theorem constsResolve_instantiate1_any {env : Env} {a : Expr}
    (ha : a.constsResolve env = true) :
    ∀ (e : Expr) (k : Nat), e.constsResolve env = true →
      (e.instantiate1 a k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [ConLeche.Expr.instantiate1, ConLeche.Expr.constsResolve]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [ConLeche.Expr.constsResolve]

theorem constsResolve_instPisWith {env₀ : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, a.constsResolve env₀ = true) →
      e.constsResolve env₀ = true → instPisWith as e = some r → r.constsResolve env₀ = true
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true] at he
      refine constsResolve_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx)) ?_ h'
      have ha := has a List.mem_cons_self
      exact constsResolve_instantiate1_any ha b 0 he.2

theorem constsResolve_replaceApps {env₀ : Env} {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us e, f c us = some e → e.constsResolve env₀ = true) :
    ∀ (e : Expr), e.constsResolve env₀ = true → (e.replaceApps f b n).constsResolve env₀ = true := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve]
  | fvar i ty ih => intro h; simpa [ConLeche.Expr.replaceApps] using h
  | sort u => intro _; simp [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve]
  | const c us =>
    intro h
    rw [ConLeche.Expr.replaceApps_const]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · exact h
  | lit l => intro h; simpa [ConLeche.Expr.replaceApps] using h
  | app a x iha ihx =>
    intro h
    rw [ConLeche.Expr.replaceApps_app]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceApps, ConLeche.Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-- A canonical abstraction resolves wherever the type does. -/
theorem canonOf_constsResolve {env₀ : Env} {ty A : Expr} (he : ty.constsResolve env₀ = true)
    (hA : CanonOf ty A) : A.constsResolve env₀ = true := by
  have hp : ∀ n, ∀ x ∈ canonParams n, x.constsResolve env₀ = true := fun _ x hx => by
    obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp [ConLeche.Expr.constsResolve]
  rcases hA with ⟨names, us, n, hA⟩ | ⟨n, hA⟩
  · unfold ConLeche.nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    refine constsResolve_replaceApps (fun c us' r hr => ?_) _ (constsResolve_instPisWith (hp _) he ht)
    obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
    simp [ConLeche.Expr.constsResolve]
  · exact constsResolve_instPisWith (hp _) he hA

end ConLeche.Model
