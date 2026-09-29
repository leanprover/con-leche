module

public import ConLeche.Model.Inductives.GenRuleSyn
public import ConLeche.Semantics.ConstsBound
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Abstract

public section

/-!
# The stored rule's `ih` pieces name no recursor (lane GENREC-C)

The rule's `ih` pieces — its telescopes' domains, the calls' index and
major arguments — are, up to their free variables, the generator's
pieces of the walked field types (`ClassCtor.tyN`) and the declared field
types (`ClassCtor.tyD`) — and so are the minor premises' inductive
hypotheses in the stored recursor TYPE, which is checked at the
constructors' environment (`classConstOk`: its constants resolve there).
So the rule's pieces name only constants of the constructors'
environment (`CBNF`, constants bound with the free variables forgotten).

`eraseFVars` forgets every free variable (index and annotation); it is a
homomorphism for every operation the generator opens telescopes with,
so two openings of the same term at different variables agree after
it.
-/

namespace ConLeche.Model
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (ConstsBound)
open ConLeche (Env Expr Name Level ConstantVal BinderMeta ClassGen ClassCtor)

/-! ## Forgetting the free variables -/

/-- The one variable every free variable is sent to. -/
@[expose] def F0 : Expr := .fvar 0 (.sort .zero)

/-- Every free variable forgotten. -/
@[expose] def eraseFVars (e : Expr) : Expr := e.replaceFVars fun _ => some F0

/-- **Constants bound, the free variables forgotten.** -/
@[expose] def CBNF (env : Env) (e : Expr) : Prop := ConstsBound env (eraseFVars e)

@[simp] theorem eraseFVars_fvar (i : Nat) (T : Expr) : eraseFVars (.fvar i T) = F0 := rfl

theorem eraseFVars_app (f a : Expr) :
    eraseFVars (.app f a) = .app (eraseFVars f) (eraseFVars a) := rfl

theorem eraseFVars_instantiate1 (v : Expr) :
    ∀ (e : Expr) (k : Nat),
      eraseFVars (e.instantiate1 v k) = (eraseFVars e).instantiate1 (eraseFVars v) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars]
    split
    · rfl
    · split <;> rfl
  | fvar i T _ => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at ihf iha ⊢
    rw [ihf, iha]
  | lam t b m iht ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihb ⊢
    rw [iht, ihb]
  | forallE t b m iht ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihb ⊢
    rw [iht, ihb]
  | letE t v' b iht ihv ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihv ihb ⊢
    rw [iht, ihv, ihb]
  | proj s i e ih =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at ih ⊢
    rw [ih]

theorem eraseFVars_mkAppN : ∀ (as : List Expr) (f : Expr),
    eraseFVars (Expr.mkAppN f as) = Expr.mkAppN (eraseFVars f) (as.map eraseFVars)
  | [], _ => rfl
  | a :: as, f => by
    show eraseFVars (Expr.mkAppN (.app f a) as) = _
    rw [eraseFVars_mkAppN as]; rfl

theorem eraseFVars_getAppArgs : ∀ (e : Expr),
    (eraseFVars e).getAppArgs = e.getAppArgs.map eraseFVars := by
  intro e
  induction e with
  | app f a ihf _ =>
    rw [eraseFVars_app]
    simp only [Expr.getAppArgs, List.map_append, ihf, List.map_cons, List.map_nil]
  | _ => rfl

/-! ## `CBNF` -/

theorem constsBound_eraseFVars {env : Env} : ∀ (e : Expr), ConstsBound env e → CBNF env e := by
  intro e
  induction e with
  | fvar i T _ => intro _; simp [CBNF, F0]
  | app f a ihf iha =>
    intro h; rw [ConLeche.Semantics.constsBound_app] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_app] at ihf iha ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_lam] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_lam] at iht ihb ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_forallE] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at iht ihb ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_letE] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_letE] at iht ihv ihb ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h; rw [ConLeche.Semantics.constsBound_proj] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_proj] at ih ⊢
    exact ih h
  | _ => intro h; exact h

theorem eraseFVars_of_erasedEq : ∀ {a b : Expr}, Expr.ErasedEq a b → eraseFVars a = eraseFVars b
  | .bvar i, .bvar j, h => by obtain rfl : i = j := h; rfl
  | .fvar _ _, .fvar _ _, _ => rfl
  | .sort _, .sort _, h => by obtain rfl := h; rfl
  | .const _ _, .const _ _, h => by obtain ⟨rfl, rfl⟩ := h; rfl
  | .lit _, .lit _, h => by obtain rfl := h; rfl
  | .app f a, .app g b, h => by
    show Expr.app (eraseFVars f) (eraseFVars a) = Expr.app (eraseFVars g) (eraseFVars b)
    rw [eraseFVars_of_erasedEq h.1, eraseFVars_of_erasedEq h.2]
  | .lam t b m, .lam t' b' m', h => by
    obtain ⟨rfl, h1, h2⟩ := h
    show Expr.lam (eraseFVars t) (eraseFVars b) m = Expr.lam (eraseFVars t') (eraseFVars b') m
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2]
  | .forallE t b m, .forallE t' b' m', h => by
    obtain ⟨rfl, h1, h2⟩ := h
    show Expr.forallE (eraseFVars t) (eraseFVars b) m
      = Expr.forallE (eraseFVars t') (eraseFVars b') m
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2]
  | .letE t v b, .letE t' v' b', h => by
    obtain ⟨h1, h2, h3⟩ := h
    show Expr.letE (eraseFVars t) (eraseFVars v) (eraseFVars b)
      = Expr.letE (eraseFVars t') (eraseFVars v') (eraseFVars b')
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2, eraseFVars_of_erasedEq h3]
  | .proj s i e, .proj s' i' e', h => by
    obtain ⟨rfl, rfl, h1⟩ := h
    show Expr.proj s i (eraseFVars e) = Expr.proj s i (eraseFVars e')
    rw [eraseFVars_of_erasedEq h1]
  | .bvar _, .fvar _ _, h | .bvar _, .sort _, h | .bvar _, .const _ _, h | .bvar _, .app _ _, h
  | .bvar _, .lam _ _ _, h | .bvar _, .forallE _ _ _, h | .bvar _, .letE _ _ _, h
  | .bvar _, .lit _, h | .bvar _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .fvar _ _, .bvar _, h | .fvar _ _, .sort _, h | .fvar _ _, .const _ _, h
  | .fvar _ _, .app _ _, h | .fvar _ _, .lam _ _ _, h | .fvar _ _, .forallE _ _ _, h
  | .fvar _ _, .letE _ _ _, h | .fvar _ _, .lit _, h | .fvar _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .sort _, .bvar _, h | .sort _, .fvar _ _, h | .sort _, .const _ _, h | .sort _, .app _ _, h
  | .sort _, .lam _ _ _, h | .sort _, .forallE _ _ _, h | .sort _, .letE _ _ _, h
  | .sort _, .lit _, h | .sort _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .const _ _, .bvar _, h | .const _ _, .fvar _ _, h | .const _ _, .sort _, h
  | .const _ _, .app _ _, h | .const _ _, .lam _ _ _, h | .const _ _, .forallE _ _ _, h
  | .const _ _, .letE _ _ _, h | .const _ _, .lit _, h | .const _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .app _ _, .bvar _, h | .app _ _, .fvar _ _, h | .app _ _, .sort _, h
  | .app _ _, .const _ _, h | .app _ _, .lam _ _ _, h | .app _ _, .forallE _ _ _, h
  | .app _ _, .letE _ _ _, h | .app _ _, .lit _, h | .app _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .lam _ _ _, .bvar _, h | .lam _ _ _, .fvar _ _, h | .lam _ _ _, .sort _, h
  | .lam _ _ _, .const _ _, h | .lam _ _ _, .app _ _, h | .lam _ _ _, .forallE _ _ _, h
  | .lam _ _ _, .letE _ _ _, h | .lam _ _ _, .lit _, h | .lam _ _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .forallE _ _ _, .bvar _, h | .forallE _ _ _, .fvar _ _, h | .forallE _ _ _, .sort _, h
  | .forallE _ _ _, .const _ _, h | .forallE _ _ _, .app _ _, h | .forallE _ _ _, .lam _ _ _, h
  | .forallE _ _ _, .letE _ _ _, h | .forallE _ _ _, .lit _, h
  | .forallE _ _ _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .letE _ _ _, .bvar _, h | .letE _ _ _, .fvar _ _, h | .letE _ _ _, .sort _, h
  | .letE _ _ _, .const _ _, h | .letE _ _ _, .app _ _, h | .letE _ _ _, .lam _ _ _, h
  | .letE _ _ _, .forallE _ _ _, h | .letE _ _ _, .lit _, h
  | .letE _ _ _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .lit _, .bvar _, h | .lit _, .fvar _ _, h | .lit _, .sort _, h | .lit _, .const _ _, h
  | .lit _, .app _ _, h | .lit _, .lam _ _ _, h | .lit _, .forallE _ _ _, h
  | .lit _, .letE _ _ _, h | .lit _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .proj _ _ _, .bvar _, h | .proj _ _ _, .fvar _ _, h | .proj _ _ _, .sort _, h
  | .proj _ _ _, .const _ _, h | .proj _ _ _, .app _ _, h | .proj _ _ _, .lam _ _ _, h
  | .proj _ _ _, .forallE _ _ _, h | .proj _ _ _, .letE _ _ _, h
  | .proj _ _ _, .lit _, h => by simp [Expr.ErasedEq] at h

theorem CBNF_abstract1 {env : Env} (i : Nat) :
    ∀ (e : Expr) (k : Nat), CBNF env (e.abstract1 i k) → CBNF env e := by
  intro e
  induction e with
  | fvar j T _ => intro _ _; simp [CBNF, F0]
  | app f a ihf iha =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_app] at ihf iha h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_lam] at iht ihb h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at iht ihb h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_letE] at iht ihv ihb h ⊢
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s j e ih =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_proj] at ih h ⊢
    exact ih k h
  | _ => intro k h; exact h

/-- A closed telescope's pieces carry its constants. -/
theorem CBNF_closeTelescope {env : Env} :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (b : Expr),
      CBNF env (ConLeche.closeTelescope nds i b) → (∀ nd ∈ nds, CBNF env nd.1) ∧ CBNF env b
  | [], _, b, h => ⟨(fun _ h' => nomatch h'), h⟩
  | (d, bm) :: nds, i, b, h => by
    simp only [ConLeche.closeTelescope, CBNF, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at h
    have h2 : CBNF env (ConLeche.closeTelescope nds (i + 1) b) :=
      CBNF_abstract1 i _ 0 h.2
    obtain ⟨hn, hb⟩ := CBNF_closeTelescope nds (i + 1) b h2
    refine ⟨fun nd hnd => ?_, hb⟩
    rcases List.mem_cons.mp hnd with rfl | hnd
    · exact h.1
    · exact hn nd hnd

theorem CBNF_mkAppN {env : Env} :
    ∀ (as : List Expr) (f : Expr),
      CBNF env (Expr.mkAppN f as) ↔ CBNF env f ∧ ∀ a ∈ as, CBNF env a
  | [], f => by simp; rfl
  | a :: as, f => by
    have ih := CBNF_mkAppN (env := env) as (.app f a)
    show CBNF env (Expr.mkAppN (.app f a) as) ↔ _
    rw [ih]
    have happ : CBNF env (.app f a) ↔ CBNF env f ∧ CBNF env a := by
      simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_app]
    rw [happ]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

end ConLeche.Model
