import Setlec.Kernel.ExprOps

/-!
# Free-variable bounds and shifting

Pure syntactic metatheory for nanoda-style free variables (de Bruijn levels
with annotated types):

* `fvarsBelow d e`: every `fvar` leaf reachable in `e` (not descending into
  `fvar` type annotations) has index `< d`.
* `shiftFrom p e`: bump every reachable `fvar` index `≥ p` by one (type
  annotations of shifted `fvar`s are shifted too).
* `shiftFrom_instantiate1`: shifting commutes with opening a binder — the
  key equation that lets weakening proofs step under a binder.

Everything here is used by the model's weakening lemmas
(`Setlec.Model.InterpLemmas`).
-/

namespace Setlec.Expr

/-- Every reachable `fvar` index is `< d`.  (Type annotations of `fvar`s
are not descended into: the interpretation never reads them at leaves;
their well-formedness is tracked separately by `FvarsOk`.) -/
def fvarsBelow (d : Nat) : Expr → Prop
  | .bvar _ | .sort _ | .const .. | .lit _ => True
  | .fvar idx _ _ => idx < d
  | .app f a => fvarsBelow d f ∧ fvarsBelow d a
  | .lam _ ty body _ | .forallE _ ty body _ => fvarsBelow d ty ∧ fvarsBelow d body
  | .letE _ ty val body => fvarsBelow d ty ∧ fvarsBelow d val ∧ fvarsBelow d body
  | .proj _ _ e => fvarsBelow d e

theorem fvarsBelow_mono {d d' : Nat} (h : d ≤ d') :
    ∀ {e : Expr}, fvarsBelow d e → fvarsBelow d' e := by
  intro e
  induction e <;> simp_all [fvarsBelow] <;> omega

/-- Bump every reachable `fvar` index `≥ p` by one. -/
def shiftFrom (p : Nat) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => if idx ≥ p then .fvar (idx + 1) n (shiftFrom p ty) else .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (shiftFrom p f) (shiftFrom p a)
  | .lam n ty body bi => .lam n (shiftFrom p ty) (shiftFrom p body) bi
  | .forallE n ty body bi => .forallE n (shiftFrom p ty) (shiftFrom p body) bi
  | .letE n ty val body => .letE n (shiftFrom p ty) (shiftFrom p val) (shiftFrom p body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (shiftFrom p e)

/-- Shifting from `p` does nothing to a term whose reachable `fvar`s are
below `p`... except inside `fvar` type annotations, which `fvarsBelow` does
not constrain; hence this lemma requires annotation-free positions only in
the sense that it recurses with the same hypothesis shape. -/
theorem shiftFrom_eq_self {p : Nat} :
    ∀ {e : Expr}, fvarsBelow p e → shiftFrom p e = e := by
  intro e
  induction e <;> simp_all [fvarsBelow, shiftFrom]

/-- A term with all reachable `fvar`s below `0` has none. -/
theorem not_hasFvar_of_fvarsBelow_zero :
    ∀ {e : Expr}, Expr.fvarsBelow 0 e → e.hasFvar = false := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- Well-scoped at depth `d`: every reachable `fvar` has index `< d`, and
its type annotation is itself well-scoped at that index (annotations may
only mention strictly earlier variables). -/
def WScoped : (d : Nat) → Expr → Prop
  | d, .fvar idx _ ty => idx < d ∧ WScoped idx ty
  | d, .app f a => WScoped d f ∧ WScoped d a
  | d, .lam _ ty body _ | d, .forallE _ ty body _ => WScoped d ty ∧ WScoped d body
  | d, .letE _ ty val body => WScoped d ty ∧ WScoped d val ∧ WScoped d body
  | d, .proj _ _ e => WScoped d e
  | _, .bvar _ | _, .sort _ | _, .const .. | _, .lit _ => True
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

theorem WScoped.mono : ∀ {e : Expr} {d d' : Nat}, d ≤ d' → WScoped d e → WScoped d' e := by
  intro e
  induction e with
  | fvar idx n ty _ =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨Nat.lt_of_lt_of_le hw.1 h, hw.2⟩
  | app f a ihf iha =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihf h hw.1, iha h hw.2⟩
  | lam n ty body bi ihty ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihbody h hw.2⟩
  | forallE n ty body bi ihty ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihbody h hw.2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihval h hw.2.1, ihbody h hw.2.2⟩
  | proj s i e ih =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ih h hw
  | _ => intro d d' h hw; simp [WScoped]

theorem WScoped.fvarsBelow : ∀ {e : Expr} {d : Nat}, WScoped d e → Expr.fvarsBelow d e := by
  intro e
  induction e with
  | fvar idx n ty _ =>
    intro d hw
    simp only [WScoped] at hw
    simpa [Expr.fvarsBelow] using hw.1
  | app f a ihf iha =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam n ty body bi ihty ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihbody hw.2⟩
  | forallE n ty body bi ihty ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihbody hw.2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihval hw.2.1, ihbody hw.2.2⟩
  | proj s i e ih =>
    intro d hw
    simp only [WScoped] at hw
    exact ih hw
  | _ => intro d hw; simp [Expr.fvarsBelow]

theorem WScoped.instantiate1 {d : Nat} {n : Name} {ty : Expr} (hty : WScoped d ty) :
    ∀ {e : Expr} (k : Nat), WScoped d e →
      WScoped (d + 1) (e.instantiate1 (.fvar d n ty) k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · simp only [WScoped]
      exact ⟨Nat.lt_succ_self d, hty⟩
    · split <;> simp [WScoped]
  | fvar idx n' ty' _ =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨Nat.lt_succ_of_lt hw.1, hw.2⟩
  | app f a ihf iha =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihf _ hw.1, iha _ hw.2⟩
  | lam n' ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | forallE n' ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | letE n' ty' val body ihty ihval ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihval _ hw.2.1, ihbody _ hw.2.2⟩
  | proj s i e ih =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ih _ hw
  | _ => intro k hw; simp [Expr.instantiate1, WScoped]

theorem WScoped.of_not_hasFvar : ∀ {e : Expr} {d : Nat}, e.hasFvar = false → WScoped d e := by
  intro e
  induction e <;> intro d h <;> simp_all [Expr.hasFvar, WScoped]

/-- Shifting commutes with instantiation by an `fvar` at the shifted
index: opening at `d` then shifting from `p ≤ d` equals shifting the body
first and opening at `d + 1` with the shifted annotation. -/
theorem shiftFrom_instantiate1 {p d : Nat} (hpd : p ≤ d) {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      shiftFrom p (e.instantiate1 (.fvar d n ty) k) =
        (shiftFrom p e).instantiate1 (.fvar (d + 1) n (shiftFrom p ty)) k := by
  intro e
  induction e <;> intro k <;>
    simp_all [instantiate1, shiftFrom]
  case bvar i =>
    split
    · simp [shiftFrom, hpd]
    · split <;> simp [shiftFrom]
  case fvar idx n' ty' ih =>
    split <;> simp [instantiate1]

/-- Opening a binder keeps reachable-`fvar` bounds. -/
theorem fvarsBelow_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ {e : Expr} (k : Nat), fvarsBelow d e →
      fvarsBelow (d + 1) (e.instantiate1 (.fvar d n ty) k) := by
  intro e
  induction e <;> intro k hb <;> simp_all [instantiate1, fvarsBelow]
  case bvar i =>
    split
    · simp [fvarsBelow]
    · split <;> simp [fvarsBelow]
  case fvar idx n' ty' ih => omega

end Setlec.Expr
