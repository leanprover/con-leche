import Setlec.Model.TeleElim

/-!
# Constructing values over a `∀`-telescope

The *direct* installation path for simple structures (non-recursive,
single-constructor, index-free, provably-nonzero result sort) has to
**build** the set-theoretic values of the type former, the constructor
and the recursor instead of borrowing them from a preprocessor
artifact.  Every one of those values is a λ-tower over a stored
`∀`-telescope whose body is computed from the telescope's argument
values.

This module provides that missing *introduction* direction — the whole
existing telescope machinery (`TeleFit.elim`, `TeleFitLam.fold`,
`closeLamsAt_fold`) is elimination-only:

* `teleLamV k d ρ ty S` — the `k`-binder λ-tower over the telescope
  `ty`, with the tags read off the telescope's own codomain-sort
  annotations, whose body at the argument values `xs` (and the final
  frame `d'`, `ρ'`) is `S d' ρ' xs`;
* `teleLamV_mem` — it inhabits the interpretation of `ty`, provided the
  body inhabits the interpretation of every fitting residual;
* `teleLamV_fold` — applying it along a fitting value spine computes
  the body.

Both lemmas take the same body obligation `TeleBody`, since `app_lam'`
needs the fibre memberships that `lam_mem` establishes.

The dependent-pair tower (the structure's own model) lives in
`Setlec.Model.DirectTower`.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {cval : ConstVal V}

open SetTheory Expr

/-- `stripPis` only inspects the `∀`-spine, which `instantiate1`
preserves. -/
theorem stripPis_instantiate1_isSome :
    ∀ (k : Nat) (e v : Expr) (j : Nat),
      (Expr.stripPis k e).isSome = true →
      (Expr.stripPis k (e.instantiate1 v j)).isSome = true := by
  intro k
  induction k with
  | zero => intro e v j _; rfl
  | succ k ih =>
    intro e v j h
    match e with
    | .forallE n ty body m =>
      rw [Expr.instantiate1, Expr.stripPis]
      rw [Expr.stripPis] at h
      have hb : (Expr.stripPis k body).isSome = true := by
        cases hs : Expr.stripPis k body with
        | none => rw [hs] at h; exact nomatch h
        | some p => rfl
      have := ih body v (j + 1) hb
      cases hs : Expr.stripPis k (body.instantiate1 v (j + 1)) with
      | none => rw [hs] at this; exact nomatch this
      | some p => rfl
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch h

/-- The body obligation of a λ-tower over `ty`: at every fitting value
spine of the right length the body value inhabits the interpretation of
the residual. -/
def TeleBody (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) (k d : Nat) (ρ : Nat → V) (ty : Expr)
    (S : Nat → (Nat → V) → List V → V) : Prop :=
  ∀ (xs : List V) (d' : Nat) (ρ' : Nat → V) (rest : Expr),
    TeleFit V cval env φ d ρ ty xs d' ρ' rest → xs.length = k →
    ∃ Q, interpExpr V cval env φ d' ρ' rest = some Q ∧ S d' ρ' xs ∈ˢ Q

/-- The `k`-binder λ-tower over the `∀`-telescope `ty` whose body is
computed from the argument values (see the module docs).  Outside the
telescope (fewer than `k` binders) the junk value `∅`. -/
noncomputable def teleLamV (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat) :
    Nat → Nat → (Nat → V) → Expr → (Nat → (Nat → V) → List V → V) → V
  | 0, d, ρ, _, S => S d ρ []
  | k + 1, d, ρ, .forallE n ty body _m, S =>
    SetTheory.lamC
      ((interpExpr V cval env φ d ρ ty).getD SetTheory.empty)
      (fun x => teleLamV V cval env φ k (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty))
        (fun d' ρ' xs => S d' ρ' (x :: xs)))
  | _ + 1, _, _, _, _ => SetTheory.empty

@[simp] theorem teleLamV_zero (d : Nat) (ρ : Nat → V) (ty : Expr)
    (S : Nat → (Nat → V) → List V → V) :
    teleLamV V cval env φ 0 d ρ ty S = S d ρ [] := rfl

theorem teleLamV_forallE (k d : Nat) (ρ : Nat → V) (n : Name)
    (ty body : Expr) (m : BinderMeta)
    (S : Nat → (Nat → V) → List V → V) :
    teleLamV V cval env φ (k + 1) d ρ (.forallE n ty body m) S =
      SetTheory.lamC
        ((interpExpr V cval env φ d ρ ty).getD SetTheory.empty)
        (fun x => teleLamV V cval env φ k (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))
          (fun d' ρ' xs => S d' ρ' (x :: xs))) := rfl

/-- The λ-tower inhabits the interpretation of its telescope. -/
theorem teleLamV_mem :
    ∀ (k : Nat) {d : Nat} {ρ : Nat → V} {ty : Expr} {P : V}
      {S : Nat → (Nat → V) → List V → V},
      (Expr.stripPis k ty).isSome = true →
      interpExpr V cval env φ d ρ ty = some P →
      AnnotOk V cval env φ d ρ ty →
      TeleBody V cval env φ k d ρ ty S →
      teleLamV V cval env φ k d ρ ty S ∈ˢ P := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty P S _ hi _ hS
    obtain ⟨Q, hQ, hmem⟩ := hS [] d ρ ty TeleFit.nil rfl
    rw [hi] at hQ
    obtain rfl := Option.some.inj hQ
    exact hmem
  | succ k ih =>
    intro d ρ ty P S hstrip hi hA hS
    match ty with
    | .forallE n dom body m =>
      rw [Expr.stripPis] at hstrip
      have hb : (Expr.stripPis k body).isSome = true := by
        cases hs : Expr.stripPis k body with
        | none => rw [hs] at hstrip; exact nomatch hstrip
        | some p => rfl
      simp only [AnnotOk] at hA
      obtain ⟨-, hcond⟩ := hA
      rw [interpExpr] at hi
      cases hdom : interpExpr V cval env φ d ρ dom with
      | none => rw [hdom] at hi; exact nomatch hi
      | some A =>
        rw [hdom] at hi
        dsimp only at hi
        obtain rfl := Option.some.inj hi
        rw [teleLamV_forallE, hdom]
        dsimp only [Option.getD]
        refine lamC_mem ?_
        intro x hx
        obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
        obtain ⟨w, hwi⟩ := hwfact
        rw [hwi]
        dsimp only [Option.getD]
        refine ih (stripPis_instantiate1_isSome k body _ 0 hb) hwi hAb ?_
        intro xs d' ρ' rest hfit hlen
        exact hS (x :: xs) d' ρ' rest (TeleFit.cons hdom hx hfit)
          (by simp [hlen])
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hstrip

/-- Applying the λ-tower along a fitting value spine computes the
body. -/
theorem teleLamV_fold :
    ∀ {k : Nat} {d : Nat} {ρ : Nat → V} {ty : Expr} {xs : List V}
      {d' : Nat} {ρ' : Nat → V} {rest : Expr}
      {S : Nat → (Nat → V) → List V → V},
      (Expr.stripPis k ty).isSome = true →
      TeleFit V cval env φ d ρ ty xs d' ρ' rest → xs.length = k →
      AnnotOk V cval env φ d ρ ty →
      TeleBody V cval env φ k d ρ ty S →
      SpineFold V (teleLamV V cval env φ k d ρ ty S) xs = S d' ρ' xs := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty xs d' ρ' rest S _ hfit hlen _ _
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    rfl
  | succ k ih =>
    intro d ρ ty xs d' ρ' rest S hstrip hfit hlen hA hS
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ n dom body m x xs d₂ ρ₂ rest A hdom hx hfit =>
      rw [Expr.stripPis] at hstrip
      have hb : (Expr.stripPis k body).isSome = true := by
        cases hs : Expr.stripPis k body with
        | none => rw [hs] at hstrip; exact nomatch hstrip
        | some p => rfl
      have hb' : (Expr.stripPis k (body.instantiate1 (.fvar d n dom))).isSome
          = true := stripPis_instantiate1_isSome k body _ 0 hb
      simp only [AnnotOk] at hA
      obtain ⟨-, hcond⟩ := hA
      have hbodyS : ∀ y, y ∈ˢ A →
          TeleBody V cval env φ k (d + 1) (updV V ρ d y)
            (body.instantiate1 (.fvar d n dom))
            (fun d' ρ' zs => S d' ρ' (y :: zs)) := by
        intro y hy zs d₃ ρ₃ rest₃ hfit₃ hlen₃
        exact hS (y :: zs) d₃ ρ₃ rest₃ (TeleFit.cons hdom hy hfit₃)
          (by simp [hlen₃])
      rw [teleLamV_forallE, hdom]
      dsimp only [Option.getD]
      rw [SpineFold_cons]
      have hfib : ∀ y, y ∈ˢ A →
          teleLamV V cval env φ k (d + 1) (updV V ρ d y)
              (body.instantiate1 (.fvar d n dom))
              (fun d' ρ' zs => S d' ρ' (y :: zs)) ∈ˢ
            ((interpExpr V cval env φ (d + 1) (updV V ρ d y)
              (body.instantiate1 (.fvar d n dom))).getD SetTheory.empty) := by
        intro y hy
        obtain ⟨hAb, hwfact⟩ := hcond y A hdom hy
        obtain ⟨w, hwi⟩ := hwfact
        rw [hwi]
        dsimp only [Option.getD]
        exact teleLamV_mem k hb' hwi hAb (hbodyS y hy)
      rw [app_lamC hx]
      obtain ⟨hAb, -⟩ := hcond x A hdom hx
      exact ih hb' hfit (by simpa using hlen) hAb (hbodyS x hx)

end Setlec
