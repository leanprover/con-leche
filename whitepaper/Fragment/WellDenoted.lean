module

public import Fragment.Interp

@[expose] public section

/-!
# The semantic invariant `WellDenoted`

There is no typing judgement in the proof.  In its place stands a
**semantic** judgement on terms, `WellDenoted M φ ρ e`, defined
inductively: it holds of a term when it holds of the subterms and one
condition on the term's own shape is met.  Each binder shape and the
application come in two rules, one per regime — the function-space
reading and the propositional reading — and the regime of a `λ` or
`∀` is decided by its annotation:

* an application applies a member of some function space to a member
  of its domain (`appFun`), or a member of a propositional `∀` — a
  truth value — to a member of its domain, where the fibres are truth
  values (`appProp`);
* a λ has a bounded codomain — some fibre family the body lands in —
  and if its annotation says "proposition" the fibres are truth values
  (`lamFun`/`lamProp`);
* a Π's body is well-denoted at every point of the domain, and if its
  annotation says "proposition" the body IS a truth value there
  (`piFun`/`piProp`);
* variables, sorts and constants are always well-denoted.

The binder rules are where the annotation is held to account: the
datum may claim "proposition" only where the body really denotes a
truth value.  Unlike a typing judgement the predicate is preserved by
β without a substitution lemma about derivations: it transports along
`Expr.inst` by the substitution lemmas of `Interp.lean`
(`WellDenoted_inst0`), and a β step at a well-denoted redex keeps the
denotation and the invariant (`WellDenoted_beta_graph`,
`WellDenoted_beta`).

The inversion lemmas `WellDenoted_app`/`_lam`/`_pi` merge each pair of
rules back into one clause with the regime as a Boolean — the shape
con-leche's `ConLeche/Semantics/WellDenoted.lean` has as a recursive
definition on `AnnotTerm` (with `AnnotValid`, the annotation's
truthfulness, kept there as a separate conjunct `WellDenotedV`); the
proofs below go through them.

A **context** `Γ` is satisfied by an environment `ρ` (`Sat`) when each
`ρ i` is a member of what `Γ[i]` denotes under the rest of `ρ`, with
`Γ[i]` itself well-denoted there — the semantic reading of `Γ ⊢`.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V]

/-- **The semantic invariant**, as an inductively defined judgement
`WellDenoted M φ ρ e` (see the module docstring): `e` is well-denoted
under the environment `ρ`, the constant model `M` and the level
valuation `φ`. -/
inductive WellDenoted (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → Expr → Prop
  /-- A variable is always well-denoted: it denotes whatever `ρ` holds. -/
  | bvar {ρ : Nat → V} {i : Nat} : WellDenoted M φ ρ (.bvar i)
  /-- A sort is always well-denoted: it denotes a universe. -/
  | sort {ρ : Nat → V} {u : Level} : WellDenoted M φ ρ (.sort u)
  /-- A constant is always well-denoted: it denotes what the model `M` says. -/
  | const {ρ : Nat → V} {c : Name} {ls : List Level} : WellDenoted M φ ρ (.const c ls)
  /-- **Application, function regime**: both parts are well-denoted, the
  function denotes a member of some function space `piSet A B`, and the
  argument a member of its domain `A`. -/
  | appFun {ρ : Nat → V} {f a : Expr} {A : V} {B : V → V} :
      WellDenoted M φ ρ f → WellDenoted M φ ρ a →
      interp M φ ρ f ∈ˢ piSet A B → interp M φ ρ a ∈ˢ A →
      WellDenoted M φ ρ (.app f a)
  /-- **Application, propositional regime**: both parts are well-denoted,
  the function denotes a member of the propositional `∀` over `A` with
  fibres `B` — the truth value of "every fibre is `{pt}`" — the
  argument a member of `A`, and the fibres are truth values. -/
  | appProp {ρ : Nat → V} {f a : Expr} {A : V} {B : V → V} :
      WellDenoted M φ ρ f → WellDenoted M φ ρ a →
      interp M φ ρ f ∈ˢ truthVal (∀ x, x ∈ˢ A → B x = one) → interp M φ ρ a ∈ˢ A →
      (∀ x, x ∈ˢ A → B x ∈ˢ univ 0) →
      WellDenoted M φ ρ (.app f a)
  /-- **λ, function regime** (the annotation does not hold): the domain is
  well-denoted, the body is well-denoted under every value of the
  domain, and its value lies in `B x` for every such `x` — some fibre
  family `B` bounds the body. -/
  | lamFun {ρ : Nat → V} {A : Expr} {pw : PropWhen} {b : Expr} {B : V → V} :
      pw.holds φ = false →
      WellDenoted M φ ρ A →
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) →
      (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) →
      WellDenoted M φ ρ (.lam A pw b)
  /-- **λ, propositional regime** (the annotation holds): as `lamFun`, and
  the codomain's fibres `B x` are truth values. -/
  | lamProp {ρ : Nat → V} {A : Expr} {pw : PropWhen} {b : Expr} {B : V → V} :
      pw.holds φ = true →
      WellDenoted M φ ρ A →
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) →
      (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) →
      (∀ x, x ∈ˢ interp M φ ρ A → B x ∈ˢ univ 0) →
      WellDenoted M φ ρ (.lam A pw b)
  /-- **∀, function regime** (the annotation does not hold): the domain is
  well-denoted and the body is well-denoted under every value of the
  domain. -/
  | piFun {ρ : Nat → V} {A : Expr} {pw : PropWhen} {B : Expr} :
      pw.holds φ = false →
      WellDenoted M φ ρ A →
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) →
      WellDenoted M φ ρ (.pi A pw B)
  /-- **∀, propositional regime** (the annotation holds): as `piFun`, and
  the body denotes a truth value at every value of the domain. -/
  | piProp {ρ : Nat → V} {A : Expr} {pw : PropWhen} {B : Expr} :
      pw.holds φ = true →
      WellDenoted M φ ρ A →
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) →
      (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) B ∈ˢ univ 0) →
      WellDenoted M φ ρ (.pi A pw B)

variable (M : Name → List Nat → V) (φ : Name → Nat)

/-! ### Inversion

The three merged clauses: each pair of regime rules, as one
bi-implication with the regime as a Boolean (`pw.holds φ` at a binder,
an existential `p` at an application).  Every proof below reads the
judgement through these. -/

@[simp] theorem WellDenoted_bvar (ρ : Nat → V) (i : Nat) :
    WellDenoted M φ ρ (.bvar i) := .bvar
@[simp] theorem WellDenoted_sort (ρ : Nat → V) (u : Level) :
    WellDenoted M φ ρ (.sort u) := .sort
@[simp] theorem WellDenoted_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    WellDenoted M φ ρ (.const c ls) := .const

theorem WellDenoted_pi (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) :
    WellDenoted M φ ρ (.pi A pw B) ↔
      (WellDenoted M φ ρ A ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) ∧
        (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A →
          interp M φ (cons x ρ) B ∈ˢ univ 0)) := by
  constructor
  · intro h
    cases h with
    | piFun hp hA hB => exact ⟨hA, hB, fun h => by rw [hp] at h; exact nomatch h⟩
    | piProp _ hA hB hz => exact ⟨hA, hB, fun _ => hz⟩
  · rintro ⟨hA, hB, hz⟩
    cases hp : pw.holds φ
    · exact .piFun hp hA hB
    · exact .piProp hp hA hB (hz hp)

theorem WellDenoted_lam (ρ : Nat → V) (A : Expr) (pw : PropWhen) (b : Expr) :
    WellDenoted M φ ρ (.lam A pw b) ↔
      (WellDenoted M φ ρ A ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) ∧
          (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A → B x ∈ˢ univ 0)) := by
  constructor
  · intro h
    cases h with
    | lamFun hp hA hb hfib => exact ⟨hA, hb, _, hfib, fun h => by rw [hp] at h; exact nomatch h⟩
    | lamProp _ hA hb hfib hz => exact ⟨hA, hb, _, hfib, fun _ => hz⟩
  · rintro ⟨hA, hb, B, hfib, hz⟩
    cases hp : pw.holds φ
    · exact .lamFun hp hA hb hfib
    · exact .lamProp hp hA hb hfib (hz hp)

theorem WellDenoted_app (ρ : Nat → V) (f a : Expr) :
    WellDenoted M φ ρ (.app f a) ↔
      (WellDenoted M φ ρ f ∧ WellDenoted M φ ρ a ∧
        ∃ (p : Bool) (A : V) (B : V → V),
          interp M φ ρ f ∈ˢ piR p A B ∧ interp M φ ρ a ∈ˢ A ∧
          (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)) := by
  constructor
  · intro h
    cases h with
    | appFun hf ha hslot hmem =>
      exact ⟨hf, ha, false, _, _, by rw [piR_false]; exact hslot, hmem, fun h => nomatch h⟩
    | appProp hf ha hslot hmem hz =>
      exact ⟨hf, ha, true, _, _, by rw [piR_true]; exact hslot, hmem, fun _ => hz⟩
  · rintro ⟨hf, ha, p, A, B, hslot, hmem, hz⟩
    cases p
    · rw [piR_false] at hslot; exact .appFun hf ha hslot hmem
    · rw [piR_true] at hslot; exact .appProp hf ha hslot hmem (hz rfl)

/-! ### The substitution metatheory -/

/-- The invariant through lifting. -/
theorem WellDenoted_liftN (n : Nat) :
    ∀ (e : Expr) (k : Nat) (ρ : Nat → V),
      WellDenoted M φ ρ (e.liftN n k) ↔ WellDenoted M φ (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i => intro k ρ; simp
  | sort u => intro k ρ; simp
  | const c ls => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [Expr.liftN_app, WellDenoted_app, WellDenoted_app, ihf, iha,
      interp_liftN, interp_liftN]
  | lam A pw b ihA ihb =>
    intro k ρ
    rw [Expr.liftN_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · rw [ihb, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | pi A pw B ihA ihB =>
    intro k ρ
    rw [Expr.liftN_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]

/-- The forward half of `WellDenoted_inst`, by induction on the
derivation for `e[a]`: the shape of the derivation's conclusion
determines the shape of `e` (or `e` is the substituted variable, whose
judgement is free). -/
private theorem WellDenoted_inst_mp (a : Expr) :
    ∀ {ρ : Nat → V} {e' : Expr}, WellDenoted M φ ρ e' →
      ∀ (e : Expr) (k : Nat), e' = e.inst a k → WellDenoted M φ (shiftE k 0 ρ) a →
      WellDenoted M φ (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e := by
  intro ρ₀ e' h
  induction h with
  | bvar =>
    intro e k he _
    cases e <;> first | exact .bvar | exact .sort | exact .const | simp at he
  | sort =>
    intro e k he _
    cases e <;> first | exact .bvar | exact .sort | exact .const | simp at he
  | const =>
    intro e k he _
    cases e <;> first | exact .bvar | exact .sort | exact .const | simp at he
  | appFun hf ha hslot hmem ihf iha =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app f b =>
      rw [Expr.inst_app] at he
      obtain ⟨rfl, rfl⟩ := Expr.app.inj he
      rw [interp_inst] at hslot hmem
      exact .appFun (ihf f k rfl hwa) (iha b k rfl hwa) hslot hmem
    | lam _ _ _ => simp at he
    | pi _ _ _ => simp at he
  | appProp hf ha hslot hmem hz ihf iha =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app f b =>
      rw [Expr.inst_app] at he
      obtain ⟨rfl, rfl⟩ := Expr.app.inj he
      rw [interp_inst] at hslot hmem
      exact .appProp (ihf f k rfl hwa) (iha b k rfl hwa) hslot hmem hz
    | lam _ _ _ => simp at he
    | pi _ _ _ => simp at he
  | @lamFun ρ _ _ _ B hp hA hb hfib ihA ihb =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app _ _ => simp at he
    | lam A pw b =>
      rw [Expr.inst_lam] at he
      obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj he
      refine .lamFun (B := B) hp (ihA A k rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := ihb x hx' b (k + 1) rfl (by rwa [shiftE_succ_cons])
        rwa [shiftE_succ_cons, ← cons_instE] at this
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := hfib x hx'
        rwa [interp_inst, shiftE_succ_cons, ← cons_instE] at this
    | pi _ _ _ => simp at he
  | @lamProp ρ _ _ _ B hp hA hb hfib hz ihA ihb =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app _ _ => simp at he
    | lam A pw b =>
      rw [Expr.inst_lam] at he
      obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj he
      refine .lamProp (B := B) hp (ihA A k rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
        (fun x hx => hz x (by rw [interp_inst]; exact hx))
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := ihb x hx' b (k + 1) rfl (by rwa [shiftE_succ_cons])
        rwa [shiftE_succ_cons, ← cons_instE] at this
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := hfib x hx'
        rwa [interp_inst, shiftE_succ_cons, ← cons_instE] at this
    | pi _ _ _ => simp at he
  | @piFun ρ _ _ _ hp hA hB ihA ihB =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app _ _ => simp at he
    | lam _ _ _ => simp at he
    | pi A pw B =>
      rw [Expr.inst_pi] at he
      obtain ⟨rfl, rfl, rfl⟩ := Expr.pi.inj he
      refine .piFun hp (ihA A k rfl hwa) (fun x hx => ?_)
      have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
      have := ihB x hx' B (k + 1) rfl (by rwa [shiftE_succ_cons])
      rwa [shiftE_succ_cons, ← cons_instE] at this
  | @piProp ρ _ _ _ hp hA hB hz ihA ihB =>
    intro e k he hwa
    cases e with
    | bvar _ => exact .bvar
    | sort _ => exact .sort
    | const _ _ => exact .const
    | app _ _ => simp at he
    | lam _ _ _ => simp at he
    | pi A pw B =>
      rw [Expr.inst_pi] at he
      obtain ⟨rfl, rfl, rfl⟩ := Expr.pi.inj he
      refine .piProp hp (ihA A k rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := ihB x hx' B (k + 1) rfl (by rwa [shiftE_succ_cons])
        rwa [shiftE_succ_cons, ← cons_instE] at this
      · have hx' : x ∈ˢ interp M φ ρ (A.inst a k) := by rwa [interp_inst]
        have := hz x hx'
        rwa [interp_inst, shiftE_succ_cons, ← cons_instE] at this

/-- The backward half of `WellDenoted_inst`, by induction on the
derivation for `e` under the instantiated environment. -/
private theorem WellDenoted_inst_mpr (a : Expr) :
    ∀ {ρ' : Nat → V} {e : Expr}, WellDenoted M φ ρ' e →
      ∀ (k : Nat) (ρ : Nat → V), ρ' = instE k (interp M φ (shiftE k 0 ρ) a) ρ →
      WellDenoted M φ (shiftE k 0 ρ) a → WellDenoted M φ ρ (e.inst a k) := by
  intro ρ' e h
  induction h with
  | @bvar _ i =>
    intro k ρ _ hwa
    rw [Expr.inst_bvar]
    by_cases h : i < k
    · rw [if_pos h]; exact .bvar
    · rw [if_neg h]
      by_cases h2 : i = k
      · rw [if_pos h2]; exact (WellDenoted_liftN M φ k a 0 ρ).mpr hwa
      · rw [if_neg h2]; exact .bvar
  | sort => intro k ρ _ _; exact .sort
  | const => intro k ρ _ _; exact .const
  | appFun hf ha hslot hmem ihf iha =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_app]
    exact .appFun (ihf k ρ rfl hwa) (iha k ρ rfl hwa) (by rwa [interp_inst]) (by rwa [interp_inst])
  | appProp hf ha hslot hmem hz ihf iha =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_app]
    exact .appProp (ihf k ρ rfl hwa) (iha k ρ rfl hwa) (by rwa [interp_inst])
      (by rwa [interp_inst]) hz
  | @lamFun _ _ _ _ B hp hA hb hfib ihA ihb =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_lam]
    refine .lamFun (B := B) hp (ihA k ρ rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interp_inst] at hx
      exact ihb x hx (k + 1) (cons x ρ) (by rw [cons_instE, shiftE_succ_cons])
        (by rwa [shiftE_succ_cons])
    · rw [interp_inst] at hx
      rw [interp_inst, shiftE_succ_cons, ← cons_instE]
      exact hfib x hx
  | @lamProp _ _ _ _ B hp hA hb hfib hz ihA ihb =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_lam]
    refine .lamProp (B := B) hp (ihA k ρ rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => hz x (by rwa [interp_inst] at hx))
    · rw [interp_inst] at hx
      exact ihb x hx (k + 1) (cons x ρ) (by rw [cons_instE, shiftE_succ_cons])
        (by rwa [shiftE_succ_cons])
    · rw [interp_inst] at hx
      rw [interp_inst, shiftE_succ_cons, ← cons_instE]
      exact hfib x hx
  | piFun hp hA hB ihA ihB =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_pi]
    refine .piFun hp (ihA k ρ rfl hwa) (fun x hx => ?_)
    rw [interp_inst] at hx
    exact ihB x hx (k + 1) (cons x ρ) (by rw [cons_instE, shiftE_succ_cons])
      (by rwa [shiftE_succ_cons])
  | piProp hp hA hB hz ihA ihB =>
    intro k ρ hρ hwa
    subst hρ
    rw [Expr.inst_pi]
    refine .piProp hp (ihA k ρ rfl hwa) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interp_inst] at hx
      exact ihB x hx (k + 1) (cons x ρ) (by rw [cons_instE, shiftE_succ_cons])
        (by rwa [shiftE_succ_cons])
    · rw [interp_inst] at hx
      rw [interp_inst, shiftE_succ_cons, ← cons_instE]
      exact hz x hx

/-- The invariant through instantiation, given the substituted term's
— by induction on the derivation (one half on the derivation for
`e[a]`, the other on the derivation for `e`), with the interpretation's
substitution lemma `interp_inst` at every membership. -/
theorem WellDenoted_inst :
    ∀ (e a : Expr) (k : Nat) (ρ : Nat → V),
      WellDenoted M φ (shiftE k 0 ρ) a →
      (WellDenoted M φ ρ (e.inst a k) ↔
        WellDenoted M φ (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e) :=
  fun e a k ρ ha =>
    ⟨fun h => WellDenoted_inst_mp M φ a h e k rfl ha,
     fun h => WellDenoted_inst_mpr M φ a h k ρ rfl ha⟩

/-- **Substitution at the innermost binder** — the β transport form:
`b[x := a]` is well-denoted exactly when `b` is, under `⟦a⟧ :: ρ`. -/
theorem WellDenoted_inst0 {e a : Expr} {ρ : Nat → V} (ha : WellDenoted M φ ρ a) :
    WellDenoted M φ ρ (e.inst a) ↔
      WellDenoted M φ (cons (interp M φ ρ a) ρ) e := by
  have h := WellDenoted_inst M φ e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-- The invariant through level instantiation. -/
theorem WellDenoted_instL (ps : List Name) (ls : List Level) :
    ∀ (e : Expr) (ρ : Nat → V),
      WellDenoted M φ ρ (e.instL ps ls) ↔ WellDenoted M (Level.substVal φ ps ls) ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c ls => intro ρ; simp
  | app f a ihf iha =>
    intro ρ
    rw [Expr.instL_app, WellDenoted_app, WellDenoted_app, ihf, iha, interp_instL, interp_instL]
  | lam A pw b ihA ihb =>
    intro ρ
    rw [Expr.instL_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_instL,
      PropWhen.holds_substL]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb _))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    rw [interp_instL]
  | pi A pw B ihA ihB =>
    intro ρ
    rw [Expr.instL_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_instL,
      PropWhen.holds_substL]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB _))
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp_instL]

/-! ### The β step -/

/-- **β in the graph regime, from the invariant alone.**  At a redex
whose λ is annotated `never`, the application's slot is a graph-regime
product (the λ denotes a graph, never the point), so the graph's
domain is the λ's own and the argument is in it; the graph's β fires
and the invariant transports.  No certificate is needed — this is the
soundness of `Red.betaGate`. -/
theorem WellDenoted_beta_graph {A b a : Expr} {ρ : Nat → V}
    (h : WellDenoted M φ ρ (.app (.lam A .never b) a)) :
    interp M φ ρ (.app (.lam A .never b) a) = interp M φ ρ (b.inst a) ∧
    WellDenoted M φ ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, p, A', B', hslot, hmem, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, -⟩ := hlam
  -- the slot's product is in the graph regime: the λ is not the point
  have hp : p = false := by
    cases p
    · rfl
    · exact absurd (eq_pt_of_mem_piR_true hslot) lamR_false_ne_pt
  subst hp
  -- a graph determines its domain: the slot's domain is the λ's own
  have hown : interp M φ ρ (.lam A .never b) ∈ˢ piR false (interp M φ ρ A) B :=
    lamR_mem hfib fun h => nomatch h
  have hAA : interp M φ ρ A = A' := piR_dom_unique hown hslot
  have haA : interp M φ ρ a ∈ˢ interp M φ ρ A := by rw [hAA]; exact hmem
  refine ⟨?_, (WellDenoted_inst0 M φ ha).mpr (hbody _ haA)⟩
  rw [interp_app, interp_lam, PropWhen.holds_never, app_lamR_false haA, interp_inst0]

/-- **β at any regime, given the argument's membership** — the fact the
certified β step supplies (`Red.beta`: the argument's type is
definitionally equal to the domain).  At a proposition both sides are
the point; above it the graph's β fires. -/
theorem WellDenoted_beta {A b a : Expr} {pw : PropWhen} {ρ : Nat → V}
    (h : WellDenoted M φ ρ (.app (.lam A pw b) a))
    (hmem : interp M φ ρ a ∈ˢ interp M φ ρ A) :
    interp M φ ρ (.app (.lam A pw b) a) = interp M φ ρ (b.inst a) ∧
    WellDenoted M φ ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, hz⟩ := hlam
  refine ⟨?_, (WellDenoted_inst0 M φ ha).mpr (hbody _ hmem)⟩
  rw [interp_app, interp_lam, app_lamR hmem hfib hz, interp_inst0]

/-! ### Establishing the application clause -/

/-- **The application slot, from the function's type**: a function in a
Π's interpretation and an argument in the Π's domain make a
well-denoted application, the Π's own annotation clause supplying the
truth-value component at a proposition. -/
theorem WellDenoted_app_of {ρ : Nat → V} {f a A B : Expr} {pw : PropWhen}
    (hf : WellDenoted M φ ρ f) (ha : WellDenoted M φ ρ a)
    (hpi : WellDenoted M φ ρ (.pi A pw B))
    (hmemf : interp M φ ρ f ∈ˢ interp M φ ρ (.pi A pw B))
    (hmema : interp M φ ρ a ∈ˢ interp M φ ρ A) :
    WellDenoted M φ ρ (.app f a) := by
  rw [WellDenoted_pi] at hpi
  rw [WellDenoted_app]
  exact ⟨hf, ha, pw.holds φ, interp M φ ρ A, fun x => interp M φ (cons x ρ) B,
    hmemf, hmema, hpi.2.2⟩

/-! ## Contexts -/

/-- **Satisfaction of a context**: each entry is well-denoted under the
environment beyond it, and the variable's value is a member of it.
The semantic `Γ ⊢`. -/
def Sat (M : Name → List Nat → V) (φ : Name → Nat) : List Expr → (Nat → V) → Prop
  | [], _ => True
  | A :: Γ, ρ =>
    Sat M φ Γ (fun i => ρ (i + 1)) ∧
    WellDenoted M φ (fun i => ρ (i + 1)) A ∧
    ρ 0 ∈ˢ interp M φ (fun i => ρ (i + 1)) A

@[simp] theorem Sat_nil (ρ : Nat → V) : Sat M φ [] ρ := trivial

/-- Extending the context and the environment together. -/
theorem Sat_cons {Γ : List Expr} {A : Expr} {ρ : Nat → V} {x : V} :
    Sat M φ (A :: Γ) (cons x ρ) ↔
      Sat M φ Γ ρ ∧ WellDenoted M φ ρ A ∧ x ∈ˢ interp M φ ρ A := Iff.rfl

/-- Reading an entry: `Γ[i]` is well-denoted, and `ρ i` a member of
it, under the environment shifted past `i`. -/
theorem Sat_get : ∀ {Γ : List Expr} {ρ : Nat → V} {i : Nat} {A : Expr},
    Sat M φ Γ ρ → Γ[i]? = some A →
    WellDenoted M φ (shiftE (i + 1) 0 ρ) A ∧ ρ i ∈ˢ interp M φ (shiftE (i + 1) 0 ρ) A
  | [], _, _, _, _, h => by simp at h
  | B :: Γ, ρ, 0, A, hs, h => by
    simp at h
    subst h
    rw [shiftE_zero]
    exact ⟨hs.2.1, hs.2.2⟩
  | B :: Γ, ρ, i + 1, A, hs, h => by
    simp at h
    have := Sat_get (ρ := fun j => ρ (j + 1)) hs.1 h
    rw [shiftE_zero] at this ⊢
    exact this

end Fragment
