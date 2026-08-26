import Setlec.TTVerify.SubstConst

/-!
# The standard-axiom inhabitation key

`StdAxiomKeyTT`, and the genuine test of §8.4's prediction: the first
two keys (`TrustCompilerKeyTT`, `OfReduceKeyTT`) confirmed the
*reconciliation* shape without exercising an elimination, because their
pins fixed the type on the nose and their certificates already proved
the equation.  `propext` and `Classical.choice` are the ones that
cannot avoid it.

## The prediction under test

> the witness is the layer's constant under an `Iff.rec` elimination,
> needing only the recursor's **typing**, never its iota rule.

Both halves are load-bearing.  If the *iota* rule were needed, the key
would depend on `EnvTT.rec_rules` at a modeled family — which is
established by the still-open `DeclIndTT` — and the axiom case could
not be closed before the inductive case.  Needing only `has_type` at
the stored recursor breaks that dependency.

## Why an elimination is unavoidable

The checker's `propext` is `∀ a b : Prop, Iff a b → Eq Prop a b`; the
layer's is `∀ A B : Prop, (A → B) → (B → A) → A = B`.  The conclusion
reconciles by `eq_law` and `prf`, as in `OfReduceKeyTT` — but the
*hypothesis* does not: `Iff a b` is an ordinary modeled inductive,
opaque to the bridge, and the two implications the layer's constant
demands exist only inside it.  Nothing in the layer turns an inhabitant
of an opaque family into its fields except that family's own recursor.

So this key is a reconciliation *plus* one elimination, and the
elimination is the reason `stdAxiomOk` pins `Iff`, `Iff.intro` and
`Iff.rec` rather than `Iff` alone.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The key splits by name

`stdAxiomOk` accepts exactly two names and does entirely different
things at them, so the key splits the same way — §8.6's permitted
*input-space* restriction.  Both halves are eliminations, but of
different families (`Iff`, `Nonempty`) at different motives, and they
share nothing but the shape. -/

/-- The `propext` half. -/
def PropextKeyTT : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = propextName →
    env.find? cvA.name = none →
    ∃ V : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (V ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
          HasType [] (V ψ) t

/-- The `Classical.choice` half. -/
def ChoiceKeyTT : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = choiceName →
    env.find? cvA.name = none →
    ∃ V : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (V ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
          HasType [] (V ψ) t

/-- **`StdAxiomKeyTT`, from the two halves.** -/
theorem stdAxiomKeyTT_of (hp : PropextKeyTT) (hc : ChoiceKeyTT) :
    StdAxiomKeyTT := by
  intro env m cvA hok hfresh
  rcases stdAxiomOk_name hok with hn | hn
  · exact hp m hok hn hfresh
  · exact hc m hok hn hfresh

/-! ## The pinned `Iff` family, extracted -/

/-- The three `Iff` constants `stdAxiomOk` pins, with the level-
parameter and type facts the denotation needs. -/
theorem iff_shapes {env : Env} {cvA : ConstantVal}
    (h : stdAxiomOk env cvA = true) (hp : cvA.name = propextName) :
    env.find? eqName = some eqA ∧
    (∃ cvI caps, env.find? iffName = some (.indInfo cvI caps) ∧
      cvI.levelParams = [] ∧
      cvI.type.eraseNames = iffA.toConstantVal.type.eraseNames) ∧
    (∃ cvIi, env.find? iffIntroName = some (.ctorInfo cvIi 2 2) ∧
      cvIi.levelParams = [] ∧
      cvIi.type.eraseNames = iffIntroA.toConstantVal.type.eraseNames) ∧
    (∃ cvIr mI rP rules,
      env.find? iffRecName = some (.recInfo cvIr mI rP rules) ∧
      cvIr.levelParams = iffRecA.toConstantVal.levelParams ∧
      cvIr.type.eraseNames = iffRecA.toConstantVal.type.eraseNames) ∧
    ConstantVal.matchesPin cvA propextA = true := by
  rw [stdAxiomOk, if_pos hp] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hEq, hI⟩, hIi⟩, hIr⟩, hA⟩ := h
  refine ⟨hEq, ?_, ?_, ?_, hA⟩
  · cases hf : env.find? iffName with
    | none => rw [hf] at hI; exact nomatch hI
    | some ci =>
      rw [hf] at hI
      cases ci with
      | indInfo cvI caps =>
        refine ⟨cvI, caps, rfl, ?_, ?_⟩
        · exact (matchesPin_invT hI).2
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hI
          exact hI.2
      | _ => exact nomatch hI
  · cases hf : env.find? iffIntroName with
    | none => rw [hf] at hIi; exact nomatch hIi
    | some ci =>
      rw [hf] at hIi
      cases ci with
      | ctorInfo cvIi nP nF =>
        match nP, nF, hIi with
        | 2, 2, hIi =>
          refine ⟨cvIi, rfl, (matchesPin_invT hIi).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hIi
          exact hIi.2
      | _ => exact nomatch hIi
  · cases hf : env.find? iffRecName with
    | none => rw [hf] at hIr; exact nomatch hIr
    | some ci =>
      rw [hf] at hIr
      cases ci with
      | recInfo cvIr mI rP rules =>
        match mI, rP, hIr with
        | 4, 4, hIr =>
          refine ⟨cvIr, 4, 4, rules, rfl, (matchesPin_invT hIr).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hIr
          exact hIr.2
      | _ => exact nomatch hIr

/-! ## The two pinned types, denoted

Both computations are the `denote_ofReducePin` pattern at more binders:
every constant in sight is closed, every binder is opened with an
`fvar` whose denotation is its de Bruijn index, so the resulting `VExpr`
mirrors the `Expr`'s bvar structure exactly. -/

/-- `propext`'s pinned type, denoted. -/
theorem denote_propext_type {env : Env} (m : EnvTT env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 propextA.type =
      some (.pi (.sort 0) (.pi (.sort 0)
        (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
          (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 2, .bvar 1])))) := by
  have hI : ∀ d, denote m.cval env ψ d (.const iffName [])
      = some (m.cval iffName ψ) :=
    fun d => denote_const_nolevels m ψ hfI hlpI d
  have hQ : ∀ d, denote m.cval env ψ d (.const eqName [.succ .zero])
      = some (eqV m ψ) := by
    intro d
    rw [denote_const, hEq, eqV]
    exact if_pos rfl
  simp only [iffName, eqName] at hI hQ
  simp [propextA, denote_forallE, denote_sort, Expr.instantiate1,
    denote_app, denote_fvar, VExpr.mkAppN, hI, hQ, Level.eval, eqV,
    iffName, eqName]

/-- `Iff.rec`'s pinned type, denoted. -/
theorem denote_iffRec_type {env : Env} (m : EnvTT env)
    {cvI cvIi : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = []) (ψ : Name → Nat) :
    denote m.cval env ψ 0 iffRecA.toConstantVal.type =
      some (.pi (.sort 0) (.pi (.sort 0)
        (.pi (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
            (.sort (ψ uNT)))
          (.pi (.pi (.pi (.bvar 2) (.bvar 2))
              (.pi (.pi (.bvar 2) (.bvar 4))
                (.app (.bvar 2) (VExpr.mkAppN (m.cval iffIntroName ψ)
                  [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
            (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 3, .bvar 2])
              (.app (.bvar 2) (.bvar 0))))))) := by
  have hI : ∀ d, denote m.cval env ψ d (.const iffName [])
      = some (m.cval iffName ψ) :=
    fun d => denote_const_nolevels m ψ hfI hlpI d
  have hIi : ∀ d, denote m.cval env ψ d (.const iffIntroName [])
      = some (m.cval iffIntroName ψ) :=
    fun d => denote_const_nolevels m ψ hfIi hlpIi d
  simp only [iffName, iffIntroName] at hI hIi
  simp [iffRecA, ConstantInfo.toConstantVal, denote_forallE, denote_sort,
    Expr.instantiate1, denote_app, denote_fvar, VExpr.mkAppN, hI, hIi,
    uNT, Level.eval, iffName, iffIntroName]

end Setlec.TTVerify
