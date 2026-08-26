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

-- The elimination's `inst`/`liftN` normalisations need slightly
-- different lemma sets at each of the fifteen application steps, and
-- the difference is not stable under editing; the same escape the
-- set-model install files use.
set_option linter.unusedSimpArgs false

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

/-- `Iff.intro`'s pinned type, denoted. -/
theorem denote_iffIntro_type {env : Env} (m : EnvTT env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = []) (ψ : Name → Nat) :
    denote m.cval env ψ 0 iffIntroA.toConstantVal.type =
      some (.pi (.sort 0) (.pi (.sort 0)
        (.pi (.pi (.bvar 1) (.bvar 1))
          (.pi (.pi (.bvar 1) (.bvar 3))
            (VExpr.mkAppN (m.cval iffName ψ) [.bvar 3, .bvar 2]))))) := by
  have hI : ∀ d, denote m.cval env ψ d (.const iffName [])
      = some (m.cval iffName ψ) :=
    fun d => denote_const_nolevels m ψ hfI hlpI d
  simp only [iffName] at hI
  simp [iffIntroA, ConstantInfo.toConstantVal, denote_forallE, denote_sort,
    Expr.instantiate1, denote_app, denote_fvar, VExpr.mkAppN, hI,
    Level.eval, iffName]

/-- `Eq`'s pinned type, denoted at the level assignment the axiom reads
it at.  Needed because the motive of the elimination is `Eq Prop a b`
*as a term*, and the layer will not type a spine from an equation about
it — `conv` moves types, not subjects. -/
theorem denote_eq_type {env : Env} (m : EnvTT env)
    (_hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 eqA.toConstantVal.type =
      some (.pi (.sort (ψ uNT))
        (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := by
  simp [eqA, ConstantInfo.toConstantVal, denote_forallE, denote_sort,
    Expr.instantiate1, denote_fvar, uNT, Level.eval]

/-- `Eq A a b` is a `Prop`, as a term. -/
theorem hasType_eqSpine {env : Env} (m : EnvTT env)
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Δ : List VExpr} {A a b : VExpr}
    (hA : HasType Δ A (.sort ((Level.substFn ψ
      eqA.toConstantVal.levelParams [.succ .zero]) uNT)))
    (ha : HasType Δ a A) (hb : HasType Δ b A) :
    HasType Δ (VExpr.mkAppN (eqV m ψ) [A, a, b]) (.sort 0) := by
  have hEt := cval_hasType m hEq
    (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
    (t := .pi (.sort ((Level.substFn ψ eqA.toConstantVal.levelParams
        [.succ .zero]) uNT))
      (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) (Δ := Δ)
    (by rw [denoteClosed]
        exact denote_eq_type m hEq _)
  have h1 := HasType.app hEt hA
  simp [VExpr.inst, VExpr.liftN_zero] at h1
  have h2 := HasType.app h1 ha
  simp only [VExpr.inst] at h2
  rw [show ((VExpr.liftN 1 A).inst a 0) = A from by
    rw [VExpr.inst_liftN_absorb A (Nat.le_refl 0) (Nat.le_refl 0) a,
      VExpr.liftN_zero]] at h2
  have h3 := HasType.app h2 hb
  simpa [VExpr.mkAppN, VExpr.inst, eqV] using h3

/-- One lift absorbed by one instantiation. -/
theorem inst_lift1 (e a : VExpr) : (VExpr.liftN 1 e).inst a 0 = e := by
  rw [VExpr.inst_liftN_absorb e (Nat.le_refl 0) (Nat.le_refl 0) a,
    VExpr.liftN_zero]

/-- Three lifts absorbed by two instantiations. -/
theorem inst_lift3 (e a b : VExpr) :
    ((VExpr.liftN 3 e).inst a 2).inst b 1 = VExpr.liftN 1 e := by
  rw [VExpr.inst_liftN_absorb e (show (0:Nat) ≤ 2 by omega)
      (show (2:Nat) ≤ 0 + 2 by omega) a,
    VExpr.inst_liftN_absorb e (show (0:Nat) ≤ 1 by omega)
      (show (1:Nat) ≤ 0 + 1 by omega) b]

/-- Two lifts absorbed by one instantiation. -/
theorem inst_lift2 (e a : VExpr) :
    (VExpr.liftN 2 e).inst a 1 = VExpr.liftN 1 e :=
  VExpr.inst_liftN_absorb e (show (0:Nat) ≤ 1 by omega)
    (show (1:Nat) ≤ 0 + 1 by omega) a

/-- `Iff.intro a b mp mpr : Iff a b`, as a term. -/
theorem hasType_iffIntro {env : Env} (m : EnvTT env)
    {cvI cvIi : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (_hlpIi : cvIi.levelParams = [])
    (htyIi : cvIi.type.eraseNames = iffIntroA.toConstantVal.type.eraseNames)
    (ψ : Name → Nat) {Δ : List VExpr} {a b mp mpr : VExpr}
    (ha : HasType Δ a (.sort 0)) (hb : HasType Δ b (.sort 0))
    (hmp : HasType Δ mp (arrow a b)) (hmpr : HasType Δ mpr (arrow b a)) :
    HasType Δ (VExpr.mkAppN (m.cval iffIntroName ψ) [a, b, mp, mpr])
      (VExpr.mkAppN (m.cval iffName ψ) [a, b]) := by
  have hIt := cval_hasType m hfIi ψ (Δ := Δ)
    (t := .pi (.sort 0) (.pi (.sort 0)
      (.pi (.pi (.bvar 1) (.bvar 1))
        (.pi (.pi (.bvar 1) (.bvar 3))
          (VExpr.mkAppN (m.cval iffName ψ) [.bvar 3, .bvar 2])))))
    (by show denoteClosed m.cval env ψ cvIi.type = _
        rw [denoteClosed,
          denote_erasedEq (erasedEq_of_eraseNames htyIi) 0]
        exact denote_iffIntro_type m hfI hlpI ψ)
  have h1 := HasType.app hIt ha
  simp [VExpr.inst,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.mkAppN] at h1
  have h2 := HasType.app h1 hb
  simp [VExpr.inst,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ)] at h2
  have h3 := HasType.app h2 (by simpa [arrow, inst_lift1] using hmp)
  simp [VExpr.inst,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ)] at h3
  have h4 := HasType.app h3 (by
    simpa [arrow, inst_lift1, inst_lift3] using hmpr)
  simpa [VExpr.inst, VExpr.liftN_zero, inst_lift1, inst_lift2, inst_lift3,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.liftN_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.mkAppN] using h4

/-- The layer's `propext`, applied. -/
theorem hasType_propextApp {Δ : List VExpr} {a b mp mpr : VExpr}
    (ha : HasType Δ a (.sort 0)) (hb : HasType Δ b (.sort 0))
    (hmp : HasType Δ mp (arrow a b)) (hmpr : HasType Δ mpr (arrow b a)) :
    HasType Δ (VExpr.mkAppN (.const .propext []) [a, b, mp, mpr])
      (.eqE (.sort 0) a b) := by
  have h0 : HasType Δ (VExpr.const .propext []) (BConst.type .propext []) :=
    HasType.const
  simp only [BConst.type] at h0
  have h1 := HasType.app h0 ha
  simp [VExpr.inst] at h1
  have h2 := HasType.app h1 hb
  simp [VExpr.inst] at h2
  have h3 := HasType.app h2 (by simpa [arrow, inst_lift1] using hmp)
  simp [VExpr.inst] at h3
  have h4 := HasType.app h3 (by
    simpa [arrow, inst_lift1, inst_lift3] using hmpr)
  simpa [VExpr.inst, VExpr.liftN_zero, inst_lift1, inst_lift2, inst_lift3,
    VExpr.mkAppN] using h4

/-! ## The elimination

The five applications of `Iff.rec`, in the three-binder context
`[Iff a b, Prop, Prop]`.  Each `HasType.app` produces `B.inst arg`, and
each of those has to be normalised — `inst` does *not* reduce through
the opaque valuations `⟦Iff⟧`, `⟦Iff.intro⟧`, `⟦Eq⟧` by computation, so
their closedness is what makes them inert.  That is the whole of the
bookkeeping. -/

section Propext
variable {env : Env} (m : EnvTT env)

/-- The level assignment the recursor is read at: its one parameter
sent to `0`, because the motive lands in `Prop`. -/
def atZero (ψ : Name → Nat) : Name → Nat :=
  fun q => if q = uNT then 0 else ψ q

theorem atZero_uNT (ψ : Name → Nat) : atZero ψ uNT = 0 := by
  simp [atZero]

end Propext

/-- **The elimination, typed.**  `Iff.rec` applied to the two
propositions, the constant motive `Eq Prop a b`, the minor `propext a b
mp mpr`, and the hypothesis — in the three-binder context.  Only the
recursor's *typing* is used; `EnvTT.rec_rules` never appears. -/
theorem propext_body {env : Env} (m : EnvTT env)
    {cvI cvIi cvIr : ConstantVal} {caps : IndCaps} {mI rP : Nat}
    {rules : List RecRule}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = [])
    (hfIr : env.find? iffRecName = some (.recInfo cvIr mI rP rules))
    (_hlpIr : cvIr.levelParams = iffRecA.toConstantVal.levelParams)
    (htyIr : cvIr.type.eraseNames = iffRecA.toConstantVal.type.eraseNames)
    (htyIi : cvIi.type.eraseNames = iffIntroA.toConstantVal.type.eraseNames)
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]
      (VExpr.mkAppN (m.cval iffRecName (atZero ψ))
        [.bvar 2, .bvar 1,
         .lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1])
           (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 3, .bvar 2]),
         .lam (.pi (.bvar 2) (.bvar 2))
           (.lam (.pi (.bvar 2) (.bvar 4))
             (VExpr.mkAppN (.const .propext [])
               [.bvar 4, .bvar 3, .bvar 1, .bvar 0])),
         .bvar 0])
      (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 2, .bvar 1]) := by
  have hIsame : m.cval iffName (atZero ψ) = m.cval iffName ψ :=
    m.val_params _ _ hfI _ _ (by
      show ∀ p ∈ cvI.levelParams, _
      rw [hlpI]; intro p hp; exact nomatch hp)
  have hIisame : m.cval iffIntroName (atZero ψ) = m.cval iffIntroName ψ :=
    m.val_params _ _ hfIi _ _ (by
      show ∀ p ∈ cvIi.levelParams, _
      rw [hlpIi]; intro p hp; exact nomatch hp)
  have hrec : denoteClosed m.cval env (atZero ψ) cvIr.type = some
      (.pi (.sort 0) (.pi (.sort 0)
        (.pi (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
            (.sort 0))
          (.pi (.pi (.pi (.bvar 2) (.bvar 2))
              (.pi (.pi (.bvar 2) (.bvar 4))
                (.app (.bvar 2) (VExpr.mkAppN (m.cval iffIntroName ψ)
                  [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
            (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 3, .bvar 2])
              (.app (.bvar 2) (.bvar 0))))))) := by
    rw [denoteClosed, denote_erasedEq (erasedEq_of_eraseNames htyIr) 0,
      denote_iffRec_type m hfI hlpI hfIi hlpIi (atZero ψ),
      hIsame, hIisame, atZero_uNT]
  have hRec := cval_hasType m hfIr (atZero ψ) hrec
    (Δ := [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
           VExpr.sort 0, VExpr.sort 0])
  have ha : HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
      VExpr.sort 0, VExpr.sort 0] (.bvar 2) (.sort 0) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (m.cval iffName ψ)
      [.bvar 1, .bvar 0], VExpr.sort 0, VExpr.sort 0]) (i := 2)
      (A := VExpr.sort 0) (by simp)
    simpa using this
  have hb : HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
      VExpr.sort 0, VExpr.sort 0] (.bvar 1) (.sort 0) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (m.cval iffName ψ)
      [.bvar 1, .bvar 0], VExpr.sort 0, VExpr.sort 0]) (i := 1)
      (A := VExpr.sort 0) (by simp)
    simpa using this
  have h1 := HasType.app hRec ha
  simp [VExpr.inst, VExpr.inst_eq_self_of_closed
    (m.cval_closed iffName ψ), VExpr.inst_eq_self_of_closed
    (m.cval_closed iffIntroName ψ), VExpr.mkAppN] at h1
  have h2 := HasType.app h1 hb
  simp [VExpr.inst, VExpr.inst_eq_self_of_closed
    (m.cval_closed iffName ψ), VExpr.inst_eq_self_of_closed
    (m.cval_closed iffIntroName ψ)] at h2
  have hmot : HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]
      (.lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1])
        (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 3, .bvar 2]))
      (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1])
        (.sort 0)) := by
    refine HasType.lam ?_
    refine hasType_eqSpine m hEq ψ ?_ ?_ ?_
    · exact HasType.sort
    · have := HasType.bvar (Γ := VExpr.mkAppN (m.cval iffName ψ)
        [.bvar 2, .bvar 1] :: [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]) (i := 3)
        (A := VExpr.sort 0) (by simp)
      simpa using this
    · have := HasType.bvar (Γ := VExpr.mkAppN (m.cval iffName ψ)
        [.bvar 2, .bvar 1] :: [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]) (i := 2)
        (A := VExpr.sort 0) (by simp)
      simpa using this
  have h3 := HasType.app h2 hmot
  simp [VExpr.inst, VExpr.inst_eq_self_of_closed
    (m.cval_closed iffName ψ), VExpr.inst_eq_self_of_closed
    (m.cval_closed iffIntroName ψ),
    VExpr.inst_eq_self_of_closed (m.cval_closed eqName _),
    VExpr.liftN_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.liftN_eq_self_of_closed (m.cval_closed eqName _),
    VExpr.mkAppN, eqV] at h3
  -- the minor premise: the layer's `propext`, under two λs
  have hbv : ∀ (Γ : List VExpr) (i : Nat), Γ[i]? = some (VExpr.sort 0) →
      HasType Γ (.bvar i) (.sort 0) := by
    intro Γ i hi
    simpa using HasType.bvar (Γ := Γ) (i := i) (A := VExpr.sort 0) hi
  have hmin : HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]
      (.lam (.pi (.bvar 2) (.bvar 2))
        (.lam (.pi (.bvar 2) (.bvar 4))
          (VExpr.mkAppN (.const .propext [])
            [.bvar 4, .bvar 3, .bvar 1, .bvar 0])))
      (.pi (.pi (.bvar 2) (.bvar 2))
        (.pi (.pi (.bvar 2) (.bvar 4))
          (.app (.lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 4, .bvar 3])
              (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 5, .bvar 4]))
            (VExpr.mkAppN (m.cval iffIntroName ψ)
              [.bvar 4, .bvar 3, .bvar 1, .bvar 0])))) := by
    refine HasType.lam (HasType.lam ?_)
    have ha5 : HasType [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.bvar 4) (.sort 0) :=
      hbv _ 4 (by simp)
    have hb5 : HasType [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.bvar 3) (.sort 0) :=
      hbv _ 3 (by simp)
    have hmp5 : HasType [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.bvar 1)
        (arrow (.bvar 4) (.bvar 3)) := by
      have := HasType.bvar (Γ := [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]) (i := 1)
        (A := VExpr.pi (.bvar 2) (.bvar 2)) (by simp)
      simpa [arrow, VExpr.liftN] using this
    have hmpr5 : HasType [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.bvar 0)
        (arrow (.bvar 3) (.bvar 4)) := by
      have := HasType.bvar (Γ := [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]) (i := 0)
        (A := VExpr.pi (.bvar 2) (.bvar 4)) (by simp)
      simpa [arrow, VExpr.liftN] using this
    have hprop := hasType_propextApp ha5 hb5 hmp5 hmpr5
    have hlaw := m.eq_law hEq
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
      [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.sort 0) (.bvar 4) (.bvar 3)
      (by rw [show (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.succ Level.zero]) uNT = 1 from rfl]
          simpa using HasType.sort
            (Γ := [VExpr.pi (.bvar 2) (.bvar 4),
                   VExpr.pi (.bvar 2) (.bvar 2),
                   VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
                   VExpr.sort 0, VExpr.sort 0]) (u := 0))
      ha5 hb5
    have hQ := Deq.conv hprop (Deq.symm hlaw)
    have hIi5 := hasType_iffIntro m hfI hlpI hfIi hlpIi htyIi ψ
      ha5 hb5 hmp5 hmpr5
    have hbeta : Deq [VExpr.pi (.bvar 2) (.bvar 4), VExpr.pi (.bvar 2) (.bvar 2),
       VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]
        (.app (.lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 4, .bvar 3])
            (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 5, .bvar 4]))
          (VExpr.mkAppN (m.cval iffIntroName ψ)
            [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))
          (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 4, .bvar 3]) := by
      refine ⟨VExpr.sort 0, ?_⟩
      have hb0 := HasType.beta (T := VExpr.sort 0)
        (b := VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 5, .bvar 4]) hIi5
      simpa [VExpr.inst,
        VExpr.inst_eq_self_of_closed (m.cval_closed eqName _),
        VExpr.mkAppN, eqV] using hb0
    exact Deq.conv hQ (Deq.symm hbeta)
  have h4 := HasType.app h3 hmin
  simp [VExpr.inst, VExpr.liftN_zero, inst_lift1, inst_lift2, inst_lift3,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.inst_eq_self_of_closed (m.cval_closed iffIntroName ψ),
    VExpr.inst_eq_self_of_closed (m.cval_closed eqName _),
    VExpr.liftN_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.liftN_eq_self_of_closed (m.cval_closed iffIntroName ψ),
    VExpr.liftN_eq_self_of_closed (m.cval_closed eqName _),
    VExpr.mkAppN, eqV] at h4
  have ht : HasType [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0] (.bvar 0)
      (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1]) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]) (i := 0)
      (A := VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0]) (by simp)
    simpa [VExpr.mkAppN, VExpr.liftN,
      VExpr.liftN_eq_self_of_closed (m.cval_closed iffName ψ)] using this
  have h5 := HasType.app h4 ht
  simp [VExpr.inst, VExpr.liftN_zero, inst_lift1, inst_lift2, inst_lift3,
    VExpr.inst_eq_self_of_closed (m.cval_closed iffName ψ),
    VExpr.inst_eq_self_of_closed (m.cval_closed eqName _),
    VExpr.mkAppN] at h5
  have hbeta2 : Deq [VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0],
       VExpr.sort 0, VExpr.sort 0]
      (.app (.lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1])
          (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 3, .bvar 2])) (.bvar 0))
        (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 2, .bvar 1]) := by
    refine ⟨VExpr.sort 0, ?_⟩
    have hb0 := HasType.beta (T := VExpr.sort 0)
      (b := VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 3, .bvar 2]) ht
    simpa [VExpr.inst,
      VExpr.inst_eq_self_of_closed (m.cval_closed eqName _),
      VExpr.mkAppN, eqV] using hb0
  simpa [VExpr.mkAppN, eqV] using Deq.conv h5 hbeta2

/-- **`PropextKeyTT`, discharged.**  Three λs and the elimination. -/
theorem propextKeyTT : PropextKeyTT := by
  intro env m cvA hok hp hfresh
  obtain ⟨hEq, ⟨cvI, caps, hfI, hlpI, htyI⟩, ⟨cvIi, hfIi, hlpIi, htyIi⟩,
    ⟨cvIr, mI, rP, rules, hfIr, hlpIr, htyIr⟩, hmpA⟩ := iff_shapes hok hp
  have hlpA : cvA.levelParams = [] := (matchesPin_invT hmpA).2
  refine ⟨fun ψ => .lam (.sort 0) (.lam (.sort 0)
    (.lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
      (VExpr.mkAppN (m.cval iffRecName (atZero ψ))
        [.bvar 2, .bvar 1,
         .lam (VExpr.mkAppN (m.cval iffName ψ) [.bvar 2, .bvar 1])
           (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 3, .bvar 2]),
         .lam (.pi (.bvar 2) (.bvar 2))
           (.lam (.pi (.bvar 2) (.bvar 4))
             (VExpr.mkAppN (.const .propext [])
               [.bvar 4, .bvar 3, .bvar 1, .bvar 0])),
         .bvar 0]))), ?_, ?_, ?_⟩
  · intro ψ
    have h1 := m.cval_closed iffName ψ
    have h2 := m.cval_closed iffRecName (atZero ψ)
    have h3 := m.cval_closed eqName
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
    simp only [VExpr.Closed, VExpr.bvarsBelow, eqV, VExpr.mkAppN] at *
    repeat' apply And.intro
    all_goals first
      | exact VExpr.bvarsBelow.mono (by omega) h1
      | exact VExpr.bvarsBelow.mono (by omega) h2
      | exact VExpr.bvarsBelow.mono (by omega) h3
      | omega
      | trivial
  · intro φ₁ φ₂ _
    dsimp only
    have hI2 : m.cval iffName φ₁ = m.cval iffName φ₂ :=
      m.val_params _ _ hfI _ _ (by
        show ∀ p ∈ cvI.levelParams, _
        rw [hlpI]; intro p hp; exact nomatch hp)
    have hR2 : m.cval iffRecName (atZero φ₁)
        = m.cval iffRecName (atZero φ₂) :=
      m.val_params _ _ hfIr _ _ (by
        show ∀ p ∈ cvIr.levelParams, _
        rw [hlpIr]
        intro p hp
        obtain rfl : p = uNT := by
          simpa [iffRecA, ConstantInfo.toConstantVal, uNT] using hp
        rw [atZero_uNT, atZero_uNT])
    have hQ2 : eqV m φ₁ = eqV m φ₂ := by
      refine m.val_params eqName eqA hEq _ _ ?_
      intro p hp
      simp [Level.substFn, eqA, ConstantInfo.toConstantVal] at hp ⊢
      subst hp
      rfl
    rw [hI2, hR2, hQ2]
  · intro ψ
    refine ⟨.pi (.sort 0) (.pi (.sort 0)
      (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
        (VExpr.mkAppN (eqV m ψ) [.sort 0, .bvar 2, .bvar 1]))), ?_, ?_⟩
    · rw [denoteClosed, denote_matchesPin hmpA 0]
      exact denote_propext_type m hfI hlpI hEq ψ
    · exact HasType.lam (HasType.lam (HasType.lam
        (propext_body m hfI hlpI hfIi hlpIi hfIr hlpIr htyIr htyIi hEq ψ)))

end Setlec.TTVerify
