import Setlec.TTVerify.DeclAxiom
import Setlec.Verify.OfReducePin

/-!
# The `ofReduce*` inhabitation key

`OfReduceKeyTT`: the two compiler-trust axioms

```
Lean.ofReduceNat  : ∀ (a b : Nat),  Eq.{1} Nat  (Lean.reduceNat a) b  → Eq.{1} Nat  a b
Lean.ofReduceBool : ∀ (a b : Bool), Eq.{1} Bool (Lean.reduceBool a) b → Eq.{1} Bool a b
```

are inhabited because **the hypothesis is the conclusion**: the reduce
opaque was certified at its own install to be the identity on its
element type (`ReduceOpsTT`, discharged by `ReducePinTT`), so
`reduce a ≡ a` and the equation the hypothesis carries is already the
equation the conclusion wants.

So the witness is three lambdas and `.prf` — the layer's canonical
inhabitant of any `eqE` — and every step in between is a *conversion*:

| step | instrument |
| --- | --- |
| stored type ⇝ pinned type | `denote_matchesPin` (§14) |
| `Eq E x y` spine ⇝ `eqE E x y` former | `EnvTT.eq_law` (§11) |
| `reduce a ≡ a` | `EnvTT.reduce_ops` |

**This is the reconciliation shape at its purest.**  No layer constant
is used at all — not even `propext`'s `.const .propext`.  The axiom is
inhabited by `prf`, and the whole key is spelling alignment plus one
fact the checker already certified.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! The pinned `ofReduce` shapes and the guard inversions moved to
`Setlec/Verify/OfReducePin.lean` (task #148 T6): both soundness routes
need them and they mention no set theory. -/


/-! ## The denotation of the pinned type

Three binders, each opened with an `fvar` whose denotation is a de
Bruijn index; every constant in sight is closed, so no lifting appears
anywhere.  The computation is written out rather than automated
because the *shape* is what the witness is checked against. -/

/-- The equality former's valuation at the pinned level `1`. -/
def eqV {env : Env} (m : EnvTT env) (ψ : Name → Nat) : VExpr :=
  m.cval eqName (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])

/-- The pinned type, denoted. -/
theorem denote_ofReducePin {env : Env} (m : EnvTT env) {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName)
    {ciE : ConstantInfo} {cvR : ConstantVal}
    (hfE : env.find? (reduceElemName (ofReduceOp n)) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = [])
    (hfR : env.find? (ofReduceOp n) = some (.axiomInfo cvR))
    (hlpR : cvR.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 (ofReducePinA n).type =
      some (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
        (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
          (.pi (VExpr.mkAppN (eqV m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .app (m.cval (ofReduceOp n) ψ) (.bvar 1), .bvar 0])
            (VExpr.mkAppN (eqV m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .bvar 2, .bvar 1])))) := by
  have hE : ∀ d, denote m.cval env ψ d
      (.const (reduceElemName (ofReduceOp n)) [])
      = some (m.cval (reduceElemName (ofReduceOp n)) ψ) :=
    fun d => denote_const_nolevels m ψ hfE hlpE d
  have hR : ∀ d, denote m.cval env ψ d (.const (ofReduceOp n) [])
      = some (m.cval (ofReduceOp n) ψ) :=
    fun d => denote_const_nolevels m ψ hfR hlpR d
  have hQ : ∀ d, denote m.cval env ψ d (.const eqName [.succ .zero])
      = some (eqV m ψ) := by
    intro d
    rw [denote_const, hEq, eqV]
    exact if_pos rfl
  rw [ofReducePin_type hn]
  simp [denote_forallE, hE, Expr.instantiate1, denote_app, denote_fvar,
    Expr.mkAppN, VExpr.mkAppN, hQ, hR]

/-! ## The witness

`λ a b (h : reduce a = b). prf` — and `prf` type-checks because the
three conversions above line the conclusion up with an `eqE` the
hypothesis and the identity certificate already give. -/

/-- **`OfReduceKeyTT`, discharged.** -/
theorem ofReduceKeyTT : OfReduceKeyTT := by
  intro env m cvA hok hn hfresh
  simp only [ofReduceAxOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hEq, helem⟩, hstored⟩, hmpA⟩ := hok
  obtain ⟨ciE, hfE, hlpE, htyE⟩ := reduceElem_sort helem
  obtain ⟨cvR, hfR, hmpR⟩ : ∃ cvR, env.find? (ofReduceOp cvA.name)
      = some (.axiomInfo cvR) ∧
      ConstantVal.matchesPin cvR (reduceOpCvA (ofReduceOp cvA.name))
        = true := by
    rw [reduceStoredOk] at hstored
    cases hf : env.find? (ofReduceOp cvA.name) with
    | none => rw [hf] at hstored; exact nomatch hstored
    | some ci =>
      rw [hf] at hstored
      cases ci with
      | axiomInfo cvR => exact ⟨cvR, rfl, hstored⟩
      | _ => exact nomatch hstored
  obtain ⟨-, hlpR⟩ := matchesPin_invT hmpR
  rw [show (reduceOpCvA (ofReduceOp cvA.name)).levelParams = [] from by
    unfold reduceOpCvA; split <;> rfl] at hlpR
  have hmem : ofReduceOp cvA.name ∈ reduceOpNames := by
    unfold ofReduceOp
    split <;> decide
  -- the element type and the operation, typed
  have hEty : ∀ (Δ : List VExpr) (ψ : Name → Nat),
      HasType Δ (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        (.sort 1) := by
    intro Δ ψ
    refine cval_hasType m hfE ψ ?_
    rw [denoteClosed, htyE, denote_sort]
    rfl
  have hRty : ∀ (Δ : List VExpr) (ψ : Name → Nat),
      HasType Δ (m.cval (ofReduceOp cvA.name) ψ)
        (.pi (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)) := by
    intro Δ ψ
    refine cval_hasType m hfR ψ ?_
    show denoteClosed m.cval env ψ cvR.type = _
    rw [denoteClosed, denote_matchesPin hmpR 0,
      show (reduceOpCvA (ofReduceOp cvA.name)).type
        = .forallE (Name.anonymous.str "n")
          (.const (reduceElemName (ofReduceOp cvA.name)) [])
          (.const (reduceElemName (ofReduceOp cvA.name)) []) ⟨.default⟩
        from reduceOpCv_type hn]
    simp [denote_forallE, denote_const_nolevels m ψ hfE hlpE,
      Expr.instantiate1]
  -- the identity certificate, fired
  obtain ⟨-, hid⟩ := m.reduce_ops _ hmem cvR hfR hmpR
  refine ⟨fun ψ =>
    .lam (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
      (.lam (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        (.lam (VExpr.mkAppN (eqV m ψ)
          [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0])
          .prf)), ?_, ?_, ?_⟩
  · -- closed
    intro ψ
    have h1 := m.cval_closed (reduceElemName (ofReduceOp cvA.name)) ψ
    have h2 := m.cval_closed (ofReduceOp cvA.name) ψ
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
  · -- reads only its own level parameters (there are none, and every
    -- constant in the witness has none either, or is read at a fixed
    -- level)
    intro φ₁ φ₂ _
    dsimp only
    have hE2 : m.cval (reduceElemName (ofReduceOp cvA.name)) φ₁
        = m.cval (reduceElemName (ofReduceOp cvA.name)) φ₂ :=
      m.val_params _ ciE hfE φ₁ φ₂ (by rw [hlpE]; intro p hp; exact nomatch hp)
    have hR2 : m.cval (ofReduceOp cvA.name) φ₁
        = m.cval (ofReduceOp cvA.name) φ₂ :=
      m.val_params _ _ hfR φ₁ φ₂ (by
        rw [show (ConstantInfo.axiomInfo cvR).toConstantVal.levelParams
          = [] from hlpR]
        intro p hp; exact nomatch hp)
    have hQ2 : eqV m φ₁ = eqV m φ₂ := by
      refine m.val_params eqName eqA hEq _ _ ?_
      intro p hp
      simp [Level.substFn, eqA, ConstantInfo.toConstantVal] at hp ⊢
      subst hp
      rfl
    rw [hE2, hR2, hQ2]
  · -- and derivably of the pinned type
    intro ψ
    refine ⟨.pi (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
      (.pi (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        (.pi (VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0])
          (VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .bvar 2, .bvar 1]))), ?_, ?_⟩
    · rw [denoteClosed, denote_matchesPin hmpA 0]
      exact denote_ofReducePin m hn hfE hlpE hfR hlpR hEq ψ
    · refine HasType.lam (HasType.lam (HasType.lam ?_))
      -- the three-binder context, and the two variables it types
      have hEcl := m.cval_closed (reduceElemName (ofReduceOp cvA.name)) ψ
      have ha : HasType
          [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]
          (.bvar 2) (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        have := HasType.bvar (Γ := [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]) (i := 2)
          (A := m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) (by simp)
        rwa [VExpr.liftN_eq_self_of_closed hEcl _ 0] at this
      have hb : HasType
          [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]
          (.bvar 1) (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        have := HasType.bvar (Γ := [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]) (i := 1)
          (A := m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) (by simp)
        rwa [VExpr.liftN_eq_self_of_closed hEcl _ 0] at this
      -- the hypothesis variable, converted to the former
      have hh : HasType
          [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]
          (.bvar 0) (VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 2), .bvar 1]) := by
        have := HasType.bvar (Γ := [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]) (i := 0)
          (A := VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0])
          (by simp)
        simpa [VExpr.mkAppN, VExpr.liftN,
          VExpr.liftN_eq_self_of_closed hEcl,
          VExpr.liftN_eq_self_of_closed (m.cval_closed eqName _),
          VExpr.liftN_eq_self_of_closed
            (m.cval_closed (ofReduceOp cvA.name) ψ), eqV] using this
      have hra : HasType
          [VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
             .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1), .bvar 0],
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           m.cval (reduceElemName (ofReduceOp cvA.name)) ψ]
          (.app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 2))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        have := HasType.app (hRty _ ψ) ha
        rwa [VExpr.inst_eq_self_of_closed hEcl] at this
      -- the two equations, composed
      have hlaw : ∀ (Δ : List VExpr) (x y : VExpr),
          HasType Δ x (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
          HasType Δ y (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
          Deq Δ (VExpr.mkAppN (eqV m ψ)
            [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ, x, y])
            (.eqE (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) x y) :=
        fun Δ x y hx hy => m.eq_law hEq _ Δ _ x y (hEty Δ ψ) hx hy
      have hDhyp := Deq.intro (Deq.conv hh (hlaw _ _ _ hra hb))
      have hDid := hid ψ _ _ ha
      exact Deq.conv (t := VExpr.prf)
        (Deq.toHasType (hDid.symm.trans hDhyp) _)
        (Deq.symm (hlaw _ _ _ ha hb))

/-- **`DeclAxiomTT`, modulo the standard-axiom key alone.** -/
theorem declAxiomTT_ofReduce {F : Nat} (hstd : StdAxiomKeyTT) :
    DeclAxiomTT F :=
  declAxiomTT hstd trustCompilerKeyTT ofReduceKeyTT

end Setlec.TTVerify