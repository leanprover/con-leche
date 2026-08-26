import Setlec.TTVerify.ReducePin

/-!
# The `axiom` case

`checkDecl`'s `.axiomDecl` branch is a five-way guard chain and it is
the *only* case in `CheckDeclTT` with a branch that installs **nothing**:
a tolerated axiom (exactly `sorryAx`, by the user's ruling) is
well-formedness-checked and then skipped, so the environment is
unchanged and the derivation model is the one we started with.  That
branch is proved here in one line, and it is worth noticing that it is
one line: *the skip-and-continue design pays a zero verification tax*,
because the environment the invariant talks about never moves.

The other four branches install `.axiomInfo cvA` and owe a **closed
derivation of the axiom's pinned type** — there is no value to denote,
so unlike `def`/`theorem`/`opaque` the valuation is chosen outright and
the layer must supply the inhabitant.

## The layer already has two of them

`propext` and `Classical.choice` are `BConst`s (`Setlec/TT/Const.lean`),
with `bval` and soundness (`bval_mem_propext`, `bval_mem_choice`), so
`HasType.const` types them for free.  What the bridge owes is not an
inhabitation argument but a **shape reconciliation**: the layer's

```
propext : ∀ (A B : Prop), (A → B) → (B → A) → A = B
```

against the checker's pinned

```
propext : ∀ (a b : Prop), Iff a b → Eq Prop a b
```

— and `Iff` is an ordinary *modeled* inductive, opaque to the bridge.
That is exactly why `stdAxiomOk` pins `Iff`, `Iff.intro` and `Iff.rec`:
the witness is the layer's constant wrapped in an `Iff.rec` elimination,
and the recursor's *typing* (`EnvTT.has_type`) is all that is needed —
its iota rule never fires here.  §8.4 once more, at the last place it
could apply.

The four contents are named below, one per guard, because each guard is
a named checker function and §8.6 puts the boundary there.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-! ## The axiom install

Like `extendValueTT` but with the valuation chosen outright rather than
read off a value — `defn_eq` and `thm_ok` are both vacuous at an
`axiomInfo`, so the install is strictly smaller. -/

/-- Extend a valuation at one name by an explicitly chosen term. -/
def cvalWith (cval : TConstVal) (n : Name) (V : (Name → Nat) → VExpr) :
    TConstVal := fun c ψ => if c = n then V ψ else cval c ψ

theorem cvalWith_ne {cval : TConstVal} {n : Name}
    {V : (Name → Nat) → VExpr} {c : Name} (h : c ≠ n) :
    cvalWith cval n V c = cval c := by
  funext ψ; simp [cvalWith, h]

theorem cvalWith_self {cval : TConstVal} {n : Name}
    {V : (Name → Nat) → VExpr} : cvalWith cval n V n = V := by
  funext ψ; simp [cvalWith]

/-- **The axiom install.** -/
theorem extendAxiomTT {env : Env} (m : EnvTT env) {cv : ConstantVal}
    {V : (Name → Nat) → VExpr}
    (hfresh : env.find? cv.name = none)
    (hwf : EnvWF ⟨ConstantInfo.axiomInfo cv :: env.consts⟩)
    (hVcl : ∀ ψ : Name → Nat, VExpr.Closed (V ψ))
    (hVp : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂)
    (hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cv.type = some t ∧ HasType [] (V ψ) t)
    (hnres : reservedBasisNames.contains cv.name = false)
    (hnred : cv.name ∉ reduceOpNames) :
    Nonempty (EnvTT ⟨ConstantInfo.axiomInfo cv :: env.consts⟩) := by
  have hi : Installs env m.cval (cvalWith m.cval cv.name V)
      (.axiomInfo cv) :=
    Installs.of_fresh hfresh (fun n hn => (cvalWith_ne hn).symm)
  refine ⟨EnvTT.cons m hi hwf ?_ ?_ ?_ (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq) ?_ (fun _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) ?_ (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) ?_⟩
  · intro ψ
    show VExpr.Closed (cvalWith m.cval cv.name V cv.name ψ)
    rw [cvalWith_self]; exact hVcl ψ
  · intro φ₁ φ₂ hp
    show cvalWith m.cval cv.name V cv.name φ₁
      = cvalWith m.cval cv.name V cv.name φ₂
    rw [cvalWith_self]
    exact hVp φ₁ φ₂ hp
  · intro φ
    obtain ⟨t, ht, hd⟩ := hkey φ
    refine ⟨t, hi.denoteUp ht, ?_⟩
    show HasType [] (cvalWith m.cval cv.name V cv.name φ) t
    rw [cvalWith_self]; exact hd
  · intro hE
    have : reservedBasisNames.contains emptyName = false := by
      rw [show emptyName = cv.name from hE.symm]; exact hnres
    exact nomatch this
  · intro T cvT caps hf hcape hres hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [hT, Env.find?_cons, if_pos rfl] at hf; exact nomatch hf
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC; exact nomatch hfC
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hfPj; exact nomatch hfPj
  · intro hE
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hE
    rw [hE] at hnres
    exact nomatch hnres
  · intro hres
    show _ ∧ _
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hres
    rw [hres] at hnres
    exact nomatch hnres
  · intro cv2 heq hmem
    exact absurd hmem hnred

/-! ## The four contents, one per guard -/

/-- The two standard axioms are inhabited: `propext` through the pinned
`Iff` family, `Classical.choice` through the pinned `Nonempty`. -/
def StdAxiomKeyTT : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → env.find? cvA.name = none →
    ∃ V : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (V ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
          HasType [] (V ψ) t

/-- `Lean.trustCompiler : True` is inhabited by the pinned `True`
family's constructor. -/
def TrustCompilerKeyTT : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cvA : ConstantVal},
    trustCompilerOk env cvA = true → cvA.name = trustCompilerName →
    env.find? cvA.name = none →
    ∃ V : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (V ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
          HasType [] (V ψ) t

/-- The `ofReduce*` axioms are inhabited: the identity certificate makes
the hypothesis *be* the conclusion. -/
def OfReduceKeyTT : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cvA : ConstantVal},
    ofReduceAxOk env cvA = true →
    (cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) →
    env.find? cvA.name = none →
    ∃ V : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (V ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
          HasType [] (V ψ) t

/-- `stdAxiomOk` accepts only the two standard axioms' names. -/
theorem stdAxiomOk_name {env : Env} {cvA : ConstantVal}
    (h : stdAxiomOk env cvA = true) :
    cvA.name = propextName ∨ cvA.name = choiceName := by
  by_cases h1 : cvA.name = propextName
  · exact Or.inl h1
  by_cases h2 : cvA.name = choiceName
  · exact Or.inr h2
  rw [stdAxiomOk, if_neg h1, if_neg h2] at h
  exact nomatch h

/-! ## The guard chain

Five branches, of which two throw and one installs nothing.  The
`ConstWF` and freshness facts are shared by the three installing
branches, so they are established once before the split. -/

/-- **`DeclAxiomTT`**, modulo the three inhabitation keys. -/
theorem declAxiomTT (hstd : StdAxiomKeyTT) (htc : TrustCompilerKeyTT)
    (hofr : OfReduceKeyTT) : DeclAxiomTT F := by
  intro env env₁ cv h m
  simp only [checkDecl, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann,
    htp, htr, hst, hsort, rfl⟩ := checkConstantVal_invT hccv
  have htf : type.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F cv.type hann
        (Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
  have hbt' : type.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F cv.type hann hlbt
  have hwfc : EnvWF ⟨ConstantInfo.axiomInfo { cv with type := type } ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  -- the shared install, given a key
  have hgo : ∀ (V : (Name → Nat) → VExpr), (∀ ψ, VExpr.Closed (V ψ)) →
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → V φ₁ = V φ₂) →
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ type = some t ∧ HasType [] (V ψ) t) →
      cv.name ∉ reduceOpNames →
      Nonempty (EnvTT ⟨ConstantInfo.axiomInfo
        { cv with type := type } :: env.consts⟩) := by
    intro V hVcl hVp hkey hnr
    exact extendAxiomTT m (V := V) hfind' hwfc hVcl hVp hkey hres' hnr
  by_cases hstdok : stdAxiomOk env { cv with type := type } = true
  · rw [if_pos hstdok] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨V, hVcl, hVp, hkey⟩ := hstd m hstdok hfind'
    exact hgo V hVcl hVp hkey (by rcases stdAxiomOk_name hstdok with hh | hh <;> rw [hh] <;> decide)
  · rw [if_neg hstdok] at h
    by_cases htcn : cv.name = trustCompilerName
    · rw [if_pos htcn] at h
      by_cases htcok : trustCompilerOk env { cv with type := type } = true
      · rw [if_pos htcok] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨V, hVcl, hVp, hkey⟩ := htc m htcok htcn hfind'
        exact hgo V hVcl hVp hkey (by rw [htcn]; decide)
      · rw [if_neg htcok] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · rw [if_neg htcn] at h
      by_cases hofn : cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName
      · rw [if_pos hofn] at h
        by_cases hofok : ofReduceAxOk env { cv with type := type } = true
        · rw [if_pos hofok] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨V, hVcl, hVp, hkey⟩ := hofr m hofok hofn hfind'
          exact hgo V hVcl hVp hkey
            (by rcases hofn with hh | hh <;> rw [hh] <;> decide)
        · rw [if_neg hofok] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      · rw [if_neg hofn] at h
        by_cases hpc : cv.name = propextName ∨ cv.name = choiceName
        · rw [if_pos hpc] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        · rw [if_neg hpc] at h
          by_cases htol : toleratedAxiomNames.contains cv.name = true
          · -- the skip: nothing is installed, so nothing is owed
            rw [if_pos htol] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact ⟨m⟩
          · rw [if_neg htol] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `Lean.trustCompiler`, discharged

The smallest of the three keys, and the one that shows the shape.  The
pin fixes the axiom's type to `.const True []` *on the nose* — `eraseNames`
is the identity on a constant — so the witness is the stored
`True.intro`'s valuation and the derivation is `cval_hasType` at the
pinned type.  No layer constant is involved at all: the family is
modeled, and being modeled is enough because the *constructor* is
stored with the type the axiom wants. -/

/-- `eraseNames` fixes a bare constant. -/
theorem eraseNames_const_inv {e : Expr} {n : Name} {us : List Level}
    (h : e.eraseNames = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.eraseNames] at h <;> first
    | exact h
    | exact nomatch h

/-- `eraseNames` fixes a sort. -/
theorem eraseNames_sort_inv {e : Expr} {u : Level}
    (h : e.eraseNames = .sort u) : e = .sort u := by
  cases e <;> simp only [Expr.eraseNames] at h <;> first
    | exact h
    | exact nomatch h

/-- **`TrustCompilerKeyTT`, discharged.** -/
theorem trustCompilerKeyTT : TrustCompilerKeyTT := by
  intro env m cvA hok hname hfresh
  simp only [trustCompilerOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hok
  -- the pinned `True` and `True.intro`
  cases hfT : env.find? trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? trueIntroName with
  | none => rw [hfTi] at hTi; exact nomatch hTi
  | some ciTi =>
  rw [hfT] at hT
  rw [hfTi] at hTi
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    cases ciT with
    | indInfo cvT caps =>
      simp only [ConstantVal.matchesPin, Bool.and_eq_true,
        decide_eq_true_eq] at hT
      exact hT.1.2
    | _ => exact nomatch hT
  obtain ⟨hlpTi, htyTi⟩ : ciTi.toConstantVal.levelParams = [] ∧
      ciTi.toConstantVal.type = .const trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, eraseNames_const_inv hTi.2⟩
    | _ => exact nomatch hTi
  -- the axiom's own type is the pin, on the nose
  have htyA : cvA.type = .const trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact eraseNames_const_inv hA.2
  refine ⟨fun ψ => m.cval trueIntroName ψ, fun ψ => m.cval_closed _ _,
    ?_, fun ψ => ?_⟩
  · intro φ₁ φ₂ _
    exact m.val_params trueIntroName ciTi hfTi φ₁ φ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · refine ⟨m.cval trueName ψ, ?_, ?_⟩
    · rw [htyA]
      exact denote_const_nolevels m ψ hfT hlpT 0
    · refine cval_hasType m hfTi ψ ?_
      rw [htyTi]
      exact denote_const_nolevels m ψ hfT hlpT 0

end Setlec.TTVerify
