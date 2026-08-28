import Setlec.SetR.Bridge.Main
import Setlec.SetR.Install.Step
import Setlec.Verify.IotaWalkInv

/-!
# The declaration-level bridge (task #148, T6)

`Setlec/SetR/Bridge/*` bridges the checker's *inference* steps into the
`[set]` relation family; this file bridges its **declarations**.  Each
of `checkDecl`'s six branches is inverted into the corresponding
`Decl*R` clause of `Setlec/SetR/Decl.lean`, and `checkDeclR_of`
assembles them.  Composed with `declStepS` (`Install/Step.lean`) that
gives the `EnvS`-extension step the consistency fold runs.

Nothing semantic happens here: every lemma is V-free inversion of the
checker's own control flow.  The valuation enters only where a clause
mentions `cval`, and there it is carried, never chosen.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

/-! ## `EnvS` is an `EnvR`

The bridge runs against `EnvR` — the weakest V-free invariant its
steps need — and the install layer produces `EnvS`.  The assembly
needs the projection, and building it is what exposed **finding 7**
(recorded in `DESIGN.md`): as landed, two of `EnvR`'s fields were
stated more strongly than `EnvS.rec_rules` can supply.

`EnvS.rec_rules` is `RecRulesV`, which speaks only of rules whose
`fire ≠ .inert` and only at level arguments of the declared length;
`EnvR.rec_rhs_denotes`/`rec_params_le` quantified over *all* rules and
*all* level lists.  The gap is not cosmetic: `Empty.rec` stores **no
rules at all**, so no install could ever supply an unguarded
`rP ≤ mI`, and adding an unguarded `EnvS` field would have been owed
by every install for a fact the bridge never uses.  Both fields are
consumed at exactly one place — the iota fire site in
`Bridge/Iota.lean` — where the fired rule, its non-inertness (`hfire`)
and the level-length check (`hlenU`) are all already in scope.  The
repair is therefore to narrow the fields to their consumption, which
is what `Bridge/Env.lean` now states. -/

/-- **The bridge invariant, from the install invariant.** -/
def EnvS.toEnvR {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) : EnvR env where
  cval := m.cval
  cval_closed := m.cval_closed
  wf := m.wf
  val_params := m.val_params
  ty_denotes := fun c hc ψ => by
    obtain ⟨t, ht, -⟩ := m.mem_type c hc ψ
    exact ⟨t, ht⟩
  defn_eq := m.defn_eq
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hR⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨R, hR0, -⟩ := hR us hlen
    exact ⟨R, hR0⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.proj_ok
  thm_ok := m.thm_ok

/-! ## The shared front doors

`ConstantValR` and `ValueFrontR` are the two relations four of the six
branches are built from, and neither had a producer.  Both are the
same script: `checkConstantVal_inv` (or the branch's own `annotate`
inversion) for the syntactic conjuncts, then `checkBridge` at
`EnvS.toEnvR` for the `Infer`/`DefEq` ones, at an **arbitrary** `φ` —
which is what both relations quantify over. -/

/-- The frame conditions of a closed, `fvar`-free expression at depth
`0` — the shape every declaration-level claim is applied at ([set]
transpose of the TT lane's `closed0_frames`). -/
theorem closed0_framesR {μ : CheckMode} {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {e : Expr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    Expr.WScoped 0 e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e ∧ CtxOkR μ cval env φ 0 [] e :=
  ⟨Expr.WScoped.of_not_hasFvar hnf, hb,
    Expr.LeavesBounded.of_not_hasFvar hnf,
    CtxOkR.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf)⟩

/-- **`checkConstantVal`, bridged.**  Beside `ConstantValR` the caller
gets the annotated type's two closedness facts, which every branch
then needs for its own value front door and for `EnvWF`. -/
theorem constantValR_of {env : Env} (m : EnvR env) {μ : CheckMode} {F :
  Nat} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    ∃ type', cv' = { cv with type := type' } ∧
      type'.hasFvar = false ∧ type'.looseBVarsBounded 0 = true ∧
      ConstantValR μ F env m.cval cv type' := by
  obtain ⟨hfind, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := checkConstantVal_inv h
  have htf : type.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F cv.type hann
        (Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
  have hbt' : type.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F cv.type hann hlbt
  refine ⟨type, rfl, htf, hbt',
    Option.isNone_iff_eq_none.mpr hfind, hres, hpsh, hnd, hlbt, hitf,
    hann, htp, htr, fun φ => ?_⟩
  obtain ⟨-, ihw, -, ihi⟩ := checkBridge m φ F
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Tv, tv, hTv, htv, T', hI, hD⟩ := ihi hst hwt hbt hLt hCt
  obtain ⟨hws, hbs, hLs, hCs⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hst hwt).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hst hwt hbt hLt)
  obtain ⟨sv, hsv, hRed⟩ :=
    ihw (ensureSortCore_inv hsort) hws hbs hLs hCs htv
  rw [denote_sort] at hsv
  obtain rfl := (Option.some.inj hsv).symm
  exact ⟨Tv, T', u.eval φ, hTv, hI, DefEq.trans hD (DefEq.ofRed hRed)⟩

/-- **The value front door, bridged** — the [set] transpose of the TT
lane's `value_key`, in the relation's own vocabulary: `Infer` of the
value's denotation up to `DefEq`, then the checker's own
`vtype ≡ type` verdict composed on. -/
theorem valueFrontR_of {env : Env} (m : EnvR env) {μ : CheckMode} {F :
  Nat} {cv : ConstantVal}
    {value type' value' vtype : Expr}
    (htf : type'.hasFvar = false)
    (hbt' : type'.looseBVarsBounded 0 = true)
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotateCore μ env F 0 value = .ok value')
    (hvp : value'.allLevelParamsDefined cv.levelParams = true)
    (hvr : value'.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 value' = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype type' = .ok true)
    (hcv : ConstantValR μ F env m.cval cv type') :
    ValueFrontR μ F env m.cval cv value type' value' := by
  refine ⟨hlbv, hivf, hannv, hvp, hvr, fun φ => ?_⟩
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge m φ F
  have hvf' : value'.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F value hannv
        (Expr.WScoped.of_not_hasFvar hivf)).fvarsBelow)
  have hbv' : value'.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F value hannv hlbv
  obtain ⟨hwv, hbv, hLv, hCv⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      hvf' hbv'
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Vv, vt, hVv, hvt', T', hI, hD⟩ := ihi hvt hwv hbv hLv hCv
  obtain ⟨Tv, -, -, hTv, -, -⟩ :=
    hcv.2.2.2.2.2.2.2.2.2 φ
  obtain ⟨hwvt, hbvt, hLvt, hCvt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hvt hwv).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hvt hwv hbv hLv)
  exact ⟨Tv, Vv, T', hTv, hVv, hI,
    DefEq.trans hD
      (ihd hde hwvt hbvt hLvt hwt hbt hLt hCvt hCt hvt' hTv)⟩

/-! ## `thmDecl`

The value front doors plus one extra: the type's sort is `Prop`.  The
checker states that as `Level.isEquiv u .zero`; the relation states it
as `DefEq … sT (.sort 0)`, and `Level.isEquiv_sound` is the whole
distance between them. -/

/-- **`thmDecl`, bridged.** -/
theorem declThmR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr}
    (h : checkDecl μ (fueledOps μ F) env (.thmDecl cv value)
      = .ok env₂) :
    DeclThmR μ F env m.cval cv value env₂ := by
  simp only [checkDecl, checkThmVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  cases hst2 : inferTypeCore μ env F 0 type with
  | error e => rw [hst2] at h; exact nomatch h
  | ok stype2 =>
  rw [hst2] at h
  try dsimp only at h
  cases hsort2 : ensureSortCore μ env F 0 stype2 with
  | error e => rw [hsort2] at h; exact nomatch h
  | ok u2 =>
  rw [hsort2] at h
  try dsimp only at h
  cases hpz : Level.isEquiv u2 Level.zero with
  | none => rw [hpz] at h; simp [liftFueled] at h
  | some bz =>
  rw [hpz] at h
  cases bz with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
  simp only [liftFueled, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  refine ⟨type, value', hcv, fun φ => ?_,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    h.symm⟩
  obtain ⟨-, ihw, -, ihi⟩ := checkBridge m.toEnvR φ F
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Tv, tv2, hTv, htv2, T', hI, hD⟩ := ihi hst2 hwt hbt hLt hCt
  obtain ⟨hws, hbs, hLs, hCs⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hst2 hwt).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hst2 hwt hbt hLt)
  obtain ⟨sv, hsv, hRed⟩ :=
    ihw (ensureSortCore_inv hsort2) hws hbs hLs hCs htv2
  rw [denote_sort, Level.isEquiv_sound hpz φ] at hsv
  obtain rfl := (Option.some.inj hsv).symm
  exact ⟨Tv, T', hTv, hI, DefEq.trans hD (DefEq.ofRed hRed)⟩

/-! ## `axiomDecl`

A pure dispatch on Boolean shape gates: the two standard axioms, the
compiler-trust family, and the tolerated skip.  Nothing semantic
happens past `ConstantValR` — the axioms' *content* is the install
layer's `StdAxiomKeyS`/`OfReduceKeyS`, not the bridge's. -/

/-- **`axiomDecl`, bridged.** -/
theorem declAxiomR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    (h : checkDecl μ (fueledOps μ F) env (.axiomDecl cv) = .ok env₂) :
    DeclAxiomR μ F env m.cval cv env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValR_of m.toEnvR hccv
  refine ⟨type, hcv, ?_⟩
  by_cases hstd : stdAxiomOk env { cv with type := type } = true
  · rw [if_pos hstd] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨hstd, h.symm⟩
  rw [if_neg hstd] at h
  have hstdF : stdAxiomOk env { cv with type := type } = false := by
    revert hstd; cases stdAxiomOk env { cv with type := type } <;> simp
  by_cases htc : cv.name = trustCompilerName
  · rw [if_pos htc] at h
    by_cases htco : trustCompilerOk env { cv with type := type } = true
    · rw [if_pos htco] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inl ⟨htc, htco, h.symm⟩)
    · rw [if_neg htco] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg htc] at h
  by_cases hofr : cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName
  · rw [if_pos hofr] at h
    by_cases hofro : ofReduceAxOk env { cv with type := type } = true
    · rw [if_pos hofro] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inr (Or.inl ⟨hofr, hofro, h.symm⟩))
    · rw [if_neg hofro] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hofr] at h
  by_cases hpc : cv.name = propextName ∨ cv.name = choiceName
  · rw [if_pos hpc] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hpc] at h
  by_cases htol : toleratedAxiomNames.contains cv.name = true
  · rw [if_pos htol] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine Or.inr (Or.inr (Or.inr ⟨hstdF, htc, ?_, ?_, ?_, ?_, htol,
      h.symm⟩))
    · exact fun hh => hofr (Or.inl hh)
    · exact fun hh => hofr (Or.inr hh)
    · exact fun hh => hpc (Or.inl hh)
    · exact fun hh => hpc (Or.inr hh)
  · rw [if_neg htol] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `opaqueDecl` and `defnDecl`

The same value front doors, and then each kind's own conditional pin
pack.  Those packs are taken as **parameters** here, exactly as the TT
lane parameterises `declDefnTT` on `NatOpPinTT`/`DivModPinTT`: each is
its own inversion of its own checker routine, and keeping them out of
the branch script is what stops the branch from growing a second
subject. -/

/-- **`opaqueDecl`, bridged**, parametric in the compiler-trust pin's
own inversion. -/
theorem declOpaqueR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr}
    (hrp : ∀ {env' : Env},
      reduceOpNames.contains cv.name = true →
      checkReducePin (m := CheckM) (fueledOps μ F) env env' cv.name
          value = .ok () →
      ReducePinR μ F env env' m.cval cv.name value)
    (h : checkDecl μ (fueledOps μ F) env (.opaqueDecl cv value)
      = .ok env₂) :
    DeclOpaqueR μ F env m.cval cv value env₂ := by
  simp only [checkDecl, checkOpaqueVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨type, value', hcv,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    ?_, ?_⟩
  · by_cases hro : reduceOpNames.contains cv.name = true
    · rw [if_pos hro] at h
      cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
          ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
          value with
      | error e => rw [hrpin] at h; exact nomatch h
      | ok u =>
        rw [hrpin] at h
        simp only [Except.ok.injEq] at h
        exact h.symm
    · rw [if_neg hro] at h
      simp only [Except.ok.injEq] at h
      exact h.symm
  · intro hro
    rw [if_pos hro] at h
    cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
        ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
        value with
    | error e => rw [hrpin] at h; exact nomatch h
    | ok u =>
      rw [hrpin] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact hrp hro hrpin

/-- **`defnDecl`, bridged**, parametric in the two structural-`Nat`
pin inversions.  Both packs are phrased over the **annotated** value
the environment actually stores (`value'`), not over the stream's
`value`. -/
theorem declDefnR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (hnat : ∀ {eqs : List (Expr × Expr)},
      certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
      NatEqsR μ env m.cval eqs)
    (hdm : ∀ {env' : Env} {v : Expr},
      natDivModNames.contains cv.name = true →
      checkDivModPin (m := CheckM) (fueledOps μ F) env env' cv.name
        = .ok () →
      DivModPinR μ F env env' m.cval cv.name v)
    (h : checkDecl μ (fueledOps μ F) env (.defnDecl cv value hint)
      = .ok env₂) :
    DeclDefnR μ F env m.cval cv value hint env₂ := by
  simp only [checkDecl, checkDefnVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the environment the two pin blocks run against, and its own lookup
  have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type } value'
        hint :: env.consts⟩ : Env).find? cv.name
      = some (.defnInfo { cv with type := type } value' hint) := by
    rw [Env.find?_cons]; exact if_pos rfl
  -- **the dispatch, once**: the stored environment and the two packs
  have key : env₂ = ⟨ConstantInfo.defnInfo { cv with type := type }
        value' hint :: env.consts⟩ ∧
      (natOpNames.contains cv.name = true →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ cv.name = true ∧
        (natOpDeps cv.name).all (natOpStoredOk
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩) = true ∧
        certifyNatEqs (m := CheckM) (fueledOps μ F) env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2)) = .ok true) ∧
      (natDivModNames.contains cv.name = true →
        checkDivModPin (m := CheckM) (fueledOps μ F) env
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩ cv.name = .ok ()) := by
    by_cases hno : natOpNames.contains cv.name = true
    · rw [if_pos hno] at h
      by_cases hg : (natOpGuard ⟨ConstantInfo.defnInfo
            { cv with type := type } value' hint :: env.consts⟩ cv.name
          && (natOpDeps cv.name).all (natOpStoredOk
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩)) = true
      · rw [if_pos hg] at h
        rw [hfind2] at h
        dsimp only at h
        cases hcert : certifyNatEqs (m := CheckM) (fueledOps μ F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error e => rw [hcert] at h; exact nomatch h
        | ok v =>
        rw [hcert] at h
        cases v with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, throw, throwThe,
            MonadExceptOf.throw] at h
          exact nomatch h
        | true =>
        simp only [↓reduceIte] at h
        obtain ⟨hg1, hg2⟩ := Bool.and_eq_true _ _ |>.mp hg
        by_cases hdn : natDivModNames.contains cv.name = true
        · rw [if_pos hdn] at h
          cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) env
              ⟨ConstantInfo.defnInfo { cv with type := type } value'
                hint :: env.consts⟩ cv.name with
          | error e => rw [hpin] at h; exact nomatch h
          | ok u =>
            rw [hpin] at h
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun _ => rfl⟩
        · rw [if_neg hdn] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun hc => absurd hc hdn⟩
      · rw [if_neg hg] at h
        simp only [throw, throwThe, MonadExceptOf.throw] at h
        exact nomatch h
    · rw [if_neg hno] at h
      by_cases hdn : natDivModNames.contains cv.name = true
      · rw [if_pos hdn] at h
        cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) env
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ cv.name with
        | error e => rw [hpin] at h; exact nomatch h
        | ok u =>
          rw [hpin] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun hc => absurd hc hno, fun _ => rfl⟩
      · rw [if_neg hdn] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨rfl, fun hc => absurd hc hno, fun hc => absurd hc hdn⟩
  obtain ⟨rfl, hnatK, hdmK⟩ := key
  exact ⟨type, value', hcv,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    rfl,
    fun hc => ⟨(hnatK hc).1, (hnatK hc).2.1, hnat (hnatK hc).2.2⟩,
    fun hc => hdm hc (hdmK hc)⟩

/-! ## The comparison walks

Every `iota_j` statement walk the checker runs is a `checkDefEqList`
or a single `isDefEq`, and every one of them lands in the relation as
`DefEqAtW`/`DefEqListW`.  Those differ from what `DefEqClaimsR`
delivers in exactly one respect: they assert the two **denotations
exist**, where the claim takes them as inputs.  Everything else — the
`∀ Δ` quantification over correlating contexts, the two `CtxOkR`
premises — matches the claim's shape verbatim.

So the whole walk layer factors through one lemma, and what is left to
supply per element is a denotation and three frame facts, both of
which the opened statement's own type carries. -/

/-- **One comparison, bridged.** -/
theorem defEqAtW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} {a b : Expr}
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    {Av Bv : VExpr}
    (hAv : denote m.cval env φ d a = some Av)
    (hBv : denote m.cval env φ d b = some Bv)
    (h : isDefEqCore μ env F d a b = .ok true) :
    DefEqAtW μ env m.cval φ d a b := by
  refine ⟨Av, Bv, hAv, hBv, fun Δ hCa hCb => ?_⟩
  obtain ⟨-, -, ihd, -⟩ := checkBridge m φ F
  exact ihd h hwa hba hLa hwb hbb hLb hCa hCb hAv hBv

/-- **A comparison list, bridged** — `checkDefEqList`'s verdict pack
(`DefEqListOk`) against the relation's pointwise quantified walk.  The
per-element frames and denotations are the caller's; the fold itself
is this induction. -/
theorem defEqListW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} :
    ∀ (as bs : List Expr),
      (∀ e ∈ as ++ bs, Expr.WScoped d e ∧
        e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e ∧
        ∃ v, denote m.cval env φ d e = some v) →
      DefEqListOk μ F env d as bs →
      DefEqListW μ env m.cval φ d as bs
  | [], [], _, _ => trivial
  | a :: as, b :: bs, hfr, h => by
    obtain ⟨hwa, hba, hLa, Av, hAv⟩ := hfr a (by simp)
    obtain ⟨hwb, hbb, hLb, Bv, hBv⟩ := hfr b (by simp)
    exact ⟨defEqAtW_of m hwa hba hLa hwb hbb hLb hAv hBv h.1,
      defEqListW_of m as bs
        (fun e he => hfr e (by
          rcases List.mem_append.mp he with h' | h'
          · exact List.mem_append.mpr
              (Or.inl (List.mem_cons_of_mem _ h'))
          · exact List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem _ h'))))
        h.2⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-! ## `indDecl`, the front half: the member fold

`checkMemberVal` is `checkConstantVal` plus the model-artifact
conjuncts, so `memberValR_of` is `constantValR_of` plus four
inversions.  The fold's threaded valuation is **determined** —
`cvalModeled` at each member — so the bridge chooses nothing; it only
has to keep the recursion's `cval` in step with the environment. -/

/-- **`checkMemberVal`, bridged.** -/
theorem memberValR_of {env' : Env} (m : EnvR env') {μ : CheckMode} {F :
  Nat} {blockNames : List Name}
    {cv cvA : ConstantVal}
    (h : checkMemberVal (m := CheckM) (fueledOps μ F) blockNames env' cv
      = .ok cvA) :
    MemberValR μ F env' m.cval blockNames cv cvA := by
  simp only [checkMemberVal, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env' cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValR_of m hccv
  by_cases hms : cv.name.isModelSuffix = true
  · rw [if_pos hms] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hms] at h
  have hmsF : cv.name.isModelSuffix = false := by
    revert hms; cases cv.name.isModelSuffix <;> simp
  revert h
  cases hfm : env'.find? (cv.name.str "_model") with
  | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    match ci with
    | .defnInfo cvm mval hint =>
      intro h
      dsimp only at h
      by_cases hlp : cvm.levelParams = cv.levelParams
      · rw [if_pos hlp] at h
        by_cases het : Expr.eqUpToNames
            (type.renameConsts fun n =>
              if blockNames.contains n then n.str "_model" else n)
            cvm.type = true
        · rw [if_pos het] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨type, hcv, rfl, hmsF, cvm, mval, hint, hfm, hlp, het⟩
        · rw [if_neg het] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      · rw [if_neg hlp] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | .axiomInfo _ | .thmInfo _ _ | .indInfo _ _ | .ctorInfo _ _ _
    | .recInfo _ _ _ _ | .projInfo _ =>
      intro h
      dsimp only at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `indDecl`, the back half: the two projection-phase folds

`checkIndDecl`'s last two steps are folds over `List.range nF`.  The
template fold is a pure stored-data install and inverts outright; the
projection-function fold is parametric in `ProjFnR`'s own inversion,
for the same reason the value branches' pin packs are — one subject
per lemma. -/

/-- **The elimination-template fold, inverted.** -/
theorem templatesR_of {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (l : List Nat) {env' env₂ : Env},
      l.foldlM (installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF) env' = .ok env₂ →
      DeclIndR.TemplatesR T ctorName lps nP nF env' l env₂
  | [], env', env₂, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | i :: l, env', env₂, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' =>
      intro h
      refine ⟨env'', ?_, templatesR_of l h⟩
      simp only [installProjTemplateStep] at hstep
      by_cases hfr : (env'.find? (projFnName T i)).isNone = true
      · rw [if_pos hfr] at hstep
        simp only [installProjTemplate] at hstep
        revert hstep
        cases hrec : env'.find? (T.str "rec") with
        | none =>
          intro hstep
          dsimp only at hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          exact Or.inl hstep.symm
        | some ci =>
          match ci with
          | .recInfo cvR mI rP [rule] =>
            intro hstep
            dsimp only at hstep
            by_cases hcond :
                (env'.find? (projFnName T i)).isNone = true ∧
                  mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧
                  i < nF
            · rw [if_pos hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, hfr, hstep.symm⟩
            · rw [if_neg hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inl hstep.symm
          | .recInfo cvR mI rP [] | .recInfo cvR mI rP (_ :: _ :: _)
          | .axiomInfo _ | .defnInfo _ _ _ | .thmInfo _ _
          | .indInfo _ _ | .ctorInfo _ _ _ | .projInfo _ =>
            intro hstep
            dsimp only at hstep
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            exact Or.inl hstep.symm
      · rw [if_neg hfr] at hstep
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        exact Or.inl hstep.symm

/-- **The projection-function fold, inverted**, parametric in the
per-field install's own inversion. -/
theorem projInstallR_of {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat}
    {T ctorName : Name} {lps : List Name} {nP nF : Nat}
    (hfn : ∀ {e e' : Env} {cval : TConstVal} {i : Nat},
      (e.find? (projModelName T i)).isSome = true →
      installProjFnStep (m := CheckM) μ (fueledOps μ F) T ctorName lps
        nP nF e i = .ok e' →
      ProjFnR μ F e cval T ctorName lps nP nF i e') :
    ∀ (l : List Nat) {env' env₄ : Env} {cval : TConstVal},
      l.foldlM (installProjFnStep (m := CheckM) μ (fueledOps μ F) T
        ctorName lps nP nF) env' = .ok env₄ →
      ∃ cval₄, ProjInstallR μ F T ctorName lps nP nF env' cval l env₄
        cval₄
  | [], env', env₄, cval, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨cval, h.symm, rfl⟩
  | i :: l, env', env₄, cval, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjFnStep (m := CheckM) μ (fueledOps μ F) T
        ctorName lps nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' =>
      intro h
      by_cases hm : (env'.find? (projModelName T i)).isSome = true
      · obtain ⟨cval₄, htail⟩ := projInstallR_of m hfn l
          (cval := cvalWith cval (projFnName T i)
            (fun ψ => cval (projModelName T i) ψ)) h
        exact ⟨cval₄, _, _, Or.inl ⟨hfn hm hstep, rfl⟩, htail⟩
      · obtain ⟨cval₄, htail⟩ :=
          projInstallR_of m hfn l (cval := cval) h
        refine ⟨cval₄, _, _, Or.inr ⟨?_, ?_, rfl⟩, htail⟩
        · revert hm
          cases (env'.find? (projModelName T i)) <;> simp
        · simp only [installProjFnStep, if_neg hm, pure,
            Except.pure, Except.ok.injEq] at hstep
          exact hstep.symm

/-! ## `basisDecl`

The simplest branch: a guard on the pinned `Eq` former, then a fold of
duplicate checks.  `BasisInstallR` records exactly the fold's output —
each constant fresh, then consed — so the inversion is one induction
over `installBasisDecl_inv`. -/

/-- **The pinned-block fold, inverted** into `BasisInstallR`. -/
theorem foldlM_installBasisDecl_invR :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisInstallR env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact ⟨Option.isNone_iff_eq_none.mpr hfresh,
        foldlM_installBasisDecl_invR l h⟩

/-- **`basisDecl`, bridged.** -/
theorem declBasisR {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {kind : BasisKind}
    (h : checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂) :
    DeclBasisR env kind env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  by_cases hk : kind = .quotK
  · subst hk
    by_cases hEq : env.find? eqName = some eqA
    · simp only [hEq, if_true] at h
      exact ⟨fun _ => hEq, foldlM_installBasisDecl_invR _ h⟩
    · simp [hEq] at h
  · simp only [if_neg hk] at h
    exact ⟨fun hh => absurd hh hk, foldlM_installBasisDecl_invR _ h⟩

end Setlec.SetR
