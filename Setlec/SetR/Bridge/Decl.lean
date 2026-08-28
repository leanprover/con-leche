import Setlec.SetR.Bridge.Main
import Setlec.SetR.Install.Step

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
theorem constantValR_of {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv cv' : ConstantVal}
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
  obtain ⟨-, ihw, -, ihi⟩ := checkBridge m.toEnvR φ F
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
theorem valueFrontR_of {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
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
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge m.toEnvR φ F
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
