import Setlec.TTVerify.DeclValue
import Setlec.TTVerify.MajorStep

/-!
# The `theorem` case

The template for the three value-carrying kinds, and the shortest of
them: `checkThmVal` is `checkOpaqueVal` plus the is-a-proposition
check, and `checkDefnVal` is `checkOpaqueVal` plus the `Nat` pins.  So
what this file establishes — the walk through `checkConstantVal`, the
`hkey` package, and the vacuity of every head clause a `thmInfo`
cannot trigger — is reused twice more.

**`hkey` is the whole content**, and it is two claims composed:
`InferClaimsTT` at the checked value gives `⊢ ⟦value⟧ : ⟦vtype⟧`, and
`DefEqClaimsTT` at the checker's own `vtype ≡ type` verdict converts it
to `⊢ ⟦value⟧ : ⟦type⟧`.  That is exactly the two checks `checkThmVal`
runs, in the order it runs them — the per-declaration step is the
per-expression claims applied once each, which is why it could be left
until stage 2's end.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-- The frame conditions of a closed, `fvar`-free expression at depth
`0` — the shape every declaration-level claim is applied at. -/
theorem closed0_frames {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {e : Expr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    Expr.WScoped 0 e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e ∧ CtxOk cval env φ 0 [] e :=
  ⟨Expr.WScoped.of_not_hasFvar hnf, hb,
    Expr.LeavesBounded.of_not_hasFvar hnf,
    CtxOk.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf)⟩

/-- **The key package**, shared by all three value-carrying kinds: the
checked value is derivably of the declared type.  `InferClaimsTT` at
the value, `DefEqClaimsTT` at the checker's `vtype ≡ type` verdict. -/
theorem value_key {env : Env} (m : EnvTT env) {type value' stype vtype : Expr}
    (htf : type.hasFvar = false) (hbt' : type.looseBVarsBounded 0 = true)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hst : inferTypeCore env F 0 type = .ok stype)
    (hvt : inferTypeCore env F 0 value' = .ok vtype)
    (hde : isDefEqCore env F 0 vtype type = .ok true) :
    ∀ ψ : Name → Nat, ∃ v t,
      denoteClosed m.cval env ψ value' = some v ∧
      denoteClosed m.cval env ψ type = some t ∧ HasType [] v t := by
  intro ψ
  obtain ⟨-, -, ihd, ihi⟩ := checkClaimsTT m ψ F
  obtain ⟨hwv, hbv, hLv, hCv⟩ :=
    closed0_frames (cval := m.cval) (env := env) (φ := ψ) hvf' hbv'
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_frames (cval := m.cval) (env := env) (φ := ψ) htf hbt'
  obtain ⟨v, vt, hv, hvt', hvT⟩ := ihi hvt hwv hbv hLv hCv
  obtain ⟨t, st, ht, -, -⟩ := ihi hst hwt hbt hLt hCt
  obtain ⟨hwvt, hbvt, hLvt, hCvt⟩ := closed0_frames (cval := m.cval)
    (env := env) (φ := ψ)
    (Expr.not_hasFvar_of_fvarsBelow_zero
      (inferTypeCore_WScoped m.wf F hvt hwv).fvarsBelow)
    (inferTypeCore_looseBVars m.wf F hvt hwv hbv hLv)
  exact ⟨v, t, hv, ht,
    Deq.conv hvT (ihd hde hwvt hbvt hLvt hwt hbt hLt hCvt hCt hvt' ht)⟩

/-- **`DeclThmTT`, discharged.** -/
theorem declThmTT : DeclThmTT F := by
  intro env env₁ cv value h m
  simp only [checkDecl, checkThmVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann,
    htp, htr, hst, hsort, rfl⟩ := checkConstantVal_invT hccv
  simp only [Pure.pure, Except.pure] at h
  cases hst2 : inferTypeCore env F 0 type with
  | error e => rw [hst2] at h; exact nomatch h
  | ok stype2 =>
  rw [hst2] at h
  try dsimp only at h
  cases hsort2 : ensureSortCore env F 0 stype2 with
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
  cases hannv : annotateCore env F 0 value with
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
  cases hvt : inferTypeCore env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  -- the two annotated expressions are closed
  have htf : type.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F cv.type hann
        (Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
  have hbt' : type.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F cv.type hann hlbt
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  have hvf' : value'.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F value hannv
        (Expr.WScoped.of_not_hasFvar hivf')).fvarsBelow)
  have hbv' : value'.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F value hannv hlbv
  -- the key package: the value is derivably of the declared type
  have hkey := value_key m htf hbt' hvf' hbv' hst hvt hde
  -- and the install
  refine extendValueTT m (c₀ := .thmInfo { cv with type := type } value')
    rfl rfl hfind' ?_ hvf' hbv' hkey ?_ (fun _ _ _ heq => nomatch heq)
    (fun _ value2 heq => by injection heq with _ h2; exact h2.symm)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) hres' ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq)
  · -- the extended environment is well-formed
    refine EnvWF.cons m.wf ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩
  · -- the valuation reads only the declared parameters
    intro φ₁ φ₂ hp
    exact denote_params_ext m.val_params hp 0 value' hvp
  · -- no eta-capable family is completed by a `theorem`
    intro T cvT caps hf hcape hres hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [hT, Env.find?_cons, if_pos rfl] at hf; exact nomatch hf
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC; exact nomatch hfC
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hfPj; exact nomatch hfPj

end Setlec.TTVerify
