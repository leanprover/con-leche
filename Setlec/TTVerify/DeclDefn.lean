import Setlec.TTVerify.DeclOpaque

/-!
# The `def` case

The third and last value-carrying kind, and the same script again:
`checkDefnVal` is `checkOpaqueVal` storing a `defnInfo` instead of an
`axiomInfo`, so `defn_eq` becomes the non-vacuous field and `thm_ok`
the vacuous one.

What is new is the two **pin blocks** the checker runs afterwards, both
of which leave the environment alone and exist purely to record facts:

* the structural-`Nat` operations (`certifyNatEqs` on the operation's
  recurrence equations, in the *pre-insertion* environment with the
  operation's self-references substituted by its stored value);
* the WF-recursive `Nat.div`/`Nat.mod` pins (`checkDivModPin`).

Both are named checker functions, so §8.6 puts an obligation on each
rather than inside this case.  The case's own job is to route the
verdicts to `EnvTT.cons`'s `nat_ops` and `div_mod` head clauses, and to
show that when the guards do *not* fire the clauses are vacuous — which
is where `natOpNames.contains` and `natDivModNames.contains` do their
work.
-/

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-- The recurrence equations of a stored structural-`Nat` operation.
The obligation `certifyNatEqs` leaves behind. -/
def NatOpPinTT (F : Nat) : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cv : ConstantVal} {value value' : Expr}
    {hint : ReducibilityHint},
    cv.name ∈ natOpNames →
    env.find? cv.name = none →
    annotateCore mode env F 0 value = .ok value' →
    value'.hasFvar = false → value'.looseBVarsBounded 0 = true →
    (∀ ψ : Name → Nat, ∃ v, denoteClosed m.cval env ψ value' = some v) →
    natOpGuard ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ cv.name
      = true →
    (∀ eq ∈ (natOpEquations 0 cv.name).map (fun eq =>
        (Expr.substConst0 cv.name value' eq.1,
         Expr.substConst0 cv.name value' eq.2)),
      isDefEqCore mode env F 2 eq.1 eq.2 = .ok true) →
    ∀ eq ∈ natOpEquations 0 cv.name, ∀ φ : Name → Nat, ∃ L R,
      denote (cvalAt m.cval env cv.name value')
        ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ φ 2 eq.1
        = some L ∧
      denote (cvalAt m.cval env cv.name value')
        ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ φ 2 eq.2
        = some R ∧
      Deq [cvalAt m.cval env cv.name value' natName φ,
           cvalAt m.cval env cv.name value' natName φ] L R

/-- The `ble`-guarded characterisation of a pinned WF-recursive
operation.  The obligation `checkDivModPin` leaves behind. -/
def DivModPinTT (F : Nat) : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cv : ConstantVal} {value value' : Expr}
    {hint : ReducibilityHint},
    cv.name ∈ natDivModNames →
    env.find? cv.name = none →
    annotateCore mode env F 0 value = .ok value' →
    value'.hasFvar = false → value'.looseBVarsBounded 0 = true →
    (∀ ψ : Name → Nat, ∃ v t,
      denoteClosed m.cval env ψ value' = some v ∧
      denoteClosed m.cval env ψ cv.type = some t ∧ HasType [] v t) →
    checkDivModPin (fueledOps mode F) env
      ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ cv.name
      = .ok () →
    natOpGuard ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ cv.name
      = true ∧
    ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
      HasType Δ x (cvalAt m.cval env cv.name value' natName φ) →
      HasType Δ y (cvalAt m.cval env cv.name value' natName φ) →
      DivModClausesTT (cvalAt m.cval env cv.name value') cv.name φ Δ x y

/-- Inversion for the recurrence certifier: every equation passed. -/
theorem certifyNatEqs_inv {env : Env} :
    ∀ (eqs : List (Expr × Expr)),
      certifyNatEqs (fueledOps mode F) env eqs = .ok true →
      ∀ eq ∈ eqs, isDefEqCore mode env F 2 eq.1 eq.2 = .ok true := by
  intro eqs
  induction eqs with
  | nil => intro _ eq hq; exact nomatch hq
  | cons e es ih =>
    intro h eq hq
    simp only [certifyNatEqs, Bind.bind, Except.bind, fueledOps_isDefEq] at h
    cases hde : isDefEqCore mode env F 2 e.1 e.2 with
    | error err => rw [hde] at h; exact nomatch h
    | ok r =>
      rw [hde] at h
      cases r with
      | false => simp [pure, Except.pure] at h
      | true =>
        simp only [if_true] at h
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hde
        · exact ih h eq hq'

/-- **`DeclDefnTT`**, modulo the two `Nat` pins. -/
theorem declDefnTT (hnp : NatOpPinTT F) (hdm : DivModPinTT F) :
    DeclDefnTT F := by
  intro env env₁ cv value hint h m
  simp only [checkDecl, checkDefnVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps mode F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann,
    htp, htr, hst, hsort, rfl⟩ := checkConstantVal_invT hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  cases hannv : annotateCore mode env F 0 value with
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
  cases hvt : inferTypeCore mode env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore mode env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok bq =>
  rw [hde] at h
  cases bq with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the closedness facts, as in the other two kinds
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
  have hkey := value_key m htf hbt' hvf' hbv' hst hvt hde
  have hwfc : EnvWF ⟨ConstantInfo.defnInfo { cv with type := type } value'
      hint :: env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  -- the install, parameterised on the two pin clauses
  have hinstall : ∀ (hnat : cv.name ∈ natOpNames →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type } value'
          hint :: env.consts⟩ cv.name = true ∧
        ∀ eq ∈ natOpEquations 0 cv.name, ∀ φ : Name → Nat, ∃ L R,
          denote (cvalAt m.cval env cv.name value')
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ φ 2 eq.1 = some L ∧
          denote (cvalAt m.cval env cv.name value')
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ φ 2 eq.2 = some R ∧
          Deq [cvalAt m.cval env cv.name value' natName φ,
               cvalAt m.cval env cv.name value' natName φ] L R)
      (hdiv : cv.name ∈ natDivModNames →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type } value'
          hint :: env.consts⟩ cv.name = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
          HasType Δ x (cvalAt m.cval env cv.name value' natName φ) →
          HasType Δ y (cvalAt m.cval env cv.name value' natName φ) →
          DivModClausesTT (cvalAt m.cval env cv.name value') cv.name φ Δ
            x y),
      Nonempty (EnvTT ⟨ConstantInfo.defnInfo { cv with type := type } value'
        hint :: env.consts⟩) := by
    intro hnat hdiv
    refine extendValueTT m
      (c₀ := .defnInfo { cv with type := type } value' hint) rfl rfl hfind'
      hwfc hvf' hbv' hkey ?_
      (fun _ value2 _ heq => by injection heq with _ h2 _; exact h2.symm)
      (fun _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
      (fun _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
      (fun _ _ _ heq => nomatch heq) hres' ?_
      (fun _ _ _ _ hmem => hnat hmem) (fun _ _ _ _ hmem => hdiv hmem)
      (fun _ heq => nomatch heq)
    · intro φ₁ φ₂ hp
      exact denote_params_ext m.val_params hp 0 value' hvp
    · intro T cvT caps hf hcape hres hfam hpart
      rcases hpart with hT | hC | ⟨j, hj, hP⟩
      · rw [hT, Env.find?_cons, if_pos rfl] at hf; exact nomatch hf
      · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [hC, Env.find?_cons, if_pos rfl] at hfC; exact nomatch hfC
      · obtain ⟨-, -, hfP⟩ := hfam
        obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
        rw [hP, Env.find?_cons, if_pos rfl] at hfPj; exact nomatch hfPj
  -- the div/mod tail, walked in each branch of the `Nat`-op `if`
  have finish : ∀ (hnatcl : cv.name ∈ natOpNames →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type } value'
          hint :: env.consts⟩ cv.name = true ∧
        ∀ eq ∈ natOpEquations 0 cv.name, ∀ φ : Name → Nat, ∃ L R,
          denote (cvalAt m.cval env cv.name value')
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ φ 2 eq.1 = some L ∧
          denote (cvalAt m.cval env cv.name value')
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ φ 2 eq.2 = some R ∧
          Deq [cvalAt m.cval env cv.name value' natName φ,
               cvalAt m.cval env cv.name value' natName φ] L R)
      (hdivcl : cv.name ∈ natDivModNames →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type } value'
          hint :: env.consts⟩ cv.name = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
          HasType Δ x (cvalAt m.cval env cv.name value' natName φ) →
          HasType Δ y (cvalAt m.cval env cv.name value' natName φ) →
          DivModClausesTT (cvalAt m.cval env cv.name value') cv.name φ Δ
            x y),
      env₁ = ⟨ConstantInfo.defnInfo { cv with type := type } value'
        hint :: env.consts⟩ → Nonempty (EnvTT env₁) := by
    intro hnatcl hdivcl heq
    subst heq
    exact hinstall hnatcl hdivcl
  -- the `Nat`-operation pin block
  by_cases hnon : natOpNames.contains cv.name = true
  · rw [if_pos hnon] at h
    by_cases hg : (natOpGuard ⟨ConstantInfo.defnInfo
        { cv with type := type } value' hint :: env.consts⟩ cv.name &&
        (natOpDeps cv.name).all (natOpStoredOk ⟨ConstantInfo.defnInfo
          { cv with type := type } value' hint :: env.consts⟩)) = true
    · rw [if_pos hg] at h
      rw [show (⟨ConstantInfo.defnInfo { cv with type := type } value'
            hint :: env.consts⟩ : Env).find? cv.name
          = some (.defnInfo { cv with type := type } value' hint) from by
        rw [Env.find?_cons]
        exact if_pos rfl] at h
      dsimp only at h
      cases hcert : certifyNatEqs (fueledOps mode F) env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2)) with
      | error e => rw [hcert] at h; exact nomatch h
      | ok r =>
        rw [hcert] at h
        cases r with
        | false => simp [throw, throwThe, MonadExceptOf.throw] at h
        | true =>
          simp only [if_true] at h
          obtain ⟨hguard, -⟩ := by
            simpa only [Bool.and_eq_true] using hg
          by_cases hdmn : natDivModNames.contains cv.name = true
          · rw [if_pos hdmn] at h
            cases hpin : checkDivModPin (fueledOps mode F) env
                ⟨ConstantInfo.defnInfo { cv with type := type } value'
                  hint :: env.consts⟩ cv.name with
            | error e => rw [hpin] at h; exact nomatch h
            | ok _ =>
              rw [hpin] at h
              simp only [Except.ok.injEq] at h
              exact finish (fun _ => ⟨hguard,
        hnp m (cv := { cv with type := type }) (hint := hint)
          (List.contains_iff_mem.mp hnon) hfind' hannv hvf' hbv'
          (fun ψ => by obtain ⟨v, -, hv, -, -⟩ := hkey ψ; exact ⟨v, hv⟩)
          hguard (certifyNatEqs_inv _ hcert)⟩)
                (fun _ => hdm m (cv := { cv with type := type })
                  (hint := hint) (List.contains_iff_mem.mp hdmn) hfind' hannv
                  hvf' hbv' hkey hpin) h.symm
          · rw [if_neg hdmn] at h
            simp only [Except.ok.injEq] at h
            exact finish (fun _ => ⟨hguard,
        hnp m (cv := { cv with type := type }) (hint := hint)
          (List.contains_iff_mem.mp hnon) hfind' hannv hvf' hbv'
          (fun ψ => by obtain ⟨v, -, hv, -, -⟩ := hkey ψ; exact ⟨v, hv⟩)
          hguard (certifyNatEqs_inv _ hcert)⟩)
              (fun hmem => absurd (List.contains_iff_mem.mpr hmem) hdmn) h.symm
    · rw [if_neg hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hnon] at h
    by_cases hdmn : natDivModNames.contains cv.name = true
    · rw [if_pos hdmn] at h
      cases hpin : checkDivModPin (fueledOps mode F) env
          ⟨ConstantInfo.defnInfo { cv with type := type } value'
            hint :: env.consts⟩ cv.name with
      | error e => rw [hpin] at h; exact nomatch h
      | ok _ =>
        rw [hpin] at h
        simp only [Except.ok.injEq] at h
        exact finish (fun hmem => absurd (List.contains_iff_mem.mpr hmem) hnon)
          (fun _ => hdm m (cv := { cv with type := type })
            (hint := hint) (List.contains_iff_mem.mp hdmn) hfind' hannv
            hvf' hbv' hkey hpin) h.symm
    · rw [if_neg hdmn] at h
      simp only [Except.ok.injEq] at h
      exact finish (fun hmem => absurd (List.contains_iff_mem.mpr hmem) hnon)
        (fun hmem => absurd (List.contains_iff_mem.mpr hmem) hdmn) h.symm

end Setlec.TTVerify
