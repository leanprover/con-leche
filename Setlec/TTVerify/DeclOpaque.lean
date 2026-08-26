import Setlec.TTVerify.DeclThm

/-!
# The `opaque` case

`checkOpaqueVal` is `checkThmVal` without the is-a-proposition check,
and it stores an **`axiomInfo`** — the value is a realizability witness
and is then discarded.  The bridge still values the constant by the
value's denotation, because that is the only way `ReduceOpsTT` can
hold: the compiler-trust opaques are certified to be the identity
*through their value*, and a valuation that forgot the value could not
see it.

So the difference from the `theorem` case is entirely in what
`extendValueTT` is applied to (`.axiomInfo` rather than `.thmInfo`,
making `thm_ok` vacuous instead of `defn_eq`), plus one extra
obligation for the pinned compiler-trust family.

## The reduce-pin obligation

`checkReducePin` is a named checker function, so §8.6 puts the
obligation there.  Its content is the transpose of the set model's
`reduce_ops` install: the pinned opaque's value is definitionally the
identity on its element type, certified by
`isDefEq env 1 (.app valA x) x` at the pinned certificate variable.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-- The compiler-trust identity, at the constant being installed.  The
obligation `checkReducePin` leaves behind. -/
def ReducePinTT (F : Nat) : Prop :=
  ∀ {env : Env} (m : EnvTT env) {cv : ConstantVal} {value value' : Expr},
    cv.name ∈ reduceOpNames →
    env.find? cv.name = none →
    checkReducePin (fueledOps F) env
      ⟨ConstantInfo.axiomInfo cv :: env.consts⟩ cv.name value = .ok () →
    annotateCore env F 0 value = .ok value' →
    value'.hasFvar = false → value'.looseBVarsBounded 0 = true →
    (∀ ψ : Name → Nat, ∃ v, denoteClosed m.cval env ψ value' = some v) →
    ConstantVal.matchesPin cv (reduceOpCvA cv.name) = true →
    ((⟨ConstantInfo.axiomInfo cv :: env.consts⟩ : Env).find?
        (reduceElemName cv.name)).isSome = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
        HasType Δ X
          (cvalAt m.cval env cv.name value' (reduceElemName cv.name) φ) →
        Deq Δ (.app (cvalAt m.cval env cv.name value' cv.name φ) X) X

/-- **`DeclOpaqueTT`**, modulo the compiler-trust pin. -/
theorem declOpaqueTT (hrp : ReducePinTT F) : DeclOpaqueTT F := by
  intro env env₁ cv value h m
  simp only [checkDecl, checkOpaqueVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env cv with
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
  | ok bq =>
  rw [hde] at h
  cases bq with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the closedness facts
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
  -- the stored constant, and the pin branch
  have hwfc : EnvWF ⟨ConstantInfo.axiomInfo { cv with type := type } ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  have hinstall : ∀ (hred : ∀ cv2,
        ConstantInfo.axiomInfo { cv with type := type } = .axiomInfo cv2 →
        cv.name ∈ reduceOpNames →
        ConstantVal.matchesPin cv2 (reduceOpCvA cv.name) = true →
        ((⟨ConstantInfo.axiomInfo { cv with type := type } ::
            env.consts⟩ : Env).find? (reduceElemName cv.name)).isSome
            = true ∧
          ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
            HasType Δ X (cvalAt m.cval env cv.name value'
              (reduceElemName cv.name) φ) →
            Deq Δ (.app (cvalAt m.cval env cv.name value' cv.name φ) X) X),
      Nonempty (EnvTT ⟨ConstantInfo.axiomInfo { cv with type := type } ::
        env.consts⟩) := by
    intro hred
    refine extendValueTT m
      (c₀ := .axiomInfo { cv with type := type }) rfl rfl hfind' hwfc hvf'
      hbv' hkey
      ?_ (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
      (fun _ heq => nomatch heq) hres' ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) hred
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
  by_cases hro : reduceOpNames.contains cv.name = true
  · rw [if_pos hro] at h
    cases hpin : checkReducePin (fueledOps F) env
        ⟨ConstantInfo.axiomInfo { cv with type := type } :: env.consts⟩
        cv.name value with
    | error e => rw [hpin] at h; exact nomatch h
    | ok _ =>
      rw [hpin] at h
      simp only [Except.ok.injEq] at h
      subst h
      refine hinstall (fun cv2 heq hmem hmp => ?_)
      obtain rfl : cv2 = { cv with type := type } := by
        injection heq with h1; exact h1.symm
      exact hrp m (List.contains_iff_mem.mp hro) hfind' hpin hannv hvf'
        hbv' (fun ψ => by
          obtain ⟨v, -, hv, -, -⟩ := hkey ψ
          exact ⟨v, hv⟩) hmp
  · rw [if_neg hro] at h
    simp only [Except.ok.injEq] at h
    subst h
    refine hinstall (fun cv2 heq hmem hmp => ?_)
    exact absurd (List.contains_iff_mem.mpr hmem) hro

end Setlec.TTVerify
