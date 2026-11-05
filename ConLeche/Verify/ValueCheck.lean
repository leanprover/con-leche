module

public import ConLeche.Kernel.ValueCheck
public import ConLeche.Kernel.CheckDecl
import ConLeche.Verify.Extend.Inversions

public section

/-!
# A value declaration's guards and value check are `checkDecl`

This module inverts `headerGuards`, `valueGuards` and `checkValueGroup`
(`ConLeche/Kernel/ValueCheck.lean`) into the facts they establish (`*_inv`), assembles each from those
facts (`*_of_facts`), carries them up in fuel (`*_mono`), and assembles `checkDecl`'s own run from them
(`checkDecl_of_value_*`), which is what the model's declaration step consumes.
-/

namespace ConLeche

variable {μ : CheckMode} {F : Nat} {env : Env}
variable {pins : List NatOpPinSet}

/-! ## The guards -/

/-- The header's guards say the constant's shape at a literal's name. -/
theorem headerGuards_shape {cv : ConstantVal}
    (h : headerGuards (m := CheckM) env cv = .ok ()) : litShapeOk (.axiomInfo cv) = true := by
  by_cases hs : litShapeOk (.axiomInfo cv) = true
  · exact hs
  exfalso
  simp only [headerGuards, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  · simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  · rw [ite_eq_left hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hop : natOpName cv.name = true
  · rw [ite_eq_left hop] at h
    exact nomatch h
  simp only [hop] at h
  simp [hs] at h

theorem headerGuards_inv {cv : ConstantVal}
    (h : headerGuards (m := CheckM) env cv = .ok ()) :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧
    cv.type.constsResolve env = true := by
  simp only [headerGuards, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos =>
    rw [ite_eq_left hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hop : natOpName cv.name = true
  case pos =>
    rw [ite_eq_left hop] at h
    exact nomatch h
  simp only [hop] at h
  by_cases hshape : litShapeOk (.axiomInfo cv) = true
  case neg => simp [hshape] at h
  simp only [hshape] at h
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  by_cases htp : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : cv.type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hnd, hlb,
    by simpa using hif, htp, htr⟩

theorem valueGuards_inv {cv : ConstantVal} {value : Expr}
    (h : valueGuards (m := CheckM) env cv value = .ok ()) :
    value.looseBVarsBounded 0 = true ∧
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true := by
  simp only [valueGuards, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at h
  by_cases hlb : value.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : value.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  by_cases hvp : value.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact ⟨hlb, by simpa using hif, hvp, hvr⟩

/-! ## The value check -/

theorem checkValueGroup_inv {vg : ValueGroup}
    (h : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    ∃ stype u,
      inferTypeCore μ false env F 0 vg.cv.type = .ok stype ∧
      ensureSortCore μ false env F 0 stype = .ok u ∧
      (vg.kind = .thm → Level.isEquiv u .zero = some true) ∧
      (vg.kind = .thm → valueGuards (m := CheckM) env vg.cv vg.jv = .ok ()) ∧
      ∃ vtype,
        inferTypeCore μ false env F 0 vg.jv = .ok vtype ∧
        isDefEqCore μ false env F 0 vtype vg.cv.type = .ok true := by
  simp only [checkValueGroup, fueledOps_inferType, fueledOps_ensureSort,
    fueledOps_isDefEq, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hst : inferTypeCore μ false env F 0 vg.cv.type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore μ false env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  try dsimp only at h
  -- the theorem test and the theorem's value install, then the value's
  -- typing
  by_cases hk : vg.kind = .thm
  · rw [ite_eq_left hk] at h
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at h; simp [liftFueled] at h
    | some b =>
    rw [heqv] at h
    simp only [liftFueled, Pure.pure, Except.pure] at h
    cases b with
    | false => simp at h
    | true =>
    simp only [↓reduceIte] at h
    cases hiv : valueGuards (m := CheckM) env vg.cv vg.jv with
    | error e => rw [hiv] at h; exact nomatch h
    | ok _ =>
    rw [hiv] at h
    try dsimp only at h
    cases hvt : inferTypeCore μ false env F 0 vg.jv with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore μ false env F 0 vtype vg.cv.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok r =>
    rw [hde] at h
    cases r with
    | false => simp at h
    | true => exact ⟨stype, u, rfl, hsort, fun _ => heqv, fun _ => rfl, vtype, rfl, hde⟩
  · rw [ite_eq_right hk] at h
    cases hvt : inferTypeCore μ false env F 0 vg.jv with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore μ false env F 0 vtype vg.cv.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok r =>
    rw [hde] at h
    cases r with
    | false => simp at h
    | true =>
      have hC : vg.kind = .thm → Level.isEquiv u .zero = some true :=
        fun hk' => absurd hk' hk
      have hD : vg.kind = .thm →
          valueGuards (m := CheckM) env vg.cv vg.jv = .ok () :=
        fun hk' => absurd hk' hk
      exact ⟨stype, u, rfl, hsort, hC, hD, vtype, rfl, hde⟩

/-- The header refuses a certified operation's name. -/
theorem headerGuards_opName {cv : ConstantVal}
    (h : headerGuards (m := CheckM) env cv = .ok ()) : natOpName cv.name = false := by
  simp only [headerGuards, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  · simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  · rw [ite_eq_left hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hop : natOpName cv.name = true
  · rw [ite_eq_left hop] at h
    exact nomatch h
  simpa using hop

/-! ## Fuel -/

/-! ## `checkDecl` from the two halves -/

theorem checkConstantVal_of_facts {cv : ConstantVal} {stype : Expr} {u : Level} {a : Bool}
    (hop : (natOpName cv.name && !a) = false)
    (hfind : env.find? cv.name = none)
    (hres : reservedBasisNames.contains cv.name = false)
    (hshape : litShapeOk (.axiomInfo cv) = true)
    (hnd : Name.nodup cv.levelParams = true)
    (hlb : cv.type.looseBVarsBounded 0 = true)
    (hif : cv.type.hasFvar = false)
    (htp : cv.type.allLevelParamsDefined cv.levelParams = true)
    (htr : cv.type.constsResolve env = true)
    (hst : inferTypeCore μ false env F 0 cv.type = .ok stype)
    (hsort : ensureSortCore μ false env F 0 stype = .ok u) :
    checkConstantVal (fueledOps μ F) env cv a = .ok () := by
  simp only [checkConstantVal, fueledOps_inferType,
    fueledOps_ensureSort, Bind.bind, Except.bind, Pure.pure, Except.pure, hop, hfind, hres, hshape,
    hnd, hlb, hif, htp, htr, hst, hsort, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]

theorem checkDefnVal_of_facts {cv : ConstantVal} {value vtype : Expr}
    {hint : ReducibilityHint}
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hvp : value.allLevelParamsDefined cv.levelParams = true)
    (hvr : value.constsResolve env = true)
    (hvt : inferTypeCore μ false env F 0 value = .ok vtype)
    (hde : isDefEqCore μ false env F 0 vtype cv.type = .ok true) :
    checkDefnVal (fueledOps μ F) env cv value hint = .ok ⟨.defnInfo cv value hint :: env.consts, env.tables⟩ := by
  simp only [checkDefnVal, fueledOps_inferType, fueledOps_isDefEq,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hlb, hif, hvp, hvr, hvt, hde,
    Bool.false_eq_true, ↓reduceIte]

theorem checkThmVal_of_facts {cv : ConstantVal} {value vtype stype : Expr} {u : Level}
    (hst : inferTypeCore μ false env F 0 cv.type = .ok stype)
    (hsort : ensureSortCore μ false env F 0 stype = .ok u)
    (heqv : Level.isEquiv u .zero = some true)
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hvp : value.allLevelParamsDefined cv.levelParams = true)
    (hvr : value.constsResolve env = true)
    (hvt : inferTypeCore μ false env F 0 value = .ok vtype)
    (hde : isDefEqCore μ false env F 0 vtype cv.type = .ok true) :
    checkThmVal (fueledOps μ F) env cv value = .ok ⟨.thmInfo cv :: env.consts, env.tables⟩ := by
  simp only [checkThmVal, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, liftFueled, Bind.bind, Except.bind, Pure.pure, Except.pure, hst,
    hsort, heqv, hlb, hif, hvp, hvr, hvt, hde, Bool.false_eq_true, ↓reduceIte]

theorem checkOpaqueVal_of_facts {cv : ConstantVal} {value vtype : Expr}
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hvp : value.allLevelParamsDefined cv.levelParams = true)
    (hvr : value.constsResolve env = true)
    (hvt : inferTypeCore μ false env F 0 value = .ok vtype)
    (hde : isDefEqCore μ false env F 0 vtype cv.type = .ok true) :
    checkOpaqueVal (fueledOps μ F) env cv value = .ok ⟨.axiomInfo cv :: env.consts, env.tables⟩ := by
  simp only [checkOpaqueVal, fueledOps_inferType, fueledOps_isDefEq,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hlb, hif, hvp, hvr, hvt, hde,
    Bool.false_eq_true, ↓reduceIte]

/-- **A definition's two halves are `checkDecl`.** -/
theorem checkDecl_of_value_defn {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint} {vg : ValueGroup}
    (hnat : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false)
    (_hk : vg.kind = .defn)
    (hcvA : vg.cv = cv) (hvgjv : vg.jv = value)
    (hI : headerGuards (m := CheckM) env cv = .ok ())
    (hV : valueGuards (m := CheckM) env vg.cv value = .ok ())
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.defnDecl cv value hint)
      = .ok ⟨.defnInfo vg.cv vg.jv hint :: env.consts, env.tables⟩ := by
  obtain ⟨hfind, hres, hnd, hlb, hif, htp, htr⟩ :=
    headerGuards_inv hI
  rw [hcvA] at hV
  obtain ⟨hlbv, hivf, hvp, hvr⟩ := valueGuards_inv hV
  obtain ⟨stype, u, hst, hsort, -, -, vtype, hvt, hde⟩ := checkValueGroup_inv hC
  obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hnat
  rw [hcvA] at hst hde ⊢
  rw [hvgjv] at hvt ⊢
  have hcc := checkConstantVal_of_facts (a := true) (by simp) hfind hres (headerGuards_shape hI) hnd hlb hif htp htr hst hsort
  have hdv := checkDefnVal_of_facts (cv := cv) (hint := hint)
    hlbv hivf hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, Pure.pure, Except.pure, hcc, hdv, h1, h2,
    Bool.false_eq_true, ↓reduceIte]

/-- **A theorem's two halves are `checkDecl`**: the header's install
half, and the check half holding the RAW value (which it guards
itself). -/
theorem checkDecl_of_value_thm {cv : ConstantVal} {value : Expr} {vg : ValueGroup}
    (hk : vg.kind = .thm)
    (hcvA : vg.cv = cv) (hvgjv : vg.jv = value)
    (hI : headerGuards (m := CheckM) env cv = .ok ())
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.thmDecl cv value)
      = .ok ⟨.thmInfo vg.cv :: env.consts, env.tables⟩ := by
  obtain ⟨hfind, hres, hnd, hlb, hif, htp, htr⟩ :=
    headerGuards_inv hI
  obtain ⟨stype, u, hst, hsort, hthm, hiv, vtype, hvt, hde⟩ := checkValueGroup_inv hC
  have hV := hiv hk
  rw [hcvA, hvgjv] at hV
  obtain ⟨hlbv, hivf, hvp, hvr⟩ := valueGuards_inv hV
  rw [hcvA] at hst hde ⊢
  rw [hvgjv] at hvt
  have hcc := checkConstantVal_of_facts (a := false)
    (by simp [headerGuards_opName hI]) hfind hres (headerGuards_shape hI) hnd hlb hif htp htr hst hsort
  have htv := checkThmVal_of_facts (cv := cv) hst hsort (hthm hk)
    hlbv hivf hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, hcc, htv]

/-- **An opaque's two halves are `checkDecl`.** -/
theorem checkDecl_of_value_opaque {cv : ConstantVal} {value : Expr} {vg : ValueGroup}
    (hred : reduceOpNames.contains cv.name = false)
    (_hk : vg.kind = .opaque)
    (hcvA : vg.cv = cv) (hvgjv : vg.jv = value)
    (hI : headerGuards (m := CheckM) env cv = .ok ())
    (hV : valueGuards (m := CheckM) env vg.cv value = .ok ())
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.opaqueDecl cv value)
      = .ok ⟨.axiomInfo vg.cv :: env.consts, env.tables⟩ := by
  obtain ⟨hfind, hres, hnd, hlb, hif, htp, htr⟩ :=
    headerGuards_inv hI
  rw [hcvA] at hV
  obtain ⟨hlbv, hivf, hvp, hvr⟩ := valueGuards_inv hV
  obtain ⟨stype, u, hst, hsort, -, -, vtype, hvt, hde⟩ := checkValueGroup_inv hC
  rw [hcvA] at hst hde ⊢
  rw [hvgjv] at hvt
  have hcc := checkConstantVal_of_facts (a := false)
    (by simp [headerGuards_opName hI]) hfind hres (headerGuards_shape hI) hnd hlb hif htp htr hst hsort
  have hov := checkOpaqueVal_of_facts (cv := cv)
    hlbv hivf hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, Pure.pure, Except.pure, hcc, hov, hred,
    Bool.false_eq_true, ↓reduceIte]

end ConLeche
