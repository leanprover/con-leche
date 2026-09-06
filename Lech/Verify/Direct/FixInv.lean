import Lech.Verify.Direct.SumInv
import Lech.Kernel.Direct.RecInstall

/-!
# The direct recursive install: inversion (task #188)

The shape of a successful run of the recursive route's recursor stage
(`checkDirectFixRec`, `Lech/Kernel/Direct/RecInstall.lean`), read off
the monad: the generated recursor type with the inductive-hypothesis
binders, its scoping and sort, the comparison with the stream's, and
the generated rules — each the generator's output, scoped at the
environment holding the recursor's constant and NOT inferred.  The
former's and the constructors' stages are the sum route's
(`SumInv.lean`).
-/

namespace Lech

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem fixThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The generated rules loop: `k` rules for constructors `j, j+1, …`,
each the generator's output at its position, scoped at `envR`. -/
theorem checkDirectFixRules_inv {envR : Env} {rlps : List Name} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {tty : Expr}
    {ctors : List (Name × Nat × Expr × List Nat)} {recC : Name} {rlvls : List Level} :
    ∀ {k j : Nat} {rhss : List Expr},
      checkDirectFixRules (m := CheckM) envR rlps T lps elim large nP nIdx tty ctors recC
        rlvls k j = .ok rhss →
      rhss.length = k ∧
      ∀ i, i < k → ∃ rhs, rhss[i]? = some rhs ∧
        directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls (j + i) = some rhs ∧
        rhs.allLevelParamsDefined rlps = true ∧ rhs.constsResolve envR = true ∧
        rhs.looseBVarsBounded 0 = true ∧ rhs.hasFvar = false
  | 0, _, rhss, h => by
    simp only [checkDirectFixRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, j, rhss, h => by
    unfold checkDirectFixRules at h
    obtain ⟨rhs, hrh, h⟩ := exceptBind_ok h
    have hrh' := unwrapOr_ok hrh
    try simp only at h
    by_cases h1 : (Expr.allLevelParamsDefined rlps rhs && Expr.constsResolve envR rhs &&
        Expr.looseBVarsBounded 0 rhs && !rhs.hasFvar) = true
    case neg =>
      rw [if_neg h1] at h
      exfalso
      first
        | exact fixThrow_ne_ok h
        | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
    rw [if_pos h1] at h
    try simp only at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkDirectFixRules_inv hrest
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero =>
      exact ⟨rhs, rfl, by rw [Nat.add_zero]; exact hrh', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
    | succ i =>
      obtain ⟨rhs', hget, hgen, hlp, hres, hbv, hfv⟩ := hall i (by omega)
      have hget' : (rhs :: rest)[i + 1]? = some rhs' := by simpa using hget
      have hgen' : directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls (j + (i + 1))
          = some rhs' := by
        rw [show j + (i + 1) = j + 1 + i from by omega]; exact hgen
      exact ⟨rhs', hget', hgen', hlp, hres, hbv, hfv⟩

/-- The recursor stage's shape. -/
theorem checkDirectFixRec_shape {env : Env} {p : DirectFixParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkDirectFixRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    ∃ (cvRi : ConstantVal) (recTy sty : Expr) (u : Level),
      checkConstantVal (fueledOps mode F) env p.cvR = .ok cvRi ∧
      directRecTyR p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (directFixCtors4 ctorsA p.kinds) = some recTy ∧
      recTy.allLevelParamsDefined p.cvR.levelParams = true ∧
      recTy.constsResolve env = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      inferTypeCore mode env F 0 recTy = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u ∧
      isDefEqCore mode env F 0 cvRi.type recTy = .ok true ∧
      checkDirectFixRules (m := CheckM)
        ⟨.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ p.majorIdx p.rulePrefix []
          :: env.consts⟩
        p.cvR.levelParams p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (directFixCtors4 ctorsA p.kinds) p.cvR.name (p.cvR.levelParams.map .param)
        (directFixCtors4 ctorsA p.kinds).length 0 = .ok rhss ∧
      cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := by
  unfold checkDirectFixRec at h
  obtain ⟨cvRi, hcv, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨recTy, hrt, h⟩ := exceptBind_ok h
  have hrt' := unwrapOr_ok hrt
  try simp only at h
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg =>
    rw [if_neg h1] at h
    exfalso
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos h1] at h
  try simp only at h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exfalso
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  | true =>
  rw [if_pos rfl] at h
  try simp only at h
  obtain ⟨rhss', hrules, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
  exact ⟨cvRi, recTy, sty, u, hcv, hrt', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, hsty, hu, hb,
    hrules, rfl⟩

end Lech
