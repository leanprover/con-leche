module

public import ConLeche.Kernel.Inductives.ClassCheck
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The class check's generated recursors: the comparison runs, inverted

Check 6 of the class check (`Kernel/Inductives/ClassCheck.lean`) compares
the stream's recursor family with the GENERATED one by `isDefEq`, the
generated side annotated and inferred first (R7).  What the proof reads
off the two comparison runs (`classRuleOk`, `classRecTyOk`) at the fueled
operations: both sides annotated, both INFERRED at depth `0`, and the
defeq run's `true` — the premises of the model tier's transfer
(`closedDefEq_read_eq`, `Model/Inductives/ClassRecTransfer.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode} {F : Nat}

/-- **A stream rule against the generated one, inverted.**  The stored
rule `rhsA` is the stream's right-hand side annotated at the rule-less
recursors' environment and inferred there; the generated rule `gen` is
annotated and inferred there too, and the two are defeq. -/
theorem classRuleOk_inv {w : StructWalkers} {feT feR : FEnv} {cvR : ConstantVal}
    {pw : PropWhen} {n : Nat} {rhs gen rhsA : Expr}
    (h : classRuleOk (fueledOps mode F) w feT feR cvR pw n rhs gen = .ok rhsA) :
    rhs.looseBVarsBounded 0 = true ∧ rhs.hasFvar = false ∧
    annotateCore mode feR.env F 0 rhs = .ok rhsA ∧
    rhsA.allLevelParamsDefined cvR.levelParams = true ∧
    (∃ t, inferTypeCore mode feR.env F 0 rhsA = .ok t) ∧
    ∃ genA t, annotateCore mode feR.env F 0 gen = .ok genA ∧
      inferTypeCore mode feR.env F 0 genA = .ok t ∧
      isDefEqCore mode feR.env F 0 rhsA genA = .ok true := by
  unfold classRuleOk at h
  simp only [fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq, Bind.bind,
    Except.bind, Pure.pure, Except.pure] at h
  by_cases hlb : rhs.looseBVarsBounded 0 = true
  case neg => simp [hlb, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hlb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => simp [hfv, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hfv, Bool.false_eq_true, ↓reduceIte] at h
  cases hann : annotateCore mode feR.env F 0 rhs with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA' =>
  rw [hann] at h
  try dsimp only at h
  by_cases hlp : rhsA'.allLevelParamsDefined cvR.levelParams = true
  case neg => simp [hlp, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hlp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hres : w.resolve feR rhsA' = true
  case neg => simp [hres, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hres, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hinf : inferTypeCore mode feR.env F 0 rhsA' with
  | error e => rw [hinf] at h; exact nomatch h
  | ok t =>
  rw [hinf] at h
  try dsimp only at h
  cases hstrip : rhsA'.stripLams n with
  | none =>
    simp [hstrip, unwrapOr, throw, throwThe, MonadExceptOf.throw] at h
  | some rbs =>
  simp only [hstrip, unwrapOr, Pure.pure, Except.pure] at h
  try dsimp only at h
  by_cases hdom : rbs.1.all (fun b => w.resolve feT b.1) = true
  case neg => simp [hdom, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hdom, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hpw : rbs.1.all (fun b => b.2.pw == pw) = true
  case neg => simp [hpw, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hpw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hgann : annotateCore mode feR.env F 0 gen with
  | error e => rw [hgann] at h; exact nomatch h
  | ok genA =>
  rw [hgann] at h
  try dsimp only at h
  cases hginf : inferTypeCore mode feR.env F 0 genA with
  | error e => rw [hginf] at h; exact nomatch h
  | ok tg =>
  rw [hginf] at h
  try dsimp only at h
  cases hdq : isDefEqCore mode feR.env F 0 rhsA' genA with
  | error e => rw [hdq] at h; exact nomatch h
  | ok b =>
  rw [hdq] at h
  cases b with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  exact ⟨hlb, by simpa using hfv, rfl, hlp, ⟨t, hinf⟩, genA, tg, rfl, hginf, hdq⟩

/-- **`checkConstantValF`, inverted** (the `FEnv` twin of
`checkConstantVal_inv`, the parts the transfer reads). -/
theorem checkConstantValF_inv {fe : FEnv} {cv cv' : ConstantVal}
    (h : checkConstantValF (fueledOps mode F) fe cv = .ok cv') :
    cv.type.looseBVarsBounded 0 = true ∧ cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotateCore mode fe.env F 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      inferTypeCore mode fe.env F 0 type = .ok stype ∧
      ensureSortCore mode fe.env F 0 stype = .ok u ∧
      cv' = { cv with type := type } := by
  unfold checkConstantValF at h
  simp only [fueledOps_annotate, fueledOps_inferType, fueledOps_ensureSort, Bind.bind,
    Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  split at h
  case isFalse => exact nomatch h
  split at h
  case isFalse => exact nomatch h
  rename_i hlb
  split at h
  · exact nomatch h
  rename_i hfv
  cases hann : annotateCore mode fe.env F 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hlp
  split at h
  case isFalse => exact nomatch h
  cases hinf : inferTypeCore mode fe.env F 0 type with
  | error e => rw [hinf] at h; exact nomatch h
  | ok stype =>
  rw [hinf] at h
  try dsimp only at h
  cases hs : ensureSortCore mode fe.env F 0 stype with
  | error e => rw [hs] at h; exact nomatch h
  | ok u =>
  rw [hs] at h
  simp only [Except.ok.injEq] at h
  exact ⟨hlb, by simpa using hfv, type, stype, u, rfl, hlp, hinf, hs, h.symm⟩

/-- **A stream recursor's type against the generated one, inverted.**
The stored type (the checked constant's) and the generated one are both
annotated and inferred at the constructors' environment, and defeq. -/
theorem classRecTyOk_inv {fe : FEnv} {g : ClassGen} {k : Nat} {rc : RecShape}
    {rules : List RecRule} {c : Nat} {cvRi : ConstantVal}
    (h : classRecTyOk (fueledOps mode F) fe g k rc rules c = .ok cvRi) :
    checkConstantValF (fueledOps mode F) fe rc.cvR = .ok cvRi ∧
    ∃ gty gtyA s u, classGenRecTy g c = some gty ∧
      annotateCore mode fe.env F 0 gty = .ok gtyA ∧
      inferTypeCore mode fe.env F 0 gtyA = .ok s ∧
      ensureSortCore mode fe.env F 0 s = .ok u ∧
      isDefEqCore mode fe.env F 0 cvRi.type gtyA = .ok true := by
  unfold classRecTyOk at h
  simp only [fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hcv : checkConstantValF (fueledOps mode F) fe rc.cvR with
  | error e => rw [hcv] at h; exact nomatch h
  | ok cv =>
  rw [hcv] at h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  split at h
  case isFalse => exact nomatch h
  cases hg : classGenRecTy g c with
  | none => simp [hg, unwrapOr, throw, throwThe, MonadExceptOf.throw] at h
  | some gty =>
  simp only [hg, unwrapOr, Pure.pure, Except.pure] at h
  cases hann : annotateCore mode fe.env F 0 gty with
  | error e => rw [hann] at h; exact nomatch h
  | ok gtyA =>
  rw [hann] at h
  try dsimp only at h
  cases hinf : inferTypeCore mode fe.env F 0 gtyA with
  | error e => rw [hinf] at h; exact nomatch h
  | ok s =>
  rw [hinf] at h
  try dsimp only at h
  cases hs : ensureSortCore mode fe.env F 0 s with
  | error e => rw [hs] at h; exact nomatch h
  | ok u =>
  rw [hs] at h
  try dsimp only at h
  cases hdq : isDefEqCore mode fe.env F 0 cv.type gtyA with
  | error e => rw [hdq] at h; exact nomatch h
  | ok b =>
  rw [hdq] at h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hb
  split at h
  · exact nomatch h
  simp only [Except.ok.injEq] at h
  subst h hb
  exact ⟨rfl, gty, gtyA, s, u, rfl, hann, hinf, hs, hdq⟩

end ConLeche
