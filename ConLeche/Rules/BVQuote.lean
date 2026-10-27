module

public import ConLeche.Kernel.BVUnsat

/-!
# Quoted assignments (task #368)

The deep counterpart of a shallow `bv_decide` assignment
(`BVExpr.Assignment = Lean.RArray BVExpr.PackedBitVec`): the closed
constructor tree `quoteAssign x`, whose bit-vectors are written
`BitVec.ofNat w n`.  The rule `Infer.bvUnsat` quantifies over these
trees; the model shows every member of `⟦Assignment⟧` is one of them
(`Model/BVUnsat.lean`).
-/

@[expose] public section

namespace ConLeche.Rules

open ConLeche ConLeche.BVUnsat

def rarrayLeafName : Name := nmL ["Lean", "RArray", "leaf"]
def rarrayBranchName : Name := nmL ["Lean", "RArray", "branch"]
def packedBVName : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "PackedBitVec"]
def packedBVMkName : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "PackedBitVec", "mk"]
def bvAssignmentName : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "Assignment"]
def bvEvalName : Name := nmL ["Std", "Tactic", "BVDecide", "BVLogicalExpr", "eval"]

def finMkName : Name := nmL ["Fin", "mk"]
def bvOfFinName : Name := nmL ["BitVec", "ofFin"]
def trueIntroName' : Name := nmL ["True", "intro"]

/-- A packed bit-vector, as constructors over literals:
`PackedBitVec.mk w (BitVec.ofFin w (Fin.mk (2^w) n True.intro))`.  The
proof field is `True.intro`: proofs are not read (the boost relation does
not relate them, the model reads every proof as the point). -/
def quotePacked (p : Std.Tactic.BVDecide.BVExpr.PackedBitVec) : Expr :=
  .app (.app (.const packedBVMkName []) (.lit (.natVal p.w)))
    (.app (.app (.const bvOfFinName []) (.lit (.natVal p.w)))
      (.app (.app (.app (.const finMkName []) (.lit (.natVal (2 ^ p.w)))) (.lit (.natVal p.bv.toNat)))
        (.const trueIntroName' [])))

/-- `2 ^ w` as `BitVec`'s field type spells it (`Fin (2 ^ w)`). -/
def pow2E (w : Expr) : Expr :=
  Expr.mkAppN (.const (nmL ["HPow", "hPow"]) [.zero, .zero, .zero])
    [.const natN [], .const natN [], .const natN [],
     Expr.mkAppN (.const (nmL ["instHPow"]) [.zero, .zero])
       [.const natN [], .const natN [],
        Expr.mkAppN (.const (nmL ["instPowNat"]) [.zero]) [.const natN [], .const (nmL ["instNatPowNat"]) []]],
     Expr.mkAppN (.const ofNatN [.zero]) [.const natN [], .lit (.natVal 2),
       .app (.const instOfNatNatN []) (.lit (.natVal 2))],
     w]

/-- An assignment, as a closed constructor tree. -/
def quoteAssign : Std.Tactic.BVDecide.BVExpr.Assignment → Expr
  | .leaf p => .app (.app (.const rarrayLeafName [.zero]) (.const packedBVName [])) (quotePacked p)
  | .branch i l r =>
    .app (.app (.app (.app (.const rarrayBranchName [.zero]) (.const packedBVName []))
      (.lit (.natVal i))) (quoteAssign l)) (quoteAssign r)

end ConLeche.Rules

namespace ConLeche

/-- The gate's third argument is a stored constant without levels. -/
theorem bvUnsatArgOk_const {find? : Name → Option ConstantInfo} {a : Expr}
    (h : bvUnsatArgOk find? a = true) :
    ∃ n ci, a = .const n [] ∧ find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  unfold bvUnsatArgOk at h
  split at h
  · rename_i n
    cases hci : find? n with
    | none => rw [hci] at h; exact nomatch h
    | some ci =>
      rw [hci] at h
      exact ⟨n, ci, rfl, hci, List.isEmpty_iff.mp h⟩
  · exact nomatch h

/-- `bvUnsatHit` at its own shape, unpacked. -/
theorem bvUnsatHit_parts {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {E C a : Expr}
    (h : bvUnsatHit find? findProj? (.app (.app (.const unsatThmName []) E) C) a = true) :
    bvUnsatArgOk find? a = true ∧ bvUnsatOk find? findProj? E C = true := by
  simp only [bvUnsatHit, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

end ConLeche

namespace ConLeche

/-- The model pins hold where the gate's pin check does. -/
theorem BVUnsat.pinsOk_model {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    (h : BVUnsat.pinsOk find? findProj? = true) : ∀ p ∈ bvModelPins, BVUnsat.pinOk find? p = true := by
  simp only [BVUnsat.pinsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem bvUnsatOk_pins {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {E C : Expr}
    (h : bvUnsatOk find? findProj? E C = true) : BVUnsat.pinsOk find? findProj? = true := by
  simp only [bvUnsatOk, Bool.and_eq_true] at h
  exact h.1.2

/-- Where the gate accepts, `U` is stored as a theorem (or a checked
opaque/axiom): never an inductive type former. -/
theorem bvUnsatHit_U_notInd {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {E C a : Expr}
    (h : bvUnsatHit find? findProj? (.app (.app (.const unsatThmName []) E) C) a = true)
    (cv : ConstantVal) (caps : IndCaps) : find? unsatThmName ≠ some (.indInfo cv caps) := by
  have hp := BVUnsat.pinsOk_model (bvUnsatOk_pins (bvUnsatHit_parts h).2) bvPin.U
    (by simp [bvModelPins])
  obtain ⟨ty, hty⟩ : ∃ ty, bvPin.U = .thm unsatThmName [] ty := ⟨_, by rfl⟩
  rw [hty] at hp
  intro hf
  simp [BVUnsat.pinOk, hf] at hp

end ConLeche

namespace ConLeche.Rules

theorem quotePacked_closed (p : Std.Tactic.BVDecide.BVExpr.PackedBitVec) :
    (quotePacked p).looseBVarsBounded 0 = true ∧ (quotePacked p).hasFvar = false := by
  simp [quotePacked, Expr.looseBVarsBounded, Expr.hasFvar]

theorem quoteAssign_closed :
    ∀ x : Std.Tactic.BVDecide.BVExpr.Assignment,
      (quoteAssign x).looseBVarsBounded 0 = true ∧ (quoteAssign x).hasFvar = false
  | .leaf p => by
    have := quotePacked_closed p
    simp_all [quoteAssign, Expr.looseBVarsBounded, Expr.hasFvar]
  | .branch i l r => by
    have hl := quoteAssign_closed l
    have hr := quoteAssign_closed r
    simp_all [quoteAssign, Expr.looseBVarsBounded, Expr.hasFvar]

end ConLeche.Rules

namespace ConLeche

theorem BVUnsat.pin_U {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv, (find? unsatThmName = some (.thmInfo cv) ∨ find? unsatThmName = some (.axiomInfo cv)) ∧
      cv.levelParams = [] := by
  have hp := BVUnsat.pinsOk_model h bvPin.U (by simp [bvModelPins])
  obtain ⟨ty, hty⟩ : ∃ ty, bvPin.U = .thm unsatThmName [] ty := ⟨_, by rfl⟩
  rw [hty] at hp
  simp only [BVUnsat.pinOk] at hp
  split at hp
  · rename_i cv hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, Or.inl hf, hp.1⟩
  · rename_i cv hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, Or.inr hf, hp.1⟩
  · exact nomatch hp

theorem BVUnsat.pin_defn {find? : Name → Option ConstantInfo} {p : BVPin} {n : Name} {ty v : Expr}
    (hp : BVUnsat.pinOk find? p = true) (hpd : p = .defn n [] ty v) :
    ∃ cv hint, find? n = some (.defnInfo cv v hint) ∧ cv.levelParams = [] ∧ cv.type = ty := by
  subst hpd
  simp only [BVUnsat.pinOk] at hp
  split at hp
  · rename_i cv v' hint hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hp
    exact ⟨cv, hint, hf, h1, h2⟩
  · exact nomatch hp

theorem BVUnsat.pin_Unsat {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv v hint, find? bvUnsatName = some (.defnInfo cv v hint) ∧ cv.levelParams = [] := by
  have hp := BVUnsat.pinsOk_model h bvPin.Unsat (by simp [bvModelPins])
  obtain ⟨ty, v, hty⟩ : ∃ ty v, bvPin.Unsat = .defn bvUnsatName [] ty v := ⟨_, _, by rfl⟩
  obtain ⟨cv, hint, hf, hl, -⟩ := BVUnsat.pin_defn hp hty
  exact ⟨cv, v, hint, hf, hl⟩

theorem BVUnsat.pin_BVLE {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv v hint, find? bvLogicalExprName = some (.defnInfo cv v hint) ∧ cv.levelParams = [] ∧
      cv.type = .sort (.succ .zero) := by
  have hp := BVUnsat.pinsOk_model h bvPin.BVLE (by simp [bvModelPins])
  obtain ⟨v, hty⟩ : ∃ v, bvPin.BVLE = .defn bvLogicalExprName [] (.sort (.succ .zero)) v :=
    ⟨_, by rfl⟩
  obtain ⟨cv, hint, hf, hl, hT⟩ := BVUnsat.pin_defn hp hty
  exact ⟨cv, v, hint, hf, hl, hT⟩

end ConLeche

namespace ConLeche

open BVUnsat in
/-- `Unsat`'s pinned value: `fun x => ∀ f : Assignment, eval f x = false`. -/
def unsatValE : Expr :=
  .lam (.const bvLogicalExprName [])
    (.forallE (.const Rules.bvAssignmentName [])
      (.app (.app (.app (.const eqName [.succ .zero]) (.const boolName []))
        (.app (.app (.const Rules.bvEvalName []) (.bvar 0)) (.bvar 1)))
        (.const boolFalseName [])))

/-- `eval`'s pinned type: `Assignment → BVLogicalExpr → Bool`. -/
def evalTyE : Expr :=
  .forallE (.const Rules.bvAssignmentName []) (.forallE (.const bvLogicalExprName []) (.const boolName []))

/-- `Unsat`'s pinned type: `BVLogicalExpr → Prop`. -/
def unsatTyE : Expr := .forallE (.const bvLogicalExprName []) (.sort .zero)

theorem BVUnsat.pin_Unsat_shape {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv hint, find? bvUnsatName = some (.defnInfo cv unsatValE hint) ∧ cv.levelParams = [] ∧
      cv.type = unsatTyE := by
  have hp := BVUnsat.pinsOk_model h bvPin.Unsat (by simp [bvModelPins])
  have hty : bvPin.Unsat = .defn bvUnsatName [] unsatTyE unsatValE := by rfl
  exact BVUnsat.pin_defn hp hty

theorem BVUnsat.pin_eval_shape {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv v hint, find? Rules.bvEvalName = some (.defnInfo cv v hint) ∧ cv.levelParams = [] ∧
      cv.type = evalTyE := by
  have hp := BVUnsat.pinsOk_model h bvPin.eval (by simp [bvModelPins])
  obtain ⟨v, hty⟩ : ∃ v, bvPin.eval = .defn Rules.bvEvalName [] evalTyE v := ⟨_, by rfl⟩
  obtain ⟨cv, hint, hf, hl, hT⟩ := BVUnsat.pin_defn hp hty
  exact ⟨cv, v, hint, hf, hl, hT⟩

theorem BVUnsat.pin_Bool {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv caps, find? boolName = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
      cv.type = .sort (.succ .zero) := by
  have hp := BVUnsat.pinsOk_model h bvPin.Bool (by simp [bvModelPins])
  have hty : bvPin.Bool = .ind boolName [] (.sort (.succ .zero)) := by rfl
  rw [hty] at hp
  simp only [BVUnsat.pinOk] at hp
  split at hp
  · rename_i cv caps hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, caps, hf, hp.1, hp.2⟩
  · exact nomatch hp

theorem BVUnsat.pin_BoolFalse {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv nP nF, find? boolFalseName = some (.ctorInfo cv nP nF) ∧ cv.levelParams = [] ∧
      cv.type = .const boolName [] := by
  have hp := BVUnsat.pinsOk_model h bvPin.BoolFalse (by simp [bvModelPins])
  have hty : bvPin.BoolFalse = .ctor boolFalseName [] (.const boolName []) := by rfl
  rw [hty] at hp
  simp only [BVUnsat.pinOk] at hp
  split at hp
  · rename_i cv nP nF hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, nP, nF, hf, hp.1, hp.2⟩
  · exact nomatch hp

end ConLeche

namespace ConLeche

/-- `unsat_of_verifyBVExpr_eq_true`'s pinned statement. -/
def uTyE : Expr :=
  .forallE (.const bvLogicalExprName [])
    (.forallE (.const stringName [])
      (.forallE
        (.app (.app (.app (.const eqName [.succ .zero]) (.const boolName []))
          (.app (.app (.const (BVUnsat.nmL ["Std", "Tactic", "BVDecide", "Reflect", "verifyBVExpr"]) [])
            (.bvar 1)) (.bvar 0)))
          (.const boolTrueName []))
        (.app (.const bvUnsatName []) (.bvar 2))))

theorem BVUnsat.pin_U_shape {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} (h : BVUnsat.pinsOk find? findProj? = true) :
    ∃ cv, (find? unsatThmName = some (.thmInfo cv) ∨ find? unsatThmName = some (.axiomInfo cv)) ∧
      cv.levelParams = [] ∧ cv.type = uTyE := by
  have hp := BVUnsat.pinsOk_model h bvPin.U (by simp [bvModelPins])
  have hty : bvPin.U = .thm unsatThmName [] uTyE := by rfl
  rw [hty] at hp
  simp only [BVUnsat.pinOk] at hp
  split at hp
  · rename_i cv hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, Or.inl hf, hp.1, hp.2⟩
  · rename_i cv hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨cv, Or.inr hf, hp.1, hp.2⟩
  · exact nomatch hp

end ConLeche

namespace ConLeche

theorem bvUnsatSkip_hit {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {f a body : Expr}
    (h : bvUnsatSkip find? findProj? f a body = true) : bvUnsatHit find? findProj? f a = true := by
  simp only [bvUnsatSkip, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem bvUnsatSkip_type {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {f a body : Expr}
    (h : bvUnsatSkip find? findProj? f a body = true) : body.instantiate1 a = bvUnsatTypeOf f := by
  simp only [bvUnsatSkip, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

end ConLeche

namespace ConLeche

/-- A skipped application's function is headed by `U`. -/
theorem bvUnsatSkip_head {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {f a body : Expr}
    (h : bvUnsatSkip find? findProj? f a body = true) : f.getAppFn = .const unsatThmName [] := by
  have hhit := bvUnsatSkip_hit h
  unfold bvUnsatHit at hhit
  split at hhit
  · rename_i c E C
    simp only [Bool.and_eq_true, beq_iff_eq] at hhit
    rw [hhit.1.1]; rfl
  · exact nomatch hhit

/-- …and its argument is a stored constant without levels. -/
theorem bvUnsatSkip_arg {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {f a body : Expr}
    (h : bvUnsatSkip find? findProj? f a body = true) :
    ∃ n ci, a = .const n [] ∧ find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  have hhit := bvUnsatSkip_hit h
  unfold bvUnsatHit at hhit
  split at hhit
  · simp only [Bool.and_eq_true] at hhit
    exact bvUnsatArgOk_const hhit.1.2
  · exact nomatch hhit

end ConLeche

namespace ConLeche

/-- Where an application skips, `U` is stored as a theorem: never a former. -/
theorem bvUnsatSkip_U_notInd {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {f a body : Expr}
    (h : bvUnsatSkip find? findProj? f a body = true) (cv : ConstantVal) (caps : IndCaps) :
    find? unsatThmName ≠ some (.indInfo cv caps) := by
  have hhit := bvUnsatSkip_hit h
  unfold bvUnsatHit at hhit
  split at hhit
  · simp only [Bool.and_eq_true] at hhit
    obtain ⟨cvU, hfU, -, -⟩ := BVUnsat.pin_U_shape (bvUnsatOk_pins hhit.2)
    intro hf
    rcases hfU with h' | h' <;> rw [h'] at hf <;> exact nomatch hf
  · exact nomatch hhit

end ConLeche
