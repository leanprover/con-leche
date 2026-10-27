module

import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Semantics.Kit
import ConLeche.Model.AxiomMem
import ConLeche.Model.NatSem
import ConLeche.Semantics.Tower.SumTower
meta import ConLeche.PinGen.BVShapes

/-!
# Every member of `⟦Assignment⟧` is a quoted assignment (task #368)

The model side of `Infer.bvUnsat`: where the `bv_decide` closure is the
pinned one, every member `X` of the reading of
`BVExpr.Assignment = Lean.RArray BVExpr.PackedBitVec` is the reading of a
quoted assignment `quoteAssign x` (`assignQuote_of`).

* The stored recursors `RArray.rec`, `PackedBitVec.rec`, `BitVec.rec`,
  `Fin.rec` inhabit their (pinned) types, so at a `Prop` motive
  `fun X => truthVal (Q X)` they turn the constructor clauses of `Q`
  into `Q X` at every member (`rarray_ind` …).
* A member of `⟦Nat⟧` (the basis pin, `ω`) is a numeral.
* `BitVec w`'s field type `Fin (2 ^ w)` reads to `2 ^ w`'s numeral: the
  rule's premise `2 ^ k ⟶ lit (2 ^ k)` (its `RedSem`, the law's `hpow`).
* A member of `⟦v < n⟧` at numerals forces `v < n`: otherwise the
  stored theorems `Nat.le_of_ble_eq_true` and `Nat.not_lt_of_le` (pinned
  statements), at `Nat.ble n v = true` (the literal row), give a member
  of `⟦False⟧ = ∅`.
-/

public section

namespace ConLeche.BVQ

open ConLeche ConLeche.BVUnsat

/-! ## The pinned constants and their stored shapes -/

def rarrayN : Name := nmL ["Lean", "RArray"]
def rarrayRecN : Name := nmL ["Lean", "RArray", "rec"]
def pbvRecN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "PackedBitVec", "rec"]
def bitVecN : Name := nmL ["BitVec"]
def bitVecRecN : Name := nmL ["BitVec", "rec"]
def finN : Name := nmL ["Fin"]
def finRecN : Name := nmL ["Fin", "rec"]
def ltN : Name := nmL ["LT", "lt"]
def ltClassN : Name := nmL ["LT"]
def instLTNatN : Name := nmL ["instLTNat"]
def leN : Name := nmL ["LE", "le"]
def leClassN : Name := nmL ["LE"]
def instLENatN : Name := nmL ["instLENat"]
def notN : Name := nmL ["Not"]
def leOfBleN : Name := nmL ["Nat", "le_of_ble_eq_true"]
def notLtOfLeN : Name := nmL ["Nat", "not_lt_of_le"]
def lU : Name := nmL ["u"]
def lU1 : Name := nmL ["u_1"]

/-- The tables the shapes are spliced with (`PinGen/BVShapes.lean`). -/
private meta def shapeTables : ConLeche.PinGen.BVShapes.Tables where
  consts := [(``Nat, ``natName), (``Lean.RArray, ``rarrayN),
    (``Lean.RArray.leaf, ``Rules.rarrayLeafName), (``Lean.RArray.branch, ``Rules.rarrayBranchName),
    (``Lean.RArray.rec, ``rarrayRecN),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec, ``Rules.packedBVName),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec.mk, ``Rules.packedBVMkName),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec.rec, ``pbvRecN),
    (``BitVec, ``bitVecN), (``BitVec.ofFin, ``Rules.bvOfFinName), (``BitVec.rec, ``bitVecRecN),
    (``Fin, ``finN), (``Fin.mk, ``Rules.finMkName), (``Fin.rec, ``finRecN),
    (``True, ``trueName), (``True.intro, ``Rules.trueIntroName'),
    (``LT, ``ltClassN), (``LT.lt, ``ltN), (``instLTNat, ``instLTNatN),
    (``LE.le, ``leN), (``instLENat, ``instLENatN), (``Not, ``notN), (``False, ``falseName),
    (``Eq, ``eqName), (``Bool, ``boolName), (``Bool.true, ``boolTrueName), (``Nat.ble, ``natBleName)]
  levels := [(`u, ``lU), (`u_1, ``lU1)]

/-- The stored shapes: `(declaration suffix, constant, value?)`. -/
private meta def shapeEntries : List (String × Lean.Name × Bool) :=
  [("LeafTy", ``Lean.RArray.leaf, false), ("BranchTy", ``Lean.RArray.branch, false),
   ("RArrayRecTy", ``Lean.RArray.rec, false),
   ("PBVMkTy", ``Std.Tactic.BVDecide.BVExpr.PackedBitVec.mk, false),
   ("PBVRecTy", ``Std.Tactic.BVDecide.BVExpr.PackedBitVec.rec, false),
   ("OfFinTy", ``BitVec.ofFin, false), ("BitVecRecTy", ``BitVec.rec, false),
   ("FinMkTy", ``Fin.mk, false), ("FinRecTy", ``Fin.rec, false),
   ("leOfBleTy", ``Nat.le_of_ble_eq_true, false), ("notLtOfLeTy", ``Nat.not_lt_of_le, false),
   ("NotVal", ``Not, true), ("LTltTy", ``LT.lt, false), ("instLTNatTy", ``instLTNat, false),
   ("NatBleTy", ``Nat.ble, false), ("RArrayTy", ``Lean.RArray, false), ("BitVecTy", ``BitVec, false),
   ("FinTy", ``Fin, false), ("AssignmentVal", ``Std.Tactic.BVDecide.BVExpr.Assignment, true)]

-- `shX : Expr`, the stored shapes (checked against the pins by `rfl` below)
run_cmd Lean.Elab.Command.liftTermElabM do
  for (tag, c, val) in shapeEntries do
    ConLeche.PinGen.BVShapes.spliceExprShape shapeTables
      ((`ConLeche.BVQ).str ("sh" ++ tag)) c val

/-! ## The quoted pieces -/

/-- `Fin.mk M j True.intro`. -/
@[expose] def finQE (M j : Nat) : Expr :=
  .app (.app (.app (.const Rules.finMkName []) (.lit (.natVal M))) (.lit (.natVal j)))
    (.const Rules.trueIntroName' [])

/-- `BitVec.ofFin k (Fin.mk (2 ^ k) bv.toNat True.intro)`. -/
@[expose] def bvQE (k : Nat) (bv : BitVec k) : Expr :=
  .app (.app (.const Rules.bvOfFinName []) (.lit (.natVal k))) (finQE (2 ^ k) bv.toNat)

theorem quotePacked_eq (k : Nat) (bv : BitVec k) :
    Rules.quotePacked { w := k, bv := bv } =
      .app (.app (.const Rules.packedBVMkName []) (.lit (.natVal k))) (bvQE k bv) := rfl

/-! ## Pins as lookups -/

/-- The stored constant `n` has the pinned level parameters and type. -/
def PinS (env : Env) (n : Name) (lps : List Name) (ty : Expr) : Prop :=
  ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = lps ∧
    ci.toConstantVal.type = ty

/-- What a pin states of the stored constant. -/
def PinOf (env : Env) : BVPin → Prop
  | .defn n lps ty _ | .thm n lps ty | .ind n lps ty | .ctor n lps ty | .recr n lps ty _ =>
    PinS env n lps ty

theorem pinS_of {env : Env} {p : BVPin} (h : pinOk env.find? p = true) : PinOf env p := by
  cases p with
  | defn n lps ty v =>
    simp only [pinOk] at h; split at h
    · rename_i cv v' hint hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1.1, h.1.2⟩
    · exact nomatch h
  | thm n lps ty =>
    simp only [pinOk] at h; split at h
    · rename_i cv hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1, h.2⟩
    · rename_i cv hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1, h.2⟩
    · exact nomatch h
  | ind n lps ty =>
    simp only [pinOk] at h; split at h
    · rename_i cv caps hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1, h.2⟩
    · exact nomatch h
  | ctor n lps ty =>
    simp only [pinOk] at h; split at h
    · rename_i cv nP nF hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1, h.2⟩
    · exact nomatch h
  | recr n lps ty rules =>
    simp only [pinOk] at h; split at h
    · rename_i cv mI rP rs hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, hf, h.1.1.1, h.1.1.2⟩
    · exact nomatch h

theorem pinS_model {env : Env} (hpins : pinsOk env.find? env.findProj? = true) {p : BVPin}
    (hm : p ∈ bvModelPins) : PinOf env p :=
  pinS_of (BVUnsat.pinsOk_model hpins p hm)

section
variable {env : Env} (hpins : pinsOk env.find? env.findProj? = true)
include hpins

theorem pin_Bool' : PinS env boolName [] (.sort (.succ .zero)) := by
  obtain ⟨cv, caps, hf, hl, ht⟩ := BVUnsat.pin_Bool hpins
  exact ⟨_, hf, hl, ht⟩

theorem pin_Nat : PinS env natName [] (.sort (.succ .zero)) := by
  have h := pinS_model hpins (p := bvPin.Nat) (by simp [bvModelPins])
  have e : bvPin.Nat = .ind natName [] (.sort (.succ .zero)) := by rfl
  rw [e] at h; exact h

theorem pin_NatZero : PinS env natZeroName [] (.const natName []) := by
  have h := pinS_model hpins (p := bvPin.NatZero) (by simp [bvModelPins])
  have e : bvPin.NatZero = .ctor natZeroName [] (.const natName []) := by rfl
  rw [e] at h; exact h

theorem pin_NatSucc : PinS env natSuccName [] (.forallE (.const natName []) (.const natName [])) := by
  have h := pinS_model hpins (p := bvPin.NatSucc) (by simp [bvModelPins])
  have e : bvPin.NatSucc = .ctor natSuccName [] (.forallE (.const natName []) (.const natName [])) := by
    rfl
  rw [e] at h; exact h

theorem pin_RArray : PinS env rarrayN [lU] shRArrayTy := by
  have h := pinS_model hpins (p := bvPin.RArray) (by simp [bvModelPins])
  have e : bvPin.RArray = .ind rarrayN [lU] shRArrayTy := by rfl
  rw [e] at h; exact h

theorem pin_RArrayLeaf : PinS env Rules.rarrayLeafName [lU] shLeafTy := by
  have h := pinS_model hpins (p := bvPin.RArrayLeaf) (by simp [bvModelPins])
  have e : bvPin.RArrayLeaf = .ctor Rules.rarrayLeafName [lU] shLeafTy := by rfl
  rw [e] at h; exact h

theorem pin_RArrayBranch : PinS env Rules.rarrayBranchName [lU] shBranchTy := by
  have h := pinS_model hpins (p := bvPin.RArrayBranch) (by simp [bvModelPins])
  have e : bvPin.RArrayBranch = .ctor Rules.rarrayBranchName [lU] shBranchTy := by rfl
  rw [e] at h; exact h

theorem pin_RArrayRec : PinS env rarrayRecN [lU1, lU] shRArrayRecTy := by
  have h := pinS_model hpins (p := bvPin.RArrayRec) (by simp [bvModelPins])
  obtain ⟨rs, e⟩ : ∃ rs, bvPin.RArrayRec = .recr rarrayRecN [lU1, lU] shRArrayRecTy rs := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_PBV : PinS env Rules.packedBVName [] (.sort (.succ .zero)) := by
  have h := pinS_model hpins (p := bvPin.PBV) (by simp [bvModelPins])
  have e : bvPin.PBV = .ind Rules.packedBVName [] (.sort (.succ .zero)) := by rfl
  rw [e] at h; exact h

theorem pin_PBVMk : PinS env Rules.packedBVMkName [] shPBVMkTy := by
  have h := pinS_model hpins (p := bvPin.PBVMk) (by simp [bvModelPins])
  have e : bvPin.PBVMk = .ctor Rules.packedBVMkName [] shPBVMkTy := by rfl
  rw [e] at h; exact h

theorem pin_PBVRec : PinS env pbvRecN [lU] shPBVRecTy := by
  have h := pinS_model hpins (p := bvPin.PBVRec) (by simp [bvModelPins])
  obtain ⟨rs, e⟩ : ∃ rs, bvPin.PBVRec = .recr pbvRecN [lU] shPBVRecTy rs := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_BitVec : PinS env bitVecN [] shBitVecTy := by
  have h := pinS_model hpins (p := bvPin.BitVec) (by simp [bvModelPins])
  have e : bvPin.BitVec = .ind bitVecN [] shBitVecTy := by rfl
  rw [e] at h; exact h

theorem pin_BitVecOfFin : PinS env Rules.bvOfFinName [] shOfFinTy := by
  have h := pinS_model hpins (p := bvPin.BitVecOfFin) (by simp [bvModelPins])
  have e : bvPin.BitVecOfFin = .ctor Rules.bvOfFinName [] shOfFinTy := by rfl
  rw [e] at h; exact h

theorem pin_BitVecRec : PinS env bitVecRecN [lU] shBitVecRecTy := by
  have h := pinS_model hpins (p := bvPin.BitVecRec) (by simp [bvModelPins])
  obtain ⟨rs, e⟩ : ∃ rs, bvPin.BitVecRec = .recr bitVecRecN [lU] shBitVecRecTy rs := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_Fin : PinS env finN [] shFinTy := by
  have h := pinS_model hpins (p := bvPin.Fin) (by simp [bvModelPins])
  have e : bvPin.Fin = .ind finN [] shFinTy := by rfl
  rw [e] at h; exact h

theorem pin_FinMk : PinS env Rules.finMkName [] shFinMkTy := by
  have h := pinS_model hpins (p := bvPin.FinMk) (by simp [bvModelPins])
  have e : bvPin.FinMk = .ctor Rules.finMkName [] shFinMkTy := by rfl
  rw [e] at h; exact h

theorem pin_FinRec : PinS env finRecN [lU] shFinRecTy := by
  have h := pinS_model hpins (p := bvPin.FinRec) (by simp [bvModelPins])
  obtain ⟨rs, e⟩ : ∃ rs, bvPin.FinRec = .recr finRecN [lU] shFinRecTy rs := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_True : PinS env trueName [] (.sort .zero) := by
  have h := pinS_model hpins (p := bvPin.True) (by simp [bvModelPins])
  have e : bvPin.True = .ind trueName [] (.sort .zero) := by rfl
  rw [e] at h; exact h

theorem pin_TrueIntro : PinS env Rules.trueIntroName' [] (.const trueName []) := by
  have h := pinS_model hpins (p := bvPin.TrueIntro) (by simp [bvModelPins])
  have e : bvPin.TrueIntro = .ctor Rules.trueIntroName' [] (.const trueName []) := by rfl
  rw [e] at h; exact h

theorem pin_leOfBle : PinS env leOfBleN [] shleOfBleTy := by
  have h := pinS_model hpins (p := bvPin.leOfBle) (by simp [bvModelPins])
  have e : bvPin.leOfBle = .thm leOfBleN [] shleOfBleTy := by rfl
  rw [e] at h; exact h

theorem pin_notLtOfLe : PinS env notLtOfLeN [] shnotLtOfLeTy := by
  have h := pinS_model hpins (p := bvPin.notLtOfLe) (by simp [bvModelPins])
  have e : bvPin.notLtOfLe = .thm notLtOfLeN [] shnotLtOfLeTy := by rfl
  rw [e] at h; exact h

theorem pin_Not : PinS env notN [] (.forallE (.sort .zero) (.sort .zero)) := by
  have h := pinS_model hpins (p := bvPin.Not) (by simp [bvModelPins])
  obtain ⟨v, e⟩ : ∃ v, bvPin.Not = .defn notN [] (.forallE (.sort .zero) (.sort .zero)) v := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_False : PinS env falseName [] (.sort .zero) := by
  have h := pinS_model hpins (p := bvPin.False) (by simp [bvModelPins])
  have e : bvPin.False = .ind falseName [] (.sort .zero) := by rfl
  rw [e] at h; exact h

theorem pin_BoolTrue : PinS env boolTrueName [] (.const boolName []) := by
  have h := pinS_model hpins (p := bvPin.BoolTrue) (by simp [bvModelPins])
  have e : bvPin.BoolTrue = .ctor boolTrueName [] (.const boolName []) := by rfl
  rw [e] at h; exact h

theorem pin_NatBle : PinS env natBleName [] shNatBleTy := by
  have h := pinS_model hpins (p := bvPin.NatBle) (by simp [bvModelPins])
  obtain ⟨v, e⟩ : ∃ v, bvPin.NatBle = .defn natBleName [] shNatBleTy v := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_LTcls : ∃ ty, PinS env ltClassN [lU] ty := by
  have h := pinS_model hpins (p := bvPin.LTcls) (by simp [bvModelPins])
  obtain ⟨ty, e⟩ : ∃ ty, bvPin.LTcls = .ind ltClassN [lU] ty := ⟨_, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_LTlt : PinS env ltN [lU] shLTltTy := by
  have h := pinS_model hpins (p := bvPin.LTlt) (by simp [bvModelPins])
  obtain ⟨v, e⟩ : ∃ v, bvPin.LTlt = .defn ltN [lU] shLTltTy v := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_instLTNat : PinS env instLTNatN [] shinstLTNatTy := by
  have h := pinS_model hpins (p := bvPin.instLTNat) (by simp [bvModelPins])
  obtain ⟨v, e⟩ : ∃ v, bvPin.instLTNat = .defn instLTNatN [] shinstLTNatTy v := ⟨_, by rfl⟩
  rw [e] at h; exact h

theorem pin_LEle : ∃ ty, PinS env leN [lU] ty := by
  have h := pinS_model hpins (p := bvPin.LEle) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.LEle = .defn leN [lU] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_instLENat : ∃ ty, PinS env instLENatN [] ty := by
  have h := pinS_model hpins (p := bvPin.instLENat) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.instLENat = .defn instLENatN [] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_hPow : ∃ ty, PinS env (nmL ["HPow", "hPow"]) [nmL ["u"], nmL ["v"], nmL ["w"]] ty := by
  have h := pinS_model hpins (p := bvPin.hPow) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.hPow = .defn (nmL ["HPow", "hPow"]) [nmL ["u"], nmL ["v"], nmL ["w"]] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_instHPow : ∃ ty, PinS env (nmL ["instHPow"]) [lU1, nmL ["u_2"]] ty := by
  have h := pinS_model hpins (p := bvPin.instHPow) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.instHPow = .defn (nmL ["instHPow"]) [lU1, nmL ["u_2"]] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_instPowNat : ∃ ty, PinS env (nmL ["instPowNat"]) [lU1] ty := by
  have h := pinS_model hpins (p := bvPin.instPowNat) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.instPowNat = .defn (nmL ["instPowNat"]) [lU1] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_instNatPowNat : ∃ ty, PinS env (nmL ["instNatPowNat"]) [] ty := by
  have h := pinS_model hpins (p := bvPin.instNatPowNat) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.instNatPowNat = .defn (nmL ["instNatPowNat"]) [] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_ofNat : ∃ ty, PinS env ofNatN [lU] ty := by
  have h := pinS_model hpins (p := bvPin.ofNat) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.ofNat = .defn ofNatN [lU] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

theorem pin_instOfNatNat : ∃ ty, PinS env instOfNatNatN [] ty := by
  have h := pinS_model hpins (p := bvPin.instOfNatNat) (by simp [bvModelPins])
  obtain ⟨ty, v, e⟩ : ∃ ty v, bvPin.instOfNatNat = .defn instOfNatNatN [] ty v := ⟨_, _, by rfl⟩
  rw [e] at h; exact ⟨_, h⟩

end

end ConLeche.BVQ

namespace ConLeche.Model
open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name CheckMode ConstantInfo)
open ConLeche.BVQ ConLeche.BVUnsat

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The all-zero level assignment: every level in this file is `0`. -/
@[expose] def ψ0 : Name → Nat := fun _ => 0

/-- A pinned constant's leaf at the zero levels. -/
abbrev K (m : EnvModel V env) (n : Name) : Term := m.acval n ψ0

theorem denote_constK (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name}
    {lps : List Name} {ty : Expr} {us : List Level}
    (hp : PinS env n lps ty) (hlen : us.length = lps.length)
    (hz : ∀ p ∈ lps, Level.substFn ψ lps us p = 0) :
    denote m.acval env ψ d (.const n us) = some (K m n) := by
  obtain ⟨ci, hf, hl, -⟩ := hp
  rw [denote_const hf (by rw [hl]; exact hlen), hl]
  congr 1
  exact m.acval_params n ci hf _ _ (by rw [hl]; exact hz)

theorem denote_constK0 (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name} {ty : Expr}
    (hp : PinS env n [] ty) : denote m.acval env ψ d (.const n []) = some (K m n) :=
  denote_constK m hp rfl (fun _ h => nomatch h)

theorem denote_constK1 (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name} {l : Name}
    {ty : Expr} {u : Level} (hp : PinS env n [l] ty) (hu : u.eval ψ = 0) :
    denote m.acval env ψ d (.const n [u]) = some (K m n) :=
  denote_constK m hp rfl (fun p hp' => by
    simp only [List.mem_singleton] at hp'; subst hp'; simp [Level.substFn, hu])

theorem denote_constK2 (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name} {l1 l2 : Name}
    {ty : Expr} {u1 u2 : Level} (hp : PinS env n [l1, l2] ty) (hu1 : u1.eval ψ = 0)
    (hu2 : u2.eval ψ = 0) :
    denote m.acval env ψ d (.const n [u1, u2]) = some (K m n) :=
  denote_constK m hp rfl (fun p hp' => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [Level.substFn, hu1, hu2] <;> split <;> simp [hu1, hu2])

theorem denote_constK3 (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name}
    {l1 l2 l3 : Name} {ty : Expr} {u1 u2 u3 : Level} (hp : PinS env n [l1, l2, l3] ty)
    (hu1 : u1.eval ψ = 0) (hu2 : u2.eval ψ = 0) (hu3 : u3.eval ψ = 0) :
    denote m.acval env ψ d (.const n [u1, u2, u3]) = some (K m n) :=
  denote_constK m hp rfl (fun p hp' => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> simp [Level.substFn, hu1, hu2, hu3] <;>
      (repeat' split) <;> simp [hu1, hu2, hu3])

@[simp] theorem eval_ψ0 (l : Name) : (Level.param l).eval ψ0 = 0 := by rfl
@[simp] theorem ψ0_apply (l : Name) : ψ0 l = 0 := by rfl
@[simp] theorem eval_zero' (ψ : Name → Nat) : Level.zero.eval ψ = 0 := by rfl

theorem denote_constK1z (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name} {l : Name}
    {ty : Expr} (hp : PinS env n [l] ty) :
    denote m.acval env ψ d (.const n [.zero]) = some (K m n) :=
  denote_constK1 m hp (by simp)

theorem denote_constK1p (m : EnvModel V env) {d : Nat} {n : Name} {l l' : Name}
    {ty : Expr} (hp : PinS env n [l] ty) :
    denote m.acval env ψ0 d (.const n [.param l']) = some (K m n) :=
  denote_constK1 m hp (by simp)

theorem denote_constK2z (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name} {l1 l2 : Name}
    {ty : Expr} (hp : PinS env n [l1, l2] ty) :
    denote m.acval env ψ d (.const n [.zero, .zero]) = some (K m n) :=
  denote_constK2 m hp (by simp) (by simp)

theorem denote_constK3z (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {n : Name}
    {l1 l2 l3 : Name} {ty : Expr} (hp : PinS env n [l1, l2, l3] ty) :
    denote m.acval env ψ d (.const n [.zero, .zero, .zero]) = some (K m n) :=
  denote_constK3 m hp (by simp) (by simp) (by simp)

/-- `2 ^ ·`'s head, as `BitVec`'s field type reads (`Rules.pow2E`). -/
@[expose] def powP (m : Name → (Name → Nat) → Term) : Term :=
  .app (.app (.app (.app (.app (m (nmL ["HPow", "hPow"]) ψ0) (m natName ψ0)) (m natName ψ0))
    (m natName ψ0))
    (.app (.app (.app (m (nmL ["instHPow"]) ψ0) (m natName ψ0)) (m natName ψ0))
      (.app (.app (m (nmL ["instPowNat"]) ψ0) (m natName ψ0)) (m (nmL ["instNatPowNat"]) ψ0))))
    (.app (.app (.app (m ofNatN ψ0) (m natName ψ0)) (numeralAV 2))
      (.app (m instOfNatNatN ψ0) (numeralAV 2)))

/-- `2 ^ x`, as `BitVec`'s field type reads (`Rules.pow2E`). -/
@[expose] def powT (m : Name → (Name → Nat) → Term) (x : Term) : Term := .app (powP m) x

-- `tX acv : Term`, the readings `simp` computes from the stored shapes
run_cmd Lean.Elab.Command.liftTermElabM do
  for (tag, c, val) in ConLeche.BVQ.shapeEntries do
    ConLeche.PinGen.BVShapes.spliceTermShape ConLeche.BVQ.shapeTables ``ψ0 ``powT
      ((`ConLeche.Model).str ("t" ++ tag)) c val

theorem natN_eq_natName : natN = natName := by rfl

theorem natLitT_numeral (n : Nat) :
    natLitT (.const .natZero []) (.const .natSucc []) n = numeralAV n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natLitT, numeralAV, ih]

/-- The `Nat` block is stored (the pins), so literals read. -/
theorem natLit_ok (hpins : pinsOk env.find? env.findProj? = true) :
    ConLeche.natLitSupported env = true := by
  have h1 := BVUnsat.pinsOk_model hpins bvPin.Nat (by simp [bvModelPins])
  have h2 := BVUnsat.pinsOk_model hpins bvPin.NatZero (by simp [bvModelPins])
  have h3 := BVUnsat.pinsOk_model hpins bvPin.NatSucc (by simp [bvModelPins])
  rw [show bvPin.Nat = .ind natName [] (.sort (.succ .zero)) by rfl] at h1
  rw [show bvPin.NatZero = .ctor natZeroName [] (.const natName []) by rfl] at h2
  rw [show bvPin.NatSucc = .ctor natSuccName [] (.forallE (.const natName []) (.const natName []))
    by rfl] at h3
  simp only [pinOk] at h1 h2 h3
  unfold ConLeche.natLitSupported ConLeche.natIndOk ConLeche.natZeroOk ConLeche.natSuccOk
  split at h1 <;> split at h2 <;> split at h3 <;> simp_all

section
variable (mp : EnvModelM V μ env) (hpins : pinsOk env.find? env.findProj? = true)
include mp hpins

theorem acval_nat (ψ : Name → Nat) : mp.base2.acval natName ψ = .const .nat [] := by
  obtain ⟨ci, hf, -, -⟩ := BVQ.pin_Nat hpins
  exact mp.base2.acval_pinned hf (by decide) (by simp +decide [pinnedStructT])

theorem acval_natZero (ψ : Name → Nat) : mp.base2.acval natZeroName ψ = .const .natZero [] := by
  obtain ⟨ci, hf, -, -⟩ := BVQ.pin_NatZero hpins
  exact mp.base2.acval_pinned hf (by decide) (by simp +decide [pinnedStructT])

theorem acval_natSucc (ψ : Name → Nat) : mp.base2.acval natSuccName ψ = .const .natSucc [] := by
  obtain ⟨ci, hf, -, -⟩ := BVQ.pin_NatSucc hpins
  exact mp.base2.acval_pinned hf (by decide) (by simp +decide [pinnedStructT])

/-- `Eq` is stored (it occurs in `Unsat`'s stored value), as the basis pin. -/
theorem eq_stored : env.find? eqName = some eqA := by
  obtain ⟨cvS, hS, hfS, hlS, htS⟩ := BVUnsat.pin_Unsat_shape hpins
  have hdefS := mp.defn_reads ψ0 cvS ConLeche.unsatValE ⟨hS, Env.find?_mem hfS⟩
  obtain ⟨ciEq, hfEq⟩ : ∃ ci, env.find? eqName = some ci := by
    obtain ⟨-, b0, -, hb0, -⟩ := denote_lam_inv hdefS
    simp [Expr.instantiate1] at hb0
    obtain ⟨-, b1, -, hb1, -⟩ := denote_forallE_inv hb0
    simp [Expr.instantiate1] at hb1
    obtain ⟨f1, -, hf1, -, -⟩ := denote_app_inv hb1
    obtain ⟨f2, -, hf2, -, -⟩ := denote_app_inv hf1
    obtain ⟨f3, -, hf3, -, -⟩ := denote_app_inv hf2
    rw [denote] at hf3
    cases hq : env.find? eqName with
    | none => rw [hq] at hf3; exact nomatch hf3
    | some ci => exact ⟨ci, rfl⟩
  have := (mp.base2.basis_pinned eqName ciEq hfEq (by decide)).1
  rw [hfEq, this]; simp [pinnedInfo]

theorem denote_eq1 (ψ : Name → Nat) (d : Nat) :
    denote mp.base2.acval env ψ d (.const eqName [.succ .zero]) =
      some (mp.base2.acval eqName (fun _ => 1)) := by
  rw [denote_const (eq_stored mp hpins) rfl]
  congr 1
  refine mp.base2.acval_params eqName _ (eq_stored mp hpins) _ _ fun p hp => ?_
  simp only [eqA, ConLeche.ConstantInfo.toConstantVal, List.mem_singleton] at hp ⊢
  subst hp
  simp [Level.substFn, Level.eval]

theorem denote_lit (ψ : Name → Nat) (d n : Nat) :
    denote mp.base2.acval env ψ d (.lit (.natVal n)) = some (numeralAV n) := by
  rw [denote_natLit (natLit_ok hpins), acval_natZero mp hpins, acval_natSucc mp hpins,
    natLitT_numeral]

theorem den_RArrayRec (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shRArrayRecTy = some (tRArrayRecTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tRArrayRecTy, shRArrayRecTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK1p mp.base2 (BVQ.pin_RArray hpins), denote_constK1p mp.base2 (BVQ.pin_RArrayLeaf hpins), denote_constK1p mp.base2 (BVQ.pin_RArrayBranch hpins)]

theorem den_PBVRec (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shPBVRecTy = some (tPBVRecTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tPBVRecTy, shPBVRecTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_PBV hpins), denote_constK0 mp.base2 (BVQ.pin_PBVMk hpins), denote_constK0 mp.base2 (BVQ.pin_BitVec hpins)]

theorem den_BitVecRec (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shBitVecRecTy = some (tBitVecRecTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tBitVecRecTy, powT, powP, shBitVecRecTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, denote_lit mp hpins, Level.eval, natN_eq_natName, Rules.pow2E, Expr.mkAppN, denote_constK0 mp.base2 (BVQ.pin_Fin hpins), denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_BitVec hpins), denote_constK0 mp.base2 (BVQ.pin_BitVecOfFin hpins), denote_constK0 mp.base2 (BVQ.pin_instNatPowNat hpins).choose_spec, denote_constK0 mp.base2 (BVQ.pin_instOfNatNat hpins).choose_spec, denote_constK1z mp.base2 (BVQ.pin_instPowNat hpins).choose_spec, denote_constK1z mp.base2 (BVQ.pin_ofNat hpins).choose_spec, denote_constK2z mp.base2 (BVQ.pin_instHPow hpins).choose_spec, denote_constK3z mp.base2 (BVQ.pin_hPow hpins).choose_spec]

theorem den_FinRec (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shFinRecTy = some (tFinRecTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tFinRecTy, shFinRecTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Fin hpins), denote_constK0 mp.base2 (BVQ.pin_FinMk hpins), denote_constK0 mp.base2 (BVQ.pin_instLTNat hpins), denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK1z mp.base2 (BVQ.pin_LTlt hpins)]

theorem den_Leaf (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shLeafTy = some (tLeafTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tLeafTy, shLeafTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK1p mp.base2 (BVQ.pin_RArray hpins)]

theorem den_Branch (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shBranchTy = some (tBranchTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tBranchTy, shBranchTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK1p mp.base2 (BVQ.pin_RArray hpins)]

theorem den_PBVMk (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shPBVMkTy = some (tPBVMkTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tPBVMkTy, shPBVMkTy, denote_forallE, denote_app, denote_fvar, Expr.instantiate1, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_PBV hpins), denote_constK0 mp.base2 (BVQ.pin_BitVec hpins)]

theorem den_OfFin (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shOfFinTy = some (tOfFinTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tOfFinTy, powT, powP, shOfFinTy, denote_forallE, denote_app, denote_fvar, Expr.instantiate1, denote_lit mp hpins, natN_eq_natName, Rules.pow2E, Expr.mkAppN, denote_constK0 mp.base2 (BVQ.pin_Fin hpins), denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_BitVec hpins), denote_constK0 mp.base2 (BVQ.pin_instNatPowNat hpins).choose_spec, denote_constK0 mp.base2 (BVQ.pin_instOfNatNat hpins).choose_spec, denote_constK1z mp.base2 (BVQ.pin_instPowNat hpins).choose_spec, denote_constK1z mp.base2 (BVQ.pin_ofNat hpins).choose_spec, denote_constK2z mp.base2 (BVQ.pin_instHPow hpins).choose_spec, denote_constK3z mp.base2 (BVQ.pin_hPow hpins).choose_spec]

theorem den_FinMk (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shFinMkTy = some (tFinMkTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tFinMkTy, shFinMkTy, denote_forallE, denote_app, denote_fvar, Expr.instantiate1, denote_constK0 mp.base2 (BVQ.pin_Fin hpins), denote_constK0 mp.base2 (BVQ.pin_instLTNat hpins), denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK1z mp.base2 (BVQ.pin_LTlt hpins)]

theorem den_leOfBle (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shleOfBleTy = some (tleOfBleTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tleOfBleTy, shleOfBleTy, denote_forallE, denote_app, denote_fvar, Expr.instantiate1, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_NatBle hpins), denote_constK0 mp.base2 (BVQ.pin_instLENat hpins).choose_spec, denote_constK0 mp.base2 (BVQ.pin_BoolTrue hpins), denote_constK1z mp.base2 (BVQ.pin_LEle hpins).choose_spec, denote_constK0 mp.base2 (BVQ.pin_Bool' hpins), denote_eq1 mp hpins]

theorem den_notLtOfLe (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shnotLtOfLeTy = some (tnotLtOfLeTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tnotLtOfLeTy, shnotLtOfLeTy, denote_forallE, denote_app, denote_fvar, Expr.instantiate1, denote_constK0 mp.base2 (BVQ.pin_instLTNat hpins), denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_instLENat hpins).choose_spec, denote_constK0 mp.base2 (BVQ.pin_Not hpins), denote_constK1z mp.base2 (BVQ.pin_LTlt hpins), denote_constK1z mp.base2 (BVQ.pin_LEle hpins).choose_spec]

theorem den_NotVal (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shNotVal = some (tNotVal mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tNotVal, shNotVal, denote_forallE, denote_lam, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_False hpins)]

theorem den_LTlt (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shLTltTy = some (tLTltTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tLTltTy, shLTltTy, denote_forallE, denote_app, denote_sort, denote_fvar, Expr.instantiate1, Level.eval, denote_constK1p mp.base2 (BVQ.pin_LTcls hpins).choose_spec]

theorem den_instLTNat (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shinstLTNatTy = some (tinstLTNatTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tinstLTNatTy, shinstLTNatTy, denote_app, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK1z mp.base2 (BVQ.pin_LTcls hpins).choose_spec]

theorem den_NatBle (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shNatBleTy = some (tNatBleTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tNatBleTy, shNatBleTy, denote_forallE, Expr.instantiate1, denote_constK0 mp.base2 (BVQ.pin_Nat hpins), denote_constK0 mp.base2 (BVQ.pin_Bool' hpins)]

omit hpins in
theorem den_RArrayTy (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shRArrayTy = some (tRArrayTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tRArrayTy, shRArrayTy, denote_forallE, denote_sort, Expr.instantiate1, Level.eval]

theorem den_BitVecTy (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shBitVecTy = some (tBitVecTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tBitVecTy, shBitVecTy, denote_forallE, denote_sort, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Nat hpins)]

theorem den_FinTy (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shFinTy = some (tFinTy mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tFinTy, shFinTy, denote_forallE, denote_sort, Expr.instantiate1, Level.eval, denote_constK0 mp.base2 (BVQ.pin_Nat hpins)]

theorem den_AssignmentVal (ψ : Name → Nat) (h0 : ∀ l, ψ l = 0) (d : Nat) :
    denote mp.base2.acval env ψ d shAssignmentVal = some (tAssignmentVal mp.base2.acval) := by
  obtain rfl : ψ = ψ0 := funext h0
  simp [tAssignmentVal, shAssignmentVal, denote_app, denote_constK0 mp.base2 (BVQ.pin_PBV hpins), denote_constK1z mp.base2 (BVQ.pin_RArray hpins)]


/-! ## The leaves' values -/

/-- A pinned constant's value (its leaf is closed). -/
noncomputable def kv (n : Name) : V := interp V (fun _ => pt) (K mp.base2 n)

omit hpins in
@[simp] theorem interp_K (ρ : Nat → V) (n : Name) : interp V ρ (K mp.base2 n) = kv mp n :=
  acval_interp_closed mp.base2 n ψ0 ρ _

theorem kv_nat : kv mp natName = (omega : V) := by
  simp only [kv, K, acval_nat mp hpins, interp_const, bval]

omit hpins in
theorem interp_powT (ρ : Nat → V) (x : Term) :
    interp V ρ (powT mp.base2.acval x) = interp V (cons (interp V ρ x) (fun _ => pt)) (powT mp.base2.acval (.bvar 0)) := by
  simp [powT, powP, interp_numeralAV]

/-- The value of `2 ^ w`. -/
noncomputable def powV (w : V) : V := interp V (cons w (fun _ => pt)) (powT mp.base2.acval (.bvar 0))

omit hpins in
@[simp] theorem interp_powT' (ρ : Nat → V) (x : Term) :
    interp V ρ (powT mp.base2.acval x) = powV mp (interp V ρ x) := interp_powT mp ρ x

/-- `v < n`'s value. -/
noncomputable def ltV (v n : V) : V :=
  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (kv mp ltN) omega) (kv mp instLTNatN)) v) n

omit hpins in
theorem memK {n : Name} {lps : List Name} {ty : Expr} {ta : Term} (hp : PinS env n lps ty)
    (hden : denote mp.base2.acval env ψ0 0 ty = some ta) :
    kv mp n ∈ˢ interp V (fun _ => pt) ta := by
  obtain ⟨ci, hf, -, rfl⟩ := hp
  have := mp.mem_type ci (Env.find?_mem hf) ψ0 ta hden (fun _ => pt)
  rwa [Env.find?_name hf, interp_K] at this

/-! ## The stored types, as memberships -/

theorem mem_RArray : kv mp rarrayN ∈ˢ piV (univ 1 : V) (fun _ => univ 1) := by
  have h := memK mp (BVQ.pin_RArray hpins) (den_RArrayTy mp ψ0 (fun _ => rfl) 0)
  simpa [tRArrayTy] using h

theorem mem_BitVec : kv mp bitVecN ∈ˢ piV (omega : V) (fun _ => univ 1) := by
  have h := memK mp (BVQ.pin_BitVec hpins) (den_BitVecTy mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tBitVecTy, kv_nat mp hpins] using h

theorem mem_Fin : kv mp finN ∈ˢ piV (omega : V) (fun _ => univ 1) := by
  have h := memK mp (BVQ.pin_Fin hpins) (den_FinTy mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tFinTy, kv_nat mp hpins] using h

theorem mem_PBV : kv mp Rules.packedBVName ∈ˢ (univ 1 : V) := by
  have h := memK mp (BVQ.pin_PBV hpins) (by simp [denote_sort, Level.eval] :
    denote mp.base2.acval env ψ0 0 (.sort (.succ .zero)) = some (.sort 1))
  simpa using h

theorem mem_Nat : (omega : V) ∈ˢ (univ 1 : V) := by
  have h := memK mp (BVQ.pin_Nat hpins) (by simp [denote_sort, Level.eval] :
    denote mp.base2.acval env ψ0 0 (.sort (.succ .zero)) = some (.sort 1))
  simpa [kv_nat mp hpins] using h

theorem mem_Leaf : kv mp Rules.rarrayLeafName ∈ˢ
    piV (univ 1 : V) (fun A => piV A (fun _ => SetTheory.app (kv mp rarrayN) A)) := by
  have h := memK mp (BVQ.pin_RArrayLeaf hpins) (den_Leaf mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tLeafTy] using h

theorem mem_Branch : kv mp Rules.rarrayBranchName ∈ˢ
    piV (univ 1 : V) (fun A => piV (omega : V) (fun _ => piV (SetTheory.app (kv mp rarrayN) A)
      (fun _ => piV (SetTheory.app (kv mp rarrayN) A) (fun _ => SetTheory.app (kv mp rarrayN) A)))) := by
  have h := memK mp (BVQ.pin_RArrayBranch hpins) (den_Branch mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tBranchTy, kv_nat mp hpins] using h

theorem mem_PBVMk : kv mp Rules.packedBVMkName ∈ˢ
    piV (omega : V) (fun w => piV (SetTheory.app (kv mp bitVecN) w) (fun _ => kv mp Rules.packedBVName)) := by
  have h := memK mp (BVQ.pin_PBVMk hpins) (den_PBVMk mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tPBVMkTy, kv_nat mp hpins] using h

theorem mem_OfFin : kv mp Rules.bvOfFinName ∈ˢ
    piV (omega : V) (fun w => piV (SetTheory.app (kv mp finN) (powV mp w))
      (fun _ => SetTheory.app (kv mp bitVecN) w)) := by
  have h := memK mp (BVQ.pin_BitVecOfFin hpins) (den_OfFin mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tOfFinTy, kv_nat mp hpins] using h

theorem mem_FinMk : kv mp Rules.finMkName ∈ˢ
    piV (omega : V) (fun n => piV (omega : V) (fun v => piV (ltV mp v n)
      (fun _ => SetTheory.app (kv mp finN) n))) := by
  have h := memK mp (BVQ.pin_FinMk hpins) (den_FinMk mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tFinMkTy, kv_nat mp hpins, ltV] using h

theorem mem_LTlt : kv mp ltN ∈ˢ
    piV (univ 1 : V) (fun A => piV (SetTheory.app (kv mp ltClassN) A) (fun _ =>
      piV A (fun _ => piV A (fun _ => (univ 0 : V))))) := by
  have h := memK mp (BVQ.pin_LTlt hpins) (den_LTlt mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tLTltTy] using h

theorem mem_instLTNat : kv mp instLTNatN ∈ˢ SetTheory.app (kv mp ltClassN) (omega : V) := by
  have h := memK mp (BVQ.pin_instLTNat hpins) (den_instLTNat mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tinstLTNatTy, kv_nat mp hpins] using h

/-- `v < n` at numbers is a proposition. -/
theorem ltV_mem {v n : V} (hv : v ∈ˢ (omega : V)) (hn : n ∈ˢ (omega : V)) :
    ltV mp v n ∈ˢ (univZero : V) := by
  have h1 := app_mem_piV (mem_LTlt mp hpins) (mem_Nat mp hpins)
  have h2 := app_mem_piV h1 (mem_instLTNat mp hpins)
  have h3 := app_mem_piV h2 hv
  have h4 := app_mem_piV h3 hn
  rw [univ_zero] at h4
  exact h4


/-! ## Induction at a `Prop` motive

A stored recursor inhabits its type; at the motive `fun X => truthVal (Q X)`
its minor premises are the point exactly when the constructor clauses of
`Q` hold, and its value at a member `X` inhabits `truthVal (Q X)`. -/

omit mp hpins in
theorem ptPi {A : V} {B : V → V} (h : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ B x) :
    piV A B ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ piV A B :=
  ⟨piV_mem_univZero_of fun x hx => (h x hx).1, pt_mem_piV_of h⟩

omit mp hpins in
/-- The motive `fun X => truthVal (Q X)` on `R`. -/
theorem motive_mem (R : V) (Q : V → Prop) :
    lamV R (fun X => truthVal (Q X)) ∈ˢ piV R (fun _ => (univ 0 : V)) :=
  lamV_mem (fun _ _ => by rw [univ_zero]; exact truthVal_mem_univZero _) (fun _ _ => IsTy_univ 0)

omit mp hpins in
theorem motive_app {R X : V} (Q : V → Prop) (hX : X ∈ˢ R) :
    SetTheory.app (lamV R (fun X => truthVal (Q X))) X = truthVal (Q X) := app_lamV hX

theorem rarray_ind (Q : V → Prop) {A : V} (hA : A ∈ˢ (univ 1 : V))
    (hl : ∀ a, a ∈ˢ A → Q (SetTheory.app (SetTheory.app (kv mp Rules.rarrayLeafName) A) a))
    (hb : ∀ p, p ∈ˢ (omega : V) → ∀ l, l ∈ˢ SetTheory.app (kv mp rarrayN) A →
      ∀ r, r ∈ˢ SetTheory.app (kv mp rarrayN) A → Q l → Q r →
      Q (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (kv mp Rules.rarrayBranchName) A) p) l) r)) :
    ∀ X, X ∈ˢ SetTheory.app (kv mp rarrayN) A → Q X := by
  intro X hX
  have hm := memK mp (BVQ.pin_RArrayRec hpins) (den_RArrayRec mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tRArrayRecTy, interp_pi, interp_app, interp_bvar, interp_sort, cons_zero, cons_succ,
    interp_K, kv_nat mp hpins] at hm
  have hlf : ∀ a, a ∈ˢ A → SetTheory.app (SetTheory.app (kv mp Rules.rarrayLeafName) A) a ∈ˢ
      SetTheory.app (kv mp rarrayN) A := fun a ha => by
    have h1 := app_mem_piV (mem_Leaf mp hpins) hA
    have h2 := app_mem_piV h1 ha
    exact h2
  have hbr : ∀ p, p ∈ˢ (omega : V) → ∀ l, l ∈ˢ SetTheory.app (kv mp rarrayN) A →
      ∀ r, r ∈ˢ SetTheory.app (kv mp rarrayN) A →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (kv mp Rules.rarrayBranchName) A) p) l) r ∈ˢ SetTheory.app (kv mp rarrayN) A :=
    fun p hp l hl' r hr => by
      have h1 := app_mem_piV (mem_Branch mp hpins) hA
      have h2 := app_mem_piV h1 hp
      have h3 := app_mem_piV h2 hl'
      have h4 := app_mem_piV h3 hr
      exact h4
  have h1 := app_mem_piV hm hA
  have h2 := app_mem_piV h1 (motive_mem (SetTheory.app (kv mp rarrayN) A) Q)
  have h3 := app_mem_piV h2 (pt_mem_piV_of fun a ha => by
    rw [motive_app Q (hlf a ha)]
    exact ⟨truthVal_mem_univZero _, pt_mem_truthVal (hl a ha)⟩)
  have h4 := app_mem_piV h3 (pt_mem_piV_of fun p hp => ptPi fun l hl' => ptPi fun r hr =>
    ptPi fun x hx => ptPi fun y hy => by
      rw [motive_app Q hl'] at hx
      rw [motive_app Q hr] at hy
      rw [motive_app Q (hbr p hp l hl' r hr)]
      exact ⟨truthVal_mem_univZero _,
        pt_mem_truthVal (hb p hp l hl' r hr (of_mem_truthVal hx) (of_mem_truthVal hy))⟩)
  have h5 := app_mem_piV h4 hX
  rw [motive_app Q hX] at h5
  exact of_mem_truthVal h5


theorem pbv_ind (Q : V → Prop)
    (hmk : ∀ w, w ∈ˢ (omega : V) → ∀ b, b ∈ˢ SetTheory.app (kv mp bitVecN) w →
      Q (SetTheory.app (SetTheory.app (kv mp Rules.packedBVMkName) w) b)) :
    ∀ X, X ∈ˢ kv mp Rules.packedBVName → Q X := by
  intro X hX
  have hm := memK mp (BVQ.pin_PBVRec hpins) (den_PBVRec mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tPBVRecTy, interp_pi, interp_app, interp_bvar, interp_sort, cons_zero, cons_succ,
    interp_K, kv_nat mp hpins] at hm
  have hmkM : ∀ w, w ∈ˢ (omega : V) → ∀ b, b ∈ˢ SetTheory.app (kv mp bitVecN) w →
      SetTheory.app (SetTheory.app (kv mp Rules.packedBVMkName) w) b ∈ˢ kv mp Rules.packedBVName :=
    fun w hw b hb => by
      have h1 := app_mem_piV (mem_PBVMk mp hpins) hw
      have h2 := app_mem_piV h1 hb
      exact h2
  have h1 := app_mem_piV hm (motive_mem (kv mp Rules.packedBVName) Q)
  have h2 := app_mem_piV h1 (pt_mem_piV_of fun w hw => ptPi fun b hb => by
    rw [motive_app Q (hmkM w hw b hb)]
    exact ⟨truthVal_mem_univZero _, pt_mem_truthVal (hmk w hw b hb)⟩)
  have h3 := app_mem_piV h2 hX
  rw [motive_app Q hX] at h3
  exact of_mem_truthVal h3

theorem bitvec_ind (Q : V → Prop) {w : V} (hw : w ∈ˢ (omega : V))
    (hof : ∀ f, f ∈ˢ SetTheory.app (kv mp finN) (powV mp w) →
      Q (SetTheory.app (SetTheory.app (kv mp Rules.bvOfFinName) w) f)) :
    ∀ X, X ∈ˢ SetTheory.app (kv mp bitVecN) w → Q X := by
  intro X hX
  have hm := memK mp (BVQ.pin_BitVecRec hpins) (den_BitVecRec mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tBitVecRecTy, interp_pi, interp_app, interp_bvar, interp_sort, cons_zero, cons_succ,
    interp_K, kv_nat mp hpins, interp_powT'] at hm
  have hofM : ∀ f, f ∈ˢ SetTheory.app (kv mp finN) (powV mp w) →
      SetTheory.app (SetTheory.app (kv mp Rules.bvOfFinName) w) f ∈ˢ
        SetTheory.app (kv mp bitVecN) w :=
    fun f hf => by
      have h1 := app_mem_piV (mem_OfFin mp hpins) hw
      have h2 := app_mem_piV h1 hf
      exact h2
  have h0 := app_mem_piV hm hw
  have h1 := app_mem_piV h0 (motive_mem (SetTheory.app (kv mp bitVecN) w) Q)
  have h2 := app_mem_piV h1 (pt_mem_piV_of fun f hf => by
    rw [motive_app Q (hofM f hf)]
    exact ⟨truthVal_mem_univZero _, pt_mem_truthVal (hof f hf)⟩)
  have h3 := app_mem_piV h2 hX
  rw [motive_app Q hX] at h3
  exact of_mem_truthVal h3

theorem fin_ind (Q : V → Prop) {n : V} (hn : n ∈ˢ (omega : V))
    (hmk : ∀ v, v ∈ˢ (omega : V) → ∀ h, h ∈ˢ ltV mp v n →
      Q (SetTheory.app (SetTheory.app (SetTheory.app (kv mp Rules.finMkName) n) v) h)) :
    ∀ X, X ∈ˢ SetTheory.app (kv mp finN) n → Q X := by
  intro X hX
  have hm := memK mp (BVQ.pin_FinRec hpins) (den_FinRec mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tFinRecTy, interp_pi, interp_app, interp_bvar, interp_sort, cons_zero, cons_succ,
    interp_K, kv_nat mp hpins] at hm
  have hmkM : ∀ v, v ∈ˢ (omega : V) → ∀ h, h ∈ˢ ltV mp v n →
      SetTheory.app (SetTheory.app (SetTheory.app (kv mp Rules.finMkName) n) v) h ∈ˢ
        SetTheory.app (kv mp finN) n :=
    fun v hv h hh => by
      have h1 := app_mem_piV (mem_FinMk mp hpins) hn
      have h2 := app_mem_piV h1 hv
      have h3 := app_mem_piV h2 hh
      exact h3
  have h0 := app_mem_piV hm hn
  have h1 := app_mem_piV h0 (motive_mem (SetTheory.app (kv mp finN) n) Q)
  have h2 := app_mem_piV h1 (pt_mem_piV_of fun v hv => ptPi fun h hh => by
    rw [motive_app Q (hmkM v hv h hh)]
    exact ⟨truthVal_mem_univZero _, pt_mem_truthVal (hmk v hv h hh)⟩)
  have h3 := app_mem_piV h2 hX
  rw [motive_app Q hX] at h3
  exact of_mem_truthVal h3


/-! ## `False`, `Not`, `True.intro`, `Eq`, `Assignment` -/

theorem kv_false : kv mp falseName = (empty : V) := by
  obtain ⟨ci, hf, -, -⟩ := BVQ.pin_False hpins
  have h := mp.base2.acval_pinned (ψ := ψ0) (t := .const .empty [0]) hf (by decide)
    (by simp +decide [pinnedStructT])
  simp only [kv, K, h, interp_const, bval]

theorem kv_not : kv mp notN = lamV (univ 0 : V) (fun P => piV P (fun _ => (empty : V))) := by
  have hp := BVUnsat.pinsOk_model hpins bvPin.Not (by simp [bvModelPins])
  obtain ⟨cv, hint, hf, hl, -⟩ := BVUnsat.pin_defn hp
    (show bvPin.Not = .defn notN [] (.forallE (.sort .zero) (.sort .zero)) shNotVal by rfl)
  have hd := mp.defn_reads ψ0 cv shNotVal ⟨hint, Env.find?_mem hf⟩
  have hn : cv.name = notN := Env.find?_name hf
  rw [den_NotVal mp hpins ψ0 (fun _ => rfl) 0, hn] at hd
  have h := congrArg (interp V (fun _ => pt)) (Option.some.inj hd)
  simp only [tNotVal, interp_lam, interp_pi, interp_sort, interp_K, kv_false mp hpins] at h
  exact h.symm

theorem kv_assignment :
    kv mp Rules.bvAssignmentName = SetTheory.app (kv mp rarrayN) (kv mp Rules.packedBVName) := by
  have hp := BVUnsat.pinsOk_model hpins bvPin.Assignment (by simp [bvModelPins])
  obtain ⟨cv, hint, hf, hl, -⟩ := BVUnsat.pin_defn hp
    (show bvPin.Assignment = .defn Rules.bvAssignmentName [] (.sort (.succ .zero)) shAssignmentVal
      by rfl)
  have hd := mp.defn_reads ψ0 cv shAssignmentVal ⟨hint, Env.find?_mem hf⟩
  have hn : cv.name = Rules.bvAssignmentName := Env.find?_name hf
  rw [den_AssignmentVal mp hpins ψ0 (fun _ => rfl) 0, hn] at hd
  have h := congrArg (interp V (fun _ => pt)) (Option.some.inj hd)
  simp only [tAssignmentVal, interp_app, interp_K] at h
  exact h.symm

theorem kv_trueIntro : kv mp Rules.trueIntroName' = (pt : V) := by
  have h1 := memK mp (BVQ.pin_TrueIntro hpins) (denote_constK0 mp.base2 (d := 0) (BVQ.pin_True hpins))
  have h2 := memK mp (BVQ.pin_True hpins) (by simp [denote_sort, Level.eval] :
    denote mp.base2.acval env ψ0 0 (.sort .zero) = some (.sort 0))
  simp only [interp_K, interp_sort, univ_zero] at h1 h2
  exact eq_pt_of_mem_univZero h2 h1

theorem mem_Bool : kv mp boolName ∈ˢ (univ 1 : V) := by
  have h := memK mp (BVQ.pin_Bool' hpins) (by simp [denote_sort, Level.eval] :
    denote mp.base2.acval env ψ0 0 (.sort (.succ .zero)) = some (.sort 1))
  simpa using h

theorem mem_BoolTrue : kv mp boolTrueName ∈ˢ kv mp boolName := by
  have h := memK mp (BVQ.pin_BoolTrue hpins) (denote_constK0 mp.base2 (d := 0) (BVQ.pin_Bool' hpins))
  simpa using h

theorem mem_NatBle : kv mp natBleName ∈ˢ
    piV (omega : V) (fun _ => piV (omega : V) (fun _ => kv mp boolName)) := by
  have h := memK mp (BVQ.pin_NatBle hpins) (den_NatBle mp hpins ψ0 (fun _ => rfl) 0)
  simpa [tNatBleTy, kv_nat mp hpins] using h

/-- `Eq`'s leaf at `Bool`'s level. -/
noncomputable def kvEq : V := interp V (fun _ => pt) (mp.base2.acval eqName (fun _ => 1))

omit hpins in
@[simp] theorem interp_Eq1 (ρ : Nat → V) :
    interp V ρ (mp.base2.acval eqName (fun _ => 1)) = kvEq mp :=
  acval_interp_closed mp.base2 eqName _ ρ _

/-! ## The `<` bound -/

/-- **A member of `⟦j < M⟧` at numerals forces `j < M`**: otherwise
`Nat.le_of_ble_eq_true` at `Nat.ble M j = true` (the literal row) and
`Nat.not_lt_of_le` give a member of `⟦False⟧ = ∅`. -/
theorem lt_of_ltV {φ : Name → Nat} (hop : Rules.NatOpRow mp.base2 φ) {j M : Nat} {h : V}
    (hh : h ∈ˢ ltV mp (vnat j) (vnat M)) : j < M := by
  refine Classical.byContradiction fun hlt => ?_
  have hle : M ≤ j := Nat.le_of_not_lt hlt
  -- `Nat.ble M j` reads to `true`
  have hS : ConLeche.natOpStored env natBleName = true := by
    have hp := BVUnsat.pinsOk_model hpins bvPin.NatBle (by simp [bvModelPins])
    obtain ⟨v, e⟩ : ∃ v, bvPin.NatBle = .defn natBleName [] shNatBleTy v := ⟨_, by rfl⟩
    rw [e] at hp
    simp only [pinOk] at hp
    unfold ConLeche.natOpStored
    split at hp
    · rename_i cv v' hint hf; rw [hf]
    · exact nomatch hp
  have hden : denote mp.base2.acval env φ 0
      (.app (.app (.const natBleName []) (.lit (.natVal M))) (.lit (.natVal j))) =
      some (.app (.app (K mp.base2 natBleName) (numeralAV M)) (numeralAV j)) := by
    simp [denote_app, denote_constK0 mp.base2 (BVQ.pin_NatBle hpins), denote_lit mp hpins]
  have hres : ConLeche.natOpResult natBleName M j = some (.const boolTrueName []) := by
    simp +decide [ConLeche.natOpResult, hle]
  obtain ⟨ra, hra, hval⟩ := hop (by simp [Rules.natBinOpNames]) hS rfl rfl hres hden
  rw [denote_constK0 mp.base2 (BVQ.pin_BoolTrue hpins)] at hra
  obtain rfl := Option.some.inj hra
  have hwd : WellDenoted V (fun _ => pt)
      (.app (.app (K mp.base2 natBleName) (numeralAV M)) (numeralAV j)) := by
    have h1 := app_mem_piV (mem_NatBle mp hpins) (vnat_mem_omega M)
    rw [WellDenoted_app, WellDenoted_app]
    refine ⟨⟨?_, numeralAV_wellDenoted M _, ?_⟩, numeralAV_wellDenoted j _, ?_⟩
    · exact mp.base2.acval_wellDenoted _ _ _
    · simp only [interp_K, interp_numeralAV]
      exact piV_slot (mem_NatBle mp hpins) (vnat_mem_omega M) IsTy_omega
    · simp only [interp_app, interp_K, interp_numeralAV]
      exact piV_slot h1 (vnat_mem_omega j) IsTy_omega
  have hble := (hval _ hwd).2
  simp only [interp_app, interp_K, interp_numeralAV] at hble
  -- the `Eq` member, hence a member of `⟦M ≤ j⟧`
  have hBm : SetTheory.app (SetTheory.app (kv mp natBleName) (vnat M)) (vnat j) ∈ˢ kv mp boolName := by
    have h1 := app_mem_piV (mem_NatBle mp hpins) (vnat_mem_omega M)
    have h2 := app_mem_piV h1 (vnat_mem_omega j)
    exact h2
  have hEq := (mp.eq_law (eq_stored mp hpins) (fun _ => 1)).1 (fun _ => pt) (kv mp boolName)
    _ _ (mem_Bool mp hpins) hBm (mem_BoolTrue mp hpins)
  simp only [interp_Eq1] at hEq
  have hm := memK mp (BVQ.pin_leOfBle hpins) (den_leOfBle mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tleOfBleTy, interp_pi, interp_app, interp_bvar, cons_zero, cons_succ, interp_K,
    interp_Eq1, kv_nat mp hpins] at hm
  have l1 := app_mem_piV hm (vnat_mem_omega M)
  have l2 := app_mem_piV l1 (vnat_mem_omega j)
  have l3 := app_mem_piV l2 (show (pt : V) ∈ˢ SetTheory.app (SetTheory.app (SetTheory.app (kvEq mp)
      (kv mp boolName)) (SetTheory.app (SetTheory.app (kv mp natBleName) (vnat M)) (vnat j)))
      (kv mp boolTrueName) by rw [hEq, hble]; exact pt_mem_eqv_self _)
  have hn := memK mp (BVQ.pin_notLtOfLe hpins) (den_notLtOfLe mp hpins ψ0 (fun _ => rfl) 0)
  simp only [tnotLtOfLeTy, interp_pi, interp_app, interp_bvar, cons_zero, cons_succ, interp_K,
    kv_nat mp hpins] at hn
  have n1 := app_mem_piV hn (vnat_mem_omega M)
  have n2 := app_mem_piV n1 (vnat_mem_omega j)
  have n3 := app_mem_piV n2 l3
  have hL : ltV mp (vnat j) (vnat M) ∈ˢ (univ 0 : V) := by
    rw [univ_zero]; exact ltV_mem mp hpins (vnat_mem_omega j) (vnat_mem_omega M)
  have n4 := n3
  rw [kv_not mp hpins] at n4
  change _ ∈ˢ SetTheory.app _ (ltV mp (vnat j) (vnat M)) at n4
  rw [app_lamV hL] at n4
  have n5 := app_mem_piV n4 hh
  exact not_mem_empty _ n5


/-! ## `2 ^ k` -/

omit hpins in
theorem powP_closed : Term.bvarsBelow 0 (powP mp.base2.acval) := by
  simp only [powP, Term.bvarsBelow]
  have := fun n => mp.base2.cval_closed n ψ0
  exact ⟨⟨⟨⟨⟨this _, this _⟩, this _⟩, this _⟩, ⟨⟨this _, this _⟩, this _⟩, ⟨this _, this _⟩, this _⟩,
    ⟨⟨this _, this _⟩, numeralAV_below 2 0⟩, this _, numeralAV_below 2 0⟩

omit mp hpins in
theorem wd_closed_cons {t : Term} (ht : Term.bvarsBelow 0 t) {ρ : Nat → V} {y : V}
    (h : WellDenoted V (cons y ρ) t) : WellDenoted V ρ t := by
  have e := (WellDenoted_liftN V 1 t 0 (cons y ρ)).mp
  rw [liftN_eq_self_of_closed ht 0 1, shiftE_succ_cons, shiftE_zero_zero] at e
  exact e h

theorem den_pow (ψ : Name → Nat) (d k : Nat) :
    denote mp.base2.acval env ψ d (Rules.pow2E (.lit (.natVal k))) =
      some (powT mp.base2.acval (numeralAV k)) := by
  simp [Rules.pow2E, Expr.mkAppN, denote_app, powT, powP, natN_eq_natName, denote_lit mp hpins,
    denote_constK0 mp.base2 (BVQ.pin_Nat hpins),
    denote_constK0 mp.base2 (BVQ.pin_instNatPowNat hpins).choose_spec,
    denote_constK0 mp.base2 (BVQ.pin_instOfNatNat hpins).choose_spec,
    denote_constK1z mp.base2 (BVQ.pin_instPowNat hpins).choose_spec,
    denote_constK1z mp.base2 (BVQ.pin_ofNat hpins).choose_spec,
    denote_constK2z mp.base2 (BVQ.pin_instHPow hpins).choose_spec,
    denote_constK3z mp.base2 (BVQ.pin_hPow hpins).choose_spec]

/-- **`2 ^ k` reads to its numeral**, from the rule's `2 ^ k ⟶ lit (2 ^ k)`. -/
theorem powV_vnat {φ : Name → Nat} {d : Nat} {ρ : Nat → V}
    (hpow : ∀ (k : Nat) (pk lk : Term),
      denote mp.base2.acval env φ d (Rules.pow2E (.lit (.natVal k))) = some pk →
      WellDenoted V ρ pk → interp V ρ pk ≠ pt →
      denote mp.base2.acval env φ d (.lit (.natVal (2 ^ k))) = some lk →
      interp V ρ pk = interp V ρ lk) (k : Nat) :
    powV mp (vnat k) = vnat (2 ^ k) := by
  -- `BitVec.ofFin`'s stored type is graded: `Fin (2 ^ w)` is, at `w = k`
  obtain ⟨ci, hf, hl, ht⟩ := BVQ.pin_BitVecOfFin hpins
  obtain ⟨ta, hta, hwdT, -⟩ := mp.constType (φ := ψ0) 0 Rules.bvOfFinName ci [] hf (by simp [hl])
  rw [hl, ht, show shOfFinTy.instantiateLevelParams [] [] = shOfFinTy by rfl,
    den_OfFin mp hpins ψ0 (fun _ => rfl) 0] at hta
  obtain rfl := Option.some.inj hta
  have hw := (hwdT ρ).1
  simp only [tOfFinTy, WellDenoted_pi, interp_K, kv_nat mp hpins] at hw
  have hw2 := (hw.2.2.1 (vnat k) (vnat_mem_omega k)).1
  rw [WellDenoted_app] at hw2
  obtain ⟨-, hwp, v, A, B, hFin, hpA, hv0, -⟩ := hw2
  simp only [powT, WellDenoted_app, interp_app, interp_bvar, cons_zero] at hwp hpA
  simp only [interp_K] at hFin
  have hP : WellDenoted V ρ (powP mp.base2.acval) := wd_closed_cons (powP_closed mp) hwp.1
  have hPi : ∀ ρ' : Nat → V, interp V ρ' (powP mp.base2.acval) = interp V ρ (powP mp.base2.acval) :=
    fun ρ' => interp_closed V (powP_closed mp) ρ' ρ
  have hpV : powV mp (vnat k) =
      SetTheory.app (interp V ρ (powP mp.base2.acval)) (vnat k) := by
    simp only [powV, powT, interp_app, interp_bvar, cons_zero, hPi]
  -- the slot of `Fin` pins its domain to `ω`, so `2 ^ k`'s value is a number
  have hFne : kv mp finN ≠ pt := fun h => by
    have h1 := app_mem_piV (mem_Fin mp hpins) (vnat_mem_omega 0)
    rw [h, app_pt] at h1
    exact ne_pt_of_mem_univ h1 rfl
  have hv : v ≠ 0 := fun h => hFne (eq_pt_of_mem_piR_zero (h ▸ hFin))
  have hFin' := mem_Fin mp hpins
  unfold piV at hFin'
  have hprop : propN (omega : V) (fun _ => (univ 1 : V)) ≠ 0 := fun h =>
    hFne (eq_pt_of_mem_piR_zero (h ▸ hFin'))
  have hA : A = omega := piR_dom_unique hv hprop hFin hFin'
  rw [hA] at hpA
  rw [hPi] at hpA
  rw [← hpV] at hpA
  have hne : powV mp (vnat k) ≠ pt := ne_pt_of_mem_strict strict_omega hpA
  have hwd : WellDenoted V ρ (powT mp.base2.acval (numeralAV k)) := by
    rw [powT, WellDenoted_app]
    refine ⟨hP, numeralAV_wellDenoted k ρ, ?_⟩
    obtain ⟨-, -, v', A', B', h1, h2, h3, h4⟩ := hwp
    refine ⟨v', A', B', ?_, ?_, h3, h4⟩
    · rwa [hPi] at h1
    · rw [interp_numeralAV]; exact h2
  have hval := hpow k _ _ (den_pow mp hpins φ d k) hwd
    (by rw [interp_powT', interp_numeralAV]; exact hne) (denote_lit mp hpins φ d (2 ^ k))
  rw [interp_powT', interp_numeralAV, interp_numeralAV] at hval
  exact hval


/-! ## The quotes read, graded, to the members -/

omit mp hpins in
theorem wd_app {ρ : Nat → V} {f a : Term} {F x A : V} {B : V → V}
    (hf : WellDenoted V ρ f ∧ interp V ρ f = F) (ha : WellDenoted V ρ a ∧ interp V ρ a = x)
    (hfm : F ∈ˢ piV A B) (ham : x ∈ˢ A) (hA : IsTy A) :
    WellDenoted V ρ (.app f a) ∧ interp V ρ (.app f a) = SetTheory.app F x := by
  obtain ⟨hf, rfl⟩ := hf
  obtain ⟨ha, rfl⟩ := ha
  rw [WellDenoted_app]
  exact ⟨⟨hf, ha, piV_slot hfm ham hA⟩, rfl⟩

omit hpins in
theorem wdK (ρ : Nat → V) (n : Name) :
    WellDenoted V ρ (K mp.base2 n) ∧ interp V ρ (K mp.base2 n) = kv mp n :=
  ⟨mp.base2.acval_wellDenoted _ _ _, interp_K mp ρ n⟩

omit mp hpins in
theorem wdN (ρ : Nat → V) (k : Nat) :
    WellDenoted V ρ (numeralAV k) ∧ interp V ρ (numeralAV k) = vnat k :=
  ⟨numeralAV_wellDenoted k ρ, interp_numeralAV k ρ⟩

omit mp in
theorem pin_Assignment' : PinS env Rules.bvAssignmentName [] (.sort (.succ .zero)) := by
  have hp := BVUnsat.pinsOk_model hpins bvPin.Assignment (by simp [bvModelPins])
  obtain ⟨cv, hint, hf, hl, ht⟩ := BVUnsat.pin_defn hp
    (show bvPin.Assignment = .defn Rules.bvAssignmentName [] (.sort (.succ .zero)) shAssignmentVal
      by rfl)
  exact ⟨_, hf, hl, ht⟩

theorem finQ_wd (ρ : Nat → V) (M j : Nat) (hlt : (pt : V) ∈ˢ ltV mp (vnat j) (vnat M)) :
    WellDenoted V ρ (.app (.app (.app (K mp.base2 Rules.finMkName) (numeralAV M)) (numeralAV j))
      (K mp.base2 Rules.trueIntroName')) ∧
    interp V ρ (.app (.app (.app (K mp.base2 Rules.finMkName) (numeralAV M)) (numeralAV j))
      (K mp.base2 Rules.trueIntroName')) =
      SetTheory.app (SetTheory.app (SetTheory.app (kv mp Rules.finMkName) (vnat M)) (vnat j))
        (kv mp Rules.trueIntroName') := by
  have h0 := mem_FinMk mp hpins
  have h1 := app_mem_piV h0 (vnat_mem_omega M)
  have h2 := app_mem_piV h1 (vnat_mem_omega j)
  have w1 := wd_app (wdK mp ρ _) (wdN ρ M) h0 (vnat_mem_omega M) IsTy_omega
  have w2 := wd_app w1 (wdN ρ j) h1 (vnat_mem_omega j) IsTy_omega
  exact wd_app w2 (wdK mp ρ _) h2 (by rw [kv_trueIntro mp hpins]; exact hlt)
    (Or.inl (ltV_mem mp hpins (vnat_mem_omega j) (vnat_mem_omega M)))

section
variable {φ : Name → Nat} {d : Nat} {ρ : Nat → V}

theorem finQ_ok (M j : Nat) (hlt : (pt : V) ∈ˢ ltV mp (vnat j) (vnat M)) :
    ∃ q, denote mp.base2.acval env φ d (finQE M j) = some q ∧ WellDenoted V ρ q ∧
      interp V ρ q = SetTheory.app (SetTheory.app (SetTheory.app (kv mp Rules.finMkName)
        (vnat M)) (vnat j)) pt := by
  refine ⟨.app (.app (.app (K mp.base2 Rules.finMkName) (numeralAV M)) (numeralAV j))
    (K mp.base2 Rules.trueIntroName'), ?_, ?_, ?_⟩
  · simp [finQE, denote_app, denote_lit mp hpins, denote_constK0 mp.base2 (BVQ.pin_FinMk hpins),
      denote_constK0 mp.base2 (BVQ.pin_TrueIntro hpins)]
  · exact (finQ_wd mp hpins ρ M j hlt).1
  · exact (finQ_wd mp hpins ρ M j hlt).2.trans (by rw [kv_trueIntro mp hpins])


variable (hop : Rules.NatOpRow mp.base2 φ)
    (hpow : ∀ (k : Nat) (pk lk : Term),
      denote mp.base2.acval env φ d (Rules.pow2E (.lit (.natVal k))) = some pk →
      WellDenoted V ρ pk → interp V ρ pk ≠ pt →
      denote mp.base2.acval env φ d (.lit (.natVal (2 ^ k))) = some lk →
      interp V ρ pk = interp V ρ lk)

include hop in
theorem fin_quote (M : Nat) : ∀ f, f ∈ˢ SetTheory.app (kv mp finN) (vnat M) →
    ∃ j, j < M ∧ ∃ q, denote mp.base2.acval env φ d (finQE M j) = some q ∧
      WellDenoted V ρ q ∧ interp V ρ q = f :=
  fin_ind mp hpins _ (vnat_mem_omega M) fun v hv h hh => by
    obtain ⟨j, rfl⟩ := mem_omega_iff.mp hv
    obtain rfl := eq_pt_of_mem_univZero (ltV_mem mp hpins hv (vnat_mem_omega M)) hh
    obtain ⟨q, hq, hw, hi⟩ := finQ_ok mp hpins (φ := φ) (d := d) (ρ := ρ) M j hh
    exact ⟨j, lt_of_ltV mp hpins hop hh, q, hq, hw, hi⟩

include hop hpow in
theorem bv_quote (k : Nat) : ∀ b, b ∈ˢ SetTheory.app (kv mp bitVecN) (vnat k) →
    ∃ (bv : BitVec k) (q : Term), denote mp.base2.acval env φ d (bvQE k bv) = some q ∧
      WellDenoted V ρ q ∧ interp V ρ q = b :=
  bitvec_ind mp hpins _ (vnat_mem_omega k) fun f hf => by
    have hpk := powV_vnat mp hpins hpow k
    have hf' := hf
    rw [hpk] at hf'
    obtain ⟨j, hj, qf, hqf, hwf, hif⟩ := fin_quote mp hpins (d := d) (ρ := ρ) hop (2 ^ k) f hf'
    refine ⟨BitVec.ofFin ⟨j, hj⟩, .app (.app (K mp.base2 Rules.bvOfFinName) (numeralAV k)) qf,
      ?_, ?_⟩
    · simp [bvQE, denote_app, denote_lit mp hpins, denote_constK0 mp.base2 (BVQ.pin_BitVecOfFin hpins),
        hqf]
    · have h0 := mem_OfFin mp hpins
      have h1 := app_mem_piV h0 (vnat_mem_omega k)
      have w1 := wd_app (wdK mp ρ _) (wdN ρ k) h0 (vnat_mem_omega k) IsTy_omega
      have hT : IsTy (SetTheory.app (kv mp finN) (powV mp (vnat k))) := by
        rw [hpk]; exact IsTy_of_mem_univ (app_mem_piV (mem_Fin mp hpins) (vnat_mem_omega _))
      exact wd_app w1 ⟨hwf, hif⟩ h1 hf hT

include hop hpow in
theorem pbv_quote : ∀ a, a ∈ˢ kv mp Rules.packedBVName →
    ∃ (p : Std.Tactic.BVDecide.BVExpr.PackedBitVec) (q : Term),
      denote mp.base2.acval env φ d (Rules.quotePacked p) = some q ∧
      WellDenoted V ρ q ∧ interp V ρ q = a :=
  pbv_ind mp hpins _ fun w hw b hb => by
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hw
    obtain ⟨bv, qb, hqb, hwb, hib⟩ := bv_quote mp hpins hop hpow k b hb
    refine ⟨{ w := k, bv := bv }, .app (.app (K mp.base2 Rules.packedBVMkName) (numeralAV k)) qb,
      ?_, ?_⟩
    · rw [quotePacked_eq]
      simp [denote_app, denote_lit mp hpins, denote_constK0 mp.base2 (BVQ.pin_PBVMk hpins), hqb]
    · have h0 := mem_PBVMk mp hpins
      have h1 := app_mem_piV h0 (vnat_mem_omega k)
      have w1 := wd_app (wdK mp ρ _) (wdN ρ k) h0 (vnat_mem_omega k) IsTy_omega
      exact wd_app w1 ⟨hwb, hib⟩ h1 hb
        (IsTy_of_mem_univ (app_mem_piV (mem_BitVec mp hpins) (vnat_mem_omega k)))

include hop hpow in
theorem assign_quote : ∀ X, X ∈ˢ SetTheory.app (kv mp rarrayN) (kv mp Rules.packedBVName) →
    ∃ (x : Std.Tactic.BVDecide.BVExpr.Assignment) (q : Term),
      denote mp.base2.acval env φ d (Rules.quoteAssign x) = some q ∧
      WellDenoted V ρ q ∧ interp V ρ q = X := by
  have hRA : IsTy (SetTheory.app (kv mp rarrayN) (kv mp Rules.packedBVName)) :=
    IsTy_of_mem_univ (app_mem_piV (mem_RArray mp hpins) (mem_PBV mp hpins))
  refine rarray_ind mp hpins _ (mem_PBV mp hpins) (fun a ha => ?_) (fun p hp l hl r hr Ql Qr => ?_)
  · obtain ⟨pv, qp, hqp, hwp, hip⟩ := pbv_quote mp hpins hop hpow a ha
    refine ⟨.leaf pv, .app (.app (K mp.base2 Rules.rarrayLeafName) (K mp.base2 Rules.packedBVName)) qp,
      ?_, ?_⟩
    · simp [Rules.quoteAssign, denote_app, denote_constK1z mp.base2 (BVQ.pin_RArrayLeaf hpins),
        denote_constK0 mp.base2 (BVQ.pin_PBV hpins), hqp]
    · have h0 := mem_Leaf mp hpins
      have h1 := app_mem_piV h0 (mem_PBV mp hpins)
      have w1 := wd_app (wdK mp ρ _) (wdK mp ρ _) h0 (mem_PBV mp hpins) (IsTy_univ 1)
      exact wd_app w1 ⟨hwp, hip⟩ h1 ha (IsTy_of_mem_univ (mem_PBV mp hpins))
  · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hp
    obtain ⟨xl, ql, hql, hwl, hil⟩ := Ql
    obtain ⟨xr, qr, hqr, hwr, hir⟩ := Qr
    refine ⟨.branch i xl xr, .app (.app (.app (.app (K mp.base2 Rules.rarrayBranchName)
      (K mp.base2 Rules.packedBVName)) (numeralAV i)) ql) qr, ?_, ?_⟩
    · simp [Rules.quoteAssign, denote_app, denote_constK1z mp.base2 (BVQ.pin_RArrayBranch hpins),
        denote_constK0 mp.base2 (BVQ.pin_PBV hpins), denote_lit mp hpins, hql, hqr]
    · have h0 := mem_Branch mp hpins
      have h1 := app_mem_piV h0 (mem_PBV mp hpins)
      have h2 := app_mem_piV h1 hp
      have h3 := app_mem_piV h2 hl
      have w1 := wd_app (wdK mp ρ _) (wdK mp ρ _) h0 (mem_PBV mp hpins) (IsTy_univ 1)
      have w2 := wd_app w1 (wdN ρ i) h1 hp IsTy_omega
      have w3 := wd_app w2 ⟨hwl, hil⟩ h2 hl hRA
      exact wd_app w3 ⟨hwr, hir⟩ h3 hr hRA

include hop hpow in
/-- **(1) Every member of `⟦Assignment⟧` is a quoted assignment.** -/
theorem assignQuote_of {A : Term}
    (hA : denote mp.base2.acval env φ d (.const Rules.bvAssignmentName []) = some A)
    (X : V) (hX : X ∈ˢ interp V ρ A) :
    ∃ (x : Std.Tactic.BVDecide.BVExpr.Assignment) (qa : Term),
      denote mp.base2.acval env φ d (Rules.quoteAssign x) = some qa ∧
      WellDenoted V ρ qa ∧ interp V ρ qa = X := by
  rw [denote_constK0 mp.base2 (pin_Assignment' hpins)] at hA
  obtain rfl := Option.some.inj hA
  rw [interp_K, kv_assignment mp hpins] at hX
  exact assign_quote mp hpins hop hpow X hX

end

end

end ConLeche.Model
