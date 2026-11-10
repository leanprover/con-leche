module

public import ConLeche.Cached.StateC
import ConLeche.Cached.CoreC

public section

/-!
# The ground engine's completeness at the `Bool.true` site (task #423)

The ground engine (`ConLeche/Cached/Ground4.lean`) answers the comparison
`t =?= Bool.true`, `t` closed, by evaluating `t`.  Without the fallback,
its answer is the comparison's (`g4SiteAnswer`).  Removing the fallback is
safe exactly when the engine never answers `false` where the incumbent's
reduction reaches `Bool.true`; this file states that property and proves
the parts that need no simulation.

* `siteEval`: the engine at the site, a fresh program, an explicit fuel.
* `SiteNeverFalse`: the incumbent's (cached, deterministic) `whnf` of a
  closed `t` reaching `Bool.true` excludes the engine's answer `false`.
* `SiteComplete`: the strong form — some fuel gives `true` — under the
  hypothesis that the incumbent's run meets no hand-back corner, phrased
  as `NoHandBack` (an engine run that does not stop at a hand-back
  reason).
* Proved here: the engine's answer is never a manufactured `true`
  (`g4SiteAnswer_eq_some_true`), and the literal fragment: the engine's
  `Nat` operation on two literals computes official's result
  (`g4NatVal_natOpResult`, `g4NatBool_natOpResult`), and its refusals are
  the cached core's (`g4NatPreRefuses_iff`, `g4SizeOver_natResultRefused`).

The proof plan for the rest (the simulation between the incumbent's
whnf states and the engine's states) is in DESIGN.md, `#423
completeness`.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-- **The engine at the site**: a fresh program (`{}`), fuel `fuel`, and the
answer without fallback (`none`: hand back to the incumbent). -/
def siteEval (fe : FEnv) (maxNat fuel : Nat) (t : Expr) : Option Bool :=
  let r := ground4BoolCoreF fe.find? fe.findProj? (natLitStoredF fe) (strLitStoredF fe) maxNat fuel
    {} t
  g4SiteAnswer r.1.1 r.1.2.2

/-- The engine's raw outcome (value or abort reason) at fuel `fuel`. -/
def siteRaw (fe : FEnv) (maxNat fuel : Nat) (t : Expr) : Option Bool × String :=
  let r := ground4BoolCoreF fe.find? fe.findProj? (natLitStoredF fe) (strLitStoredF fe) maxNat fuel
    {} t
  (r.1.1, r.1.2.2)

/-- The incumbent's `whnf` of `t` (the cached core's plain tower at fuel
`fuel`) reaches `Bool.true` from state `s`. -/
def IncumbentWhnfTrue (mode : CheckMode) (fe : FEnv) (fuel depth : Nat) (t : Expr)
    (s : CState) : Prop :=
  ∃ s', ((coreKnotI mode false fe fuel).whnf depth t).run s = .ok (.const boolTrueName [], s')

/-- **Completeness, weak form** (the property the fallback's removal
needs): where the incumbent's `whnf` of a closed `t` reaches `Bool.true`,
the engine at its own fuel does not answer `false` (it answers `true`, or
hands back). -/
def SiteNeverFalse : Prop :=
  ∀ (mode : CheckMode) (fe : FEnv) (fuel depth : Nat) (t : Expr) (s : CState),
    Expr.hasFvar t = false → Expr.looseBVarsBounded 0 t = true →
    IncumbentWhnfTrue mode fe fuel depth t s →
    siteEval fe s.maxNatSize groundFuel t ≠ some false

/-- The engine's run at fuel `n` stops at no hand-back reason. -/
def NoHandBack (fe : FEnv) (maxNat : Nat) (t : Expr) : Prop :=
  ∀ n, (siteRaw fe maxNat n t).2 ∉ ["refuse", "wf nat op", "black hole", "struct-eta major"]

/-- **Completeness, strong form**: where the incumbent's `whnf` of a closed
`t` reaches `Bool.true` and the engine meets no hand-back corner, some fuel
makes the engine answer `true`. -/
def SiteComplete : Prop :=
  ∀ (mode : CheckMode) (fe : FEnv) (fuel depth : Nat) (t : Expr) (s : CState),
    Expr.hasFvar t = false → Expr.looseBVarsBounded 0 t = true →
    IncumbentWhnfTrue mode fe fuel depth t s → NoHandBack fe s.maxNatSize t →
    ∃ n, siteEval fe s.maxNatSize n t = some true

/-! ## Proved: the answer map and the literal fragment -/

/-- The site's answer is `true` only where the engine computed `true`:
the no-fallback map turns aborts into `false` or a hand-back, never into
`true`. -/
theorem g4SiteAnswer_eq_some_true (r : Option Bool) (why : String) :
    g4SiteAnswer r why = some true ↔ r = some true := by
  cases r with
  | some b => simp [g4SiteAnswer]
  | none =>
    simp only [g4SiteAnswer, reduceCtorEq, iff_false]
    split <;> simp

/-- A value the engine computed is the site's answer. -/
theorem g4SiteAnswer_some (b : Bool) (why : String) : g4SiteAnswer (some b) why = some b := rfl

/-- The literal fragment, the `Nat`-valued operations: on two literals the
engine's `g4NatVal` is official's `natOpResult` (`reduce_bin_nat_op`), for
every operation index of `natBin14Names` but the two `Bool`-valued ones. -/
theorem g4NatVal_natOpResult (op a b : Nat) (hop : op < 14) (hk : op ≠ 4 ∧ op ≠ 5) :
    natOpResult (natBin14Names[op]!) a b = some (.lit (.natVal (g4NatVal op a b))) := by
  obtain ⟨h4, h5⟩ := hk
  match op, hop with
  | 0, _ | 1, _ | 2, _ | 3, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ =>
    simp [natOpResult, natBin14Names, g4NatVal, natPredName, natAddName, natSubName,
      natMulName, natPowName, natDivName, natModName, natGcdName, natLandName, natLorName,
      natXorName, natShiftLeftName, natShiftRightName, natBeqName, natBleName]
  | 4, _ => exact absurd rfl h4
  | 5, _ => exact absurd rfl h5

/-- The literal fragment, the `Bool`-valued operations (`beq`, `ble`): the
engine's `0`/`1` is official's constructor. -/
theorem g4NatBool_natOpResult (op a b : Nat) (hk : op = 4 ∨ op = 5) :
    natOpResult (natBin14Names[op]!) a b =
      some (.const (if g4NatVal op a b == 1 then boolTrueName else boolFalseName) []) := by
  rcases hk with rfl | rfl
  · by_cases h : a = b <;>
      simp [h, natOpResult, natBin14Names, g4NatVal, natPredName, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]
  · by_cases h : a ≤ b <;>
      simp [h, natOpResult, natBin14Names, g4NatVal, natPredName, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]

/-- The one-word fast path of the size test is the size test. -/
theorem g4SizeOver_eq (maxNat n : Nat) : g4SizeOver maxNat n = decide (natSizeBytes n > maxNat) := by
  unfold g4SizeOver
  split
  · rename_i h
    have hlog : n.log2 < 64 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hn)).mpr (by simpa [g4Word] using h)
    have : natSizeBytes n = 8 := by
      unfold natSizeBytes; rw [Nat.div_eq_of_lt hlog]
    simp [this]
  · simp

/-- The literal fragment, the maximum `Nat` size before computing: the
engine's refusal of `pow` (`3`) and `shiftLeft` (`12`) is the cached
core's (`natOpRefusal`). -/
theorem g4NatPreRefuses_iff (maxNat op a b : Nat) (hop : op = 3 ∨ op = 12) :
    g4NatPreRefuses maxNat op a b = true ↔ (natOpRefusal maxNat (natBin14Names[op]!) a b).isSome := by
  rcases hop with rfl | rfl
  · by_cases h1 : natCountMax < b <;> by_cases h2 : (1 < a ∧ ¬b = 0) ∧ maxNat / b < natSizeBytes a <;>
      simp_all [g4NatPreRefuses, natOpRefusal, natBin14Names, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]
    all_goals (split <;> simp_all <;> omega)
  · by_cases h0 : a = 0 <;> by_cases h1 : natCountMax < b <;>
      by_cases h2 : maxNat < natSizeBytes a + b / 8 + 1 <;>
      simp_all [g4NatPreRefuses, natOpRefusal, natBin14Names, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]
    all_goals (split <;> simp_all <;> omega)

/-- ... and no other operation refuses before computing. -/
theorem natOpRefusal_other (maxNat op a b : Nat) (hop : op < 14) (h : op ≠ 3 ∧ op ≠ 12) :
    natOpRefusal maxNat (natBin14Names[op]!) a b = none := by
  obtain ⟨h3, h12⟩ := h
  match op, hop with
  | 0, _ | 1, _ | 2, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 13, _ =>
    simp [natOpRefusal, natBin14Names, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]
  | 3, _ => exact absurd rfl h3
  | 12, _ => exact absurd rfl h12

/-- The literal fragment, the maximum `Nat` size after computing: the
engine's size test on the result of `add`, `sub`, `mul` is the cached
core's `natResultRefused`, and no other operation is refused there. -/
theorem g4SizeOver_natResultRefused (maxNat op a b : Nat) (hop : op < 14) (hk : op ≠ 4 ∧ op ≠ 5) :
    (op ≤ 2 && g4SizeOver maxNat (g4NatVal op a b)) =
      natResultRefused maxNat (natBin14Names[op]!) (.lit (.natVal (g4NatVal op a b))) := by
  obtain ⟨h4, h5⟩ := hk
  match op, hop with
  | 0, _ | 1, _ | 2, _ | 3, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ =>
    simp [g4SizeOver_eq, natResultRefused, natBin14Names, natAddName, natSubName, natMulName, natPowName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName,
      natShiftRightName, natBeqName, natBleName]
  | 4, _ => exact absurd rfl h4
  | 5, _ => exact absurd rfl h5

end ConLeche.Verify.Ground
