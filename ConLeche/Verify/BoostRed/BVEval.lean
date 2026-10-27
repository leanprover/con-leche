module

public import ConLeche.Verify.BoostRed.Boost
import ConLeche.Verify.BoostRed.BVGate
public import Std.Tactic.BVDecide
meta import ConLeche.Verify.BoostRed.Boost
meta import ConLeche.Verify.BoostRed.BVGate
-- `Nat.land`/`Nat.lor`/`Nat.xor` are in `eval`'s closure (the bitwise
-- `BitVec` operations); the translation reads their bodies.
import all Init.Data.Nat.Bitwise.Basic

/-!
# The boost of `BVLogicalExpr.eval` (task #368)
-/

public section

#boost Std.Tactic.BVDecide.BVLogicalExpr.eval

-- `eval`'s boost relation, from the checker's gate
#boost_assemble BoostLem.Std.Tactic.BVDecide.BVLogicalExpr.eval.D191958766 as
  ConLeche.Rules.BoostRed.bvEval_good

-- the numerals, the bit-vector literal and `2 ^ w`, from the gate
#boost_assemble BoostLem.OfNat.ofNat.D879300811 as ConLeche.Rules.BoostRed.bvOfNat_good
#boost_assemble BoostLem.instOfNatNat.D191958766 as ConLeche.Rules.BoostRed.bvInstOfNatNat_good
#boost_assemble BoostLem.BitVec.ofNat.D191958766 as ConLeche.Rules.BoostRed.bvBitVecOfNat_good
#boost_assemble BoostLem.HPow.hPow.D775553369 as ConLeche.Rules.BoostRed.bvHPow_good
#boost_assemble BoostLem.instHPow.D564800577 as ConLeche.Rules.BoostRed.bvInstHPow_good
#boost_assemble BoostLem.instPowNat.D879300811 as ConLeche.Rules.BoostRed.bvInstPowNat_good
#boost_assemble BoostLem.instNatPowNat.D191958766 as ConLeche.Rules.BoostRed.bvInstNatPowNat_good
