module

public import ConLeche.Cached.IotaReadC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# The cached ι reading rule is the specification's (task #622)
-/

namespace ConLeche.Cached

open ConLeche

theorem iotaPartsAtC_eq (cvj : ConstantVal) (cnP mI rP : Nat) (rl : RecRule) :
    iotaPartsAtC cvj cnP mI rP rl = iotaPartsAt cvj cnP mI rP rl := by
  simp only [iotaPartsAtC, iotaPartsAt, Expr.instantiateLiftC_spec]

theorem iotaPartsOfC_eq (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) :
    iotaPartsOfC cv mI rP i rl = iotaPartsOf cv mI rP i rl := by
  simp only [iotaPartsOfC, iotaPartsOf, Expr.liftLooseBVarsC_spec, Expr.dropVarsC_eq]
  rfl

theorem ruleReadsBC_eq (f : Name → Option ConstantInfo) (cv : ConstantVal) (mI rP i : Nat)
    (rl : RecRule) : ruleReadsBC f cv mI rP i rl = ruleReadsB f cv mI rP i rl := by
  simp only [ruleReadsBC, ruleReadsB, iotaPartsOfC_eq, iotaPartsAtC_eq]
  rfl

theorem recReadsOkC_eq (f : Name → Option ConstantInfo) :
    recReadsOkC f = recReadsOk f := by
  funext ci
  cases ci <;> simp only [recReadsOkC, recReadsOk, ruleReadsBC_eq]

theorem blockReadsOkC_eq (f : Name → Option ConstantInfo) (p : BlockShape) :
    blockReadsOkC f p = blockReadsOk f p := by
  simp only [blockReadsOkC, blockReadsOk, recReadsOkC_eq, blockRecsC_eq]

end ConLeche.Cached
