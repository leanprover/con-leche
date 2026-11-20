module

public import ConLeche.Kernel.Inductives.IotaRead
public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The ι reading rule, cached (task #622)

`blockReadsOk`'s twin (`ConLeche/Kernel/Inductives/IotaRead.lean`): the same reading with the
term walks that copy a term — instantiating levels, lifting, instantiating and dropping
variables — replaced by the cached tier's sharing-preserving ones (`instLevelParams`,
`liftLooseBVarsC`, `instantiateLiftC`, `dropVarsC`, `blockRecsC`); the comparisons are the specification's (`==` compares shared subterms once).
`blockReadsOkC_eq` (`ConLeche/Verify/Cached/IotaReadC.lean`) is its equation to the
specification.
-/

namespace ConLeche.Cached

open ConLeche

/-- `iotaPartsAt` over `instLevelParams` and `instantiateLiftC`. -/
def iotaPartsAtC (cvj : ConstantVal) (cnP : Nat) (mI rP : Nat) (rl : RecRule) :
    Option IotaParts := do
  let lvls := rl.ctorLevels cvj.levelParams
  let params := rl.iotaParams rP cnP
  let (_, ctorBody) ← (Expr.instLevelParams cvj.levelParams lvls cvj.type).stripPis cnP
  let (fieldDoms, concl) ← (Expr.instantiateLiftC ctorBody params.reverse).stripPis rl.nfields
  let indices := concl.getAppArgs.drop cnP
  guard (params.length = cnP ∧ rP ≤ mI ∧ indices.length = mI - rP)
  pure ⟨fieldDoms, indices, lvls, params⟩

/-- `iotaPartsOf` over `liftLooseBVarsC` and `dropVarsC`. -/
def iotaPartsOfC (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Option IotaParts := do
  let nF := rl.nfields
  let nIdx := mI - rP
  let (pre, doms, body, _) ← iotaFrame cv mI rP
  let .bvar k := body.getAppFn | none
  let q ← (minorsOf pre (rP + nIdx - k))[i]?
  let (fd, inner) ← (pre.getD q default).stripPis nF
  let .const _ us := (doms.getD nIdx default).getAppFn | none
  let args := (doms.getD nIdx default).getAppArgs
  pure ⟨fd.mapIdx (fun j d => Expr.liftLooseBVarsC (rP - q) d j),
    (inner.piTele.2.getAppArgs.take nIdx).map
      (fun a => Expr.liftLooseBVarsC (rP - q) (Expr.dropVarsC inner.piTele.1 a) nF),
    us, (args.take (args.length - nIdx)).map (Expr.dropVarsC nIdx)⟩

/-- `paramsAnnEq` over `instLevelParams`. -/
def paramsAnnEqC (find? : Name → Option ConstantInfo) (cvj : ConstantVal) (cnP : Nat)
    (cv : ConstantVal) (rl : RecRule) : Bool :=
  match cv.type.stripPis cnP,
    (Expr.instLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams) cvj.type).stripPis
      cnP with
  | some (rd, _), some (pd, _) => listRel (annEq find?) rd pd
  | _, _ => false

/-- `iotaPartsRel` over `paramsAnnEqC`. -/
def iotaPartsRelC (find? : Name → Option ConstantInfo) (cvj : ConstantVal) (cnP : Nat)
    (cv : ConstantVal) (rl : RecRule) (p' p : IotaParts) : Bool :=
  p'.idx == p.idx && p'.us == p.us && p'.params == p.params &&
    (listRel Expr.lvlEq p'.fieldDoms p.fieldDoms ||
      (rl.fire == .plain && paramsAnnEqC find? cvj cnP cv rl &&
        listRel (annEq find?) p'.fieldDoms p.fieldDoms))

/-- `ruleReadsB` over the cached readings. -/
def ruleReadsBC (find? : Name → Option ConstantInfo) (cv : ConstantVal) (mI rP i : Nat)
    (rl : RecRule) : Bool :=
  match iotaPartsOfC cv mI rP i rl, find? rl.ctor with
  | some p', some (.ctorInfo cvj cnP _ _) =>
    match iotaPartsAtC cvj cnP mI rP rl with
    | some p => iotaPartsRelC find? cvj cnP cv rl p' p
    | none => false
  | _, _ => false

/-- `recReadsOk` over `ruleReadsBC`. -/
def recReadsOkC (find? : Name → Option ConstantInfo) : ConstantInfo → Except CheckError Unit
  | .recInfo cv mI rP _ rules =>
    (rules.zipIdx).forM fun (rl, i) =>
      unless ruleReadsBC find? cv mI rP i rl do
        throw (.invalid s!"the recursor {cv.name}'s minor premise for {rl.ctor} does not \
          state the constructor's fields, indices and parameters as the constructor's type \
          does")
  | _ => pure ()

/-- `blockReadsOk` over `blockRecsC` and `recReadsOkC`. -/
def blockReadsOkC (find? : Name → Option ConstantInfo) (p : BlockShape) :
    Except CheckError Unit :=
  (blockRecsC p p.recs).forM (recReadsOkC find?)

end ConLeche.Cached
