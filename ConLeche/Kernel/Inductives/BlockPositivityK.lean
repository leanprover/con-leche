module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Kernel.Inductives.PositivityK

@[expose] public section

/-!
# The block's positivity stage, key-named (PRIMREC / NESTKN-M5, UNWIRED)

`checkBlockPositivityK` is `checkBlockPositivity` (`BlockInstall.lean`) with
the key-named walk `nestBlockCtorsK` (`PositivityK.lean`) in place of the
path walk `nestBlockCtors`.  Nothing calls it; at the switch its body
becomes `checkBlockPositivity`'s and this module is deleted (DESIGN
"PRIMREC / NESTKN-M5").
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The block's positivity, key-named** (PRIMREC / NESTKN-M5, UNWIRED):
`checkBlockPositivity` with the key-named walk `nestBlockCtorsK`
(`PositivityK.lean`) in place of the path walk — the same result shape, the
same U2 pass on its normal forms.  The switch makes this the body of
`checkBlockPositivity` (DESIGN "PRIMREC / NESTKN-M5"). -/
def checkBlockPositivityK (ops : CheckerOps m) (env₁ : Env) (find? : Name → Option ConstantInfo)
    (consts : List ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (List (List NestFieldKind)) × List (List Expr) × NestNodes) := do
  let cvTa0 ← unwrapOr cvTas.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (openPisAtFvars p.nP cvTa0.type 0)
    (.internal "direct rec: type former telescope")
  let ctx : NestCtx := ⟨p.memberNames, p.lps, p.nP, p.nIdxs, pq.1, p.resSort, find?, consts⟩
  let holes ← unwrapOr (nestHoles ctx) (.internal "direct rec: a member is not a stored former")
  let (kinds, nfs, st) ← nestBlockCtorsK ops env₁ ctx holes ctorsAs
  checkAbsCtorTysAll ops env₁ ctx holes ctorsAs nfs
  pure (kinds, nfs, ⟨st.nodes.toList, nestMemberNfs ctx ctorsAs nfs ++ st.ctorNfs.toList⟩)

end ConLeche
