module

public import ConLeche.Kernel.Inductives.SumInstall
public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# CONFORMANCE: the recursor generated and compared

**Not needed for soundness** (see `ConLeche/Conformance/RecGen.lean`).
`checkBlockRecConform` is the reject-only recursor conformance check
the fold runs after the primitive-recursion check
(`checkBlockRec = thenConform checkBlockRecK checkBlockRecConform`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`).  At a one-member,
one-recursor block it compares the stream's rules with the generated
ones (`nativeRulesOk`), then generates the recursor type, checks it and
compares it with the stream's by one `isDefEq` (`checkNativeRec`); the
results are discarded.  The index-threaded twin the cached driver runs
is `RecConformF.lean`; the bridges (the fueled and cached simulations)
are in `ConLeche/Verify/`.

**The recursor pin** (task #220): everything the stream's recursor
RECORD claims — its name, its level parameters, its argument sums, its
rules — is compared here, where a mismatch is `.invalid`.  Official
never reads the exported recursor as an input either: `add_inductive`
generates one and the replay compares the record with it structurally
(`checkPostponedRecursors`, `Lean4Checker/Replay.lean` — "Invalid
recursor", "No such recursor").
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- The generated rules for constructors `j, j+1, …` (`k` of them),
each scoped at the environment holding the recursor's constant
(`envR`): a rule mentions the recursor and is not inferred. -/
def checkNativeRules (envR : Env) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRules envR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- Stage 3: the recursor, generated and compared — the generated
type has the inductive-hypothesis binders in each minor
(`structRecTyR`); the generated rules are scoped at the environment
holding the recursor's constant. -/
def checkNativeRec (ops : CheckerOps m) (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- THE RECURSOR PIN (task #220), split off the type-and-constructor
  -- gate above and thrown here: official generates the recursor and its
  -- replay compares the exported record with the generated one
  -- structurally, so a record naming something other than the generated
  -- `T.rec` ("No such recursor") or contradicting it in its argument
  -- sums or its rules ("Invalid recursor") is INVALID INPUT
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let envR : Env := ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩
  let rhss ← checkNativeRules envR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- **The recursor CONFORMANCE check** (the maintainer's decision of
2026-09-23, lane CONF1): the one-member route's GENERATE-AND-COMPARE,
kept after the recursor stage became a check.

Unverified and reject-only: no proof consumes it, it only shrinks
the accept set (unlike the recursor name-set check `blockRecNameSetOk`,
which the proofs read).  Soundness comes from the primitive-recursion
check (`checkBlockRecK`), which runs FIRST (`checkBlockRec`),
so that the check is exercised on every block; this then brings the
verdict back to official's on a stream whose recursor is a valid
primitive recursion but not the one official generates (the argument
sums, the rule bodies, the recursor's type).

It is the old one-member route's generate-and-compare stage — the
stream's rules against the generated ones (`nativeRulesOk`), then the
recursor generated and compared (`checkNativeRec`) — with the results
discarded.

**Coverage: ONE member with ONE recursor only.**  For a mutual block
(`k ≥ 2`) the kernel has NO generator (the old route handed mutual
blocks to the untrusted modeller), so the check is SKIPPED there, and
such a block's recursors are held to the primitive-recursion check
and the records' pins (`checkBlockRecPins`) alone. -/
def checkBlockRecConform (ops : CheckerOps m) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) : m Unit :=
  match p.members, p.recs, cvTas, ctorsAs with
  | [_], [_], [cvTa], [ctorsA] => do
    let pn := p.toNative
    unless nativeRulesOk pn.cvR.name (pn.cvR.levelParams.map .param) .never pn.nP
        pn.ctors.length ctorsA pn.kinds pn.rhss pn.cvR.type do
      throw (.invalid "direct rec: recursor rules are not the generated ones")
    discard <| checkNativeRec ops env pn cvTa ctorsA
  | _, _, _, _ => pure ()

end ConLeche
