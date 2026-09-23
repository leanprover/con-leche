module

public import ConLeche.Kernel.Inductives.SumInstallF
import ConLeche.Kernel.Inductives.NativeInstall

@[expose] public section

/-!
# The direct recursive install, through the index (task #188)

`checkNative`'s recursor stage (`ConLeche/Kernel/Inductives/NativeInstall.lean`)
over an `FEnv`, the mirror the cached drivers run; the former's and
the constructors' stages are the sum route's mirrors.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkNativeRules` through the index. -/
def checkNativeRulesF (w : StructWalkers) (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && w.resolve feR rhs &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRulesF w feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- `checkNativeRec` through the index. -/
def checkNativeRecF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- the recursor pin (task #220), as in `checkNativeRec`
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && w.resolve fe recTy &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rhss ← checkNativeRulesF w feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- `checkBlockRecConform` through the index: the unverified,
reject-only recursor CONFORMANCE check (the one-member
generate-and-compare, `checkNativeRecF`), at ONE member with ONE
recursor; SKIPPED at `k ≥ 2`, where the kernel has no generator.  The
cached driver runs it after the recursor stage's check
(`checkBlockRecKS`), through `thenConform`.  It lives here, beside the
generator it runs, rather than with the block mirrors
(`BlockInstallF.lean`): those do not import the one-member mirror. -/
def checkBlockRecConformF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    (p : BlockParts) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m Unit :=
  match p.members, p.recs, cvTas, ctorsAs with
  | [_], [_], [cvTa], [ctorsA] => do
    let pn := p.toNative
    unless nativeRulesOk pn.cvR.name (pn.cvR.levelParams.map .param) .never pn.nP
        pn.ctors.length ctorsA pn.kinds pn.rhss pn.cvR.type do
      throw (.invalid "direct rec: recursor rules are not the generated ones")
    discard <| checkNativeRecF ops w fe pn cvTa ctorsA
  | _, _, _, _ => pure ()

end Mirrors

end ConLeche
