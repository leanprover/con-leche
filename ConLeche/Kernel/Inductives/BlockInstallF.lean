module

public import ConLeche.Kernel.Inductives.SumInstallF

@[expose] public section

/-!
# The uniform inductive install, through the index

`checkBlock`'s stages (`ConLeche/Kernel/Inductives/BlockInstall.lean`)
over an `FEnv`, the mirrors the cached drivers run — the `F` twin of
every stage at every `k`.  Each stage
differs from the pure one only in how the environment is read
(`w.resolve fe` for `Expr.constsResolve env`, `fe.push` for the
`consts` cons, `checkConstantValF` for `checkConstantVal`) and in
nothing else, so the cached agreements stay positional.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Stage 1: the formers -/

/-- `checkBlockTele` through the index. -/
def checkBlockTeleF (ops : CheckerOps m) (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    m (ConstantVal × Level) := do
  let cvTa₀ ← checkConstantValF ops fe ms.cvT
  let (cvTa, s) ← checkSumTeleF ops fe ms.cvT (nP + ms.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + ms.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  pure (cvTa, s)

/-- `checkBlockTeles` through the index. -/
def checkBlockTelesF (ops : CheckerOps m) (fe : FEnv) (nP : Nat) :
    List MemberShape → m (List (ConstantVal × Level))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTeleF ops fe nP ms
    let rs ← checkBlockTelesF ops fe nP rest
    pure (r :: rs)

/-- `checkBlockDomsAt` through the index. -/
def checkBlockDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtF ops fe off fvs doms j

/-- `checkBlockAgree` through the index. -/
def checkBlockAgreeF (ops : CheckerOps m) (fe : FEnv) (nP : Nat)
    (cvTa0 : ConstantVal) (s0 : Level) :
    List (ConstantVal × Level) → m Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (openPisAtFvars nP cvTa0.type 0)
      (.internal "block: type former telescope")
    let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq0.1.length do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtF ops fe 0 tq.1 (tq0.1.map Expr.fvarTypeD) nP
    unless ← liftFueled "level comparison" (Level.isEquiv s s0) do
      throw (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgreeF ops fe nP cvTa0 s0 rest

/-- `consBlockInds` through the index. -/
def consBlockIndsF (p₁ : BlockShape) (isRec : Bool) :
    List ConstantVal → Nat → FEnv → FEnv
  | [], _, fe => fe
  | cvTa :: rest, i, fe =>
    consBlockIndsF p₁ isRec rest (i + 1) (fe.push (.indInfo cvTa (blockCapsAt p₁ i isRec)))

/-- `checkBlockInds` through the index. -/
def checkBlockIndsF (ops : CheckerOps m) (fe : FEnv) (p : BlockParts) (isRec : Bool) :
    m (FEnv × List ConstantVal × BlockShape) :=
  match p.members with
  | [] => throw (.internal "block: no type former")
  | ms0 :: rest => do
    let (cvTa0, s0) ← checkBlockTeleF ops fe p.nP ms0
    let cvs ← checkBlockTelesF ops fe p.nP rest
    checkBlockAgreeF ops fe p.nP cvTa0 s0 cvs
    let p₁ := p.toBlockShape.withSort s0
    let cvTas := cvTa0 :: cvs.map (·.1)
    pure (consBlockIndsF p₁ isRec cvTas 0 fe, cvTas, p₁)

/-! ## Stage 1b: the constructors -/

/-- `checkBlockCtors` through the index. -/
def checkBlockCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (p : BlockShape) :
    List (MemberShape × ConstantVal) →
      m (List (List (ConstantVal × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtorsF ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtorsF ops fe₀ fe p rest
    pure (ctorsA :: restC, sortss :: restS)

/-! ## Stage 2: the tail -/

/-- `checkBlockIdxSorts` through the index. -/
def checkBlockIdxSortsF (ops : CheckerOps m) (fe₁ : FEnv) (p : BlockShape) :
    List (MemberShape × ConstantVal) → m (List (List Level))
  | [] => pure []
  | (ms, cvTa) :: rest => do
    let tq ← unwrapOr (openPisAtFvars (p.nP + ms.nIdx) cvTa.type 0)
      (.internal "direct rec: type former telescope")
    let isorts ← checkStructFieldSortsIF ops fe₁ true false p.resSort p.nP (tq.1.drop p.nP) []
      ms.nIdx
    let rest ← checkBlockIdxSortsF ops fe₁ p rest
    pure (isorts :: rest)

/-- `consBlockCtors` through the index. -/
def consBlockCtorsF (nP : Nat) : List (List (ConstantVal × Nat)) → FEnv → FEnv
  | [], fe => fe
  | ctorsA :: rest, fe => consBlockCtorsF nP rest (consSumCtorsF nP ctorsA fe)

/-- Push a list of records, head first. -/
def FEnv.pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => FEnv.pushAll rest (fe.push ci)

/-! ## The recursor stage -/

/-- `consBlockRecsBare` through the index. -/
def consBlockRecsBareF (p : BlockShape) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cvRa, _nIdx) :: rest, fe =>
    consBlockRecsBareF p (m + 1) rest
      (fe.push (.recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m) []))

/-!
The recursor stage has NO `F` twin here: it is written once over the
index (`genRecCheck`, `GenRec.lean`, run by `checkBlockRec` and by the
cached `checkBlockTailS`); `consBlockRecsBareF` is the environment
holding the rule-less recursors its rules are inferred at.
-/

/-! ## The tables and the install -/

/-- `checkBlockTables` through the index. -/
def checkBlockTablesF (w : StructWalkers) (p : BlockShape) :
    List (MemberShape × List (ConstantVal × Nat) × List (List Level)) → FEnv → m FEnv
  | [], fe => pure fe
  | (ms, ctorsA, sortss) :: rest, fe => do
    let fe' ←
      (match ctorsA, sortss with
       | [cA], [sorts] =>
         if ms.nIdx == 0 then
           checkStructProjTableF w ms.cvT.name cA.1.name p.lps p.nP cA.2 p.resSort
             (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe
         else pure fe
       | _, _ => pure fe)
    checkBlockTablesF w p rest fe'

end Mirrors

end ConLeche
