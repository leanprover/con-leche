module

public import ConLeche.Kernel.Inductives.SumInstallF

@[expose] public section

/-!
# The uniform inductive install, through the index (milestone M5)

`checkBlock`'s stages (`ConLeche/Kernel/Inductives/BlockInstall.lean`)
over an `FEnv`, the mirrors the cached drivers run — the `F` twin of
every stage at every `k` (milestone M1's open item 2).  Each stage
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
    unless Level.isEquiv s s0 == some true do
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
def checkBlockCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (p : BlockShape) (ctx : NestCtx) :
    List (MemberShape × ConstantVal) →
      m (List (List (ConstantVal × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtorsF ops fe₀ fe ctx ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtorsF ops fe₀ fe p ctx rest
    pure (ctorsA :: restC, sortss :: restS)

/-- `checkBlockPass` through the index. -/
def checkBlockPassF (ops : CheckerOps m) (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    m (BlockPass FEnv × Bool) := do
  let (fe₁, cvTas, p₁) ← checkBlockIndsF ops fe p₀ isRec
  let pC := p₀.complete p₁
  let ctx ← unwrapOr (blockNestCtxOf pC.toBlockShape cvTas fe₁.find? fe₁.env.consts)
    (.internal "direct rec: type former telescope")
  let (ctorsAs, sortsss) ← checkBlockCtorsF ops fe₁ fe₁ pC.toBlockShape ctx
    (pC.members.zip cvTas)
  let kinds ← classifyBlockKinds pC.memberNames pC.lps pC.nP pC.nIdxs ctorsAs
  let p := pC.withKinds kinds
  pure (⟨fe₁, cvTas, p, ctorsAs, sortsss⟩,
    (List.range p.k).all fun i => blockCaps p i == blockCapsAt p₁ i isRec)

/-! ## Stage 2: the tail -/

/-- `blockOpenedOk` through the index. -/
def blockOpenedOkF (w : StructWalkers) (fe₀ : FEnv) (names : List Name) (lps : List Name)
    (nP : Nat) (nIdxs : List Nat) (cty : Expr) (nF : Nat) (ks : List BlockFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (w.resolve fe₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => w.resolve fe₀ x.fvarTypeD
        | some x, .recursive tgt =>
          decide (tgt < names.length) &&
          x.fvarTypeD.getAppFn == Expr.const (nameAt names tgt) (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdxAt nIdxs tgt &&
          (x.fvarTypeD.getAppArgs.drop nP).all (w.resolve fe₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive tgt =>
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            decide (tgt < names.length) &&
            afvs.length != 0 &&
            afvs.all (fun a => w.resolve fe₀ a.fvarTypeD) &&
            body.getAppFn == Expr.const (nameAt names tgt) (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdxAt nIdxs tgt &&
            (body.getAppArgs.drop nP).all (w.resolve fe₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- `blockMemberFieldsOk` through the index. -/
def blockMemberFieldsOkF (w : StructWalkers) (fe₀ : FEnv) (names : List Name) (lps : List Name)
    (nP : Nat) (nIdxs : List Nat) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List BlockFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && blockOpenedOkF w fe₀ names lps nP nIdxs cA.1.type cA.2 ks
    | _, _ => false

/-- `blockFieldsOk` through the index. -/
def blockFieldsOkF (w : StructWalkers) (fe₀ : FEnv) (names : List Name) (lps : List Name)
    (nP : Nat) (nIdxs : List Nat) (ctorsAs : List (List (ConstantVal × Nat)))
    (kinds : List (List (List BlockFieldKind))) : Bool :=
  ctorsAs.length == kinds.length &&
  (List.range ctorsAs.length).all fun mi =>
    match ctorsAs[mi]?, kinds[mi]? with
    | some ctorsA, some kss => blockMemberFieldsOkF w fe₀ names lps nP nIdxs ctorsA kss
    | _, _ => false

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

/-- `consBlockRecs` through the index. -/
def consBlockRecsF (find? : Name → Option ConstantInfo) (p : BlockShape) (nP : Nat) :
    Nat → List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cvRa, rhss, _nIdx, ctorsA) :: rest, fe =>
    consBlockRecsF find? p nP (m + 1) rest
      (fe.push (.recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m)
        (sumRules find? cvRa.name nP (p.majorIdxAt m) (p.rulePrefixAt m) cvRa.type ctorsA rhss)))

/-- The records `consBlockRecsF` pushes, in push order. -/
def blockRecInfosF (find? : Name → Option ConstantInfo) (p : BlockShape) (nP : Nat) :
    Nat → List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → List ConstantInfo
  | _, [] => []
  | m, (cvRa, rhss, _nIdx, ctorsA) :: rest =>
    .recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m)
        (sumRules find? cvRa.name nP (p.majorIdxAt m) (p.rulePrefixAt m) cvRa.type ctorsA rhss)
      :: blockRecInfosF find? p nP (m + 1) rest

/-- Push a list of records, head first. -/
def FEnv.pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => FEnv.pushAll rest (fe.push ci)

/-- **`consBlockRecsF`, every record built before the first push** (lane
LIN1).  The driver hands `consBlockRecsF` a `find?` that is a closure
over the very `FEnv` it pushes onto (`fe₂.find?`, `checkBlockTailS`);
threaded through the recursion, that closure holds the index at RC 2
across the first `FEnv.push`, which then copies the whole bucket array
— one full index copy per inductive block.  Here every record is read
first, the closure dies, and the pushes run on a unique index.  Same
value (`consBlockRecsF_eq_fast`, `@[csimp]`): `find?` is a parameter,
not the accumulated environment, so reading it early changes nothing. -/
def consBlockRecsFFast (find? : Name → Option ConstantInfo) (p : BlockShape) (nP : Nat)
    (m : Nat) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (fe : FEnv) : FEnv :=
  FEnv.pushAll (blockRecInfosF find? p nP m rs) fe

@[csimp] theorem consBlockRecsF_eq_fast : @consBlockRecsF = @consBlockRecsFFast := by
  funext find? p nP m rs fe
  induction rs generalizing m fe with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨cvRa, rhss, nIdx, ctorsA⟩ := r
    simp only [consBlockRecsF, consBlockRecsFFast, blockRecInfosF, FEnv.pushAll]
    exact ih (m + 1) _

/-! ## The recursor stage (milestone M5) -/

/-- `consBlockRecsBare` through the index. -/
def consBlockRecsBareF (p : BlockShape) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cvRa, _nIdx) :: rest, fe =>
    consBlockRecsBareF p (m + 1) rest
      (fe.push (.recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m) []))

/-!
The recursor stage has NO `F` twin here: its check is written once over
the index (`targetRecCheck`, `RecCheck.lean`, run by `checkBlockRecT` and
the cached `checkBlockRecS`); `consBlockRecsBareF` is the environment
holding the `k` rule-less recursors its rules are annotated at.
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
