module

public import ConLeche.Kernel.Inductives.NativeInstallF
public import ConLeche.Kernel.Inductives.BlockInstall

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
def checkBlockCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (p : BlockShape) :
    List (MemberShape × ConstantVal) →
      m (List (List (ConstantVal × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtorsF ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtorsF ops fe₀ fe p rest
    pure (ctorsA :: restC, sortss :: restS)

/-- `checkBlockPass` through the index. -/
def checkBlockPassF (ops : CheckerOps m) (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    m (BlockPass FEnv × Bool) := do
  let (fe₁, cvTas, p₁) ← checkBlockIndsF ops fe p₀ isRec
  let pC := p₀.complete p₁
  let (ctorsAs, sortsss) ← checkBlockCtorsF ops fe₁ fe₁ pC.toBlockShape
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
          x.fvarTypeD.getAppFn == Expr.const (nameAt names tgt) (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdxAt nIdxs tgt &&
          (x.fvarTypeD.getAppArgs.drop nP).all (w.resolve fe₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive tgt =>
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
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
def consBlockRecsF (find? : Name → Option ConstantInfo) (nP rP : Nat) :
    List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, rhss, nIdx, ctorsA) :: rest, fe =>
    consBlockRecsF find? nP rP rest
      (fe.push (.recInfo cvRa (rP + nIdx) rP
        (sumRules find? cvRa.name nP (rP + nIdx) rP cvRa.type ctorsA rhss)))

/-! ## The recursor stage (milestone M5) -/

/-- `consBlockRecsBare` through the index. -/
def consBlockRecsBareF (rP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, nIdx) :: rest, fe =>
    consBlockRecsBareF rP rest (fe.push (.recInfo cvRa (rP + nIdx) rP []))

/-- `checkBlockRecTys` through the index. -/
def checkBlockRecTysF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (p : BlockShape)
    (mems : List (Name × Nat × Expr)) :
    List (MemberShape × ConstantVal) → Nat → m (List (ConstantVal × Nat))
  | [], _ => pure []
  | (ms, cvTa) :: rest, mi => do
    let cvRi ← checkConstantValF ops fe ms.cvR
    let recTy ← unwrapOr (blockRecTySpliced ms.cvT.name p.lps p.elim p.large p.nP p.k
        p.numCtors ms.nIdx mi cvTa.type mems cvRi.type)
      (.invalid "direct rec: the recursor's type does not have the generated telescope")
    unless recTy.allLevelParamsDefined ms.cvR.levelParams && w.resolve fe recTy &&
        recTy.looseBVarsBounded 0 && !recTy.hasFvar do
      throw (.internal "direct rec: recursor type scoping")
    let sty ← ops.inferType fe.env 0 recTy
    let _u ← ops.ensureSort fe.env 0 sty
    unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
      throw (.invalid "direct rec: recursor type is not the generated one")
    let rs ← checkBlockRecTysF ops w fe p mems rest (mi + 1)
    pure ((⟨ms.cvR.name, ms.cvR.levelParams, recTy⟩, ms.nIdx) :: rs)

/-- `checkBlockRule` through the index. -/
def checkBlockRuleF (ops : CheckerOps m) (w : StructWalkers) (feR : FEnv) (p : BlockShape)
    (recNames : List Name) (rlvls : List Level) (recTy : Expr) (mi : Nat)
    (cvR : ConstantVal) (cA : ConstantVal × Nat) (ks : List BlockFieldKind)
    (J : Nat) (rhs : Expr) : m Expr := do
  let nP := p.nP
  let k := p.k
  let N := p.numCtors
  let nF := cA.2
  unless rhs.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in rule of {cvR.name}")
  if rhs.hasFvar then
    throw (.invalid s!"free variable in rule of {cvR.name}")
  let rhsA ← ops.annotate feR.env 0 rhs
  unless rhsA.allLevelParamsDefined cvR.levelParams do
    throw (.invalid s!"undeclared universe parameter in rule of {cvR.name}")
  unless w.resolve feR rhsA do
    throw (unresolvedConstsError s!"rule of {cvR.name}" rhsA)
  unless blockRulePrefixOk cvR.type nP k N J nF rhsA do
    throw (.invalid s!"direct rec: the rule of {cA.1.name} does not bind the recursor's \
      parameters, motives, minor premises and the constructor's fields")
  let (_rbs, body) ← unwrapOr (rhsA.stripLams (nP + k + N + nF))
    (.invalid s!"direct rec: the rule of {cA.1.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  let fr : BlockRuleFrame :=
    { recNames := recNames, rlvls := rlvls, nIdxs := p.nIdxs, nP := nP, k := k, N := N,
      nF := nF, ks := ks,
      teleOf := structFieldTeleOf cA.1.type nP nF,
      idxOf := structFieldIdxOf cA.1.type nP nF,
      recIdx := blockRecIdxOf ks,
      pw := Level.zeronessOf (structElimLevel p.elim p.large) }
  let body'' ← unwrapOr (abstractIh fr 0 body)
    (.invalid s!"direct rec: the rule of {cA.1.name} is not a primitive recursion — a block \
      recursor occurs outside a call on a recursive field of this constructor")
  let (fvsPref, _) ← unwrapOr (openPisAtFvars (nP + k + N) recTy 0)
    (.internal "direct rec: recursor prefix telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsPref.take nP) cA.1.type)
    (.internal "direct rec: constructor parameter telescope")
  let (fvsF, cbody) ← unwrapOr (openPisAtFvars nF crest (nP + k + N))
    (.internal "direct rec: constructor field telescope")
  let ihTele := blockIhPis nF (k + N) fr.pw (blockTgtsOf ks) fr.teleOf fr.idxOf fr.recIdx 0 body''
  let (_fvsIh, bodyO) ← unwrapOr
    (openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse) (nP + k + N + nF))
    (.internal "direct rec: inductive-hypothesis telescope")
  let depth := nP + k + N + nF + fr.nR
  let tyB ← ops.inferType feR.env depth bodyO
  let motive ← unwrapOr fvsPref[nP + mi]? (.internal "direct rec: motive variable")
  let concl := Expr.mkAppN motive
    ((cbody.getAppArgs.drop nP) ++
      [Expr.mkAppN (.const cA.1.name (p.lps.map .param)) (fvsPref.take nP ++ fvsF)])
  unless ← ops.isDefEq feR.env depth tyB concl do
    throw (.invalid s!"direct rec: the rule of {cA.1.name} does not produce the minor's \
      conclusion")
  pure rhsA

/-- `checkBlockRules` through the index. -/
def checkBlockRulesF (ops : CheckerOps m) (w : StructWalkers) (feR : FEnv) (p : BlockShape)
    (recNames : List Name) (rlvls : List Level) (recTy : Expr) (mi : Nat) (cvR : ConstantVal) :
    List ((ConstantVal × Nat) × List BlockFieldKind) → List Expr → Nat → m (List Expr)
  | [], [], _ => pure []
  | (cA, ks) :: cs, rhs :: rhss, J => do
    let r ← checkBlockRuleF ops w feR p recNames rlvls recTy mi cvR cA ks J rhs
    let rest ← checkBlockRulesF ops w feR p recNames rlvls recTy mi cvR cs rhss (J + 1)
    pure (r :: rest)
  | _, _, _ =>
    throw (.invalid "direct rec: the recursor's rules do not cover its constructors")

/-- `checkBlockMembersRules` through the index. -/
def checkBlockMembersRulesF (ops : CheckerOps m) (w : StructWalkers) (feR : FEnv)
    (p : BlockParts) (recNames : List Name) (rlvls : List Level)
    (cvRas : List (ConstantVal × Nat)) :
    List ((MemberShape × List (ConstantVal × Nat)) × List (List BlockFieldKind)) → Nat →
      m (List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
  | [], _ => pure []
  | ((ms, ctorsA), kss) :: rest, mi => do
    let (cvRa, nIdx) ← unwrapOr cvRas[mi]? (.internal "direct rec: recursor record")
    let rhss ← checkBlockRulesF ops w feR p.toBlockShape recNames rlvls cvRa.type mi ms.cvR
      (ctorsA.zip kss) ms.rhss (p.offs mi)
    let rest' ← checkBlockMembersRulesF ops w feR p recNames rlvls cvRas rest (mi + 1)
    pure ((cvRa, rhss, nIdx, ctorsA) :: rest')

/-- The block's recursor names and the level arguments every
recursive call carries (the rule stage's two constants). -/
def blockRecCallData (p : BlockParts) : List Name × List Level :=
  (p.members.map (·.cvR.name),
    (p.members.head?.map fun ms => ms.cvR.levelParams.map Level.param).getD [])

/-!
`checkBlockRecK` itself has NO `F` twin: its two halves run at
DIFFERENT environments (the types at the block's, the rules at the one
holding the `k` rule-less recursors), and the cached operations are
built at a fixed index — so the cached driver composes
`checkBlockRecPins`, `checkBlockRecTysF`, `consBlockRecsBareF` and
`checkBlockMembersRulesF` itself, with its flush and a fresh
`sharedOpsC` in between (`ConLeche/Cached/CheckerC.lean`, the
arrangement `checkIndRecsS` uses for the modelled route).
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
