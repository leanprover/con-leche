module

public import ConLeche.Kernel.Inductives.NativeInstall
public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The uniform inductive install, at k members (milestone M1)

ONE installer over `BlockParts` (`ConLeche/Kernel/Inductives/BlockParts.lean`),
in official's order (`declare_inductive_types`, `check_constructors`,
`declare_recursors`, `inductive.cpp`):

0. the members' and the constructors' names are distinct;
1. **PASS**: every member's type former — the constant check,
   official's telescope loop (`checkSumTele`), the result sort — and,
   from member 1 on, official's two agreements (the parameter domains
   are definitionally member 0's; the result sorts are equivalent);
   THEN all k formers are consed at once (nothing of a constructor is
   looked at before every former is in the environment), the
   constructors are checked per member at THAT environment, and their
   fields are classified against the whole member list;
2. **TAIL**: the elimination restriction, the index binders' sorts, the
   kinds re-checked on the stored constructors, the constructors
   consed, the recursor stage, and the projection table at every
   structure-like member.

The recursor stage is milestone M5's: until then it is the one-member
stage (`checkNativeRec`, `ConLeche/Kernel/Inductives/NativeInstall.lean`)
at `k = 1` and a decline at `k ≥ 2` — which the route's gate
(`blockRouteK1Only`) makes unreachable.  Every stage agrees with the
one-member stage at `k = 1`
(`ConLeche/Verify/Inductives/BlockOneInstall.lean`), which is what lets
the run relation, the P tier and the cached mirrors keep their
one-member statements while the route is the k-ary one.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The capability record, per member -/

/-- **The capability record of member `m`** (`nativeCapsAt` at a
member): official's `is_structure_like` is `ncnstrs == 1 &&
nindices == 0 && !is_rec` with `is_rec` read over ALL constructors of
ALL members, so η and unit-likeness are the MEMBER's data at the
BLOCK's recursion verdict; rule K is official's `is_K_target`, which
requires `m_ind_types.size() == 1` — a one-member block. -/
def blockCapsAt (p : BlockShape) (mi : Nat) (isRec : Bool) : IndCaps :=
  match (p.members.getD mi default).ctors, (p.members.getD mi default).nIdx with
  | [c], nIdx =>
    { eta := nIdx == 0 && !p.isProp && !isRec
      etaCtor := c.1.name
      etaParams := p.nP
      etaFields := c.2
      unitlike := nIdx == 0 && c.2 == 0
      unitParams := p.nP
      ruleK := p.k == 1 && c.2 == 0 && p.isProp
      sortZ := Level.zeronessOf p.resSort }
  | _, _ => {}

/-- Official's `is_rec` off the classified kinds, BLOCK-wide: some
field of some constructor of some member is recursive or reflexive. -/
def blockIsRec (kinds : List (List (List BlockFieldKind))) : Bool :=
  kinds.any fun kss => kss.any fun ks => ks.any fun k =>
    match k with
    | .recursive _ => true
    | .reflexive _ => true
    | _ => false

/-- The block's capability record at member `mi`, at its classified
kinds. -/
def blockCaps (p : BlockParts) (mi : Nat) : IndCaps :=
  blockCapsAt p.toBlockShape mi (blockIsRec p.kinds)

/-- **The syntactic reading of `is_rec`** (task #268 at k members):
does SOME member of the block occur in SOME declared field domain of
SOME constructor of SOME member?  Official's `is_rec` is a `find` over
all constructors of all types (`inductive.cpp`), and the raw
occurrence is a superset of the classified verdict, which the pass's
own classification confirms.  Read only where the record depends on it
— a member with one constructor — as `blockCapsAt` does. -/
def blockRawRec (p : BlockParts) : Bool :=
  p.members.any fun ms =>
    match ms.ctors with
    | [c] =>
      match c.1.type.stripPis (p.nP + c.2) with
      | some (cbs, _) => (cbs.drop p.nP).any fun b => b.1.mentionsAnyConst p.memberNames
      | none => false
    | _ => false

/-! ## Stage 1: the formers -/

/-- One member's type former: the constant check, official's telescope
loop (task #195) and the result sort — `checkSumInd`'s body without
the environment cons, which at k members happens only once every
former has been checked. -/
def checkBlockTele (ops : CheckerOps m) (env : Env) (nP : Nat) (ms : MemberShape) :
    m (ConstantVal × Level) := do
  let cvTa₀ ← checkConstantVal ops env ms.cvT
  let (cvTa, s) ← checkSumTele ops env ms.cvT (nP + ms.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + ms.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  pure (cvTa, s)

/-- The members' type formers, in block order. -/
def checkBlockTeles (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List MemberShape → m (List (ConstantVal × Level))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTele ops env nP ms
    let rs ← checkBlockTeles ops env nP rest
    pure (r :: rs)

/-- **Official's two agreements between the members**
(`check_inductive_types`, `inductive.cpp`): every member's parameter
domains are DEFINITIONALLY member 0's, and every member's result sort
is equivalent to member 0's.  Both are REJECTS with official's
messages.  A one-member block reaches this with an empty list and is
not touched. -/
def checkBlockAgree (ops : CheckerOps m) (env : Env) (nP : Nat)
    (cvTa0 : ConstantVal) (s0 : Level) :
    List (ConstantVal × Level) → m Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (openPisAtFvars nP cvTa0.type 0)
      (.internal "block: type former telescope")
    let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    checkStructDomsAt ops env 0 tq.1 (tq0.1.map Expr.fvarTypeD) nP
    unless Level.isEquiv s s0 == some true do
      throw (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgree ops env nP cvTa0 s0 rest

/-- The members' formers consed, in block order (member 0 deepest),
each with ITS capability record at the block's `is_rec` verdict. -/
def consBlockInds (p₁ : BlockShape) (isRec : Bool) :
    List ConstantVal → Nat → Env → Env
  | [], _, env => env
  | cvTa :: rest, i, env =>
    consBlockInds p₁ isRec rest (i + 1) ⟨.indInfo cvTa (blockCapsAt p₁ i isRec) :: env.consts⟩

/-- **Stage 1**: the k type formers, checked, agreed and consed —
official's `declare_inductive_types`, which puts every former in the
environment before any constructor is looked at. -/
def checkBlockInds (ops : CheckerOps m) (env : Env) (p : BlockParts) (isRec : Bool) :
    m (Env × List ConstantVal × BlockShape) :=
  match p.members with
  | [] => throw (.internal "block: no type former")
  | ms0 :: rest => do
    let (cvTa0, s0) ← checkBlockTele ops env p.nP ms0
    let cvs ← checkBlockTeles ops env p.nP rest
    checkBlockAgree ops env p.nP cvTa0 s0 cvs
    let p₁ := p.toBlockShape.withSort s0
    let cvTas := cvTa0 :: cvs.map (·.1)
    pure (consBlockInds p₁ isRec cvTas 0 env, cvTas, p₁)

/-! ## Stage 1b: the constructors -/

/-- The constructors of every member, at the environment holding ALL
the formers (the resolution guard pointed at that same environment, as
the one-member stage does). -/
def checkBlockCtors (ops : CheckerOps m) (env₀ env : Env) (p : BlockShape) :
    List (MemberShape × ConstantVal) →
      m (List (List (ConstantVal × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtors ops env₀ env ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtors ops env₀ env p rest
    pure (ctorsA :: restC, sortss :: restS)

/-- **The fields' kinds, classified at install** on the stored
constructors — their field domains normalised by official's positivity
walk — against the WHOLE member list: a non-positive or non-valid
occurrence is INVALID, a nested one a positive decline. -/
def classifyMemberKinds (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (ctorsA : List (ConstantVal × Nat)) : m (List (List BlockFieldKind)) := do
  let kinds ← unwrapOr (ctorsA.mapM (blockCtorKinds names lps nP nIdxs))
    (.notImplemented "direct rec: constructor telescope")
  if kinds.any (fun ks => ks.any (· == .negative)) then
    throw (.invalid "direct rec: non positive or non valid occurrence of the inductive type")
  if kinds.any (fun ks => ks.any (· == .unsupported)) then
    throw (.notImplemented "direct rec: a nested occurrence of the block (not modeled here)")
  pure kinds

/-- The fields' kinds of every member, in block order. -/
def classifyBlockKinds (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat) :
    List (List (ConstantVal × Nat)) → m (List (List (List BlockFieldKind)))
  | [] => pure []
  | ctorsA :: rest => do
    let kss ← classifyMemberKinds names lps nP nIdxs ctorsA
    let rest' ← classifyBlockKinds names lps nP nIdxs rest
    pure (kss :: rest')

/-- **What one pass over the formers and the constructors yields**
(`NativePass` at k members). -/
structure BlockPass (E : Type) where
  /-- the environment holding all k formers, at the record the pass ran at -/
  env₁ : E
  /-- the annotated formers, in block order -/
  cvTas : List ConstantVal
  /-- the completed record: the sort read, the kinds classified -/
  p : BlockParts
  /-- the annotated (normalised) constructors, per member -/
  ctorsAs : List (List (ConstantVal × Nat))
  /-- the fields' sorts, per member, per constructor -/
  sortsss : List (List (List Level))

/-- **One pass over the formers and the constructors** at a given
`is_rec` verdict (task #268 at k members).  The last component says
whether the classification confirms the verdict the pass ran at. -/
def checkBlockPass (ops : CheckerOps m) (env : Env) (p₀ : BlockParts) (isRec : Bool) :
    m (BlockPass Env × Bool) := do
  let (env₁, cvTas, p₁) ← checkBlockInds ops env p₀ isRec
  let pC := p₀.complete p₁
  let (ctorsAs, sortsss) ← checkBlockCtors ops env₁ env₁ pC.toBlockShape
    (pC.members.zip cvTas)
  let kinds ← classifyBlockKinds pC.memberNames pC.lps pC.nP pC.nIdxs ctorsAs
  let p := pC.withKinds kinds
  pure (⟨env₁, cvTas, p, ctorsAs, sortsss⟩,
    (List.range p.k).all fun i => blockCaps p i == blockCapsAt p₁ i isRec)

/-! ## Stage 2: the tail -/

/-- The target member's name, read positionally.  A target out of
range cannot occur — the classification's targets are members of the
block — and reading member 0 there keeps the ONE-member reading exact
(`[T].getD tgt` would be a junk name at a junk target). -/
def nameAt (names : List Name) (tgt : Nat) : Name := names.getD tgt (names.headD default)

/-- The target member's index count (`nameAt`'s companion). -/
def nIdxAt (nIdxs : List Nat) (tgt : Nat) : Nat := nIdxs.getD tgt (nIdxs.headD 0)

/-- The kinds the recogniser computed, re-checked on one annotated
constructor type OPENED at variables (`nativeOpenedOk` at k members):
a recursive or reflexive field's domain is the TARGET member at the
opened parameter variables followed by that member's index
expressions. -/
def blockOpenedOk (env₀ : Env) (names : List Name) (lps : List Name) (nP : Nat)
    (nIdxs : List Nat) (cty : Expr) (nF : Nat) (ks : List BlockFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => x.fvarTypeD.constsResolve env₀
        | some x, .recursive tgt =>
          x.fvarTypeD.getAppFn == Expr.const (nameAt names tgt) (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdxAt nIdxs tgt &&
          (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive tgt =>
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => a.fvarTypeD.constsResolve env₀) &&
            body.getAppFn == Expr.const (nameAt names tgt) (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdxAt nIdxs tgt &&
            (body.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- The kinds, re-checked on every annotated constructor of one member. -/
def blockMemberFieldsOk (env₀ : Env) (names : List Name) (lps : List Name) (nP : Nat)
    (nIdxs : List Nat) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List BlockFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && blockOpenedOk env₀ names lps nP nIdxs cA.1.type cA.2 ks
    | _, _ => false

/-- The kinds, re-checked on every member's constructors. -/
def blockFieldsOk (env₀ : Env) (names : List Name) (lps : List Name) (nP : Nat)
    (nIdxs : List Nat) (ctorsAs : List (List (ConstantVal × Nat)))
    (kinds : List (List (List BlockFieldKind))) : Bool :=
  ctorsAs.length == kinds.length &&
  (List.range ctorsAs.length).all fun mi =>
    match ctorsAs[mi]?, kinds[mi]? with
    | some ctorsA, some kss => blockMemberFieldsOk env₀ names lps nP nIdxs ctorsA kss
    | _, _ => false

/-- Every member's INDEX binders' universes, exposed for the model's
index-tuple universe: the member's telescope opened at variables, each
index domain's sort inferred (no bound is checked — the sorts are
read, not compared). -/
def checkBlockIdxSorts (ops : CheckerOps m) (env₁ : Env) (p : BlockShape) :
    List (MemberShape × ConstantVal) → m (List (List Level))
  | [] => pure []
  | (ms, cvTa) :: rest => do
    let tq ← unwrapOr (openPisAtFvars (p.nP + ms.nIdx) cvTa.type 0)
      (.internal "direct rec: type former telescope")
    let isorts ← checkStructFieldSortsI ops env₁ true false p.resSort p.nP (tq.1.drop p.nP) []
      ms.nIdx
    let rest ← checkBlockIdxSorts ops env₁ p rest
    pure (isorts :: rest)

/-- The members' constructors consed, member by member, in block
order. -/
def consBlockCtors (nP : Nat) : List (List (ConstantVal × Nat)) → Env → Env
  | [], env => env
  | ctorsA :: rest, env => consBlockCtors nP rest (consSumCtors nP ctorsA env)

/-- The members' recursors consed with their rules, in block order.
`find?` is the environment holding the block's constructors (the
recursors' own records are not read by `recRuleBits`). -/
def consBlockRecs (find? : Name → Option ConstantInfo) (nP rP : Nat) :
    List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → Env → Env
  | [], env => env
  | (cvRa, rhss, nIdx, ctorsA) :: rest, env =>
    consBlockRecs find? nP rP rest
      ⟨.recInfo cvRa (rP + nIdx) rP
        (sumRules find? cvRa.name nP (rP + nIdx) rP cvRa.type ctorsA rhss) :: env.consts⟩

/-- **The recursor stage, milestone M1's interim**: at ONE member it is
the one-member stage — the stream's rules against the generated ones
(`nativeRulesOk`), then the recursor generated and compared
(`checkNativeRec`).  At two or more members it is a positive DECLINE
until milestone M5 replaces the whole stage by a CHECK; the route's
gate makes that arm unreachable in the meantime. -/
def checkBlockRec (ops : CheckerOps m) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) :=
  match p.members, cvTas, ctorsAs with
  | [ms], [cvTa], [ctorsA] => do
    let pn := p.toNative
    unless nativeRulesOk pn.cvR.name (pn.cvR.levelParams.map .param) .never pn.nP
        pn.ctors.length ctorsA pn.kinds pn.rhss pn.cvR.type do
      throw (.invalid "direct rec: recursor rules are not the generated ones")
    let (cvRa, rhss) ← checkNativeRec ops env pn cvTa ctorsA
    pure [(cvRa, rhss, ms.nIdx, ctorsA)]
  | _, _, _ => throw (.notImplemented "block rec: the mutual recursor stage")

/-- **The projection table at every STRUCTURE-LIKE member** (one
constructor, no index): the member's table at the tagged tower's
projection offset `1`; nothing at any other member. -/
def checkBlockTables (p : BlockShape) :
    List (MemberShape × List (ConstantVal × Nat) × List (List Level)) → Env → m Env
  | [], env => pure env
  | (ms, ctorsA, sortss) :: rest, env => do
    let env' ←
      (match ctorsA, sortss with
       | [cA], [sorts] =>
         if ms.nIdx == 0 then
           checkStructProjTable ms.cvT.name cA.1.name p.lps p.nP cA.2 p.resSort
             (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 env
         else pure env
       | _, _ => pure env)
    checkBlockTables p rest env'

/-- **The install after the pass**: the elimination restriction, the
index binders' sorts, the kinds re-checked, the constructors consed,
the recursor stage, the recursors consed, and the projection tables. -/
def checkBlockTail (ops : CheckerOps m) (env : Env) (q : BlockPass Env) : m Env := do
  let p := q.p
  -- **the elimination restriction** (official `elim_only_at_universe_zero`,
  -- `inductive.cpp`): a large eliminator on a block whose sort may be
  -- `Prop` needs ONE member with at most one constructor — official
  -- returns `true` (eliminate into `Prop` only) as soon as
  -- `m_ind_types.size() > 1` or `num_intros > 1`; the one-constructor
  -- case is the subsingleton criterion, taken per field at
  -- `checkStructFieldSortsI`
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSorts ops q.env₁ p.toBlockShape (p.members.zip q.cvTas)
  -- the kinds, re-checked on the stored (normalised) constructors in
  -- the opened form the model reads
  unless blockFieldsOk env p.memberNames p.lps p.nP p.nIdxs q.ctorsAs p.kinds do
    throw (.internal "direct rec: field kinds")
  let env₂ := consBlockCtors p.nP q.ctorsAs q.env₁
  let rs ← checkBlockRec ops env₂ p q.cvTas q.ctorsAs
  let env₃ := consBlockRecs env₂.find? p.nP p.rulePrefix rs env₂
  checkBlockTables p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-- Check and install a block on the uniform route: the distinct
names, the pass over the formers and the constructors — again where
the capability record's syntactic reading overshot (task #268) — and
the install after it. -/
def checkBlock (ops : CheckerOps m) (env : Env) (p₀ : BlockParts) : m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let (q, settled) ← checkBlockPass ops env p₀ (blockRawRec p₀)
  if settled then checkBlockTail ops env q
  else do
    let (q', settled') ← checkBlockPass ops env p₀ (blockIsRec q.p.kinds)
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkBlockTail ops env q'

end ConLeche
