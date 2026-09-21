module

public import ConLeche.Kernel.Inductives.NativeInstall
import ConLeche.Kernel.Inductives.BlockParts
public import ConLeche.Kernel.Inductives.BlockRec

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

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

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

/-- **The parameter-domain agreement's own comparison**
(`checkStructDomsAt` with official's verdict): between MEMBERS a
domain mismatch is a REJECT — official's `check_inductive_types` fails
with "parameters of all inductive datatypes must match" — where the
shared helper, written for the constructor stage's parameter pins,
declines.  Walks from the last binder to the first, as it does. -/
def checkBlockDomsAt (ops : CheckerOps m) (env : Env) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    unless ← ops.isDefEq env (off + j) a.fvarTypeD b do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAt ops env off fvs doms j

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
    unless tq.1.length == tq0.1.length do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAt ops env 0 tq.1 (tq0.1.map Expr.fvarTypeD) nP
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
def consBlockRecs (find? : Name → Option ConstantInfo) (p : BlockShape) (nP : Nat) :
    Nat → List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → Env → Env
  | _, [], env => env
  | m, (cvRa, rhss, _nIdx, ctorsA) :: rest, env =>
    consBlockRecs find? p nP (m + 1) rest
      ⟨.recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m)
        (sumRules find? cvRa.name nP (p.majorIdxAt m) (p.rulePrefixAt m) cvRa.type ctorsA rhss)
        :: env.consts⟩

/-! ### The recursor stage as CHECKING (milestone M5)

`ConLeche/Kernel/Inductives/BlockRec.lean` holds the generated pieces
and the primitive-recursion abstraction; here are the three stages
that consume them — the pins, the types, the rules — and the dispatch
that keeps the one-member generate-and-compare stage live behind
`blockRecCheckOn`. -/

/-- The `k` RULE-LESS recursors, consed in block order: the
environment a rule's right-hand side is annotated, resolved and typed
at (official's `declare_recursors` puts every recursor of the block in
the environment before any rule is looked at). -/
def consBlockRecsBare (p : BlockShape) : Nat → List (ConstantVal × Nat) → Env → Env
  | _, [], env => env
  | m, (cvRa, _nIdx) :: rest, env =>
    consBlockRecsBare p (m + 1) rest
      ⟨.recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m) [] :: env.consts⟩

/-- **Pairwise definitional equality of binder domains, REJECTING**
(`checkDefEqList` with official's verdict).  Between a rule's
`λ`-domains and the recursor's own binders — or between a recursor's
parameter domains and the block's — a mismatch is INVALID INPUT, not a
feature this route lacks: official generates the recursor from the
block and its replay compares the exported one structurally.  The
shared helper's `.notImplemented` is written for the modelled route's
iota certificates, where a mismatch really is an uncharted shape. -/
def checkBlockDefEqList (ops : CheckerOps m) (env : Env) (depth : Nat) (what : String) :
    List Expr → List Expr → m Unit
  | [], [] => pure ()
  | a :: as, b :: bs => do
    unless ← ops.isDefEq env depth a b do
      throw (.invalid s!"direct rec: {what}")
    checkBlockDefEqList ops env depth what as bs
  | _, _ => throw (.invalid s!"direct rec: {what} (arity)")

/-- **Stage (b): every member's recursor TYPE.**

The stream's type is checked as a constant's type and STORED AS IS —
nothing is generated and nothing is compared with a generated term.
What is checked is the SHAPE the ruling of 2026-09-21 fixes, with the
argument sums read off the record (`BlockShape.rulePrefixAt` /
`majorIdxAt`):

* `nP ≤ rP`, and the type has `mI + 1 = rP + nIdx_m + 1` `∀` binders;
* the first `nP` binder DOMAINS are the block's parameter domains,
  compared BINDER BY BINDER with the member's own opened former
  telescope (the constructors' stage pins them the same way);
* the binders `nP … rP-1` are ARBITRARY — the stretch official fills
  with the motives and the minor premises is never looked inside;
* the binder `mI` — the MAJOR — has type `T_m p⃗ ı⃗` with the head the
  member's own constant at the block's level parameters, `p⃗` the
  first `nP` binders and `ı⃗` EXACTLY the index binders `rP … mI-1`.
  This is what ASSIGNS the recursor to member `m`, and it is what
  makes the ι step's index matching and the model's predecessor index
  mean anything;
* the CONCLUSION is arbitrary — except that, when a large eliminator
  is not allowed (`blockLargeElimAllowed`, official's
  `elim_only_at_universe_zero` said declaratively), it must be a
  PROPOSITION: its sort under the opened binders is `Sort 0`. -/
def checkBlockRecTys (ops : CheckerOps m) (env : Env) (p : BlockShape) (nested : Bool) :
    List (MemberShape × ConstantVal) → Nat → m (List (ConstantVal × Nat))
  | [], _ => pure []
  | (ms, cvTa) :: rest, mi => do
    let cvRi ← checkConstantVal ops env ms.cvR
    let rP := p.rulePrefixAt mi
    let mI := p.majorIdxAt mi
    unless p.nP ≤ rP do
      throw (.invalid "direct rec: the recursor's rule prefix is shorter than the block's \
        parameters")
    let (fvs, concl) ← unwrapOr (openPisAtFvars (mI + 1) cvRi.type 0)
      (.invalid "direct rec: the recursor's type does not bind its parameters, its indices \
        and its major premise")
    -- the block's parameter domains, binder by binder
    let (tfvs, _) ← unwrapOr (openPisAtFvars p.nP cvTa.type 0)
      (.internal "direct rec: type former telescope")
    checkBlockDefEqList ops env p.nP
      s!"the recursor {ms.cvR.name}'s parameter domains are not the block's"
      (tfvs.map Expr.fvarTypeD) ((fvs.take p.nP).map Expr.fvarTypeD)
    -- the MAJOR: the member at its parameters and its index binders
    let maj ← unwrapOr fvs[mI]? (.internal "direct rec: major premise")
    let mty := maj.fvarTypeD
    unless mty.getAppFn == Expr.const ms.cvT.name (p.lps.map .param) &&
        mty.getAppArgs.length == p.nP + ms.nIdx &&
        mty.getAppArgs.take p.nP == fvs.take p.nP &&
        mty.getAppArgs.drop p.nP == (fvs.drop rP).take ms.nIdx do
      throw (.invalid "direct rec: the recursor's major premise is not the member at its \
        parameters and its index binders")
    -- the ELIMINATION restriction (official `elim_only_at_universe_zero`)
    unless blockLargeElimAllowed p nested do
      let s ← ops.inferType env (mI + 1) concl
      unless ← ops.isDefEq env (mI + 1) s (.sort .zero) do
        throw (.invalid "direct rec: large eliminator on a block whose sort may be Prop")
    let rs ← checkBlockRecTys ops env p nested rest (mi + 1)
    pure ((cvRi, ms.nIdx) :: rs)

/-- **Stage (c): ONE rule.**

The right-hand side is annotated at the environment holding the `k`
RULE-LESS recursors (a rule mentions them) and must bind `rP + nF`
variables: the recursor's own prefix and the constructor's fields.
Their domains are compared BINDER BY BINDER (`checkDefEqList`) with
the opened STORED recursor type's prefix and the constructor's
telescope at the same parameters — the whole-type comparison of stage
(b) is not made at all any more, and per-binder equality is what the
model needs to read the stored λ-tower at the frames the ι step
applies it at.

The body then goes through the primitive-recursion abstraction
(`abstractIh`) and the residue is TYPED at the CONSTRUCTORS'
environment (`envT`), under the opened frame `x⃗ f⃗ ih⃗`, against
`rec_m`'s OWN conclusion instantiated at `x⃗`, at the constructor's
index expressions and at the major `C_J p⃗ f⃗`.

What is returned — and stored — is the ANNOTATED STREAM right-hand
side; the abstraction is the model's reading of it and nothing of it
is kept. -/
def checkBlockRule (opsR : CheckerOps m) (envR : Env) (opsT : CheckerOps m) (envT : Env)
    (p : BlockShape) (recNames : List Name) (rlvls : List Level)
    (recTys : List Expr) (mIs rPs : List Nat) (mi : Nat)
    (cvR : ConstantVal) (cA : ConstantVal × Nat) (ks : List BlockFieldKind)
    (rhs : Expr) : m Expr := do
  let nP := p.nP
  let rP := p.rulePrefixAt mi
  let nF := cA.2
  let recTy ← unwrapOr recTys[mi]? (.internal "direct rec: recursor type")
  unless rhs.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in rule of {cvR.name}")
  if rhs.hasFvar then
    throw (.invalid s!"free variable in rule of {cvR.name}")
  let rhsA ← opsR.annotate envR 0 rhs
  unless rhsA.allLevelParamsDefined cvR.levelParams do
    throw (.invalid s!"undeclared universe parameter in rule of {cvR.name}")
  unless rhsA.constsResolve envR do
    throw (unresolvedConstsError s!"rule of {cvR.name}" rhsA)
  let (_rbs, body) ← unwrapOr (rhsA.stripLams (rP + nF))
    (.invalid s!"direct rec: the rule of {cA.1.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  -- the frame: the recursor's own prefix, then the CONSTRUCTOR's
  -- fields at those parameters (they are what the ι step substitutes)
  let (fvsPref, _) ← unwrapOr (openPisAtFvars rP recTy 0)
    (.internal "direct rec: recursor prefix telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsPref.take nP) cA.1.type)
    (.internal "direct rec: constructor parameter telescope")
  let (fvsF, cbody) ← unwrapOr (openPisAtFvars nF crest rP)
    (.internal "direct rec: constructor field telescope")
  -- **G2**: the rule's λ-domains, binder by binder
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsPref ++ fvsF) rhsA)
    (.invalid s!"direct rec: the rule of {cA.1.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  checkBlockDefEqList opsT envT (rP + nF)
    s!"the rule of {cA.1.name} does not bind the recursor's prefix and the constructor's \
      fields"
    ((fvsPref ++ fvsF).map Expr.fvarTypeD) ldoms
  let fr : BlockRuleFrame :=
    { recNames := recNames, rlvls := rlvls, mIs := mIs, rPs := rPs, nP := nP, rP := rP,
      nF := nF, ks := ks,
      teleOf := structFieldTeleOf cA.1.type nP nF,
      idxOf := structFieldIdxOf cA.1.type nP nF,
      recIdx := blockRecIdxOf ks,
      pw := Level.zeronessOf (structElimLevel p.elim p.large) }
  let body'' ← unwrapOr (abstractIh fr 0 body)
    (.invalid s!"direct rec: the rule of {cA.1.name} is not a primitive recursion — a block \
      recursor occurs outside a call on a recursive field of this constructor at the \
      rule's own prefix")
  let ihTele ← unwrapOr
    (blockIhPis nP rP nF fr.pw (fun c => recTys.getD c (.sort .zero)) (blockTgtsOf ks)
      fr.teleOf fr.idxOf fr.recIdx 0 body'')
    (.invalid s!"direct rec: the rule of {cA.1.name} recurses into a recursor whose type \
      does not bind the call's arguments")
  let (_fvsIh, bodyO) ← unwrapOr
    (openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse) (rP + nF))
    (.internal "direct rec: inductive-hypothesis telescope")
  let depth := rP + nF + fr.nR
  let tyB ← opsT.inferType envT depth bodyO
  -- the recursor's OWN conclusion at the rule's prefix, the
  -- constructor's index expressions and the major `C_J p⃗ f⃗`
  let concl ← unwrapOr
    (Expr.instPisAtLift
      (fvsPref ++ (cbody.getAppArgs.drop nP) ++
        [Expr.mkAppN (.const cA.1.name (p.lps.map .param)) (fvsPref.take nP ++ fvsF)])
      recTy)
    (.internal "direct rec: recursor conclusion")
  unless ← opsT.isDefEq envT depth tyB concl do
    throw (.invalid s!"direct rec: the rule of {cA.1.name} does not produce the recursor's \
      conclusion at that constructor")
  pure rhsA

/-- One member's rules, in constructor order (`J` is the constructor's
GLOBAL index, which is the minor premise it fires). -/
def checkBlockRules (opsR : CheckerOps m) (envR : Env) (opsT : CheckerOps m) (envT : Env)
    (p : BlockShape) (recNames : List Name) (rlvls : List Level)
    (recTys : List Expr) (mIs rPs : List Nat) (mi : Nat) (cvR : ConstantVal) :
    List ((ConstantVal × Nat) × List BlockFieldKind) → List Expr → m (List Expr)
  | [], [] => pure []
  | (cA, ks) :: cs, rhs :: rhss => do
    let r ← checkBlockRule opsR envR opsT envT p recNames rlvls recTys mIs rPs mi cvR cA ks rhs
    let rest ← checkBlockRules opsR envR opsT envT p recNames rlvls recTys mIs rPs mi cvR
      cs rhss
    pure (r :: rest)
  | _, _ =>
    throw (.invalid "direct rec: the recursor's rules do not cover its constructors")

/-- Every member's rules, in block order. -/
def checkBlockMembersRules (opsR : CheckerOps m) (envR : Env) (opsT : CheckerOps m)
    (envT : Env) (p : BlockParts)
    (recNames : List Name) (rlvls : List Level) (cvRas : List (ConstantVal × Nat)) :
    List ((MemberShape × List (ConstantVal × Nat)) × List (List BlockFieldKind)) → Nat →
      m (List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
  | [], _ => pure []
  | ((ms, ctorsA), kss) :: rest, mi => do
    let (cvRa, nIdx) ← unwrapOr cvRas[mi]? (.internal "direct rec: recursor record")
    let rhss ← checkBlockRules opsR envR opsT envT p.toBlockShape recNames rlvls
      (cvRas.map (·.1.type)) (List.range p.k |>.map p.majorIdxAt)
      (List.range p.k |>.map p.rulePrefixAt) mi ms.cvR (ctorsA.zip kss) ms.rhss
    let rest' ← checkBlockMembersRules opsR envR opsT envT p recNames rlvls cvRas rest (mi + 1)
    pure ((cvRa, rhss, nIdx, ctorsA) :: rest')

/-- **Stage (a): the recursor RECORDS' pins** (task #220 at k
members), thrown before anything is computed. -/
def checkBlockRecPins (p : BlockParts) : m Unit := do
  unless p.members.all (fun ms => ms.cvR.name == ms.cvT.name.str "rec") do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless blockRecLpsOk p.toBlockShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")

/-- **The recursor stage as CHECKING, at any number of members**
(milestone M5, design §4.2): the recursor records' pins, then every
member's type, then — at the environment holding all `k` rule-less
recursors — every member's rules. -/
def checkBlockRecK (ops : CheckerOps m) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) := do
  -- (a) the recursor RECORDS' pins (task #220 at k members): official's
  -- replay compares every exported recursor with the generated one
  -- structurally, so a record naming something other than the generated
  -- `T_m.rec`, or contradicting it in its level parameters, its
  -- argument sums, its rules' constructors or the block's constructor
  -- GROUPING, is INVALID INPUT — thrown before anything is computed
  checkBlockRecPins p
  -- (b) every member's recursor type
  let cvRas ← checkBlockRecTys ops env p.toBlockShape (blockNested p.kinds)
    (p.members.zip cvTas) 0
  let envR := consBlockRecsBare p.toBlockShape 0 cvRas env
  -- (c) every member's rules: ANNOTATED and resolved at the
  -- environment holding all k rule-less recursors (a rule mentions
  -- them), but TYPED at `env` — the CONSTRUCTORS' environment, before
  -- they are consed.  **G1**: the abstracted residue and its whole
  -- opened frame (parameters, motives, minors, fields, `ih` openers)
  -- are recursor-free BY CONSTRUCTION — that is what the abstraction
  -- is for — and the model's typing consumer cannot be instantiated
  -- at an environment holding the very recursors whose typing the
  -- certificate is being built for: a model of that environment owes
  -- every constant's leaf a type, and the recursors' is the
  -- recursion theorem itself.
  checkBlockMembersRules ops envR ops env p (p.members.map (·.cvR.name))
    ((p.members.head?.map fun ms => ms.cvR.levelParams.map Level.param).getD [])
    cvRas ((p.members.zip ctorsAs).zip p.kinds) 0

/-- **The recursor stage, behind its gate** (`blockRecCheckOn`).

With the gate LIFTED the stage is the CHECK of milestone M5
(`checkBlockRecK`) at every `k`.  With it down — the shipped
configuration — the stage is milestone M1's interim one: at ONE member
the existing generate-and-compare (the stream's rules against the
generated ones, `nativeRulesOk`, then the recursor generated and
compared, `checkNativeRec`), at two or more a positive decline, which
the route's own gate (`blockRouteK1Only`) makes unreachable.

Why BOTH arms are gated, and not only the one-member one:

* at `k = 1` the CHECK accepts more than the generate-and-compare
  stage (any primitively recursive rule body, not only the generated
  one), so the two are not equal and the one-member bridge
  `checkBlock_one` — which the P tier's `declNative` reaches the route
  through — would stop being an equality;
* at `k ≥ 2` the CHECK's rules are MUTUALLY recursive: a rule of
  `rec_0` may name `rec_1`, so its right-hand side resolves at the
  environment holding all `k` RULE-LESS recursors and NOT at the one
  holding `rec_0` alone.  `EnvWF`'s recursor clause
  (`ConLeche/Verify/EnvWF.lean`) is checked at the environment each
  constant is consed into, and `envWF_consBlockRecs`
  (`ConLeche/Verify/Inductives/BlockWF.lean`) conses the `k` recursors
  one at a time, so the WF chain has to be restated for a SIMULTANEOUS
  cons before this arm can be live.  That restatement is milestone
  M6's entry cost, and the gate is what keeps the tree proved until
  then.

Both go with `blockRouteK1Only` at the flip. -/
def checkBlockRec (ops : CheckerOps m) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) :=
  if blockRecCheckOn then checkBlockRecK ops env p cvTas ctorsAs
  else
    match p.members, cvTas, ctorsAs with
    | [ms], [cvTa], [ctorsA] => do
      let pn := p.toNative
      unless nativeRulesOk pn.cvR.name (pn.cvR.levelParams.map .param) .never pn.nP
          pn.ctors.length ctorsA pn.kinds pn.rhss pn.cvR.type do
        throw (.invalid "direct rec: recursor rules are not the generated ones")
      let (cvRa, rhss) ← checkNativeRec ops env pn cvTa ctorsA
      pure [(cvRa, rhss, ms.nIdx, ctorsA)]
    | _, _, _ => do
      -- the recursor RECORDS' pins (task #220 at k members) are thrown
      -- FIRST, as the CHECK's own stage opens with them
      checkBlockRecPins p
      throw (.notImplemented "block rec: the mutual recursor stage")

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
  let env₃ := consBlockRecs env₂.find? p.toBlockShape p.nP 0 rs env₂
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
