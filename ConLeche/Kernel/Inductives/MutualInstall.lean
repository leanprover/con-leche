module

public import ConLeche.Kernel.Inductives.NativeInstall
public import ConLeche.Kernel.Inductives.MutualParts

@[expose] public section

/-!
# The mutual install (pure fueled checker; task #278)

A mutual block `T_1 … T_k` (`mutualParts?`,
`ConLeche/Kernel/Inductives/MutualParts.lean`) installs exactly as the
fixpoint route installs a single block — official's checks, the
recursors generated, compared with the stream's records, stored:

1. **the formers**, each checked and read at official's telescope
   (`checkSumTele`, task #195) **at the pre-block environment** — as
   official's `check_inductive_types` runs before
   `declare_inductive_types`, so a former type mentioning an earlier
   member is rejected — and consed afterwards with the block's
   capability record (none: K never fires on a mutual block,
   η/unit-likeness at a recursion-free block's structure-like members
   are a later task); then official's cross-member checks
   (`check_inductive_types`): the parameter domains definitionally the
   first former's, the result sorts equivalent, one level-parameter
   list;
2. **the eliminator**: a mutual block whose sort is not provably
   nonzero eliminates into `Prop` only (`elim_only_at_universe_zero`);
   the stream's recursors must carry the generated level parameters
   (official's replay: "Invalid recursor");
3. **the constructors**, each at the environment holding all `k`
   formers: the constant check, the field domains normalised by
   official's positivity walk over the MEMBER LIST (`normPosDomM`: a
   domain mentioning any member is `whnf`'d, under its Π binders while
   a member occurs), the result pinned at the constructor's own member
   (`is_valid_ind_app`), the parameter domains pinned against the
   member's former, the fields' universe bound; the field kinds
   classified member-aware (`mutualCtorKinds`: recursive or reflexive
   with the member the field targets, non-positive — a REJECT — or a
   nested occurrence — the modeled path's, a positive decline) and
   re-checked on the opened annotated type (`mutualFieldsOk`, what
   the model reads);
4. **the recursors**: `T_m.rec`'s type generated with `k` motives
   (`mutualRecTy`, official's `mk_rec_infos`), compared with the
   stream's by one `isDefEq`; the `k` recursors provisioned rule-less
   together (a rule mentions the sibling recursors), the rules
   generated (`mutualRecRhs`, `mk_rec_rules`) and scope-checked there,
   the stream's rule bodies compared structurally (`mutualRulesOk`);
   the recursors stored with the generated rules, `paramsBlind` set as
   on the fixpoint route (the law holds at any fitting parameter
   spines);
5. **the projection table** of every structure-like member (one
   constructor, no index — official's `infer_proj` condition), at the
   tagged tower's offset as on the fixpoint route.

Nothing is generated and checked as a declaration, and no step beyond
official's own checks can fail on a block official accepts: the model
tier proves the stored block modelled by instantiating the fixpoint
route's theorems at the tagged sum of the members' index tuples
(`ConLeche/Model/Inductives/DeclMutual.lean`).  Verdicts: an official
reject is `.invalid`; a nested occurrence is a positive decline.  The
index-threaded twins are `ConLeche/Kernel/Inductives/MutualInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The block record and its readers -/

/-- **The block record the install takes** (task #279's R4): the
formers with their index counts, the constructors, the parameter
count, the level parameters and the eliminator's level-parameter
shape — nothing of the stream's recursor records, which are compared
separately (`checkMutual`). -/
structure MutualBlock where
  /-- the formers in block order, each with its index count -/
  formers : List (ConstantVal × Nat)
  /-- the constructors in block order, member by member -/
  ctors : List MutualCtor
  nP : Nat
  lps : List Name
  large : Bool
  elim : Name
  deriving Repr, Inhabited

/-- The block record of a recognised mutual block. -/
def MutualParts.toBlock (p : MutualParts) : MutualBlock :=
  ⟨p.members.map (fun mb => (mb.cv, mb.nIdx)), p.ctors, p.nP, p.lps, p.large, p.elim⟩

def MutualBlock.k (b : MutualBlock) : Nat := b.formers.length
def MutualBlock.n (b : MutualBlock) : Nat := b.ctors.length
def MutualBlock.rulePrefix (b : MutualBlock) : Nat := b.nP + b.k + b.n
def MutualBlock.elimLevel (b : MutualBlock) : Level := structElimLevel b.elim b.large
def MutualBlock.rlps (b : MutualBlock) : List Name :=
  if b.large then b.elim :: b.lps else b.lps
def MutualBlock.memberNames (b : MutualBlock) : List Name := b.formers.map (·.1.name)
/-- The recursor name of member `m`: `T_m.rec`, official's `mk_rec_name`. -/
def MutualBlock.recName (b : MutualBlock) (mIdx : Nat) : Name :=
  (b.formers.getD mIdx default).1.name.str "rec"
def MutualBlock.blockNames (b : MutualBlock) : List Name :=
  b.memberNames ++ b.ctors.map (·.cv.name) ++ (List.range b.k).map b.recName
/-- The constructors of member `m`, with their global indices. -/
def MutualBlock.ownCtors (b : MutualBlock) (mIdx : Nat) : List (Nat × MutualCtor) :=
  (b.ctors.zipIdx.map fun (c, J) => (J, c)).filter fun (_, c) => c.member == mIdx
/-- The members as the classification reads them: `(T_m, m, nIdx_m)`. -/
def MutualBlock.members3 (b : MutualBlock) : List (Name × Nat × Nat) :=
  b.formers.zipIdx.map fun ((cv, nIdx), mIdx) => (cv.name, mIdx, nIdx)
def MutualBlock.nIdxOf (b : MutualBlock) (mIdx : Nat) : Nat := (b.formers.getD mIdx default).2

/-- A former after its stage: the annotated, telescope-shaped constant,
its index count and its result sort. -/
structure MutualFormerA where
  cvTa : ConstantVal
  nIdx : Nat
  s : Level
  deriving Repr, Inhabited

/-- The constructors' members are non-decreasing in block order (the
parser lists the constructors member by member; a constructor whose
result names a member other than the one it is listed under is
official's "invalid return type"). -/
def mutualCtorsGrouped : List MutualCtor → Bool
  | [] => true
  | [_] => true
  | c :: c' :: cs => c.member ≤ c'.member && mutualCtorsGrouped (c' :: cs)

/-! ## Stages 0–2: the shape, the formers, the cross-member checks -/

/-- Stage 0: the block's shape, official's rejects — distinct names,
one level-parameter list, every constructor returning a member, the
constructors grouped by member in member order. -/
def mutualShapeOk (b : MutualBlock) : m Unit := do
  unless b.blockNames.Nodup do
    throw (.invalid "mutual: duplicate declaration in the block")
  unless b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps) do
    throw (.invalid "mutual: the block's members do not share its level parameters")
  unless b.ctors.all (fun c => c.member < b.k) do
    throw (.invalid "mutual: invalid constructor return type")
  unless mutualCtorsGrouped b.ctors do
    throw (.invalid "mutual: a constructor returns a member other than the one it is \
      listed under")

/-- **Stage 1's checks, all at the pre-block environment**: every
former's type is checked and read at official's telescope
(`checkSumTele`, task #195) in the environment the block starts from,
as official's `check_inductive_types` does — `declare_inductive_types`
comes after, so a former type mentioning an earlier member of the same
block is official's "unknown identifier" and is rejected here too. -/
def mutualFormerChecks (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List (ConstantVal × Nat) → m (List MutualFormerA)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    let cvTa₀ ← checkConstantVal ops env cv
    let (cvTa, s) ← checkSumTele ops env cv (nP + nIdx) cvTa₀
    let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + nIdx))
      (.internal "mutual: type former telescope")
    unless tbody == Expr.sort s do
      throw (.internal "mutual: type former result sort")
    let fs ← mutualFormerChecks ops env nP rest
    pure (⟨cvTa, nIdx, s⟩ :: fs)

/-- The formers' conses, in block order (the first former deepest),
each with the block's capability record (`{}`) as the fixpoint route's
`checkSumInd` conses its one former. -/
def consMutualFormers : List MutualFormerA → Env → Env
  | [], env => env
  | f :: fs, env => consMutualFormers fs ⟨.indInfo f.cvTa {} :: env.consts⟩

/-- Stage 1: the formers checked at the pre-block environment and
consed afterwards; returns the environment holding all of them and the
checked formers in order. -/
def mutualFormers (ops : CheckerOps m) (nP : Nat) (formers : List (ConstantVal × Nat))
    (env : Env) : m (Env × List MutualFormerA) := do
  let fms ← mutualFormerChecks ops env nP formers
  pure (consMutualFormers fms env, fms)

/-- Official's `check_inductive_types` parameter check: member `m`'s
parameter domains, opened at variables, are definitionally the first
former's (`checkStructDomsAt` with official's verdict). -/
def mutualDomsOk (ops : CheckerOps m) (env : Env) (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "mutual: parameter index")
    let b ← unwrapOr doms[j]? (.internal "mutual: parameter index")
    unless ← ops.isDefEq env j a.fvarTypeD b do
      throw (.invalid "mutual: parameters of all inductive datatypes must match")
    mutualDomsOk ops env fvs doms j

/-- Stage 2: official's cross-member checks (`check_inductive_types`):
every former's result sort equivalent to the first's, its parameter
domains definitionally the first's. -/
def mutualCrossChecks (ops : CheckerOps m) (env : Env) (nP : Nat) (f₀ : MutualFormerA)
    (doms₀ : List Expr) : List MutualFormerA → m Unit
  | [] => pure ()
  | f :: rest => do
    unless ← liftFueled "level comparison" (Level.isEquiv f.s f₀.s) do
      throw (.invalid "mutual: mutually inductive types must live in the same universe")
    let tq ← unwrapOr (openPisAtFvars nP f.cvTa.type 0) (.internal "mutual: former telescope")
    mutualDomsOk ops env tq.1 doms₀ nP
    mutualCrossChecks ops env nP f₀ doms₀ rest

/-! ## Stage 3: the constructors, member-aware -/

/-- Does `e` mention some member of the block? -/
def mentionsMember (memberNames : List Name) (e : Expr) : Bool :=
  memberNames.any fun T => e.mentionsConst T

/-- **Official's positivity walk over the member list, as a
normalisation** (`normPosDom` at a mutual block): a field domain
mentioning any member is `whnf`'d, and — while a member occurs —
walked under its Π binders (a Π domain mentioning a member is
official's "non positive occurrence", INVALID), each body `whnf`'d in
turn. -/
def normPosDomM (ops : CheckerOps m) (env : Env) (memberNames : List Name) :
    Nat → Nat → Expr → m Expr
  | _, 0, _ => throw (.notImplemented "mutual: positivity walk fuel")
  | d, fuel + 1, e => do
    if !mentionsMember memberNames e then pure e else
    let w ← ops.whnf env d e
    if !mentionsMember memberNames w then pure w else
    match w with
    | .forallE dom body bm =>
      if mentionsMember memberNames dom then
        throw (.invalid "mutual: non positive occurrence of the datatypes being declared")
      else do
        let body' ← normPosDomM ops env memberNames (d + 1) fuel (body.instantiate1 (.fvar d dom))
        pure (.forallE dom (body'.abstract1 d) bm)
    | _ => pure w

/-- `normFieldDoms` at a mutual block. -/
def normFieldDomsM (ops : CheckerOps m) (env : Env) (memberNames : List Name) :
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Expr)
  | _, 0, e => pure ([], e)
  | i, n + 1, .forallE dom body bm => do
    let dom' ← normPosDomM ops env memberNames i 1024 dom
    let (bs, r) ← normFieldDomsM ops env memberNames (i + 1) n (body.instantiate1 (.fvar i dom))
    pure ((dom', bm) :: bs, r)
  | _, _ + 1, _ => throw (.notImplemented "mutual: constructor field telescope")

/-- `normCtorVal` at a mutual block: the checked constructor with its
field domains normalised over the member list. -/
def normCtorValM (ops : CheckerOps m) (env : Env) (memberNames : List Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) : m ConstantVal := do
  let (cbs, _) ← unwrapOr (cvCa.type.stripPis nP)
    (.notImplemented "mutual: constructor telescope")
  let (fvsP, crest) ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "mutual: constructor telescope")
  let pbs := List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs
  let (fbs, resid) ← normFieldDomsM ops env memberNames nP nF crest
  let ty' := closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantVal ops env { cvC with type := ty' }

/-- **One constructor's type** at a mutual block (`checkSumCtor` with
the normalisation over the member list and the residual pinned at the
constructor's own member `T`): the constant check, the annotated result
shape (member `T` at the parameters followed by `nIdx` index
expressions — official's `is_valid_ind_app`, "invalid return type"
otherwise), the parameter pins against the member's former's opened
telescope, the field domains resolving at the environment holding the
formers, the index expressions resolving there too (a member in an
index argument is caught by the kinds), and the per-field universe
bound.  Returns the annotated constructor and its fields' sorts. -/
def checkMutualCtor (ops : CheckerOps m) (env : Env) (memberNames : List Name) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
  let cvCa₀ ← checkConstantVal ops env cvC
  let cvCa ← normCtorValM ops env memberNames nP nF cvC cvCa₀
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "mutual: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "mutual: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "mutual: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
    (.notImplemented "mutual: type former telescope")
  checkStructDomsAt ops env 0 cq.1 (tq.1.map Expr.fvarTypeD) nP
  let xq ← unwrapOr (openPisAtFvars nF cq.2 nP)
    (.notImplemented "mutual: constructor field telescope")
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "mutual: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolve env do
    throw (.notImplemented "mutual: field domain after the block")
  unless (xq.2.getAppArgs.drop nP).all fun e => e.constsResolve env do
    throw (.invalid "mutual: index expression mentions an unknown constant")
  let sorts ← checkStructFieldSortsI ops env isProp large resSort nP xq.1
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- Stage 3 over the constructors, at the environment holding all the
formers (`fms`: the checked formers, indexed by member); returns the
annotated constructors with their field counts and their fields'
sorts. -/
def checkMutualCtors (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (fms : List MutualFormerA) (isProp : Bool) :
    List MutualCtor → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let f := fms.getD c.member default
    let (cvCa, sorts) ← checkMutualCtor ops env b.memberNames f.cvTa.name b.lps b.nP f.nIdx f.s
      isProp b.large c.cv c.nF f.cvTa
    let (rest, srest) ← checkMutualCtors ops env b fms isProp cs
    pure ((cvCa, c.nF) :: rest, sorts :: srest)

/-- Official's `check_positivity` telescope walk on a field domain
that mentions some member (`recPositivity` at a mutual block): `k`
binders of the field's own telescope have been peeled.  A member
application at the head with the block's parameters, that member's
arity and index expressions free of the block is a recursive
(`k = 0`) or reflexive field TARGETING that member; any other
member-headed application is official's "non valid occurrence"
(`.negative`); another head is a nested occurrence (`.unsupported`,
the modeled path's). -/
def mutualPositivity (members : List (Name × Nat × Nat)) (lps : List Name) (nP o : Nat) :
    Expr → Nat → RecFieldKind × Nat
  | .forallE dom body _, k =>
    if mentionsMember (members.map (·.1)) dom then (.negative, 0)
    else mutualPositivity members lps nP o body (k + 1)
  | e, k =>
    if !mentionsMember (members.map (·.1)) e then (.ordinary, 0)
    else
      match e.getAppFn with
      | .const T' us =>
        match members.find? (·.1 == T') with
        | some (_, m', nIdx') =>
          if us == lps.map .param && e.getAppArgs.length == nP + nIdx' &&
              e.getAppArgs.take nP == structPsAt (o + k) nP &&
              (e.getAppArgs.drop nP).all (fun a => !mentionsMember (members.map (·.1)) a) then
            ((if k == 0 then .recursive else .reflexive), m')
          else (.negative, 0)
        | none => (.unsupported, 0)
      | _ => (.unsupported, 0)

/-- The kinds of one constructor's fields at a mutual block
(`recCtorKinds`), each with the member it targets; a recursive field a
later binder or the residual mentions is `.unsupported`, and a
residual index expression mentioning a member makes every field
`.negative` (official's "invalid return type"). -/
def mutualCtorKinds (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat)
    (c : ConstantVal × Nat) : Option (List (RecFieldKind × Nat)) :=
  match c.1.type.stripPis (nP + c.2) with
  | some (cbs, cbody) =>
    let ks := (List.range c.2).map fun i =>
      let dom := (cbs.getD (nP + i) default).1
      if !mentionsMember (members.map (·.1)) dom then (RecFieldKind.ordinary, 0)
      else
        match mutualPositivity members lps nP i dom 0 with
        | (.recursive, m') => if structUsedLater c.1.type nP i then (.unsupported, 0)
                              else (.recursive, m')
        | (.reflexive, m') => if structUsedLater c.1.type nP i then (.unsupported, 0)
                              else (.reflexive, m')
        | k => k
    if (cbody.getAppArgs.drop nP).all (fun a => !mentionsMember (members.map (·.1)) a) then some ks
    else some (ks.map fun _ => (.negative, 0))
  | none => none

/-- The recursive positions with their targets. -/
def mutualRecFieldsOf (ks : List (RecFieldKind × Nat)) : List (Nat × Nat) :=
  (List.range ks.length).filterMap fun i =>
    match ks.getD i (.ordinary, 0) with
    | (.recursive, m') => some (i, m')
    | (.reflexive, m') => some (i, m')
    | _ => none

/-- The fields' kinds classified at install on the stored constructors
(`classifyFixKinds` at a mutual block): a non-positive or non-valid
occurrence is INVALID, a nested occurrence a positive decline. -/
def classifyMutualKinds (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat)
    (ctorsA : List (ConstantVal × Nat)) : m (List (List (RecFieldKind × Nat))) := do
  let kinds ← unwrapOr (ctorsA.mapM (mutualCtorKinds members lps nP))
    (.notImplemented "mutual: constructor telescope")
  if kinds.any (fun ks => ks.any (·.1 == .negative)) then
    throw (.invalid "mutual: non positive or non valid occurrence of the datatypes being declared")
  if kinds.any (fun ks => ks.any (·.1 == .unsupported)) then
    throw (.notImplemented "mutual: a nested occurrence of the block (not modeled here)")
  pure kinds

/-- The kinds re-checked on the annotated constructor type opened at
variables (`nativeOpenedOk` at a mutual block): an ordinary field's
domain resolves before the block; a recursive field's domain is its
TARGET member at the opened parameter variables followed by that
member's index expressions resolving before the block, and the
variable occurs in no later field's domain nor in the residual; a
reflexive field's telescope opened likewise; the residual's index
expressions resolve before the block. -/
def mutualOpenedOk (env₀ : Env) (members : List (Name × Nat × Nat)) (lps : List Name)
    (nP : Nat) (cty : Expr) (nF : Nat) (ks : List (RecFieldKind × Nat)) : Bool :=
  let nIdxOf : Nat → Nat := fun m' => ((members.find? (·.2.1 == m')).map (·.2.2)).getD 0
  let nameOf : Nat → Name := fun m' => ((members.find? (·.2.1 == m')).map (·.1)).getD .anonymous
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i (.ordinary, 0) with
        | some x, (.ordinary, _) => x.fvarTypeD.constsResolve env₀
        | some x, (.recursive, m') =>
          x.fvarTypeD.getAppFn == Expr.const (nameOf m') (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdxOf m' &&
          (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, (.reflexive, m') =>
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => a.fvarTypeD.constsResolve env₀) &&
            body.getAppFn == Expr.const (nameOf m') (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdxOf m' &&
            (body.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- The kinds, re-checked on every annotated constructor. -/
def mutualFieldsOk (env₀ : Env) (members : List (Name × Nat × Nat)) (lps : List Name)
    (nP : Nat) (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat))) :
    Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && mutualOpenedOk env₀ members lps nP cA.1.type cA.2 ks
    | _, _ => false

/-! ## Stage 4: the recursors -/

/-- The constructors' conses (`consSumCtors`). -/
def consMutualCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | c :: cs, env => consMutualCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

/-- The generators' data: the formers and the constructors with their
recursive fields, off the annotated constructors and the classified
kinds. -/
def mutualGenData (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat))) :
    List MutualFormer × List MutualCtor4 :=
  (fms.map fun f => ⟨f.cvTa.name, f.nIdx, f.cvTa.type⟩,
   List.zipWith (fun (c, cA) ks => ⟨c.cv.name, c.nF, cA.1.type, c.member, mutualRecFieldsOf ks⟩)
     (b.ctors.zip ctorsA) kinds)

/-- Stage 4a: member `m`'s recursor type, generated and compared with
the stream's record when given (the fixpoint route's `checkNativeRec`
comparison: the generated type is scoped, inferred, and the stream's
is `isDefEq`'d against it); returns the generated constant. -/
def checkMutualRecTy (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (mIdx : Nat)
    (streamRec : Option ConstantVal) : m ConstantVal := do
  let recTy ← unwrapOr (mutualRecTy b.lps b.elim b.large b.nP formers4 ctors4 mIdx)
    (.internal "mutual: recursor type")
  unless recTy.allLevelParamsDefined b.rlps && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "mutual: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  if let some cvR := streamRec then
    let cvRi ← checkConstantVal ops env cvR
    unless ← ops.isDefEq env 0 cvRi.type recTy do
      throw (.invalid s!"mutual: the type of {cvR.name} is not the generated one")
  pure ⟨b.recName mIdx, b.rlps, recTy⟩

/-- Stage 4a over the members. -/
def checkMutualRecTys (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    Nat → m (List ConstantVal)
  | 0 => pure []
  | mIdx' + 1 => do
    let earlier ← checkMutualRecTys ops env b formers4 ctors4 streamRecs mIdx'
    let cvRa ← checkMutualRecTy ops env b formers4 ctors4 mIdx'
      (streamRecs.bind fun rs => (rs[mIdx']?).map (·.1))
    pure (earlier ++ [cvRa])

/-- The `k` recursors provisioned rule-less (`provisionRecs`): a rule
mentions the sibling recursors, so every rule is scoped at the
environment holding all of them. -/
def provisionMutualRecs (b : MutualBlock) (fms : List MutualFormerA) :
    List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | (cvRa, mIdx) :: rest, env =>
    let rP := b.rulePrefix
    let mI := rP + (fms.getD mIdx default).nIdx
    provisionMutualRecs b fms rest ⟨.recInfo cvRa mI rP [] :: env.consts⟩

/-- Stage 4b: member `m`'s rules — generated, scoped at the environment
holding the rule-less recursors (`checkNativeRules`), the stream's
compared structurally when given. -/
def checkMutualMemberRules (envR : Env) (b : MutualBlock) (formers4 : List MutualFormer)
    (ctors4 : List MutualCtor4) (mIdx : Nat) (streamRec : Option (ConstantVal × List RecRule)) :
    m (List (MutualCtor × Expr)) := do
  let recOf : Nat → Name := b.recName
  let rlvls := b.rlps.map Level.param
  let own := b.ownCtors mIdx
  if let some (cvR, rules) := streamRec then
    unless mutualRulesOk recOf rlvls b.nP b.k b.n ctors4 (own.map (·.1)) (rules.map (·.rhs))
        cvR.type do
      throw (.invalid s!"mutual: the rules of {cvR.name} are not the generated ones")
  own.mapM fun (J, c) => do
    let rhs ← unwrapOr (mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4 recOf rlvls J)
      (.internal "mutual: recursor rule")
    unless rhs.allLevelParamsDefined b.rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "mutual: recursor rule scoping")
    pure (c, rhs)

/-- Stage 4b over the members. -/
def checkMutualAllRules (envR : Env) (b : MutualBlock) (formers4 : List MutualFormer)
    (ctors4 : List MutualCtor4) (streamRecs : Option (List (ConstantVal × List RecRule))) :
    Nat → m (List (List (MutualCtor × Expr)))
  | 0 => pure []
  | mIdx' + 1 => do
    let earlier ← checkMutualAllRules envR b formers4 ctors4 streamRecs mIdx'
    let rules ← checkMutualMemberRules envR b formers4 ctors4 mIdx' (streamRecs.bind (·[mIdx']?))
    pure (earlier ++ [rules])

/-- The stored rules of a recursor: the generated right-hand sides
with the rescue bits read off the block's store (`sumRules`'
arrangement), `paramsBlind` set — the route's rule law holds at any
pair of fitting parameter spines. -/
def mutualRules (find? : Name → Option ConstantInfo) (recName : Name) (nP mI rP : Nat)
    (recTy : Expr) : List (MutualCtor × Expr) → List RecRule
  | [] => []
  | (c, rhs) :: rest =>
    recRuleBits find? recName
      { ctor := c.cv.name, nfields := c.nF, ctorParams := nP,
        fire := if Expr.recRulePlain recTy mI rP nP then .plain else .inert,
        rhs := rhs, paramsBlind := true }
      :: mutualRules find? recName nP mI rP recTy rest

/-- Stage 4c: the recursors stored as a group with their rules, on the
environment holding the formers and constructors (`env₂`). -/
def storeMutualRecs (env₂ : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | (cvRa, mIdx) :: rest, env =>
    let rP := b.rulePrefix
    let mI := rP + (fms.getD mIdx default).nIdx
    storeMutualRecs env₂ b fms rulesOf rest
      ⟨.recInfo cvRa mI rP (mutualRules env₂.find? cvRa.name b.nP mI rP cvRa.type
          (rulesOf.getD mIdx [])) :: env.consts⟩

/-! ## Stage 5: the projection tables -/

/-- **The projection table** at a STRUCTURE-LIKE member — one
constructor, no index — official's `infer_proj` condition
(`type_checker.cpp`: one constructor, `nparams + nindices` arguments,
no `is_rec`, no single-type condition), the fixpoint route's table at
the tagged tower's offset `1` (`checkNativeTable`); the guard levels
are official's join over the fields' sorts from the constructors'
stage.  Nothing at any other member. -/
def mutualMemberTable (b : MutualBlock) (f : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (mIdx : Nat) (env : Env) : m Env :=
  match b.ownCtors mIdx with
  | [(J, c)] =>
    if f.nIdx == 0 then
      let cvCa := (ctorsA.getD J default).1
      checkStructProjTable f.cvTa.name c.cv.name b.lps b.nP c.nF f.s
        (structProjGuards cvCa.type b.nP c.nF (sortss.getD J [])) 1 cvCa env
    else pure env
  | _ => pure env

/-- Stage 5 over the members. -/
def mutualTables (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) : List (MutualFormerA × Nat) → Env → m Env
  | [], env => pure env
  | (f, mIdx) :: rest, env => do
    let env' ← mutualMemberTable b f ctorsA sortss mIdx env
    mutualTables b ctorsA sortss rest env'

/-! ## The install -/

/-- **Check and install a mutual block from its block record** (see
the module docstring); `streamRecs` are the stream's recursor records
in member order, compared with the generated recursors when given. -/
def checkMutualCore (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (streamRecs : Option (List (ConstantVal × List RecRule))) : m Env := do
  let nP := b.nP
  mutualShapeOk b
  -- 1. the formers, consed
  let (env₁, fms) ← mutualFormers ops nP b.formers env
  let f₀ ← unwrapOr fms[0]? (.internal "mutual: no member")
  -- 2. the cross-member checks and the eliminator
  let tq₀ ← unwrapOr (openPisAtFvars nP f₀.cvTa.type 0) (.internal "mutual: former telescope")
  mutualCrossChecks ops env₁ nP f₀ (tq₀.1.map Expr.fvarTypeD) fms
  unless b.large == f₀.s.isNeverZero do
    throw (.invalid "mutual: the recursors' level parameters are not the generated ones")
  let isProp := Level.isEquiv f₀.s .zero == some true
  -- 3. the constructors at the environment holding the formers, their
  -- kinds classified on the stored (normalised) constructors and
  -- re-checked in the opened form the model reads
  let (ctorsA, sortss) ← checkMutualCtors ops env₁ b fms isProp b.ctors
  let kinds ← classifyMutualKinds b.members3 b.lps nP ctorsA
  unless mutualFieldsOk env b.members3 b.lps nP ctorsA kinds do
    throw (.internal "mutual: field kinds")
  let env₂ := consMutualCtors nP ctorsA env₁
  -- 4. the recursors: the types generated and compared, the rules
  -- generated at the rule-less provision and compared, the group stored
  let (formers4, ctors4) := mutualGenData b fms ctorsA kinds
  let cvRas ← checkMutualRecTys ops env₂ b formers4 ctors4 streamRecs b.k
  let envR := provisionMutualRecs b fms cvRas.zipIdx env₂
  let rulesOf ← checkMutualAllRules envR b formers4 ctors4 streamRecs b.k
  let env₃ := storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂
  -- 5. the projection tables of the structure-like members
  mutualTables b ctorsA sortss fms.zipIdx env₃

/-- Check and install a **recognised mutual block**: the recursor
records' structural pin (thrown here, as official's replay rejects a
recursor that is not the generated one), then the core with the
stream's records compared. -/
def checkMutual (ops : CheckerOps m) (env : Env) (p : MutualParts) : m Env := do
  unless p.recPinned do
    throw (.invalid "mutual: a recursor record is not the generated recursor")
  checkMutualCore ops env p.toBlock (some (p.members.map fun mb => (mb.cvR, mb.rules)))

end ConLeche
