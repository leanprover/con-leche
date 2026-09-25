module

public import ConLeche.Kernel.Inductives.SumInstall
public import ConLeche.Conformance.RecConform
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
   constructors are checked per member at THAT environment, and the ONE
   positivity function runs on them (its kinds are the capability
   record's `is_rec`);
2. **TAIL**: the elimination restriction, the index binders' sorts, the
   constructors consed, the recursor stage, and the projection table at
   every structure-like member.

The recursor stage (`BlockTail.lean`) CHECKS the stream's recursors
(primitive recursion, `targetRecCheck`) at every `k`, then runs the reject-only,
unverified conformance check (`checkBlockRecConform`, in
`ConLeche/Conformance/`: the one-member recursor generator, generate
and compare), through `thenConform`.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The capability record, per member -/

/-- **The capability record of member `m`**: official's
`is_structure_like` is `ncnstrs == 1 && nindices == 0 && !is_rec` with
`is_rec` read over ALL constructors of ALL members, so η and
unit-likeness are the MEMBER's data at the BLOCK's recursion verdict;
rule K is official's `is_K_target`, which requires
`m_ind_types.size() == 1` — a one-member block.  At a FIELDLESS
constructor the record claims BOTH unit-likeness and η, as official's
`is_structure_like` does: the recursor's major-premise rescue
(`Core.lean`, the `etaFields = 0` arm — arena
`073_typeSingletonRecReduction`) keys on η.  (Granting η at a
recursive structure-like was tried and is UNSOUND IN PRACTICE though
sound in the model: on `ind_nest_via_refl` the tool's nested model over
a reflexive `W1 α = sup (a : α) (f : Nat → W1 α)` made `isDefEq` spin
through η-expansion — official's `!is_rec` is load-bearing.) -/
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
      sortZ := Level.zeronessOf p.resSort
      all := p.memberNames
      nparams := p.nP }
  | _, _ => { all := p.memberNames, nparams := p.nP }

/-- **The syntactic reading of `is_rec`** (task #268 at k members):
does SOME member of the block occur in SOME declared field domain of
SOME constructor of SOME member?  Official's `is_rec` is a `find` over
all constructors of all types (`inductive.cpp`), and the raw
occurrence is a superset of the walk's verdict, which the pass's own
positivity run confirms (`nestIsRec`).  Read only where the record depends on it
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
    unless ← liftFueled "level comparison" (Level.isEquiv s s0) do
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

/-- **The block's positivity context** at the canonical parameter
variables `fvsP` (the head former's opened telescope) and an
environment's lookup: the members, their level parameters, the shared
parameter count, the members' index counts and the block's sort. -/
def BlockShape.nestCtx (p : BlockShape) (fvsP : List Expr)
    (find? : Name → Option ConstantInfo) (consts : List ConstantInfo) : NestCtx :=
  ⟨p.memberNames, p.lps, p.nP, p.nIdxs, fvsP, p.resSort, find?, consts⟩

/-- The constructors of every member, at the environment holding ALL
the formers (the resolution guard pointed at that same environment, as
the one-member stage does), each stored as declared. -/
def checkBlockCtors (ops : CheckerOps m) (env₀ env : Env) (p : BlockShape) :
    List (MemberShape × ConstantVal) →
      m (List (List (ConstantVal × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtors ops env₀ env ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtors ops env₀ env p rest
    pure (ctorsA :: restC, sortss :: restS)

/-! ## Positivity: the ONE function, on the stored constructors (lane HOLE2)

Charter item 3: "There is ONE positivity function in the kernel … The
theorem is 'returns true ⇒ the operator is monotone', proved by
inversion of that function's run."  The install runs `nestPos`
(`nestedBlockPositivity`, `Kernel/Inductives/Positivity.lean`) on the
STORED constructors, the members abstracted to holes at the canonical
parameter variables; with the route switch off (`nst = false`, which
only the proofs' switch-off statements still use; the dispatch hands the
install `true`) a field kind other than hole-free, a member, or a member
under binders declines.  Beside it, each member-abstracted
constructor type is TYPED at the holes' context (E2E-DESIGN's U2): the
typing the monotonicity proof reads at every hole value.  The walk's
kinds are the capability record's `is_rec` (`checkBlockPass`); there is
no other classifier. -/

/-- **U2**: every member-abstracted constructor type is a type at the
holes' context (parameters, then one hole per member), and the fields of
its positivity NORMAL FORM `tyN` (the walk's output, lane ALPHA1) have
their universes bounded by the family's there (at a `Type`-valued
family).  The row reads the normal form, not the declared type: the
model's fields with holes ARE the normal form's readings (their binder
bits and universes are read off this row).  Beside it, an internal
scoping assertion on `tyN`: its level parameters are the block's (whnf
unfolds at the use site's levels, so it never fires; the model's
readings of `tyN` are level-congruent through it). -/
def checkAbsCtorTys (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (ConstantVal × Nat) → List Expr → m Unit
  | c :: cs, tyN :: ns => do
    let crest ← unwrapOr (instPisWith ctx.params (nestAbstract ctx holes c.1.type))
      (.internal "direct rec: constructor parameter telescope")
    let ty ← ops.inferType env (ctx.hiAt 0) crest
    let _ ← ops.ensureSort env (ctx.hiAt 0) ty
    unless tyN.allLevelParamsDefined ctx.lps do
      throw (.internal "direct rec: a positivity normal form outside the block's level \
        parameters")
    -- the fields' universes AT THE HOLES' CONTEXT (lane HOLE2, stage B):
    -- official's per-field bound, the members variables — the model's
    -- hole operator reads every field in the family's universe at every
    -- tuple of the tuple space, which no stored reading reaches
    let xq ← unwrapOr (openPisAtFvars c.2 tyN (ctx.hiAt 0))
      (.internal "direct rec: abstracted constructor fields")
    let _ ← checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
      ctx.sort (ctx.hiAt 0) xq.1 [] c.2
    checkAbsCtorTys ops env ctx holes cs ns
  | _, _ => pure ()

/-- `checkAbsCtorTys` on every member's constructors. -/
def checkAbsCtorTysAll (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → List (List Expr) → m Unit
  | cs :: css, ns :: nss => do
    checkAbsCtorTys ops env ctx holes cs ns
    checkAbsCtorTysAll ops env ctx holes css nss
  | _, _ => pure ()

/-- **The block's positivity, on its stored constructors** (see the
section docstring): the canonical parameter variables are the first
former's opened telescope; `find?`/`consts` are the environment's lookup
(the pure `Env`'s or the index's).  Returns the walk's field kinds and
its normal forms (member-abstracted, at the walk's context; OUTPUT only:
nothing is stored from them).  `nst` is the route switch (the dispatch
passes `true`): off, a container occurrence declines (the flat guard);
on, the walk's verdict is the install's. -/
def checkBlockPositivity (ops : CheckerOps m) (env₁ : Env) (find? : Name → Option ConstantInfo)
    (consts : List ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (nst : Bool := false) :
    m (List (List (List NestFieldKind)) × List (List Expr)) := do
  let cvTa0 ← unwrapOr cvTas.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (openPisAtFvars p.nP cvTa0.type 0)
    (.internal "direct rec: type former telescope")
  let ctx : NestCtx := ⟨p.memberNames, p.lps, p.nP, p.nIdxs, pq.1, p.resSort, find?, consts⟩
  let holes ← unwrapOr (nestHoles ctx) (.internal "direct rec: a member is not a stored former")
  -- the walk on the STORED (declared) constructors; their normal forms are output only
  let (kinds, nfs, _) ← nestBlockCtors ops env₁ ctx holes ctorsAs {}
  unless nst || nestKindsFlat kinds do
    throw (.notImplemented "direct rec: a nested occurrence of the block (not modeled here)")
  checkAbsCtorTysAll ops env₁ ctx holes ctorsAs nfs
  pure (kinds, nfs)

/-- **What one pass over the formers and the constructors yields**
(`NativePass` at k members). -/
structure BlockPass (E : Type) where
  /-- the environment holding all k formers, at the record the pass ran at -/
  env₁ : E
  /-- the annotated formers, in block order -/
  cvTas : List ConstantVal
  /-- the completed record: the sort read -/
  p : BlockParts
  /-- the annotated constructors, per member, AS DECLARED (lane ALPHA1) -/
  ctorsAs : List (List (ConstantVal × Nat))
  /-- the fields' sorts, per member, per constructor -/
  sortsss : List (List (List Level))
  /-- the positivity function's field kinds, per member, per constructor -/
  kinds : List (List (List NestFieldKind))
  /-- the positivity function's normal forms, per member, per constructor
  (member-abstracted at the walk's context) -/
  nfs : List (List Expr)

/-- **The constructors at the positivity function's normal forms**
(lane ALPHA1): each annotated constructor with its type replaced by its
normal form `nf` (member-abstracted at the walk's context, the pass's
`nfs`) made concrete again (`nestConcreteCtor`).  Fed ONLY to the
reject-only recursor conformance check (`checkBlockRecConform`), whose
one-member generator classifies and generates on the telescope official's
`check_positivity` sees (the fields whnf'd); nothing the model reads. -/
def blockNormalCtors (p : BlockShape) (ctorsAs : List (List (ConstantVal × Nat)))
    (nfs : List (List Expr)) : List (List (ConstantVal × Nat)) :=
  let ctx := p.nestCtx [] (fun _ => none) []
  (ctorsAs.zip nfs).map fun (cs, ns) => (cs.zip ns).map fun (c, n) =>
    let ty := (nestConcreteCtor ctx c.1.type n).getD c.1.type
    ({ c.1 with type := ty }, c.2)

/-- **One pass over the formers and the constructors** at a given
`is_rec` verdict (task #268 at k members): the formers, the
constructors, and the positivity function on the stored constructors.
The last component says whether the walk's `is_rec` (`nestIsRec`)
confirms the verdict the pass ran at.  `nst` is the route switch
(`checkBlockPositivity`). -/
def checkBlockPass (ops : CheckerOps m) (env : Env) (p₀ : BlockParts) (isRec : Bool)
    (nst : Bool := false) :
    m (BlockPass Env × Bool) := do
  let (env₁, cvTas, p₁) ← checkBlockInds ops env p₀ isRec
  let pC := p₀.complete p₁
  let (ctorsAs, sortsss) ← checkBlockCtors ops env₁ env₁ pC.toBlockShape
    (pC.members.zip cvTas)
  -- positivity: the one function on the stored constructors, and U2
  let (kinds, nfs) ← checkBlockPositivity ops env₁ env₁.find? env₁.consts pC cvTas ctorsAs nst
  pure (⟨env₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs⟩,
    (List.range pC.k).all fun i =>
      blockCapsAt pC.toBlockShape i (nestIsRec kinds) == blockCapsAt p₁ i isRec)

/-! ## Stage 2: the tail -/

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
that consume them — the pins, the types, the rules — and the
reject-only conformance check after them. -/

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

/-- **The member's parameter-and-index telescope, opened at the
RECURSOR's own binder numbering** (lane SEC2, 2026-09-22).

The parameters take fvars `0 … nP-1` — the recursor's own first `nP`
binders — and the INDEX telescope takes `rP … rP+nIdx-1`, which is
where the recursor binds its indices.  Without that offset the two
telescopes are not comparable at all: an index domain that mentions an
earlier index names fvar `nP+i` on the member's side and fvar `rP+i`
on the recursor's, so a binder-by-binder `isDefEq` would fail on every
family whose indices depend on one another. -/
def openPisParamsIdx (nP nIdx rP : Nat) (ty : Expr) : Option (List Expr × Expr) :=
  match openPisAtFvars nP ty 0 with
  | none => none
  | some (pfvs, body) =>
    match openPisAtFvars nIdx body rP with
    | none => none
    | some (ifvs, rest) => some (pfvs ++ ifvs, rest)

/-- **The CHECKED elimination level IS the GENERATED one** (lane SEC2,
2026-09-22).

The rule frame the model reads carries
`pw := Level.zeronessOf (structElimLevel p.elim p.large)`, and nothing
tied that level to the one stage (b) actually read off the recursors'
CONCLUSIONS.  `BlockShape.large` is a level-parameter SHAPE, so two
residues were open: at `large = true` a recursor may carry an unused
fresh parameter and still conclude in `Prop`, and the frame then reads
"maybe non-zero" where the truth is zero (conservative); at
`large = false` with a never-zero result sort `blockLargeElimAllowed`'s
FIRST disjunct fires, the conclusion is unconstrained, and the frame
claims the induction binders are PROPOSITIONS while the elimination is
into `Type` — the wrong direction.

One pure check closes both: every recursor's conclusion sort is
`Level.isEquiv` to `structElimLevel p.elim p.large`.  It is true of
every stream official emits — the motive lands in `Sort elim` when the
eliminator is large and in `Prop` when it is not, and `p.elim` is read
off the first recursor's own level parameters (`BlockParts.lean`).

It IS D-d — one elimination level for the whole family (the ruling of
2026-09-21): every conclusion sort is equivalent to the same generated
level, so the model takes one `ℓ` per family
(`blockRecElimPin_run`, `Model/Inductives/BlockRecPreRun.lean`).  The
separate pairwise check D-d once had (every conclusion sort
`Level.isEquiv` to the FIRST one's) was deleted by lane INVERT
(2026-09-23): the pin implies it semantically, which is the currency
the model reads, and deleting it moved no verdict (arena and e2e
batteries unchanged). -/
def checkBlockRecElimPin (p : BlockShape) (us : List Level) : m Unit := do
  unless ← liftFueled "level comparison"
      (Level.isEquivList us (us.map fun _ => structElimLevel p.elim p.large)) do
    throw (.invalid "direct rec: the block's recursors do not eliminate at the generated \
      elimination level")

/-- **The COUNTING half of the elimination guard, in the MODEL's
currency** (lane SEC2, 2026-09-22).

`blockLargeElimAllowed` (`BlockRec.lean`) is read per RECURSOR, and the
arm it guards is an `isDefEq` of the conclusion's inferred type against
`Sort 0` — a RUN, not a level.  The model cannot invert that run: what
it holds of a recursor's conclusion is the LEVEL the stage returned
(`ensureSort`, the entry's third component), and the only route from
"the conclusion's type is definitionally `Sort 0`" to "that level
evaluates to `0`" goes through the whole defeq-soundness pile at the
recursor's own opened telescope, in a context nothing reconstructs.

So the checker says it in the currency the model reads.  Two clauses:

* **a block declares a family at all** (`0 < p.k`).  Nothing else in
  the stage says so, and it is what stops "some recursor eliminates at
  a non-zero level" from being vacuously compatible with an empty
  recursor list;
* **a block a large eliminator is not ALLOWED on eliminates at a level
  equivalent to zero** — literally `blockLargeElimAllowed`, the very
  disjunction stage (b) reads, with the level list in place of the
  `isDefEq` run.  It rejects nothing official emits: when official's
  criterion fires its elimination level IS `Level.zero` (the recursor
  carries no fresh parameter and its motive lands in `Prop`), so the
  second disjunct holds; when it does not, the first does.

Stating it as the GUARD rather than as the one counting fact the
squash arm needed is deliberate: the arm needs four facts, not one, and
`blockLargeElim_counting` (`Model/Inductives/BlockRecPreRun.lean`)
already reads all four off the verdict at a `Prop` result sort.  So the
run gets the VERDICT here and the four facts there — one fact, one
route, one name — instead of a second derivation of `k = 1` in the
level currency beside the regime lane's.

What it buys is the fact the recursor model's `huniq` at a `Prop`
block with a large motive cannot do without: `ℓ ψ ≠ 0` and `w ψ = 0`
FORCE one member with at most one constructor
(`blockRecCounting_run`, `Model/Inductives/BlockRecPreHpre.lean`), so
the decoding of a major is a function of its index.  The per-field subsingleton
half of the same criterion is the constructors' stage's
(`checkStructFieldSortsI`) and the per-recursor half is stage (b)'s
`isDefEq`; this is the third, and it is the only one the model can
read. -/
def checkBlockRecSmallElim (p : BlockShape) (nested : Bool) (us : List Level) : m Unit := do
  unless 0 < p.k do
    throw (.invalid "direct rec: the block declares no family")
  unless blockLargeElimAllowed p nested ||
      us.all (fun u => Level.isEquiv u .zero == some true) do
    throw (.invalid "direct rec: a block a large eliminator is not allowed on \
      eliminates only into Prop")

/-- **The family's rule PREFIX is SHARED** (the finding of lane RM16,
adopted as a ruling on 2026-09-22; DESIGN).

Stage (b) compares a recursor's first `nP` binder domains with the
block's parameters and leaves the stretch `nP … rP-1` — the motives
and the minor premises — unread.  That is not enough: a guarded call
in a rule passes the CALLER's own prefix variables (the strict ruling
of 2026-09-21), so the caller's prefix values are handed to the
CALLEE's recursor, and nothing typed them against the callee's prefix
domains — the rule check abstracts the call into an `ih` variable
whose type is an `instPisAtLift` of the callee's type BEFORE the
residue is typed, so without this agreement the arguments would be
checked against the caller's prefix only.

Official generates one shared prefix (the parameters, then ALL the
motives, then ALL the minors) for a block's recursors, so requiring
them to agree binder by binder up to defeq accepts every real stream;
a family whose recursors carry different motive-and-minor telescopes
is INVALID INPUT.

It is a pass of its own, over the CHECKED constant values stage (b)
returns, rather than a widening of stage (b)'s own comparison: the
first recursor's prefix is the reference and stage (b) is a fold with
no accumulator. -/
def checkBlockRecPrefixAt (ops : CheckerOps m) (env : Env) (p : BlockShape) (rP0 : Nat)
    (doms0 : List Expr) : List ConstantVal → Nat → m Unit
  | [], _ => pure ()
  | cv :: rest, ri => do
    unless p.rulePrefixAt ri == rP0 do
      throw (.invalid "direct rec: the block's recursors do not share their rule prefix \
        (their prefixes have different lengths)")
    let (fvs, _) ← unwrapOr (openPisAtFvars rP0 cv.type 0)
      (.invalid "direct rec: the recursor's type does not bind the family's rule prefix")
    checkBlockDefEqList ops env rP0
      "the block's recursors do not share their rule prefix"
      doms0 (fvs.map Expr.fvarTypeD)
    checkBlockRecPrefixAt ops env p rP0 doms0 rest (ri + 1)

/-- **Stage (b'):** the prefix agreement, at the first recursor's own
opening as the reference. -/
def checkBlockRecPrefixAgree (ops : CheckerOps m) (env : Env) (p : BlockShape)
    (cvRs : List ConstantVal) : m Unit :=
  match cvRs with
  | [] => pure ()
  | cv0 :: rest => do
    let (fvs0, _) ← unwrapOr (openPisAtFvars (p.rulePrefixAt 0) cv0.type 0)
      (.invalid "direct rec: the recursor's type does not bind the family's rule prefix")
    checkBlockRecPrefixAt ops env p (p.rulePrefixAt 0) (fvs0.map Expr.fvarTypeD) rest 1

/-- **Run a stage, then a reject-only check; return the stage's
result.**  The seam between a verified stage and an unverified
conformance check: the check can only turn an `ok` into an error,
never change what the stage returned, so a proof about the stage
reads through it with one lemma (`thenConform_ok`,
`ConLeche/Verify/Inductives/BlockWF.lean`) and never peels the check. -/
@[inline] def thenConform {α : Type} (stage : m α) (conform : m Unit) : m α := do
  let r ← stage
  conform
  pure r

end ConLeche
