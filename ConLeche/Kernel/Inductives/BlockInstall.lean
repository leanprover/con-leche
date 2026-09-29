module

public import ConLeche.Kernel.Inductives.SumInstall
public import ConLeche.Kernel.Inductives.SumParts
import ConLeche.Kernel.Inductives.BlockParts
public import ConLeche.Kernel.Inductives.BlockRec

@[expose] public section

/-!
# The uniform inductive install, at k members

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
2. **TAIL**: the index binders' sorts, the
   constructors consed, the recursor stage, and the projection table at
   every structure-like member.

The recursor stage (`BlockTail.lean`) GENERATES the recursors
(`genRecCheck`, `GenRec.lean`) at every `k`: the stream's recursor
types are compared with the generated ones, the stream's rules are
never read.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The capability record, per member -/

/-- **The capability record of member `m`**: official's
`is_non_rec_structure` (`inductive.cpp:28`, v4.34.0) is
`ncnstrs == 1 && nindices == 0 && !is_rec` with `is_rec` read over ALL
constructors of ALL members, so η and unit-likeness are the MEMBER's
data at the BLOCK's recursion verdict; rule K is official's
`is_K_target`, which requires `m_ind_types.size() == 1` — a one-member
block.  BOTH η (`try_eta_struct_core`, `type_checker.cpp:896`) and
unit-η (`is_def_eq_unit_like`, `type_checker.cpp:1162`) are gated on
`is_non_rec_structure`, so both carry `!isRec` (unit-η at a member of a
recursive block would be an accept-superset, stream
`whnfswap_unitpost_bad`).  At a FIELDLESS constructor of a
non-recursive block the record claims BOTH unit-likeness and η, as
official's gate does: the recursor's major-premise rescue (`Core.lean`,
the `etaFields = 0` arm — arena `073_typeSingletonRecReduction`) keys
on η.  (Granting η at a recursive structure-like is sound in the model
but not in practice: at a reflexive `W1 α = sup (a : α) (f : Nat →
W1 α)` `isDefEq` spins through η-expansion, `ind_nest_via_refl` —
official's `!is_rec` is load-bearing.) -/
def blockCapsAt (p : BlockShape) (mi : Nat) (isRec : Bool) : IndCaps :=
  match (p.members.getD mi default).ctors, (p.members.getD mi default).nIdx with
  | [c], nIdx =>
    { eta := nIdx == 0 && !p.isProp && !isRec
      etaCtor := c.1.name
      etaParams := p.nP
      etaFields := c.2
      unitlike := nIdx == 0 && c.2 == 0 && !isRec
      unitParams := p.nP
      ruleK := p.k == 1 && c.2 == 0 && p.isProp
      sortZ := Level.zeronessOf p.resSort
      all := p.memberNames
      nparams := p.nP }
  | _, _ => { all := p.memberNames, nparams := p.nP }

/-- Does some binder domain of the SYNTACTIC `∀`-telescope of `e`
mention one of `names`?  No reduction: the walk stops at the first
non-`∀`, as official's `while (is_pi(t))` loop does. -/
def Expr.piDomsMentionAny (names : List Name) : Expr → Bool
  | .forallE ty b _ => ty.mentionsAnyConst names || b.piDomsMentionAny names
  | _ => false

/-- **Official's `is_rec`** (`inductive.cpp:308`, v4.34.0, stored by
`declare_inductive_types` into every member's `inductive_val`): does
SOME member of the block occur in SOME binder domain of the syntactic
`∀`-telescope of SOME DECLARED constructor type of SOME member?  A
`find` on the raw domain — no `whnf`, so a domain `Const Nat T` whose
reduct is block-free still counts (reading the verdict off the
positivity walk's normalised kinds instead would be an
accept-superset, stream `whnfswap_unitcaps_bad`).  Known before any
constructor is checked, so the formers are installed at it once.  The
parameter domains are scanned too, as official does; they cannot hold a
member on a stream official accepts (`check_uniform_ind_occs`). -/
def blockRawRec (p : BlockParts) : Bool :=
  p.members.any fun ms => ms.ctors.any fun c => c.1.type.piDomsMentionAny p.memberNames

/-! ## Stage 1: the formers -/

/-- One member's type former: the constant check, official's telescope
loop (task #195) and the result sort — without the environment cons,
which at k members happens only once every former has been checked. -/
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

/-! ## Positivity: the ONE function, on the stored constructors

Charter item 3: "There is ONE positivity function in the kernel … The
theorem is 'returns true ⇒ the operator is monotone', proved by
inversion of that function's run."  The install runs `nestPos` on the
STORED constructors as the walk's ROOT frame (`nestRoot`,
`Kernel/Inductives/Positivity.lean`): the members abstracted to holes at
the canonical parameter variables, each constructor TYPED there (the
typing the monotonicity proof reads at every hole value — a frame types
its constructors), walked, recorded.  The root's own lines follow: the
members' uniform occurrences (`nestRootLinesAll`) and the fields'
universes at the holes (`checkAbsCtorSorts`).  The walk's kinds are the
model's; the capability record's `is_rec` is official's syntactic one
(`blockRawRec`), not read off them. -/

/-- **The fields' universes at the holes** (the root's line, U2's sort
half): the fields of every constructor's positivity NORMAL FORM `tyN`
(the root frame's output) have their universes bounded by the family's
at the holes' context (at a `Type`-valued family) — the model's hole
operator reads every field in the family's universe at every tuple of
the tuple space, which no stored reading reaches; the row reads the
normal form, not the declared type: the model's fields with holes ARE
the normal form's readings.  Beside it, an internal scoping assertion on
`tyN`: its level parameters are the block's (whnf unfolds at the use
site's levels, so it never fires; the model's readings of `tyN` are
level-congruent through it). -/
def checkAbsCtorSorts (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (ConstantVal × Nat) → List (List NestFieldKind × Expr) → m Unit
  | c :: cs, o :: os => do
    unless o.2.allLevelParamsDefined ctx.lps do
      throw (.internal "direct rec: a positivity normal form outside the block's level \
        parameters")
    let xq ← unwrapOr (openPisAtFvars c.2 o.2 (ctx.hiAt 0))
      (.internal "direct rec: abstracted constructor fields")
    let _ ← checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
      ctx.sort (ctx.hiAt 0) xq.1 [] c.2
    checkAbsCtorSorts ops env ctx cs os
  | _, _ => pure ()

/-- `checkAbsCtorSorts` on every member's constructors. -/
def checkAbsCtorSortsAll (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (List (ConstantVal × Nat)) → List (List (List NestFieldKind × Expr)) → m Unit
  | cs :: css, os :: oss => do
    checkAbsCtorSorts ops env ctx cs os
    checkAbsCtorSortsAll ops env ctx css oss
  | _, _ => pure ()

/-- **The walk's context** of a block: the canonical parameter variables
are the first former's opened telescope, `find?`/`consts` the
environment's lookup (the pure `Env`'s or the index's), with the
members' holes (`nestHoles`).  Built by the positivity check and again by
the recursor stage's seeds (`genRecCheck`), from the same inputs. -/
def blockNestCtx (p : BlockShape) (cvTas : List ConstantVal)
    (find? : Name → Option ConstantInfo) (consts : List ConstantInfo) :
    m (NestCtx × List Expr) := do
  let cvTa0 ← unwrapOr cvTas.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (openPisAtFvars p.nP cvTa0.type 0)
    (.internal "direct rec: type former telescope")
  let ctx := p.nestCtx pq.1 find? consts
  let holes ← unwrapOr (nestHoles ctx) (.internal "direct rec: a member is not a stored former")
  pure (ctx, holes)

/-- **The block's positivity, on its stored constructors** (see the
section docstring), at the walk's context (`blockNestCtx`): the root
frame and its own lines.  Returns the walk's field kinds, its normal
forms (member-abstracted, at the walk's context; OUTPUT only: nothing is
stored from them) and its state — the cache and the recorded constructor
normal forms, which the recursor stage's seeds continue
(`genRecCheck`); the walk's verdict is the install's. -/
def checkBlockPositivity (ops : CheckerOps m) (env₁ : Env) (find? : Name → Option ConstantInfo)
    (consts : List ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (List (List NestFieldKind)) × List (List Expr) × NestState) := do
  let (ctx, holes) ← blockNestCtx p.toBlockShape cvTas find? consts
  -- the root frame on the STORED (declared) constructors; their normal forms are output only
  let (outs, st) ← nestRoot ops env₁ ctx holes ctorsAs {}
  nestRootLinesAll ctx holes ctorsAs outs
  checkAbsCtorSortsAll ops env₁ ctx ctorsAs outs
  pure (outs.map (·.map (·.1)), outs.map (·.map (·.2)), st)

/-- **What one pass over the formers and the constructors yields**. -/
structure BlockPass (E : Type) where
  /-- the environment holding all k formers, at the record the pass ran at -/
  env₁ : E
  /-- the annotated formers, in block order -/
  cvTas : List ConstantVal
  /-- the completed record: the sort read -/
  p : BlockParts
  /-- the annotated constructors, per member, AS DECLARED -/
  ctorsAs : List (List (ConstantVal × Nat))
  /-- the fields' sorts, per member, per constructor -/
  sortsss : List (List (List Level))
  /-- the positivity function's field kinds, per member, per constructor -/
  kinds : List (List (List NestFieldKind))
  /-- the positivity function's normal forms, per member, per constructor
  (member-abstracted at the walk's context) -/
  nfs : List (List Expr)
  /-- the positivity walk's state after the members' constructors (its
  cache and the recorded constructor normal forms, `NestCtorNf`), which
  the recursor stage's seeds continue (`genRecCheck`);
  installer-local, never stored -/
  pos : NestState

/-- **One pass over the formers and the constructors** at the block's
`is_rec` verdict (`blockRawRec`, known before any constructor is
looked at, as official's `declare_inductive_types` stores it): the
formers, the constructors, and the positivity function on the stored
constructors. -/
def checkBlockPass (ops : CheckerOps m) (env : Env) (p₀ : BlockParts) (isRec : Bool) :
    m (BlockPass Env) := do
  let (env₁, cvTas, p₁) ← checkBlockInds ops env p₀ isRec
  let pC := p₀.complete p₁
  let (ctorsAs, sortsss) ← checkBlockCtors ops env₁ env₁ pC.toBlockShape
    (pC.members.zip cvTas)
  -- positivity: the one function, its root frame the stored constructors
  let (kinds, nfs, pos) ← checkBlockPositivity ops env₁ env₁.find? env₁.consts pC cvTas ctorsAs
  pure ⟨env₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, pos⟩

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

/-! ### The recursor stage as CHECKING

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

/-- **The member's parameter-and-index telescope, opened at the
RECURSOR's own binder numbering**.

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

end ConLeche
