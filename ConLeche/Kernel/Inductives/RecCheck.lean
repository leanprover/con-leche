module

public import ConLeche.Kernel.Inductives.BlockInstallF
public import ConLeche.Conformance.K53

@[expose] public section

/-!
# The recursor check: primitive recursion, classification-free

Charter item 5 (DESIGN.md, "THE CHARTER"): *recursors are CHECKED, not
generated.  The check is primitive recursion: every rule matches a
constructor and recurses only on that constructor's fields (reflexive
fields applied to enough arguments).  It is as liberal as possible:
calls on fields of ANY inductive type, with no field classification and
no target member.*

The check reads no field kind and no target member.  It takes the
recursor FAMILY the stream installs with
the block — every recursor record of the block, nested auxiliaries
like `T.rec_1` (major `List T`) included — and asks, per recursor:

* **the major** is an application `I.{us} D⃗ ı⃗` of a stored inductive
  `I` — a member of the block (at the block's levels and parameters,
  the member the recursor record names, its parameter domains the
  member's former's) or ANY other stored inductive (not `Quot`) at one
  of the block's auxiliary types, whose parameters
  `D⃗` mention only the recursor's parameter binders — at exactly the
  recursor's index binders `rP … mI-1`;
* **the rules** are one per constructor of `I` in `I`'s order (a
  member's from the block, an outside inductive's from the
  environment), each binding the recursor's prefix and that
  constructor's fields AT THE MAJOR'S INSTANTIATION `(us, D⃗)`;
* **every recursive call** in a rule body is `rec_c x⃗ e⃗ (f a⃗)` with
  `rec_c` a member of the family (at the family's levels, with the
  caller's OWN prefix `x⃗`), `f` a field of THIS rule's constructor,
  `a⃗` that field's own telescope variables (`structTeleVars`), and
  `e⃗` any recursor-free terms over `a⃗` and the frame.  The call is
  replaced by an `ih` variable whose type is `rec_c`'s STORED type
  instantiated at exactly the call's arguments, under `∀ a⃗`; the
  field's type must be `rec_c`'s major domain at `x⃗ e⃗` (defeq, under
  a hole-free `∀ a⃗`), compared with the block's members ABSTRACTED to
  free variables — the holes of charter item 2 — so that the equation
  holds at every value of the holes (the graph recursor's
  induction needs it at the separated tuple, where a concrete defeq
  says nothing).  Nothing is keyed by a field kind or a target member: the
  `ih` variables are the calls the body makes, in order of first
  occurrence, identical calls (same field, callee and index arguments)
  sharing one;
* the residue is TYPED against the recursor's conclusion at
  the prefix, the constructor's result indices and the major
  `c.{us} D⃗ f⃗`.

**Where it runs.**  The uniform route's recursor stage runs this check
(`checkBlockRecT`, `BlockTail.lean`) — a nested block's auxiliary
recursors eliminate its containers' instantiations — with `nested` the
block's container bit (`blockNestedBit`).  It is written ONCE, over
an `FEnv`, parameterised by `ShadowOps` (the operations at an index, a
flush, the walkers), so the pure install (`ShadowOps.ofOps`), the unit
tests and the cached fold (`shadowOpsC`, `ConLeche/Cached/CheckerC.lean`)
run the same code.
-/

namespace ConLeche

/-- **The operations the shadow runs on**, per index: the checker's
entry points at an `FEnv` (`opsAt`), their rule-annotation variant
(`opsRuleR`: the cached one flushes at the two environment transitions
a rule makes, `sharedOpsRuleR`), the flush at an environment change,
and the syntactic walkers.  The pure instantiation ignores the index
(the pure operations read the `Env` they are handed); the cached one
is index-bound. -/
structure ShadowOps (m : Type → Type) where
  opsAt : FEnv → CheckerOps m
  opsRuleR : FEnv → CheckerOps m
  flush : m Unit
  walkers : StructWalkers

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A checker's operations as shadow operations: the same at every
index, no flush, the plain walkers — how the PURE install runs the
check (`checkBlockRec`, `BlockTail.lean`). -/
def ShadowOps.ofOps (ops : CheckerOps m) : ShadowOps m :=
  ⟨fun _ => ops, fun _ => ops, Pure.pure (), .plain⟩

/-- The pure operations at fuel `F`, at every index (the fueled
instantiation the model reads a run of). -/
def ShadowOps.fueled (mode : CheckMode) (F : Nat) : ShadowOps CheckM :=
  ShadowOps.ofOps (fueledOps mode F)

/-! ## The major -/

/-- **A recursor's major, resolved.**  `ind.{lvls} ds ı⃗` with `ds`
the inductive's parameters at the recursor's own binders (fvars
`0 … nP-1`), `nPc` its parameter count, `nIdx` its index count at that
instantiation, `ctors` its constructors in declaration order with their
field counts, and `member` the block member it is (`none`: an outside
inductive — a nested block's container). -/
structure TargetMajor where
  ind : Name
  lvls : List Level
  ds : List Expr
  nPc : Nat
  nIdx : Nat
  ctors : List (ConstantVal × Nat)
  member : Option Nat
  /-- the universe the major lives in (its type former's result sort at
  the instantiation) -/
  sort : Level := .zero
  /-- the positivity walk's recorded normal forms of this class's
  constructors (`targetMajorNfs`, K.53′) — `none` when the family is
  checked without the walk (`targetLegacyAux`) -/
  nfs : Option (List NestCtorNf) := none
  /-- the members of the inductive's block (its recorded `IndCaps.all`; a
  member major's: the installing block's) — the class's HOME, whose
  members a call around a cycle reads as holes (`targetIntraCallOk`) -/
  home : List Name := []
  /-- PRIMREC/NESTHOME: the home table's normal forms of this class, where
  its layer of the call graph is checked against the table
  (`targetHomeOf`) — then the K.53 source of its calls, which skip
  `targetIntraCallOk`; `none` elsewhere -/
  homeNfs : Option (List NestCtorNf) := none
  deriving Inhabited

/-- **The walk's recorded constructor normal forms of a class** (K.53′):
the entries (`NestNodes.ctors`) at the class's levels whose parameters are
the class's up to the free variables' annotations (the walk opens the
block's parameters at the first former's telescope, a recursor at its
own). -/
def targetMajorNfs (aux : NestNodes) (lvls : List Level) (ds : List Expr) : List NestCtorNf :=
  aux.ctors.filter fun e =>
    e.lvls == lvls && e.ds.map Expr.eraseFVarTys == ds.map Expr.eraseFVarTys

/-- The constructors of a stored inductive `I` and its parameter count,
read off the environment (`nestContainer`'s reading: a constructor
belongs to the type its result names). -/
def targetCtorsOf (fe : FEnv) (I : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  nestContainer ⟨[], [], 0, [], [], .zero, fe.find?, fe.env.consts⟩ I

/-- The instantiated type former of an OUTSIDE major `I.{us} ds`: its
index count and its result sort (a syntactic telescope, as
`nestInstType` reads it). -/
def targetOutsideInst (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr) :
    m (Nat × Level) := do
  let some (.indInfo cvI _) := fe.find? I
    | throw (.invalid "target rec: the recursor's major is not a stored inductive")
  let some ty := instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us)
    | throw (.invalid "target rec: the major's type former does not bind its parameters \
        (official: ill-formed inductive type)")
  let (ibs, s) := ty.piBinders
  let .sort s := s
    | throw (.invalid "target rec: the major's type former is not a telescope ending in a \
        sort (official: type expected)")
  pure (ibs.length, s)

/-! ## Stage (b): every recursor's TYPE, at any major -/

/-- **An OUTSIDE major, resolved**: the stored inductive `I.{us}` (not
`Quot`) applied to `args`, its parameters `ds` (the first `nPc`
arguments) mentioning only the recursor's parameter binders, in any universe — any stored
inductive, a member of the block itself at other parameters included,
and, where the family is checked against the walk (`aux = some _`,
`targetLegacyAux`), one of the block's auxiliary types. -/
def targetOutsideMajorOf (fe : FEnv) (p : BlockShape) (aux : Option NestNodes) (I : Name)
    (us : List Level) (args : List Expr) : m TargetMajor := do
  if I == quotName then
    throw (.invalid "target rec: the recursor's major is Quot, which is no inductive")
  let some (nPc, ctors) := targetCtorsOf fe I
    | throw (.invalid "target rec: the recursor's major is not a stored inductive")
  let ds := args.take nPc
  unless ds.length == nPc &&
      ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ p.nP) do
    throw (.invalid "target rec: the major's parameters mention more than the \
      recursor's parameters")
  -- **An auxiliary type of the block** (only against the walk): the
  -- outside major `I.{us} Ds` is one of the classes of the positivity
  -- walk's nodes (`aux`, `NestState.nodes`: every node's group at its
  -- instantiation, the holes back to their constants), with official's
  -- `is_nested` (some parameter `Dᵢ` names a member of the block,
  -- `inductive.cpp` v4.34.0 :1033–1049) and not the block's own member
  -- (whose instances official never makes classes).  Official accepts an auxiliary
  -- recursor exactly at an auxiliary type of `elim_nested_inductive_fn`
  -- (a syntactic nested occurrence in the constructors and in the copied
  -- containers' constructors, each container's WHOLE block `get_all()`),
  -- restored verbatim into the recursor (`restore_nested`); the walk's
  -- nodes cover that set (N2-eager frames, the syntactic pass
  -- `nestSyn`), so this refuses nothing official accepts.  The node
  -- route's proof reads both: every outside class is a node, and a call
  -- on a field whose walked type names no member and no hole targets no
  -- class.  Read without whnf and without entering a free variable's
  -- annotation (`nestOcc` at an empty hole range).
  unless aux.all fun aux => !p.memberNames.contains I &&
      ds.any (fun x => x.nestOcc p.memberNames 0 0) && aux.keys.contains ⟨I, us, ds⟩ do
    throw (.invalid "target rec: the recursor's major is an outside inductive at an \
      instantiation that is no auxiliary type of the block (official generates no such \
      auxiliary recursor: `elim_nested_inductive`, `is_nested`)")
  let (nIdx, sI) ← targetOutsideInst fe I us ds
  pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx, ctors := ctors,
         member := none, sort := sI, nfs := aux.map (targetMajorNfs · us ds),
         home := match fe.find? I with
           | some (.indInfo _ caps) => caps.all
           | _ => [] }

/-- **A recursor's major, resolved** from its opened type `mty`
(`fvs` the recursor type's openers): a MEMBER of the block at the
block's levels and parameters, or any other stored inductive instance
(`targetOutsideMajorOf`). -/
def targetMajorOf (fe : FEnv) (p : BlockShape) (aux : Option NestNodes)
    (ctorsAs : List (List (ConstantVal × Nat))) (fvs : List Expr) (mty : Expr) :
    m TargetMajor := do
  let args := mty.getAppArgs
  match mty.getAppFn with
  | .const I us =>
    match p.memberNames.findIdx? (· == I) with
    | some t =>
      if us == p.lps.map .param && args.take p.nP == fvs.take p.nP then do
        -- a MEMBER: at the block's levels and parameters
        let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
        let ctorsA ← unwrapOr ctorsAs[t]? (.internal "target rec: member constructors")
        pure { ind := I, lvls := us, ds := fvs.take p.nP, nPc := p.nP, nIdx := ms.nIdx,
               ctors := ctorsA, member := some t, sort := p.resSort,
               nfs := aux.map (targetMajorNfs · us (fvs.take p.nP)),
               home := p.memberNames : TargetMajor }
      else
        -- an instance of a member at other parameters: a class of its own
        targetOutsideMajorOf fe p aux I us args
    | none => targetOutsideMajorOf fe p aux I us args
  | _ => throw (.invalid "target rec: the recursor's major premise is not an inductive's \
      application")

/-- **The major's index telescope**, the domains the recursor's index
binders must have: a member's at the member's own opening, an outside
inductive's at its instantiation. -/
def targetIdxDoms (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal) (rP : Nat)
    (M : TargetMajor) : m (List Expr) :=
  match M.member with
  | some t => do
    let cvTa ← unwrapOr cvTas[t]? (.internal "target rec: type former")
    let (tfs, _) ← unwrapOr (openPisParamsIdx p.nP M.nIdx rP cvTa.type)
      (.internal "target rec: type former telescope (index-domain pass)")
    pure ((tfs.drop p.nP).map Expr.fvarTypeD)
  | none => do
    let some (.indInfo cvI _) := fe.find? M.ind
      | throw (.internal "target rec: major inductive vanished")
    let some ty := instPisWith M.ds (cvI.type.instantiateLevelParams cvI.levelParams M.lvls)
      | throw (.internal "target rec: major type former telescope")
    let (ifs, _) ← unwrapOr (openPisAtFvars M.nIdx ty rP)
      (.internal "target rec: major index telescope")
    pure (ifs.map Expr.fvarTypeD)

/-- **An outside major's parameters, typed at the rule prefix**:
each `D_i` of the major
`I.{us} D⃗ ı⃗`, at the depth of the rule prefix `rP` (the `D⃗` mention only
the parameter binders).  The recursor type's own check types them only
under the index binders, which may be uninhabited; the rule law of an
auxiliary recursor's `.nested` rules (`RecRuleLaw`, `EnvWF`'s pins) reads
the pins graded at the prefix itself.  It refuses nothing the recursor
type's check (`checkConstantValF`) accepted: the `D⃗` are closed over
binders below `rP`, so their typing does not depend on the index
binders.  Official types the same terms as the auxiliary constructors'
parameters (`check_constructors`, `tc().check`, `inductive.cpp`
v4.33.0 :426, after `elim_nested_inductive` instantiates the container's
constructors at them). -/
def targetPinTys (ops : CheckerOps m) (env : Env) (d : Nat) : List Expr → m Unit
  | [] => pure ()
  | x :: xs => do
    let _ ← ops.inferType env d x
    targetPinTys ops env d xs

/-- The check at a resolved major: an outside major's parameters typed
at the rule prefix (`targetPinTys`), and — for the model's rows
`hdec`/`hrule` — the instantiation `I.{us} D⃗` itself
typed there, so the `D⃗` SATISFY the container's parameter telescope at
the instantiation (the application's typing checks each `D_i` against
the telescope's domain instantiated at the earlier ones).  Official checks
exactly this term: `tc.check(nested, …)` on every replaced nested
application `I Ds` in the parameters' context (`inductive.cpp` v4.33.0
:1223–1231, "the parametric arguments `Ds` do not appear in the auxiliary
declaration, so they would otherwise escape type checking"); the `D⃗`
mention only the parameter binders, below `rP`.  Nothing at a member. -/
def targetMajorPins (ops : CheckerOps m) (env : Env) (rP : Nat) (M : TargetMajor) : m Unit :=
  if M.member.isNone then do
    targetPinTys ops env rP M.ds
    let _ ← ops.inferType env rP (Expr.mkAppN (.const M.ind M.lvls) M.ds)
    pure ()
  else pure ()

/-- **The per-major large-elimination licence** (PRIMREC: the only
soundness guard of the family's large elimination): the major lives in
a universe that is never `Prop`, or its own block licenses large
elimination — the installing block's verdict at a member
(`blockLargeElimAllowed`, `nested` the walk's container bit), the
recorded one (`IndCaps.largeElim`) at any other inductive. -/
def targetMajorLicensed (fe : FEnv) (p : BlockShape) (nested : Bool) (M : TargetMajor) : Bool :=
  M.sort.isNeverZero ||
    match M.member with
    | some _ => blockLargeElimAllowed p nested
    | none =>
      match fe.find? M.ind with
      | some (.indInfo _ caps) => caps.largeElim
      | _ => false

/-- **One recursor's type**, at any major: the
constant check; `nP ≤ rP`; the first `nP` binder domains are the block's
parameter domains; the major resolved (`TargetMajor`) at exactly the
index binders; `mI = rP + nIdx`; the index binder domains are the
major's index telescope at its instantiation; the conclusion's sort,
Prop-pinned when the major does not license large elimination
(`targetMajorLicensed`). -/
def targetRecTy (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : Option NestNodes)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rc : RecShape) : m (ConstantVal × TargetMajor × Level) := do
  let cvRi ← checkConstantValF ops fe rc.cvR
  let rP := rc.rP
  let mI := rc.mI
  unless p.nP ≤ rP do
    throw (.invalid "target rec: the recursor's rule prefix is shorter than the block's \
      parameters")
  unless rP ≤ mI do
    throw (.invalid "target rec: the recursor's major-premise index is below its rule prefix")
  let (fvs, concl) ← unwrapOr (openPisAtFvars (mI + 1) cvRi.type 0)
    (.invalid "target rec: the recursor's type does not bind its parameters, its indices \
      and its major premise")
  let maj ← unwrapOr fvs[mI]? (.internal "target rec: major premise")
  let mty := maj.fvarTypeD
  let args := mty.getAppArgs
  let ixs := (fvs.drop rP).take (mI - rP)
  let M ← targetMajorOf fe p aux ctorsAs fvs mty
  -- K7: a member major is the member the recursor RECORD names (`RecShape.tgt`,
  -- read by the recogniser off the declared major); they differ only where
  -- the declared type reaches its major through a `let` the annotation
  -- unfolds — a record official never writes
  unless M.member.all (· == rc.tgt) do
    throw (.invalid "target rec: the recursor record's member is not its major's")
  -- an OUTSIDE major's parameters, typed at the rule prefix
  targetMajorPins ops fe.env rP M
  -- K6: the parameter domains against the MAJOR's former (a member's own;
  -- an outside major's: the first former's)
  let cvTP ← unwrapOr (M.member.elim cvTas.head? (fun t => cvTas[t]?))
    (.internal "target rec: no type former")
  let (tfvs, _) ← unwrapOr (openPisAtFvars p.nP cvTP.type 0)
    (.internal "target rec: type former telescope")
  checkBlockDefEqList ops fe.env p.nP
    s!"the recursor {rc.cvR.name}'s parameter domains are not the block's"
    (tfvs.map Expr.fvarTypeD) ((fvs.take p.nP).map Expr.fvarTypeD)
  unless mI == rP + M.nIdx do
    throw (.invalid "target rec: the recursor's major-premise index is not its rule prefix \
      plus the major's index count")
  unless args.length == M.nPc + M.nIdx && args.drop M.nPc == ixs do
    throw (.invalid "target rec: the recursor's major premise is not at its index binders")
  -- (b'') the index binder domains are the major's index telescope at
  -- its instantiation (a member's at the member's own opening)
  let idoms ← targetIdxDoms fe p cvTas rP M
  checkBlockDefEqList ops fe.env mI
    "the recursor's index domains are not the major's index telescope"
    idoms (ixs.map Expr.fvarTypeD)
  let sty ← ops.inferType fe.env (mI + 1) concl
  let u ← ops.ensureSort fe.env (mI + 1) sty
  unless targetMajorLicensed fe p nested M do
    unless ← ops.isDefEq fe.env (mI + 1) sty (.sort .zero) do
      throw (.invalid "target rec: large eliminator on a major whose sort may be Prop and \
        whose block does not license it")
  pure (cvRi, M, u)

/-! ## Stage (a): the pins, at any major -/

/-- **The recursor records' pins** (at any major).
The level parameters and the reserved names; the NAMES: the
recursors whose major is a member carry the set `{T_m.rec}`; the others (a
nested block's auxiliaries) carry pairwise
distinct names `T_0.rec_1 … T_0.rec_n` (official's naming, as a set).
The block's constructors in the stream's order are the members' in
block order (`blockRecPinOk`'s grouping conjunct).  The rule pins need
the majors' constructors and are `targetRulePins`. -/
def targetRecPins (p : BlockShape) (block : List ConstantInfo) : m Unit := do
  unless blockRecLpsOk p do
    throw (.invalid "target rec: the recursor's level parameters are not the generated ones")
  unless blockRecNamesUnreserved p do
    throw (.invalid "target rec: a recursor is named for a pinned basis constant, a literal \
      guard's slot or a certified Nat operation")
  let own := p.recs.filter fun rc => rc.tgt < p.k
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  unless blockRecNameSetOk { p with recs := own } do
    throw (.invalid "target rec: the block's recursor names are not the generated ones \
      (one T.rec per member)")
  let n0 := (p.memberNames.head?).getD .anonymous
  let wantAux := (List.range aux.length).map fun i => n0.str s!"rec_{i + 1}"
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    throw (.invalid "target rec: the block's auxiliary recursor names are not the generated \
      ones (T.rec_1 … T.rec_n)")
  -- the family's names are distinct (official: a duplicate declaration).
  -- Implied by the two name sets above (the generated names are
  -- distinct); stated here because the install conses the family one
  -- name at a time
  unless (p.recs.map (·.cvR.name)).Nodup do
    throw (.invalid "target rec: two recursors of the block share a name")
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      throw (.invalid "target rec: the recursor record is not the generated recursor \
        (constructor grouping)")
  | none => throw (.invalid "target rec: the block does not split")

/-- **The rule pins at the major**: one rule per constructor of the
major's inductive, in its order, each naming its constructor with its
field count (`blockRecPinOk`'s per-recursor conjunct, at any major). -/
def targetRulePins (rc : ConstantVal) (M : TargetMajor) (rules : List RecRule) : m Unit := do
  unless rules.length == M.ctors.length &&
      (List.range M.ctors.length).all (fun j =>
        match rules[j]?, M.ctors[j]? with
        | some r, some (cv, nF) => r.ctor == cv.name && r.nfields == nF
        | _, _ => false) do
    throw (.invalid s!"target rec: the rules of {rc.name} are not one per constructor of its \
      major's inductive, in order")

/-! ## Stage (c): one rule — the classification-free abstraction -/

/-- **A field's telescope, read through whnf** (the positivity
function's shape, `nestPos`, without its occurrence test): the domain whnf'd at its depth and, while
it is a `Π`, the body in turn — so a field whose type is a redex that
reduces to a `Π` (a container instantiated at a λ-pin,
`(fun _ => True → T) True.intro`) has the telescope official's
auxiliary recursor applies it to.  The leaf is kept as declared.  The
result is definitionally equal to the input.  `fuel` bounds the walk;
exhaustion declines. -/
def targetWhnfPis (ops : CheckerOps m) (env : Env) : Nat → Nat → Expr → m Expr
  | _, 0, _ => throw (.notImplemented "target rec: field telescope fuel")
  | d, fuel + 1, e => do
    let w ← ops.whnf env d e
    match w with
    | .forallE dom body bm => do
      let body' ← targetWhnfPis ops env (d + 1) fuel (body.instantiate1 (.fvar d dom))
      pure (.forallE dom (body'.abstract1 d) bm)
    | _ => pure e

/-! ### The holes: the block's members abstracted to free variables

Charter item 2: *the holes are ordinary open terms (members abstracted
to fvars)*.  A call's typing (the field is a value of the callee's
major type) is checked on the member-ABSTRACTED terms, not on the
concrete ones, because that is the only form whose soundness says
something at the model's SEPARATED tuple: a defeq run on the concrete
terms (members as constants, read as their carriers) equates the two
readings at the carrier alone, and the graph recursor's induction
(`GraphRecKit.ind`, via the recorded lfp clause) needs the called field
to land in the separated tuple — "the field is a hole at the callee's
class", which no carrier-level equation gives.  On the abstract
terms the same defeq holds at EVERY value of the holes, the separated
tuple included.

Member `t` at the block's levels becomes `.fvar (base + t) T_t.type`
(the former's own closed type, so the hole is applied to the
parameters exactly as the member was); a member at other levels stays
a constant.  A free variable's ANNOTATION is not abstracted: the
frame's fields keep their concrete types (a field's value fits them at
the carrier, and the separated tuple lies below it), so a hole occurs
in the abstract term only where the term itself names a member, and a
hole-free abstract term IS a concrete one.  Memoised on the node (tower-shaped DAG fields,
`tower_struct`).  It is NOT `replaceConsts`
(`Kernel/ExprOps.lean`) at the member map, on purpose: that one
rewrites free variables' annotations too, and here the frame's fields
must keep their concrete types (see below) — an abstracted annotation
would make every domain that names an earlier recursive field look
holed, and put hole variables into the `ih` types. -/

/-- The member abstraction of one term: every member at the block's
levels becomes its hole; `fvar` annotations are not entered. -/
def targetAbs (names : List Name) (lvls : List Level) (holes : List Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty
  | .sort u => .sort u
  | .lit l => .lit l
  | e@(.const n us) =>
    if us == lvls then
      match names.findIdx? (· == n) with
      | some t => holes.getD t e
      | none => e
    else e
  | .app a b => .app (targetAbs names lvls holes a) (targetAbs names lvls holes b)
  | .lam ty body bm => .lam (targetAbs names lvls holes ty) (targetAbs names lvls holes body) bm
  | .forallE ty body bm =>
    .forallE (targetAbs names lvls holes ty) (targetAbs names lvls holes body) bm
  | .letE ty v body =>
    .letE (targetAbs names lvls holes ty) (targetAbs names lvls holes v)
      (targetAbs names lvls holes body)
  | .proj s i sub => .proj s i (targetAbs names lvls holes sub)

/-- The memo's invariant: every recorded answer is the real one. -/
def TargetAbsMemoInv (names : List Name) (lvls : List Level) (holes : List Expr)
    (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ k v, memo[k]? = some v → v = targetAbs names lvls holes k

theorem TargetAbsMemoInv.insert {names : List Name} {lvls : List Level} {holes : List Expr}
    {memo : Std.HashMap Expr Expr}
    (hm : TargetAbsMemoInv names lvls holes memo) {e r : Expr}
    (heq : r = targetAbs names lvls holes e) :
    TargetAbsMemoInv names lvls holes (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- The member abstraction, memoised on the node (tower DAGs). -/
def targetAbsGo (names : List Name) (lvls : List Level) (holes : List Expr)
    (memo : Std.HashMap Expr Expr) : Expr → Expr × Std.HashMap Expr Expr
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | e@(.fvar _ _) => (e, memo)
  | e@(.const n us) =>
    if us == lvls then
      match names.findIdx? (· == n) with
      | some t => (holes.getD t e, memo)
      | none => (e, memo)
    else (e, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .app a b =>
          let (a', memo) := targetAbsGo names lvls holes memo a
          let (b', memo) := targetAbsGo names lvls holes memo b
          (.app a' b', memo)
        | .lam ty body bm =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.lam t b bm, memo)
        | .forallE ty body bm =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.forallE t b bm, memo)
        | .letE ty v body =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (v', memo) := targetAbsGo names lvls holes memo v
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.letE t v' b, memo)
        | .proj s i sub =>
          let (u, memo) := targetAbsGo names lvls holes memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoised walk is `targetAbs`.** -/
theorem targetAbsGo_spec {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Expr}, TargetAbsMemoInv names lvls holes memo →
      (targetAbsGo names lvls holes memo e).1 = targetAbs names lvls holes e ∧
        TargetAbsMemoInv names lvls holes (targetAbsGo names lvls holes memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | const n us =>
    intro memo hm
    simp only [targetAbsGo, targetAbs]
    split
    · split <;> exact ⟨rfl, hm⟩
    · exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | letE ty v body iht ihv ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [targetAbs, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [targetAbs, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [targetAbs, h1], ?_⟩
      exact h2.insert (by simp [targetAbs, h1])

/-- The executed member abstraction (one memoised DAG walk). -/
def targetAbsFast (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) : Expr :=
  (targetAbsGo names lvls holes {} e).1

@[csimp] theorem targetAbs_eq_targetAbsFast : @targetAbs = @targetAbsFast := by
  funext names lvls holes e
  exact (targetAbsGo_spec e (fun k v h => by simp at h)).1.symm

/-- The holes of a rule frame of width `base`: member `t` is
`.fvar (base + t)` at its former's type. -/
def targetHoles (formerTys : List Expr) (base : Nat) : List Expr :=
  (List.range formerTys.length).map fun t => .fvar (base + t) (formerTys.getD t default)

/-- No hole of the frame `base … base + k - 1` occurs in `e`. -/
def targetHoleFree (base k : Nat) (e : Expr) : Bool :=
  (List.range k).all fun t => !e.mentionsFvar (base + t)

/-- One `ih` variable of a rule's frame: the call it stands for, keyed
by the call itself (identical calls share one variable). -/
structure TargetIh where
  /-- the field the call recurses on -/
  field : Nat
  /-- the callee's position in the family -/
  callee : Nat
  /-- the call's index arguments, over the field's telescope and the frame -/
  idx : List Expr
  /-- `∀ a⃗ : A⃗, <the callee's stored type at the call's arguments>` -/
  ty : Expr
  /-- the variable: `.fvar (rP + nF + r) ty` -/
  fv : Expr
  deriving Inhabited

/-- What one rule's walk knows: the family, the frame's own variables. -/
structure TargetFrame where
  recNames : List Name
  rlvls : List Level
  recTys : List Expr
  mIs : List Nat
  rPs : List Nat
  rP : Nat
  /-- the rule's prefix variables (fvars `0 … rP-1`) -/
  pref : List Expr
  /-- the constructor's fields at the major's instantiation (fvars
  `rP … rP+nF-1`) -/
  fields : List Expr
  /-- each field's telescope, read through whnf (`targetWhnfPis`) -/
  teles : List (List (Expr × BinderMeta))
  /-- the family's elimination datum: the `ih` types' `∀`-binders carry
  it (their codomain is the motive's sort, not the field's) -/
  pw : PropWhen

/-- **A recursive call, recognised** at a node under `d` local binders
of the fvar-world rule body: `rec_c x⃗ e⃗ (f_i a⃗)`, with the family's
levels, `x⃗` the rule's own prefix (so `rP_c = rP`), `f_i` a field,
`a⃗ = structTeleVars m` (the field's own telescope, `m ≤ d`), and `e⃗`
recursor-free with no local binder of the site but `a⃗`.  Returns the
field, the callee, the telescope width and the index arguments. -/
def targetCall? (fr : TargetFrame) (d : Nat) (e : Expr) :
    Option (Nat × Nat × Nat × List Expr) :=
  match e.getAppFn with
  | .const r us =>
    match nameIdxOf? fr.recNames r with
    | none => none
    | some c =>
      if us != fr.rlvls then none else
      if fr.rPs.getD c 0 != fr.rP then none else
      let args := e.getAppArgs
      let mI := fr.mIs.getD c 0
      if args.length != mI + 1 then none else
      if args.take fr.rP != fr.pref then none else
      match args[mI]? with
      | none => none
      | some maj =>
        match fr.fields.findIdx? (· == maj.getAppFn) with
        | none => none
        | some i =>
          let m := (fr.teles.getD i []).length
          if !(decide (m ≤ d)) then none else
          if maj.getAppArgs != structTeleVars m then none else
          let idx := (args.drop fr.rP).take (mI - fr.rP)
          if idx.any (fun x => !x.looseBVarsBounded m || x.mentionsAnyConst fr.recNames) then none
          else some (i, c, m, idx)
  | _ => none

/-- The `ih` type of a recognised call: `∀ a⃗ : A⃗_i, recTy_c` at
`x⃗ ++ e⃗ ++ [f_i a⃗]`, its binders at the family's elimination datum —
the codomain is the motive's sort, so the field's own binder data (its
codomain's) would claim the wrong zeroness; these are the
binders of the call's λ `targetCallOk` infers. -/
def targetIhTy (fr : TargetFrame) (i c m : Nat) (idx : List Expr) : Option Expr :=
  let f := fr.fields.getD i default
  let tele := (fr.teles.getD i []).map fun b => (b.1, (⟨fr.pw⟩ : BinderMeta))
  (Expr.instPisAtLift (fr.pref ++ idx ++ [Expr.mkAppN f (structTeleVars m)])
    (fr.recTys.getD c (.sort .zero))).map (Expr.mkPisOf tele)

/-- **The classification-free abstraction**: every recognised call
replaced by `ih_r a⃗`, the `ih` variables allocated in order of first
occurrence (`base` is `rP + nF`); `none` when a family recursor occurs
anywhere else. -/
def targetAbstract (fr : TargetFrame) (base : Nat) :
    Nat → Expr → Array TargetIh → Option (Expr × Array TargetIh)
  | _, .bvar j, acc => some (.bvar j, acc)
  | _, .sort u, acc => some (.sort u, acc)
  | _, .lit l, acc => some (.lit l, acc)
  | _, .fvar i ty, acc => some (.fvar i ty, acc)
  | _, .const n us, acc => if fr.recNames.contains n then none else some (.const n us, acc)
  | d, .lam ty b bi, acc => do
    let (ty', acc) ← targetAbstract fr base d ty acc
    let (b', acc) ← targetAbstract fr base (d + 1) b acc
    pure (.lam ty' b' bi, acc)
  | d, .forallE ty b bi, acc => do
    let (ty', acc) ← targetAbstract fr base d ty acc
    let (b', acc) ← targetAbstract fr base (d + 1) b acc
    pure (.forallE ty' b' bi, acc)
  | d, .letE ty v b, acc => do
    let (ty', acc) ← targetAbstract fr base d ty acc
    let (v', acc) ← targetAbstract fr base d v acc
    let (b', acc) ← targetAbstract fr base (d + 1) b acc
    pure (.letE ty' v' b', acc)
  | d, .proj s i e, acc =>
    if fr.recNames.contains s then none else do
    let (e', acc) ← targetAbstract fr base d e acc
    pure (.proj s i e', acc)
  | d, .app f a, acc =>
    match targetCall? fr d (.app f a) with
    | some (i, c, m, idx) => do
      let ty ← targetIhTy fr i c m idx
      -- identical CALLS share one variable (the same field, callee and
      -- index arguments — hence the same target at every reading);
      -- two different calls never do, even at one type: the model reads
      -- each variable as ONE call target's value
      match acc.findIdx? (fun x => x.field == i && x.callee == c && x.idx == idx) with
      | some r =>
        let fv := (acc.getD r default).fv
        pure (Expr.mkAppN fv (structTeleVars m), acc)
      | none =>
        let fv : Expr := .fvar (base + acc.size) ty
        pure (Expr.mkAppN fv (structTeleVars m),
          acc.push ⟨i, c, idx, ty, fv⟩)
    | none => do
      let (f', acc) ← targetAbstract fr base d f acc
      let (a', acc) ← targetAbstract fr base d a acc
      pure (.app f' a', acc)

/-- A constructor's type at the major's LEVELS: a member's is stored at
the block's own level parameters, which the recursor shares; an outside
inductive's is instantiated at the major's. -/
def targetCtorAt (M : TargetMajor) (c : ConstantVal) : Expr :=
  match M.member with
  | some _ => c.type
  | none => c.type.instantiateLevelParams c.levelParams M.lvls

/-- The data every rule of the family shares. -/
structure TargetFamily where
  recNames : List Name
  rlvls : List Level
  recTys : List Expr
  mIs : List Nat
  rPs : List Nat
  /-- PRIMREC: the call graph's rank (`graphRank`) where the family is
  checked OFF the walk (`targetFlatRoute`) — the intra-SCC calls then get
  their own check (`targetIntraCallOk`); `none` against the walk -/
  ranks : Option (List Nat) := none
  /-- every recursor's major, in the family's order (stage (b)'s) -/
  majors : List TargetMajor := []

/-- Every field's type, member-abstracted (`absM`), its telescope
read through whnf at `depth` (`targetWhnfPis`), in field order. -/
def targetFieldNorms (ops : CheckerOps m) (env : Env) (depth : Nat) (absM : Expr → Expr) :
    List Expr → m (List Expr)
  | [] => pure []
  | f :: fs => do
    let t ← targetWhnfPis ops env depth (whnfWalkFuel (absM f.fvarTypeD)) (absM f.fvarTypeD)
    let ts ← targetFieldNorms ops env depth absM fs
    pure (t :: ts)

/-- **One call's typing**, on the member-abstracted terms: the field
is a value of the callee's major type at the call's arguments, under
the field's own telescope, which is hole-free.  Both abstract sides
are INFERRED first — the model's defeq reading needs them well-denoted
at every value of the holes, which only an inference run at the
abstract context supplies (the concrete terms' checks say nothing
about the holes).  Then the call itself, `λ a⃗, c x⃗ e⃗ (f a⃗)` with the
callee a variable of its stored type, is inferred at the frame: its
index arguments fit the callee's binders at every value of the
telescope. -/
def targetCallOk (opsT : CheckerOps m) (env : Env) (cn : Name) (fam : TargetFamily)
    (fvsPref fvsF fnorm : List Expr) (teles : List (List (Expr × BinderMeta)))
    (absM : Expr → Expr) (base k : Nat) (pw : PropWhen) (fwss : Option (List (List Expr)))
    (ih : TargetIh) : m Unit := do
  let fty := fnorm.getD ih.field default
  let tele := teles.getD ih.field []
  unless tele.all (fun b => targetHoleFree base k b.1) do
    throw (.invalid s!"target rec: the rule of {cn} calls a recursor on a field whose \
      telescope mentions the block")
  -- (K5) the call's index arguments name no block member at the block's
  -- levels: the model reads the call's TARGET at the CONCRETE index
  -- arguments (the graph recursor's call data), while the check below types
  -- the call on the member-ABSTRACTED ones; the two readings agree at every
  -- value of the holes only when the abstraction leaves them alone.
  -- Official forbids block occurrences in the indices of a
  -- recursive occurrence as well (`is_valid_ind_app`).
  unless ih.idx.all (fun x => absM x == x) do
    throw (.invalid s!"target rec (K5): the rule of {cn} calls a recursor at index \
      arguments that mention the block")
  let some calleeAt := Expr.instPisAtLift (fvsPref ++ ih.idx)
      (fam.recTys.getD ih.callee (.sort .zero))
    | throw (.invalid s!"target rec: the rule of {cn} recurses into a recursor whose \
        type does not bind the call's arguments")
  let .forallE majDom _ _ := calleeAt
    | throw (.invalid s!"target rec: the rule of {cn} recurses into a recursor whose \
        type does not bind the call's major")
  let fld := absM ((fvsF.getD ih.field default).fvarTypeD)
  let want := Expr.mkPisOf tele (absM majDom)
  let _ ← opsT.inferType env (base + k) fld
  let _ ← opsT.inferType env (base + k) want
  unless ← opsT.isDefEq env (base + k) fty want do
    throw (.invalid s!"target rec: the rule of {cn} calls a recursor on a field that \
      is not a value of its major type")
  -- the call is WELL-TYPED at the frame and the field's telescope
  -- alone: `λ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)` with the callee a variable of its
  -- stored type (after the frame), its λ-binders at the family's
  -- elimination datum `pw` (the rule's own).  The concrete rule body types the
  -- call only under the local binders the body happens to open, which
  -- may be uninhabited; the model reads the `ih` term — this λ — at
  -- EVERY value of the telescope, so the index arguments must fit the
  -- callee's binders there
  let callee : Expr := .fvar base (fam.recTys.getD ih.callee (.sort .zero))
  let fap := Expr.mkAppN (fvsF.getD ih.field default) (structTeleVars tele.length)
  let callTy ← opsT.inferType env (base + 1)
    (Expr.mkLamsOf (tele.map fun b => (b.1, ⟨pw⟩)) (Expr.mkAppN callee (fvsPref ++ ih.idx ++ [fap])))
  -- the `ih` variable's TYPE is well-formed at the frame, and it IS the
  -- call's type: the model grades the `ih` slot of the residue's context
  -- by the first and places the call's value in it by the second
  -- (`InferClaim` at the `ih` type, `DefEqClaim` at the pair)
  let _ ← opsT.inferType env base ih.ty
  unless ← opsT.isDefEq env (base + 1) callTy ih.ty do
    throw (.invalid s!"target rec: the rule of {cn} makes a recursive call whose type is \
      not its ih variable's")
  -- (K.53/K.53′) the callee's major at the
  -- call's arguments, under the field's telescope, IS the called field's
  -- type as the POSITIVITY WALK normalised it (`fwss`: the walk's recorded
  -- normal forms of this constructor at this class, `NestCtorNf`, read back
  -- and opened at the rule's fields) — syntactically, up to the free
  -- variables' annotations, and at EVERY node the walk derived for the
  -- class (at least one).  Official imposes it: its recursors are
  -- generated, and the callee of a recursive field is the member heading
  -- `whnf(infer_type(u_i))` with the Πs opened, at exactly that type's
  -- indices (`mk_rec_rules`, `inductive.cpp` v4.34.0 :763–775); for a
  -- nested block that member is the auxiliary type replacing the very
  -- occurrence (`replace_all_nested` :1134, no β-step), restored to it
  -- (`restore_nested` :927, :1270).  The walk's whnf runs on the holes
  -- where official's runs on the auxiliary constants — both stuck heads, and
  -- reduction never inspects a type former — so the read-back is official's
  -- restored type.  A supplied recursor calling a class only DEFEQ to the
  -- field's is not official's (`List ((fun _ => WR WT) Nat)` against
  -- `List (WR WT)`); the model's call landing reads the class and the
  -- indices off the field's node (by construction, no whnf commutation
  -- lemma).  Only where the family is checked against the walk
  -- (`fwss = some _`, `targetLegacyAux`: a cycle off the flat route; on
  -- it, `targetIntraCallOk` checks K.53 at an intra-SCC call itself).
  let wantE := (Expr.mkPisOf tele majDom).eraseFVarTys
  unless fwss.all fun fwss => !fwss.isEmpty &&
      fwss.all (fun fws => fws[ih.field]?.map Expr.eraseFVarTys == some wantE) do
    throw (.invalid s!"target rec (K.53): the rule of {cn} calls a recursor whose major is \
      not the called field's type as the positivity walk normalised it")

/-- Every call's typing (`targetCallOk`), in order of first occurrence. -/
def targetCallsOk (opsT : CheckerOps m) (env : Env) (cn : Name) (fam : TargetFamily)
    (fvsPref fvsF fnorm : List Expr) (teles : List (List (Expr × BinderMeta)))
    (absM : Expr → Expr) (base k : Nat) (pw : PropWhen) (fwss : Option (List (List Expr))) :
    List TargetIh → m Unit
  | [] => pure ()
  | ih :: ihs => do
    targetCallOk opsT env cn fam fvsPref fvsF fnorm teles absM base k pw fwss ih
    targetCallsOk opsT env cn fam fvsPref fvsF fnorm teles absM base k pw fwss ihs
/-- The domains of the first `|xs|` `∀` binders, each instantiated at the
earlier `xs` (a telescope's field types at given field variables). -/
def targetPiDomsWith : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE d b _ => (d :: ·) <$> targetPiDomsWith xs (b.instantiate1 x)
  | _ :: _, _ => none

/-- **The K.53 source of a recursor's calls**: the home table's normal
forms of its class where its layer is checked against the table
(`TargetMajor.homeNfs`), else the walk's (`TargetMajor.nfs`, or none). -/
def targetClassNfs (M : TargetMajor) : Option (List NestCtorNf) :=
  match M.homeNfs with
  | some L => some L
  | none => M.nfs

/-- **K.53′: the recorded normal forms `nfs?` of the constructor `cn` at a
class** (the walk's, `TargetMajor.nfs`, or the home table's,
`TargetMajor.homeNfs`), each opened at the rule's field variables
`fvsF` — one list of field types per recorded node (`[]` where the
recorded telescope is too short); `none` without either. -/
def targetFieldNfs (nfs? : Option (List NestCtorNf)) (cn : Name) (fvsF : List Expr) :
    Option (List (List Expr)) :=
  nfs?.map fun nfs =>
    (nfs.filter (·.ctor == cn)).map fun e => (targetPiDomsWith fvsF e.ty).getD []

/-! ### An intra-SCC call off the walk (PRIMREC, lanes FLATHOME, MEMBER)

A family checked without the positivity walk (`targetFlatRoute`) may
call around a cycle only inside ONE flat home: a class's rule calling a
class of the same block, at the same levels and parameters — an older
block's (lane FLATHOME), or the installing block's own members (lane
MEMBER: the block is its own home, `TargetMajor.home`).
The completeness of such a cycle is the home's own lfp induction
(`Model/Inductives/TargetFlat.lean`), which reads each call at the
STAGE — the home's members as holes valued by a sub-tuple of the
carrier.  So the call is typed there: the constructor's type with the
home's group abstracted to holes BEFORE it is instantiated at the
class's parameters (`grpSub`, the container substitution the walk's
frames use), its field domains at the rule's field variables, and the called field's
type defeq to the callee's hole applied to the class's parameters and
the call's indices, under the call's telescope — at every value of the
holes, so at the stage.  K.53 (official-imposed) compares the callee's
major with the field's normal form (`targetK53Conform`,
`ConLeche/Conformance/K53.lean`). -/

/-- A home's group: each member of the class's home with its former's
type at the class's levels (the holes' types, `grpSub`). -/
def targetHomeGrp (fe : FEnv) (M : TargetMajor) : List (Name × Expr) :=
  M.home.map fun n => (n, match fe.find? n with
    | some (.indInfo cv _) => cv.type.instantiateLevelParams cv.levelParams M.lvls
    | _ => default)

/-- **One call inside a cycle of a family checked off the walk** (see
above): nothing where the family is checked against the walk
(`fam.ranks = none`) or the callee lies below the caller (`rk`); else —
both classes are of ONE home at one instantiation (both the block's own
members, or both outside ones), which the route guarantees
(`targetFlatRouteOf`) — the called field's home-abstracted type is the
callee's hole at the call's arguments. -/
def targetIntraCallOk (ops : CheckerOps m) (fe : FEnv) (cn rn : Name) (fam : TargetFamily)
    (M : TargetMajor) (cA : ConstantVal) (fvsPref fvsF : List Expr)
    (teles : List (List (Expr × BinderMeta))) (base : Nat) (ih : TargetIh) : m Unit :=
  match fam.ranks with
  | none => pure ()
  | some rk =>
    if rk.getD ih.callee 0 != rk.getD ((nameIdxOf? fam.recNames rn).getD 0) 0 ||
        M.homeNfs.isSome then pure ()
    else do
    let M' := fam.majors.getD ih.callee default
    unless M.home.contains M'.ind do
      throw (.internal "target rec: a call around a cycle leaves its home (off the route)")
    let grp := targetHomeGrp fe M
    let some crestH := instPisWith M.ds
        ((cA.type.instantiateLevelParams cA.levelParams M.lvls).replaceConsts
          (grpSub M.lvls base grp))
      | throw (.internal "target rec: constructor parameter telescope (holes)")
    let some calleeAt := Expr.instPisAtLift (fvsPref ++ ih.idx)
        (fam.recTys.getD ih.callee (.sort .zero))
      | throw (.invalid s!"target rec: the rule of {cn} recurses into a recursor whose \
          type does not bind the call's arguments")
    let .forallE majDom _ _ := calleeAt
      | throw (.invalid s!"target rec: the rule of {cn} recurses into a recursor whose \
          type does not bind the call's major")
    let t := M.home.idxOf M'.ind
    let tele := teles.getD ih.field []
    let fldH := ((targetPiDomsWith fvsF crestH).getD []).getD ih.field default
    let wantH := Expr.mkPisOf tele
      (Expr.mkAppN (.fvar (base + t) (grp.getD t default).2) (M.ds ++ ih.idx))
    let d := base + grp.length
    let _ ← ops.inferType fe.env d fldH
    let _ ← ops.inferType fe.env d wantH
    unless ← ops.isDefEq fe.env d fldH wantH do
      throw (.invalid s!"target rec: the rule of {cn} calls around a cycle of its family on a \
        field that is not a value of the callee's major type at every value of its home's \
        members")
    targetK53Conform ops fe.env cn M.home M.lvls base d fldH (Expr.mkPisOf tele majDom)

/-- Every call's intra-SCC check (`targetIntraCallOk`), in order. -/
def targetIntraCallsOk (ops : CheckerOps m) (fe : FEnv) (cn rn : Name) (fam : TargetFamily)
    (M : TargetMajor) (cA : ConstantVal) (fvsPref fvsF : List Expr)
    (teles : List (List (Expr × BinderMeta))) (base : Nat) : List TargetIh → m Unit
  | [] => pure ()
  | ih :: ihs => do
    targetIntraCallOk ops fe cn rn fam M cA fvsPref fvsF teles base ih
    targetIntraCallsOk ops fe cn rn fam M cA fvsPref fvsF teles base ihs

/-- **Stage (c): ONE rule, at any major**, reading no field kind.  The
right-hand side is annotated, resolved and typed at
the rule-less recursor environment `feR`; it binds the recursor's
prefix and the constructor's fields AT THE MAJOR's instantiation,
binder by binder (G2, at `feT`); every recursive call is abstracted
(`targetAbstract`), each call's field checked to be a value of the
callee's major type at the call's arguments, and the residue typed
against the recursor's conclusion at the constructor. -/
def targetRule (opsR : CheckerOps m) (w : StructWalkers) (feR : FEnv)
    (opsT : CheckerOps m) (feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily)
    (cvR : ConstantVal) (rP : Nat) (recTy : Expr) (M : TargetMajor)
    (c : ConstantVal × Nat) (rhs : Expr) : m Expr := do
  let nF := c.2
  unless rhs.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in rule of {cvR.name}")
  if rhs.hasFvar then
    throw (.invalid s!"free variable in rule of {cvR.name}")
  let rhsA ← opsR.annotate feR.env 0 rhs
  unless rhsA.allLevelParamsDefined cvR.levelParams do
    throw (.invalid s!"undeclared universe parameter in rule of {cvR.name}")
  unless w.resolve feR rhsA do
    throw (unresolvedConstsError s!"rule of {cvR.name}" rhsA)
  let _tyR ← opsR.inferType feR.env 0 rhsA
  let (rbs, body) ← unwrapOr (rhsA.stripLams (rP + nF))
    (.invalid s!"target rec: the rule of {c.1.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  unless rbs.all (fun b => b.2.pw == Level.zeronessOf (structElimLevel p.elim p.large)) do
    throw (.invalid s!"target rec: the rule of {c.1.name} does not annotate its λ-binders \
      with the family's elimination datum")
  let (fvsPref, _) ← unwrapOr (openPisAtFvars rP recTy 0)
    (.internal "target rec: recursor prefix telescope")
  -- the constructor AT THE MAJOR's instantiation: its levels and its
  -- parameters `ds` (a member's: the block's levels and the prefix's
  -- first `nP` variables)
  let crest ← unwrapOr (instPisWith M.ds (targetCtorAt M c.1))
    (.internal "target rec: constructor parameter telescope")
  let (fvsF, cbody) ← unwrapOr (openPisAtFvars nF crest rP)
    (.internal "target rec: constructor field telescope")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsPref ++ fvsF) rhsA)
    (.invalid s!"target rec: the rule of {c.1.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  unless ldoms.all (fun t => w.resolve feT t) do
    throw (unresolvedConstsError s!"the domains of the rule of {c.1.name}" rhsA)
  checkBlockDefEqList opsT feT.env (rP + nF)
    s!"the rule of {c.1.name} does not bind the recursor's prefix and the constructor's \
      fields"
    ((fvsPref ++ fvsF).map Expr.fvarTypeD) ldoms
  -- each field's type with the block's members abstracted to the
  -- frame's HOLES (`targetHoles`, after the fields), its telescope read
  -- through whnf at the depth past the holes
  let base := rP + nF
  let k := formerTys.length
  let absM := targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys base)
  let fnorm ← targetFieldNorms opsT feT.env (base + k) absM fvsF
  -- K4: the fields' whnf-telescopes name only the
  -- recursor's universe parameters.  The call λs bind their domains, and
  -- the model's ι equations must read alike at two level valuations
  -- agreeing on those parameters (`heqP`).  Reduction never introduces a
  -- parameter (δ instantiates a stored value's own parameters away), so
  -- this rejects nothing the rule's own `allLevelParamsDefined` admits;
  -- it spares the model a level-footprint theorem for `whnf` (and, through
  -- the major's constructor expansion, for inference).
  unless fnorm.all (fun t => t.allLevelParamsDefined cvR.levelParams) do
    throw (.invalid s!"target rec: a field of {c.1.name} normalises to a type naming a \
      universe parameter the recursor does not declare")
  let fr : TargetFrame :=
    { recNames := fam.recNames, rlvls := fam.rlvls, recTys := fam.recTys, mIs := fam.mIs,
      rPs := fam.rPs, rP := rP, pref := fvsPref, fields := fvsF,
      teles := fnorm.map fun t => t.piBinders.1,
      pw := Level.zeronessOf (structElimLevel p.elim p.large) }
  let bodyF := body.instantiateList (fvsPref ++ fvsF).reverse
  let (bodyO, ihs) ← unwrapOr (targetAbstract fr (rP + nF) 0 bodyF #[])
    (.invalid s!"target rec: the rule of {c.1.name} is not a primitive recursion — a family \
      recursor occurs outside a call on a field of this constructor at the rule's own \
      prefix")
  -- every call's field is a value of the callee's major type at the
  -- call's arguments, under the field's own telescope — both sides
  -- member-ABSTRACTED, so the defeq holds at every value of the holes;
  -- the telescope the call applies the field along is hole-free (it is
  -- then a concrete telescope, the one the `ih` variable's type binds)
  targetCallsOk opsT feT.env c.1.name fam fvsPref fvsF fnorm fr.teles absM base k
    (Level.zeronessOf (structElimLevel p.elim p.large))
    (targetFieldNfs (targetClassNfs M) c.1.name fvsF)
    ihs.toList
  -- a call around a cycle of a family checked off the walk: typed at
  -- its home's holes (`targetIntraCallOk`)
  targetIntraCallsOk opsT feT c.1.name cvR.name fam M c.1 fvsPref fvsF fr.teles base ihs.toList
  let depth := rP + nF + ihs.size
  let tyB ← opsT.inferType feT.env depth bodyO
  let concl ← unwrapOr
    (Expr.instPisAtLift
      (fvsPref ++ (cbody.getAppArgs.drop M.nPc) ++
        [Expr.mkAppN (.const c.1.name M.lvls) (M.ds ++ fvsF)])
      recTy)
    (.internal "target rec: recursor conclusion")
  unless ← opsT.isDefEq feT.env depth tyB concl do
    throw (.invalid s!"target rec: the rule of {c.1.name} does not produce the recursor's \
      conclusion at that constructor")
  pure rhsA

/-! ## The family -/

/-- The recursor rules of a block, as the stream exports them, in the
block's recursor order. -/
def targetRecRules (block : List ConstantInfo) : List (List RecRule) :=
  match blockSplit block with
  | some (_, _, rs) => rs.map (·.2.2.2)
  | none => []

/-- A checked recursor's major, carrying home normal forms `x`
(`TargetMajor.homeNfs`). -/
def targetMarkTy (t : ConstantVal × TargetMajor × Level) (x : Option (List NestCtorNf)) :
    ConstantVal × TargetMajor × Level :=
  (t.1, { t.2.1 with homeNfs := x }, t.2.2)

/-- Every checked recursor's major carrying its home normal forms, by
position. -/
def targetMarkTys : List (ConstantVal × TargetMajor × Level) → List (Option (List NestCtorNf)) →
    List (ConstantVal × TargetMajor × Level)
  | [], _ => []
  | t :: ts, hn => targetMarkTy t (hn.headD none) :: targetMarkTys ts hn.tail

/-- Stage (b) at every recursor, in the record's order, the majors
carrying the home table's normal forms `hn` (`targetHomeOf`) by
position. -/
def targetRecTys (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : Option NestNodes)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) (recs : List RecShape)
    (hn : List (Option (List NestCtorNf)) := []) :
    m (List (ConstantVal × TargetMajor × Level)) :=
  match recs with
  | [] => pure []
  | rc :: rcs => do
    let t ← targetRecTy ops fe p nested aux cvTas ctorsAs rc
    let ts ← targetRecTys ops fe p nested aux cvTas ctorsAs rcs hn.tail
    pure (targetMarkTy t (hn.headD none) :: ts)

/-- The rule pins at every recursor's major (`targetRulePins`), against
the stream's rule records, pairwise. -/
def targetRulePinsAll : List (ConstantVal × TargetMajor × Level) → List (List RecRule) → m Unit
  | t :: ts, rs :: rss => do
    targetRulePins t.1 t.2.1 rs
    targetRulePinsAll ts rss
  | _, _ => pure ()

/-- **One recursor's rules** (stage (c)), one per constructor of its
major, in order. -/
def targetRules (opsR : CheckerOps m) (w : StructWalkers) (feR : FEnv) (opsT : CheckerOps m)
    (feT : FEnv) (p : BlockShape) (formerTys : List Expr) (fam : TargetFamily)
    (cvRi : ConstantVal) (rP : Nat) (M : TargetMajor) :
    List (ConstantVal × Nat) → List Expr → m (List Expr)
  | [], [] => pure []
  | cA :: cs, rhs :: rhss => do
    let r ← targetRule opsR w feR opsT feT p formerTys fam cvRi rP cvRi.type M cA rhs
    let rs ← targetRules opsR w feR opsT feT p formerTys fam cvRi rP M cs rhss
    pure (r :: rs)
  | _, _ => throw (.invalid "target rec: the recursor's rules do not cover its major's constructors")

/-- **Every recursor's rules**, in the record's order, each against its
major's constructors. -/
def targetRecsRules (opsR : CheckerOps m) (w : StructWalkers) (feR : FEnv) (opsT : CheckerOps m)
    (feT : FEnv) (p : BlockShape) (formerTys : List Expr) (fam : TargetFamily) :
    List RecShape → List (ConstantVal × TargetMajor × Level) →
      m (List (ConstantVal × TargetMajor × List Expr))
  | rc :: rcs, (cvRi, M, _) :: ts => do
    unless rc.rhss.length == M.ctors.length do
      throw (.invalid "target rec: the recursor's rules do not cover its major's constructors")
    let rhssA ← targetRules opsR w feR opsT feT p formerTys fam cvRi rc.rP M M.ctors rc.rhss
    let rest ← targetRecsRules opsR w feR opsT feT p formerTys fam rcs ts
    pure ((cvRi, M, rhssA) :: rest)
  | _, _ => pure []

/-- **The stored family, in the install's recursor-list format**: each
checked recursor, its annotated rules, its major's index count and its
major's constructors (`consBlockRecs` conses them). -/
def tgtRs (out : List (ConstantVal × TargetMajor × List Expr)) :
    List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) :=
  out.map fun t => (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors)

/-- **The firing mode of a rule at an OUTSIDE major**: the
syntactic reading of the recursor type's major domain
(`Expr.nestedRuleSyn`, the major's parameter count `nPc`, constants
resolving by `resolves`) — `.nested lvls pins`, with `pins` the major's
parameters lowered into the rule-prefix context, whose guards are
`EnvWF`'s `.nested` clause (`nestedRuleSyn_inv`); `.inert` when the
reading fails (a matched major then declines at fire time; measured
never to happen at a checked outside major). -/
def auxRuleFireR (resolves : Expr → Bool) (cv : ConstantVal) (mI rP nPc : Nat) : RecRuleFire :=
  match Expr.nestedRuleSyn resolves cv.levelParams cv.type mI rP nPc with
  | some (lvls, pins) => .nested lvls pins
  | none => .inert

/-- **One checked recursor's stored rules, at its major**: `sumRules` at the
MAJOR's parameter count and constructors;
at an OUTSIDE major (a nested block's auxiliary recursor) every rule
fires as `auxRuleFireR` reads it (`.nested` at the major's
instantiation), at a member major as `sumRules` builds it. -/
def tgtStoredRules (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (cv : ConstantVal) (mI rP : Nat) (M : TargetMajor) (rhss : List Expr) : List RecRule :=
  let rules := sumRules find? cv.name M.nPc mI rP cv.type M.ctors rhss
  match M.member with
  | none => rules.map fun rl => { rl with fire := auxRuleFireR resolves cv mI rP M.nPc }
  | some _ => rules

/-- **The block's container bit** (official's `m_nested`): some field
kind is not flat (the positivity function reached a container
instantiation).  It feeds the block's OWN large-elimination licence
(`blockLargeElimAllowed`, at its member classes); what other classes the
family eliminates is each class's own licence (`targetMajorLicensed`). -/
def blockNestedBit (kinds : List (List (List NestFieldKind))) : Bool :=
  !nestKindsFlat kinds

/-- **The checked family consed through the index, at its majors**:
`consBlockRecsF` with each recursor's rules at ITS major
(`tgtStoredRules`) — the uniform route's recursor cons, which at member
majors is `consBlockRecsF` itself. -/
def consBlockRecsTF (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cv, M, rhss) :: rest, fe =>
    consBlockRecsTF find? resolves p (m + 1) rest
      (fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (tgtStoredRules find? resolves cv (p.majorIdxAt m) (p.rulePrefixAt m) M rhss)))

/-! ## The family's call graph (PRIMREC)

The recursor check reads nothing from the positivity walk wherever the
proof needs nothing from it (`_tmp/primrec/PLAN.md`).  The proof orders
the family's classes along its CALLS (`Model/Inductives/TargetRank.lean`):
where the calls never return to a class (an acyclic call graph) the
classes' own case analysis is the whole induction; where a cycle runs
inside one FLAT home — one older block's members at one instance (lane
FLATHOME), or the installing block's own members (lane MEMBER) — the
home's own lfp induction orders it, its calls typed at the home's holes
(`targetIntraCallOk`).  Any other cycle (across homes: a nested block's
containers) is, for now,
still checked against the walk's auxiliary types and normal forms (the
node route's proof); that is the TRANSITIONAL switch `targetLegacyAux`,
which the completeness lanes narrow shape by shape. -/

/-- **The family's call graph**: recursor `c` has an edge to recursor
`c'` when some rule of `c` names `c'`.  Read off the rules as the stream
gives them, so it holds every call the check can recognise (a call names
its callee). -/
def targetCallGraph (recNames : List Name) (rhss : List (List Expr)) : List (List Nat) :=
  rhss.map fun rs => (List.range recNames.length).filter fun c' =>
    rs.any (·.mentionsConst (recNames.getD c' .anonymous))

/-- One round of reachability: every node's reach grows by its
successors' (reaches as rows of booleans over the nodes). -/
def reachStep (g : List (List Nat)) (R : List (List Bool)) : List (List Bool) :=
  (List.range g.length).map fun c => (List.range g.length).map fun x =>
    (R.getD c []).getD x false || (g.getD c []).any fun c' => (R.getD c' []).getD x false

/-- The reach relation, iterated to its fixed point (`none` if the fuel
runs out, which `g.length ^ 2 + 1` rounds never do). -/
def reachFix (g : List (List Nat)) : Nat → List (List Bool) → Option (List (List Bool))
  | 0, _ => none
  | fuel + 1, R => if reachStep g R == R then some R else reachFix g fuel (reachStep g R)

/-- **A graph's rank**: the size of every node's reach (itself
included).  An edge never climbs it; it stays level exactly inside a
strongly connected component — so the equal-rank edges are the SCCs'
own, and an acyclic graph's edges all descend. -/
def graphRank (g : List (List Nat)) : List Nat :=
  match reachFix g (g.length * g.length + 1)
      ((List.range g.length).map fun c => (List.range g.length).map (· == c)) with
  | some R => R.map (·.count true)
  | none => g.map fun _ => 0

/-- The family's call graph (`targetCallGraph` of its records). -/
def targetGraphOf (p : BlockShape) : List (List Nat) :=
  targetCallGraph (p.recs.map (·.cvR.name)) (p.recs.map (·.rhss))

/-- **The route off the walk, before the majors (PRIMREC)**: every edge of
the family's call graph that does not descend in its rank — an edge
inside a cycle — joins two recursors whose records both name a member
or both name none (`RecShape.tgt`).  A family failing it is checked against the walk
without resolving its majors twice. -/
def targetFlatRoute0 (p : BlockShape) : Bool :=
  let g := targetGraphOf p
  let r := graphRank g
  (List.range g.length).all fun c => (g.getD c []).all fun c' =>
    decide (r.getD c' 0 < r.getD c 0) ||
      (decide (p.k ≤ (p.recs.getD c default).tgt) == decide (p.k ≤ (p.recs.getD c' default).tgt))

/-- A major as the home table is matched against it (`homeMatch`). -/
def TargetMajor.homeClass (M : TargetMajor) : HomeClass :=
  ⟨M.ind, M.lvls, M.ds, M.nPc, M.ctors, M.member⟩

/-- **A flat edge**: two classes of one home — both members of the block
or both outside classes — at the same levels and parameters (lanes
FLATHOME, MEMBER: a flat home's own recursion). -/
def targetFlatEdge (M M' : TargetMajor) : Bool :=
  M.member.isNone == M'.member.isNone && M.home.contains M'.ind && M'.lvls == M.lvls &&
    M'.ds == M.ds

/-- **A HOT layer** of the call graph: rank `n` has an edge inside it
that is not flat — a cycle the flat route does not order. -/
def targetHot (p : BlockShape) (Ms : List TargetMajor) (n : Nat) : Bool :=
  let g := targetGraphOf p
  let r := graphRank g
  (List.range g.length).any fun c => r.getD c 0 == n &&
    (g.getD c []).any fun c' => r.getD c' 0 == n &&
      !targetFlatEdge (Ms.getD c default) (Ms.getD c' default)

/-- **The home layers (PRIMREC / NESTHOME)**: at the majors resolved
without the walk, every class of a hot layer matched in the home table
(`RecHome.lean`), expanded and naming a member, and the matching
consistent at those classes — then, per recursor, its class's table
normal forms where its layer is hot (the K.53 source of its calls);
`none` when some hot class is not covered.  The table's read-back runs
at the block's own names (`BlockShape.nestCtx`, no lookup). -/
def targetHomeOf (p : BlockShape) (aux : NestNodes) (Ms : List TargetMajor) :
    Option (List (Option (List NestCtorNf))) :=
  let r := graphRank (targetGraphOf p)
  let ctx := p.nestCtx [] (fun _ => none) []
  let Cs := Ms.map (·.homeClass)
  let R := Cs.map (homeMatch ctx aux.homes)
  let inS : Nat → Bool := fun c => targetHot p Ms (r.getD c 0)
  if (List.range Cs.length).all (fun c => !inS c || homeCovered ctx Cs R c) &&
      homeConsistent ctx Cs R inS && homePairConsistent Cs R inS then
    some ((List.range Cs.length).map fun c =>
      if inS c then (R.getD c none).map (·.nfs.map (·.entry)) else none)
  else none

/-- **The route off the walk (PRIMREC)**, at the resolved majors: the
majors were resolved without the walk (no recorded normal forms), and
exactly the classes of the hot layers carry the home table's normal
forms (`targetHomeOf`, lane NESTHOME) — every other layer's cycles are flat
(`targetFlatEdge`), ordered by their home's lfp induction (lane
FLATHOME).  An acyclic family is on it. -/
def targetRouteOf (p : BlockShape) (Ms : List TargetMajor) : Bool :=
  let r := graphRank (targetGraphOf p)
  Ms.all (·.nfs.isNone) &&
    (List.range Ms.length).all fun c =>
      targetHot p Ms (r.getD c 0) == (Ms.getD c default).homeNfs.isSome

/-- **TRANSITIONAL (PRIMREC): the walk's auxiliary types, where the proof
still reads them** — at a family off the route (`targetRouteOf`: a hot
layer the home table does not cover); `none` (majors any stored
inductive, no K.53′ from the walk) on it. -/
def targetLegacyAux (p : BlockShape) (Ms : List TargetMajor) (aux : NestNodes) :
    Option NestNodes :=
  if targetRouteOf p Ms then none else some aux

/-- **Stage (b), routed**: where the route may apply (`targetFlatRoute0`,
or a home table exists) the majors are resolved without the walk and
kept if they are on the route (`targetRouteOf`: no hot layer); else, if
the home table covers their hot layers (`targetHomeOf`), they carry the
table's normal forms (`targetMarkTys`, kept when the table reads the
marked majors alike); otherwise they are
resolved against the walk's auxiliary types (whose normal forms then
carry K.53′). -/
def targetRecTysRouted (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : NestNodes) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × Level)) :=
  if targetFlatRoute0 p || !aux.homes.isEmpty then do
    let tys0 ← targetRecTys ops fe p nested none cvTas ctorsAs p.recs
    if targetRouteOf p (tys0.map (·.2.1)) then pure tys0 else
    match targetHomeOf p aux (tys0.map (·.2.1)) with
    | some hn => do
      let tys1 := targetMarkTys tys0 hn
      if targetRouteOf p (tys1.map (·.2.1)) && targetHomeOf p aux (tys1.map (·.2.1)) == some hn
      then pure tys1
      else targetRecTys ops fe p nested (some aux) cvTas ctorsAs p.recs
    | none => targetRecTys ops fe p nested (some aux) cvTas ctorsAs p.recs
  else targetRecTys ops fe p nested (some aux) cvTas ctorsAs p.recs

/-- The family's shared data, from the checked recursors: on the route off
the walk also the graph's rank and the majors (`targetIntraCallOk`). -/
def targetFamilyOf (p : BlockShape) (tys : List (ConstantVal × TargetMajor × Level)) :
    TargetFamily :=
  { recNames := p.recs.map (·.cvR.name),
    rlvls := (p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [],
    recTys := tys.map (·.1.type),
    mIs := p.recs.map (·.mI),
    rPs := p.recs.map (·.rP),
    ranks := if targetRouteOf p (tys.map (·.2.1)) then some (graphRank (targetGraphOf p))
      else none,
    majors := tys.map (·.2.1) }

/-- **The target recursor check on a whole family** (charter item 5):
the pins (`targetRecPins`), every recursor's type at its major
(`targetRecTys`), the family's agreements (the counting guard, the
elimination-level pin, the shared prefix), the
rule pins at the majors, then — at the environment holding every
rule-less recursor — every rule.  `fe` holds the block's formers and
constructors; a major may be an inductive outside the block (a nested
block's containers, at its auxiliary types); `nested` is the elimination
guard's container bit as the caller reads it (`blockNestedBit`: the
positivity walk's containers), which licenses the member classes; every
other major carries its own licence (`targetMajorLicensed`).  A family
on the route off the walk (`targetFlatRouteOf`: acyclic, or cycles only
inside one flat home each — the block itself or an older block) is
checked on raw fields alone; any other keeps the walk's constraints
(`targetLegacyAux`).
Returns every recursor with
its major and its annotated right-hand sides (what the install
stores). -/
def targetRecCheck (so : ShadowOps m) (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : NestNodes)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr)) := do
  targetRecPins p block
  let tys ← targetRecTysRouted (so.opsAt fe) fe p nested aux cvTas ctorsAs
  let us := tys.map (·.2.2)
  checkBlockRecSmallElim p nested (tys.all fun t => targetMajorLicensed fe p nested t.2.1) us
  checkBlockRecElimPin p us
  checkBlockRecPrefixAgree (so.opsAt fe) fe.env p (tys.map (·.1))
  targetRulePinsAll tys (targetRecRules block)
  let feR := consBlockRecsBareF p 0 (tys.map fun t => (t.1, t.2.1.nIdx)) fe
  let out ← targetRecsRules (so.opsRuleR feR) so.walkers feR (so.opsAt fe) fe p
    (cvTas.map (·.type)) (targetFamilyOf p tys) p.recs tys
  so.flush
  pure out

end ConLeche
