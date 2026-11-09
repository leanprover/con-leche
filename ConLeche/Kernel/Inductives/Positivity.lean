module

public import ConLeche.Kernel.CheckerBase
public import ConLeche.Kernel.Inductives.FieldTele

@[expose] public section

/-!
# Positivity: the one interface

Everything the installer decides about WHERE the block occurs in a
constructor field lives here, and nothing about it anywhere else:

* **the occurrence test** at the block's whole member list
  (`Expr.mentionsAnyConst`, `ConLeche/Kernel/Inductives/StructParts.lean`,
  memoized by `@[csimp]`);
* **the normalisation** official's `check_positivity` classifies on:
  the positivity function's own normal form (the root frame's output,
  `nestRoot`; OUTPUT only — the install stores every constructor as
  declared);
* **positivity through containers** (`nestPos`, the last section): ONE
  function, official's walk with a container case that recurses into the
  container's constructors at the CONCRETE instantiation (the charter,
  items 3–4), whose ROOT frame is the block itself (`nestRoot`): the
  install's walk, and the unit tests' entry `nestedBlockPositivity`.

**The walk's run is the proofs' interface.**  The install runs it on
the stored constructors (`checkBlockPositivity`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), and the model inverts
that run (`checkBlockPositivity_inv_gen`, `DeclaredFieldShapes`).  The
capability record's `is_rec` is NOT read off its kinds: official's is
syntactic (`blockIsRec`).  There is no second classifier.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-- Which member of the block a head expression names, at the block's
own level parameters (official's `m_ind_cnsts` lookup): `none` at any
other head, INCLUDING a member's constant at other levels.  The
recogniser's constructor grouping reads it (`ctorMember?`). -/
def memberIdxAt? (names : List Name) (lvls : List Level) : Expr → Option Nat
  | .const n us => if us == lvls then names.findIdx? (· == n) else none
  | _ => none

/-! ## Closing a telescope -/

/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List Expr → Nat → Expr → Expr
  | [], _, body => body
  | dom :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0)

section

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **Official's telescope loop** (`check_inductive_types`,
`inductive.cpp`; task #195): peel `n` Π binders off `e`, reducing the
residual to weak head normal form before each binder and at the end,
where it must be a sort.  Binder `i` is opened at the free variable
`i` (its domain instantiated at the earlier ones, as `openPisAtFvars`
does), so the returned binder domains and the sort are scoped at the
free variables `0 ..< n`.  A residual that does not reduce to a Π, or
finally to a sort, is INVALID input — official fails there too. -/
def whnfTelescope (ops : CheckerOps m) (env : Env) :
    Nat → Nat → Expr → m (List Expr × Level)
  | i, 0, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .forallE dom body =>
      let (bs, s) ← whnfTelescope ops env (i + 1) n (body.instantiate1 (.fvar i dom))
      pure (dom :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- A former at its reduced telescope (official's `whnf` loop), closed. -/
def reducedFormer (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (n : Nat) :
    m ConstantVal := do
  let (bs, s) ← whnfTelescope ops env 0 n cv.type
  pure { cv with type := closeTelescope bs 0 (.sort s) }

/-- **A stored family's type former, at its telescope**: its stored type where that shows one,
else its reduct (official reads the type through `whnf`).  Every reader of a family's telescope
goes through this: what is stored is what the stream declares. -/
def familyTelescope (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (caps : IndCaps) : m Expr :=
  if formerDefHeaded cv then do
    let cvR ← reducedFormer ops env cv (caps.nparams + caps.nIdx)
    pure cvR.type
  else pure cv.type

/-- **The arguments of an application against a telescope**: each argument's type definitionally
equal to its binder's domain, the domains instantiated along the spine. -/
def checkSpineAt (ops : CheckerOps m) (env : Env) (d : Nat) : Expr → List Expr → m Unit
  | _, [] => pure ()
  | t, a :: as =>
    match t with
    | .forallE ty body => do
      let ta ← ops.inferType env d a
      unless ← ops.isDefEq env d ta ty do
        throw (.invalid "application type mismatch at a family's parameters")
      checkSpineAt ops env d (body.instantiate1 a) as
    | _ => throw (.invalid "function expected at a family's parameters")

/-- **A family at a key, typed** (official checks every replaced nested application,
`tc.check(nested, …)`, `inductive.cpp` v4.34.0 :1320): the levels its own count, the arguments
against its telescope. -/
def familyKeyCheck (ops : CheckerOps m) (env : Env) (find? : Name → Option ConstantInfo) (d : Nat)
    (c : Name) (us : List Level) (ds : List Expr) : m Unit :=
  match find? c with
  | some (.indInfo cv caps) => do
    unless us.length = cv.levelParams.length do
      throw (.invalid "incorrect number of universe levels at a family's key")
    let ty ← familyTelescope ops env cv caps
    checkSpineAt ops env d (ty.instantiateLevelParams cv.levelParams us) ds
  | _ => throw (.invalid "a family's key is no stored family")

end

/-! ## Positivity through containers — ONE function, GATED

The charter (DESIGN.md, "THE CHARTER", items 3–4): there is ONE
positivity function in the kernel; it reduces with the kernel's own
verified whnf (`ops.whnf`, β, δ, ι, …); the theorem to come is
"returns ⇒ the operator is monotone", by inversion of its run.  It
looks through a container at the CONCRETE instantiation `C (t[X])`:
the arguments `t[X]` — λ or not — are substituted into `C`'s
constructors and positivity is checked there, jointly in the member
holes `X` and in the instantiation's own recursive occurrences `Y`.
Nothing is stated or cached about a container in the abstract: the
only cache is keyed by the instantiation.  Official's nested→mutual
encoding is never mirrored: no auxiliary type, constructor or name.

**The holes are variables** (charter item 2: "the holes
are ordinary open terms (members abstracted to fvars)").  Every WHOLE
application of a member to the parameters is abstracted to a free
variable BEFORE the walk (`nestCrest`: `T_m.{lps} p⃗ ↦ X_m`, at `nP + m`,
typed by the former's type at the parameters — a family over the
member's indices), and a container's own applications `C_j q⃗` are
abstracted to its FRAME's holes before its constructors are instantiated
(charter item 4's `Y` holes, keyed by the instantiation, typed by the
container's formers at the key: families over their indices).  So every hole the monotonicity
theorem varies is a variable of the term `ops.whnf` reduces: `whnf`'s
denotation lemma is stated at one environment model, where a constant
reads one fixed leaf, and says nothing about a constant's reading at
other values.  Verdict-neutral: a member is an inductive former with
no δ and, at positivity time, no ι, so a typed variable in its place
changes no reduction; an installed container's own occurrences are at
its canonical parameters, so its frame's hole is met at the frame's
own `Ds` (anything else declines).  A frame abstracts the container's
WHOLE recorded block (`IndCaps.all`) at the instantiation and walks all
their constructors in one pass (N2-eager), as official copies the whole
group; so an
accepted frame reads the joint operator of the container's block at the
instantiation, and an instantiation in progress is only ever met as its
hole — met as a constant (reduction only) it is official's "non valid
occurrence".

**`nestPos`, the function**, by structural recursion on its fuel; its
cases are the monotonicity induction's:

* the whnf of the domain mentions no member — hole-free (`const`);
* a `Π` whose domain mentions no member — recurse on the body (`pi`);
* a hole at its frame's own parameters with hole-free indices, at its
  full arity (`holeApp`, official's `is_valid_ind_app` :338): a member
  hole — the ROOT frame's, at the block's parameters — or a container
  frame's (its instantiation in progress);
* a stored inductive `C` (not a member) applied to parameters `Ds`
  (some mentioning a member, none a field or binder variable — official
  :962) and member-free indices (`contApp`): an instantiation IN
  PROGRESS is a `Y` hole; one already accepted is a cache hit; else its
  checks — (N2) the instantiated index telescope names no member
  (official checks the auxiliary type former before the block exists,
  :219), (N3) its sort `Level.isEquiv` the block's (:250) — and then
  `nestPos` on every field of every constructor of `C` AT the
  instantiation, the instantiation pushed onto the in-progress list,
  and the constructor's result indices member-free;
* anything else — official's "non valid occurrence".

**No basis special-casing** but one: `Quot`, stored as an `.indInfo`
yet no inductive for official, is a "non valid occurrence" as a
container head.  The pinned `Eq`/`Nat`/`Empty`/`False` (and the
stream's `And`) are read from the environment like any stored inductive
— their constructors are `.ctorInfo` records with parameter counts.
The parameter-free ones never reach the container case; `Eq` (two
parameters, `α` and `a`, as official) always ends in official's
verdicts: a field in `a` is a local variable, `@Eq Prop (T p) True`
fails the instantiated `refl`'s result index ("invalid return type"),
`@Eq Prop T T` has a member in an index.

**Fuel** (derived from the input, no fixed limit):
`nestPos` recurses on an explicit fuel, one unit per `Π` body and per
container field descent — per root constructor `whnfWalkFuel` of its
instantiated type (its depth plus a slack, see "The input-derived fuel"
below), so a
telescope or a nesting written out in the input never exhausts it.
Running out THROWS
`.notImplemented` — a decline (exit 2), never an accept.  The cache of
instantiations is unbounded: every entry is a frame the walk completed.

**The seeds**: the stream's recursor family names official's
auxiliary types as its outside majors (the recursor check's classes);
the recursor check walks every class it resolved at the root like a
container instance met there (`nestSeeds`, "The seeds" below), so every
class is a node BY CONSTRUCTION — an occurrence whnf erases among
them.

**Accepted superset of official** (the charter's item 8; with an e2e
fixture; a reject-only check would go into a separate unverified
stage, never into this function): official locates
nested instances SYNTACTICALLY, before any whnf (`replace_all_nested`
:1043), so a container reached only by reduction (`F T`,
`F α := List α`) is a "non valid occurrence" there; here the container
case reads the whnf, so it accepts (`corner_nestpos_redex_bad`, D1).
A container with NO constructor is read at its RECORDED parameter
count (`IndCaps.nparams`); its frame walks nothing.

**Who calls it.**  The check's positivity stage runs the walk
(`checkBlockPositivity`, `nestRoot`); `nestedBlockPositivity` is
the unit tests' entry, on a hand-built context.
-/

section Nested

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Does a MEMBER or a HOLE occur in `e`?  Official's `has_ind_occ`:
member constants, and here also the hole variables `lo ..< hi` — a free
variable's annotation is NOT looked into (a local's type lives in the
local context, not in the term) and a `.proj` node's structure name is
no occurrence.  The specification; the cached tier runs `nestOccC`. -/
def Expr.nestOcc (names : List Name) (lo hi : Nat) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .lit _ => false
  | .fvar i _ => decide (lo ≤ i ∧ i < hi)
  | .const n _ => names.contains n
  | .app f a => nestOcc names lo hi f || nestOcc names lo hi a
  | .lam ty body => nestOcc names lo hi ty || nestOcc names lo hi body
  | .forallE ty body => nestOcc names lo hi ty || nestOcc names lo hi body
  | .letE ty val body =>
    nestOcc names lo hi ty || nestOcc names lo hi val || nestOcc names lo hi body
  | .proj _ _ sub => nestOcc names lo hi sub

/-- Instantiate the leading `Π` binders of `e` at `args`, in order
(the parameters of a constructor or a type former). -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body => instPisWith as (body.instantiate1 a)
  | _ :: _, _ => none

/-- A container INSTANTIATION `C.{lvls} Ds`, its parameters scoped at the
block's canonical parameter variables `0 ..< nP` — the key of the only
cache there is. -/
structure NestKey where
  cname : Name
  lvls : List Level
  ds : List Expr
  deriving DecidableEq, Repr, Inhabited

/-- A HOLE of the walk: the instantiation it stands for, and the first
hole index of its frame (a frame has one hole per member of the
container's group it has reached). -/
structure NestHole where
  key : NestKey
  base : Nat
  /-- the instantiated former's index count: the arguments the hole takes -/
  nIdx : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ### The input-derived fuel

The walks that read a telescope THROUGH whnf (`nestPos`, and the
recursor stage's `targetWhnfPis`) recurse on an explicit fuel, one unit
per `Π` body and per container descent.  The fuel is derived from the
term the walk starts on: its DEPTH (the longest root-to-leaf path,
`fvar` annotations not descended) bounds every `Π` and every container
argument the term carries syntactically, so a telescope or a nesting
written out in the input never exhausts it; `fuelSlack` on top covers
what the syntax does not show — a container constructor's own fields
walked in a frame, a redex that reduces to a `Π` — and keeps the fuel
at or above 1024.  Running out DECLINES (it takes a
telescope that reduction manufactures beyond both).  No proof reads
the value: the functions' theorems hold at every fuel. -/

/-- The fuel's slack above the term's depth (see the section header). -/
def fuelSlack : Nat := 1024

/-- A term's depth: the longest root-to-leaf path (`fvar` annotations
not descended).  The executed form is the cached tier's memoised
`Expr.depthC` (`depthC_spec`). -/
def Expr.depth : Expr → Nat
  | .app f a => max f.depth a.depth + 1
  | .lam ty body => max ty.depth body.depth + 1
  | .forallE ty body => max ty.depth body.depth + 1
  | .letE ty v body => max (max ty.depth v.depth) body.depth + 1
  | .proj _ _ x => x.depth + 1
  | _ => 1

/-- **The fuel of a walk through whnf** starting at `e`: its depth plus
the slack (see the section header). -/
def whnfWalkFuel (e : Expr) : Nat := e.depth + fuelSlack

/-- The field's kind as the run found it: hole-free, a member hole
(finitary or under `Π` binders), an instantiation IN PROGRESS (a `Y`
hole — only inside a container's constructors), or an accepted
instantiation (under `Π` binders when `refl`). -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving DecidableEq, Inhabited

/-- A field kind with no container instantiation. -/
def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- **Every field of every constructor of every member is flat** (no
container instantiation): the reject-only conformance check's switch
(`checkBlockTail`: it has no container arm). -/
def nestKindsFlat (ks : List (List (List NestFieldKind))) : Bool :=
  ks.all (·.all (·.all NestFieldKind.flat))

/-- **A constructor's walked normal form, recorded** (K.53′): the
constructor `ctor` of the class it builds at the
levels `lvls` and the parameters `ds`, and its field telescope as the
walk normalised it (`nestFields`' normal forms, closed over the fields,
`closeTelescope`), both READ BACK — every hole replaced by the whole
application it stands for (`nestHoleImg`: a member hole by the member
applied to the block's parameters, a frame hole by its container applied
to the frame's parameters, read back), so only the block's parameter
variables stay free.  Recorded at every node the walk derives: the
members' constructors at the block's own levels and parameters, and every
frame's constructors at the frame's key.  The recursor stage reads a
recursive call's callee off it: the called field's normal form, at the
rule's field variables, IS the callee's major type (official: the
auxiliary type replacing that very occurrence, `replace_all_nested`;
`mk_rec_rules`' `whnf(infer_type(u_i))`). -/
structure NestCtorNf where
  ctor : Name
  lvls : List Level
  ds : List Expr
  ty : Expr
  deriving Inhabited

/-- The block, as the function needs it: the members, their level
parameters, the shared parameter count and the members' index counts,
the canonical parameter variables, the block's sort, and the
environment's lookup (the pure `Env`'s or the cached index's). -/
structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  find? : Name → Option ConstantInfo
  /-- the members' type formers at their telescopes -/
  formers : List ConstantVal

/-- The run's state: the accepted instantiations (the cache, keyed by the
instantiation). -/
structure NestState where
  keys : Array NestKey := #[]
  /-- the instantiations whose frames are being walked (every group
  member at the key), outermost last: an instantiation walked at the
  EMPTY stack (`nestWalkStack`) is still in progress for the cycle check
  (`nestContKey`) -/
  active : List NestKey := []
  /-- every derived node's constructors, normalised and read back
  (`NestCtorNf`, K.53′), in walk order -/
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-- What the run found: the accepted instantiations and every member
constructor's field kinds. -/
structure NestedPositivity where
  keys : Array NestKey
  kinds : List (List (List NestFieldKind))
  /-- every member constructor's normalised type, member-abstracted at the
  walk's context (the positivity function's output; the install stores
  the declared type) -/
  normals : List (List Expr) := []
  /-- every derived node's constructors, normalised and read back
  (`NestState.ctorNfs`, K.53′) -/
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-- A stored constant's entry as a constructor of `C`: a constructor
record whose result, past its parameters and fields, is headed by `C`
(its parameter and field counts); `none` for anything else. -/
def nestCtorEntry (C : Name) : ConstantInfo → Option (ConstantVal × Nat × Nat)
  | .ctorInfo cv nPc nF =>
    match cv.type.stripPis (nPc + nF) with
    | some (_, body) =>
      match body.getAppFn with
      | .const n _ => if n == C then some (cv, nPc, nF) else none
      | _ => none
    | none => none
  | _ => none

/-- The constructors of the inductive `C` and its parameter count: the
constructor names `C`'s stored record lists (`IndCaps.ctors`, official's
`inductive_val.cnstrs`), each looked up and kept when it is a stored
constructor whose result names `C` (`nestCtorEntry`) — no scan of the
environment.  `none` when `C` is no inductive; for an inductive without
constructors, its RECORDED parameter count (`IndCaps.nparams`,
official's `inductive_val.nparams`: official nests through such a
container, its auxiliary type simply has no constructor). -/
def nestContainer (ctx : NestCtx) (C : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  match ctx.find? C with
  | some (.indInfo _ caps) =>
    let cs := caps.ctors.filterMap fun n => (ctx.find? n).bind (nestCtorEntry C)
    match cs with
    | [] => some (caps.nparams, [])
    | (_, nPc, _) :: _ => some (nPc, cs.map fun c => (c.1, c.2.2))
  | _ => none

/-- Official's "non valid occurrence" (`check_positivity` :405). -/
def nestNonValid : CheckError :=
  .invalid "nested positivity: non valid occurrence of the datatypes being declared"

/-- The first hole-free variable index of a walk under `nf` frames:
the parameters are `0 ..< nP`, the member holes `nP ..< nP + k`, and
frame `i`'s hole `nP + k + i`. -/
def NestCtx.hiAt (ctx : NestCtx) (nf : Nat) : Nat := ctx.nP + ctx.names.length + nf

/-- **The ROOT frame's entries**: the block itself is the walk's root
frame — its key each member at the block's own levels and canonical
parameters, its holes the member holes `nP + t` (base `nP`). -/
def NestCtx.rootHoles (ctx : NestCtx) : List NestHole :=
  ctx.names.mapIdx fun t n => ⟨⟨n, ctx.lps.map .param, ctx.params⟩, ctx.nP, ctx.nIdxs.getD t 0⟩

/-- **The hole `i`'s entry** under the frames `prog`: the walk's stack
read root first — the root frame's entries (`NestCtx.rootHoles`), then
`prog` from the outside — hole `i` its entry `i - nP`; `none` off the
holes. -/
def nestHoleAt (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option NestHole :=
  if ctx.nP ≤ i then (ctx.rootHoles ++ prog.reverse)[i - ctx.nP]? else none

/-! ### Reading a walked term back

A walked constructor's normal form is recorded for the recursor check
(K.53′, `NestCtorNf`) in the recursor's representation: the members and
every frame's group back to their applications (`nestHoleImg`) — the
auxiliary constructor's type exactly as `restore_nested` writes it into
official's auxiliary recursor. -/

/-- Replace the free variables `f` maps (their annotations are not
descended into: a mapped variable is replaced whole, an unmapped one is
kept as it is). -/
def Expr.replaceFVars (f : Nat → Option Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => (f i).getD (.fvar i ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app a b => .app (replaceFVars f a) (replaceFVars f b)
  | .lam ty body => .lam (replaceFVars f ty) (replaceFVars f body)
  | .forallE ty body => .forallE (replaceFVars f ty) (replaceFVars f body)
  | .letE ty v body => .letE (replaceFVars f ty) (replaceFVars f v) (replaceFVars f body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (replaceFVars f e)

/-- **The holes read back** under the frames `prog` (innermost first):
every hole stands for its entry's WHOLE application — member `m`'s hole
`nP + m` for `T_m.{lps} p⃗` (the canonical parameters), a frame's hole
for its container applied to the frame's parameters, themselves read
back (a frame's parameters mention only the holes below its own).
`none` off the holes. -/
def nestHoleImg (ctx : NestCtx) : List NestHole → Nat → Option Expr
  | [], i =>
    if ctx.nP ≤ i ∧ i < ctx.hiAt 0 then
      some (Expr.mkAppN (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param))
        ctx.params)
    else none
  | h :: prog, i =>
    if i = ctx.hiAt prog.length then
      some (Expr.mkAppN (.const h.key.cname h.key.lvls)
        (h.key.ds.map (·.replaceFVars (nestHoleImg ctx prog))))
    else nestHoleImg ctx prog i

/-! ### The whole-application abstraction

A frame abstracts its group (the root frame: the block's members) by
replacing every WHOLE application `c.{us} q⃗` — `c` a group member at the
frame's levels, applied to exactly the parameters — by the member's
hole, a family over the member's INDICES alone.  The replacement happens
BEFORE the constructor's parameters are instantiated, at the CANONICAL
variables (`nestCanonCrest`: parameter `i` the variable `i`, member `m`'s
hole the variable `n + m`, all annotated `Sort 0` — the form the model
records at the container's install); the key's parameters and the
frame's holes are then put in by one variable replacement (`nestCrest`).
A stored constructor passed official's uniform-occurrence check at its
own install (`nestUniform`), so every member occurrence in it is such an
application. -/

/-- `e` is a constant applied to EXACTLY the placeholder variables
`fvar b, …, fvar (b + n - 1)` (annotations not compared): the constant's
name and levels. -/
def Expr.phApp? (b : Nat) : Expr → Nat → Option (Name × List Level)
  | .const c us, 0 => some (c, us)
  | .app f (.fvar j _), n + 1 => if j = b + n then phApp? b f n else none
  | _, _ => none

/-- The hole a whole application is replaced by (`f` at its constant). -/
def Expr.appHole? (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) :
    Option Expr :=
  (e.phApp? b n).bind fun p => f p.1 p.2

/-- **The whole-application replacement**, pre-order: a subterm that is a
whole application `f` maps is replaced by its image, not descended into;
free variables are leaves (their annotations are not descended into).
The executed walk is the cached tier's memoised `Expr.replaceAppsC`
(`replaceAppsC_spec`). -/
def Expr.replaceApps (f : Name → List Level → Option Expr) (b n : Nat) : Expr → Expr
  | .app a x => ((Expr.app a x).appHole? f b n).getD
      (.app (replaceApps f b n a) (replaceApps f b n x))
  | .const c us => ((Expr.const c us).appHole? f b n).getD (.const c us)
  | .lam t body => .lam (replaceApps f b n t) (replaceApps f b n body)
  | .forallE t body => .forallE (replaceApps f b n t) (replaceApps f b n body)
  | .letE t v body =>
    .letE (replaceApps f b n t) (replaceApps f b n v) (replaceApps f b n body)
  | .proj s i x => .proj s i (replaceApps f b n x)
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty
  | .sort u => .sort u
  | .lit l => .lit l

/-- The canonical parameter variables `fvar 0, …, fvar (n - 1)`. -/
def nestPhs (n : Nat) : List Expr := (List.range n).map fun i => .fvar i (.sort .zero)

/-- **The canonical whole-application substitution** of the group `names`
at the levels `us` over `n` parameters: member `m` to the canonical hole
`fvar (n + m)`. -/
def nestCanonSub (names : List Name) (us : List Level) (n : Nat) :
    Name → List Level → Option Expr :=
  fun c v => if v == us then (names.findIdx? (· == c)).map fun m => .fvar (n + m) (.sort .zero)
    else none

/-- **A stored constructor type, canonically abstracted**: the
(level-instantiated) type `cty` instantiated at the canonical parameter
variables (`nestPhs n`), every whole application of a member of `names`
at the levels `us` replaced by its canonical hole (`nestCanonSub`). -/
def nestCanonCrest (names : List Name) (us : List Level) (n : Nat) (cty : Expr) : Option Expr :=
  (instPisWith (nestPhs n) cty).map (·.replaceApps (nestCanonSub names us n) 0 n)

/-- The variable replacement of a key: the canonical parameter variable
`i` to the key's parameter `ds[i]`, the canonical hole `|ds| + m` to the
frame's hole `holes[m]`. -/
def nestKeyMap (ds holes : List Expr) : Nat → Option Expr :=
  fun i => if i < ds.length then ds[i]? else holes[i - ds.length]?

/-- **A stored constructor type at a key** (see the section header): its
canonical abstraction (`nestCanonCrest`, the group `names` at the key's
levels `us`), then the key's parameters `ds` and the frame's holes
`holes` (one per member of `names`, in order) put in. -/
def nestCrest (names : List Name) (us : List Level) (ds holes : List Expr) (cty : Expr) :
    Option Expr :=
  (nestCanonCrest names us ds.length cty).map (·.replaceFVars (nestKeyMap ds holes))

/-- The instantiation's type former, checked as official checks the
auxiliary type BEFORE the block exists: (N2) its index telescope at
`Ds` names no member and no hole below `hi` (official: "unknown
constant"), (N3) its sort is `Level.isEquiv` the block's.  Returns the
index count and the container's type instantiated at the key (the type
of the frame's hole: a family over the container's indices). -/
def nestInstType (ctx : NestCtx) (ops : CheckerOps m) (env : Env) (hi : Nat) (key : NestKey) :
    m (Nat × Expr) := do
  let (cvC, capsC) ← unwrapOr (match ctx.find? key.cname with
      | some (.indInfo cv caps) => some (cv, caps)
      | _ => none)
    (.internal "nested positivity: container vanished")
  -- the container is applied at its own level count (official:
  -- `infer_constant`'s "incorrect number of universe levels", which every
  -- constant of a checked constructor type — and of every
  -- reduct of it — passed; the model reads the key's constants at it)
  unless key.lvls.length = cvC.levelParams.length do
    throw (.invalid "nested positivity: incorrect number of universe levels for a nested \
      inductive datatype (official: incorrect number of universe levels)")
  -- the container's parameters are a SYNTACTIC telescope (its canonical
  -- instantiation exists, so the N2 check below reads
  -- against the container's recorded index telescope; every stored
  -- inductive's parameters are binders of its type, as official checks)
  let tyC ← familyTelescope ops env cvC capsC
  unless (tyC.stripPis key.ds.length).isSome do
    throw (.invalid "nested positivity: invalid nested inductive datatype, its type does \
      not bind its parameters (official: ill-formed inductive type)")
  let ty ← unwrapOr (instPisWith key.ds
      (tyC.instantiateLevelParams cvC.levelParams key.lvls))
    (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind \
      its parameters (official: ill-formed inductive type)")
  let s ← unwrapOr (match ty.piBinders.2 with
      | .sort s => some s
      | _ => none)
    (.invalid "nested positivity: invalid nested inductive datatype, its type is not a \
      telescope ending in a sort (official: type expected)")
  if ty.piBinders.1.any (fun b => b.nestOcc ctx.names ctx.nP hi) then
    throw (.invalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)")
  unless ← liftFueled "level comparison" (Level.isEquiv s ctx.sort) do
    throw (.invalid "nested positivity: mutually inductive types must live in the \
      same universe")
  pure (ty.piBinders.1.length, ty)

/-- A constructor's result is headed by a variable (its member's hole,
once the members are abstracted) — `checkSumCtor` already checked the
result is the member applied, so this never fires on a checked block;
the monotonicity proof reads the result's spine off it. -/
def nestResHead (e : Expr) : Bool :=
  match e.getAppFn with
  | .fvar .. => true
  | _ => false

/-- A constructor's field telescope `cur` (`nF` fields from field `j`),
each field through `rec` at its depth `base + j`, the field opened at the
variable `base + j`: the fields' kinds, the result (all fields opened)
and the state.  `err` is thrown at a telescope that is too short. -/
def nestFields
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    Nat → Nat → Expr → NestState →
      m (List NestFieldKind × List Expr × Expr × NestState)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, j, cur, st =>
    match cur with
    | .forallE a b => do
      let (k, nd, st) ← rec prog (base + j) 0 a st
      let (ks, nds, res, st) ← nestFields rec prog base err nF (j + 1)
        (b.instantiate1 (.fvar (base + j) a)) st
      pure (k :: ks, nd :: nds, res, st)
    | _ => throw err

/-- **A frame constructor's record** (K.53′): the constructor `cv` of
the frame's key `(us, ds)` under the frames `prog`, its walked field
telescope `nds` (opened at `hi, hi + 1, …`) onto `cur` closed back, all
read back (`nestHoleImg`). -/
def nestCtorNf (ctx : NestCtx) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (nds : List Expr) (cur : Expr) :
    NestCtorNf :=
  ⟨cv.name, us, ds.map (·.replaceFVars (nestHoleImg ctx prog)),
    (closeTelescope nds hi cur).replaceFVars (nestHoleImg ctx prog)⟩

/-- **A frame's constructors** — the ROOT frame's (the block's own,
`nestRoot`) and every container frame's (`nestFrame`) alike: each with
the frame's group abstracted
(`sub`), instantiated at `ds`, TYPED at the frame's context (the holes
typed by their formers — official types its auxiliary constructors; at
the root this is the typing of the member-abstracted constructor the
monotonicity proof reads; the frame's walk is read at a graded term),
its fields through `rec` at its instantiated type (the walk, fueled: a
container frame's is its enclosing walk one fuel lower, the root's is
fueled by the constructor, `nestRoot`)
above `hi`, U4 on the walked telescope (no later field and not the
result reads a non-ordinary field), its result
indices hole-free below `hi`, and its walked normal form recorded
(K.53′).  Returns every constructor's field kinds and walked normal form
(closed over its fields, holes kept) — the root's are the check's. -/
def nestCtors (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) :
    List (ConstantVal × Nat) → NestState → m (List (List NestFieldKind × Expr) × NestState)
  | [], st => pure ([], st)
  | (cv, nF) :: cs, st => do
    -- the constructor's level parameters are distinct (the substitution law
    -- instantiates them as the recorded reading does;
    -- every stored constant passed `checkConstantVal`'s own check)
    unless Name.nodup cv.levelParams do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    -- the container's constructor at the key, its group's WHOLE
    -- applications replaced by the holes BEFORE its parameters are
    -- instantiated (`nestCrest`), WITHOUT a β-step (official's
    -- `instantiate_pi_params`, `inductive.cpp` v4.34.0)
    let crest ← unwrapOr
      (nestCrest names us ds holes (cv.type.instantiateLevelParams cv.levelParams us))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind the parameters (official: ill-formed constructor)")
    let ty ← ops.inferType env hi crest
    let _ ← ops.ensureSort env hi ty
    let (ks, nds, cur, st) ← nestFields (rec crest) prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    -- U4 on the instantiated constructor: no later field and not the result
    -- reads a field that is
    -- not ordinary (recursive, reflexive, nested or in progress) — on the
    -- walked (whnf'd) telescope.  Official rejects every instance
    -- (charter item 9)
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result depends on a recursive or nested field)")
    -- official's "invalid return type" on the instantiated constructor; its
    -- result is headed by its hole, applied to its indices alone (never
    -- fires: a stored constructor's result is its inductive applied to
    -- the parameters, which `nestCrest` abstracts)
    unless nestResHead cur && cur.getAppArgs.all
        (fun x => !x.nestOcc ctx.names ctx.nP hi) do
      throw (.invalid "nested positivity: invalid return type — a constructor's result \
        index mentions the block")
    -- K.53′: the constructor's walked normal form at the
    -- frame's key, read back (`NestCtorNf`)
    let st := { st with ctorNfs := st.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) }
    let (os, st) ← nestCtors ctx ops env rec prog hi us ds names holes cs st
    pure ((ks, closeTelescope nds hi cur) :: os, st)

/-- The constructors of every container in `cs` (at one parameter
count), looked up (`nestContainer`). -/
def nestGroupCtors (ctx : NestCtx) (nPc : Nat) :
    List Name → m (List (ConstantVal × Nat))
  | [] => pure []
  | c :: cs => do
    let q ← unwrapOr (nestContainer ctx c) nestNonValid
    let (nPc', ctors) := q
    unless nPc' == nPc || ctors.isEmpty do
      throw (.invalid "nested positivity: number of parameters mismatch in inductive \
        datatype declaration (a container's group)")
    let rest ← nestGroupCtors ctx nPc cs
    pure (ctors ++ rest)

/-- The recorded block of the inductive `C` (`IndCaps.all`, official's
`all`): `[]` when none is recorded. -/
def nestBlockOf (ctx : NestCtx) (C : Name) : List Name :=
  match ctx.find? C with
  | some (.indInfo _ caps) => caps.all
  | _ => []

/-- **A frame's group-mates** (N2-eager): every
OTHER member of the container `C`'s recorded block (`IndCaps.all`), each
once.  Official copies the whole block of every container it finds
(`for J_name : I_val->get_all()`, `inductive.cpp` v4.34.0), reachable or
not; so does the frame. -/
def nestFrameMates (ctx : NestCtx) (C : Name) : List Name :=
  (nestBlockOf ctx C).eraseDups.filter (· != C)

/-- A frame's group grown by the named containers, each at the frame's
instantiation, its hole typed by its instantiated former. -/
def nestGrowGroup (ctx : NestCtx) (ops : CheckerOps m) (env : Env) (hi : Nat) (us : List Level)
    (ds : List Expr) : List Name → List (Name × Expr) → m (List (Name × Expr))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstType ctx ops env hi ⟨c, us, ds⟩
    nestGrowGroup ctx ops env hi us ds cs (grp ++ [(c, cty)])

/-- A frame's group accepted with its instantiation: every member at the
instantiation `(us, ds)` cached, those not cached yet. -/
def nestAcceptGroup (us : List Level) (ds : List Expr) :
    List (Name × Expr) → Array NestKey → Array NestKey
  | [], keys => keys
  | (c, _) :: rest, keys =>
    nestAcceptGroup us ds rest
      (if keys.contains ⟨c, us, ds⟩ then keys else keys.push ⟨c, us, ds⟩)

/-- **A container frame** at the instantiation `(us, ds)`, its holes the
container's WHOLE recorded group `grp` (at `hi, hi + 1, …`, typed by
their instantiated formers), every one of their constructors walked with
all of them abstracted, in one pass (N2-eager).  So an accepted frame's
readings are the joint operator of the container's block at the
instantiation. -/
def nestFrame (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) : m NestState := do
  -- K.52: the instantiation `C.{us} ds` is TYPED at the frame's own depth (its holes typed by
  -- their containers' formers, as the constants they stand for).  Official imposes it: after the
  -- nested elimination, `add_inductive` type-checks every replaced nested application, and a
  -- reduct of a typed term is typed.  The model grades the key's parameters in the frame's stack
  -- context by it.
  familyKeyCheck ops env ctx.find? hi (grp.headD default).1 us ds
  let prog' := (grp.mapIdx fun _ (c, ty) =>
    ({ key := ⟨c, us, ds⟩, base := hi, nIdx := ty.piBinders.1.length } : NestHole)).reverse ++ prog
  let ctors ← nestGroupCtors ctx nPc (grp.map (·.1))
  let (_, st) ← nestCtors ctx ops env (fun _ => rec) prog' (hi + grp.length) us ds (grp.map (·.1))
    (grp.mapIdx fun i (_, ty) => Expr.fvar (hi + i) ty) ctors st
  pure st

/-- **The frame stack an instantiation is walked under**: the EMPTY one
when its parameters mention no frame hole (they then read only the
parameters and the members), else the frames it was met under. -/
def nestWalkStack (ctx : NestCtx) (prog : List NestHole) (ds : List Expr) : List NestHole :=
  if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then [] else prog

/-- An instantiation's frame (`nestCont`'s last cases): the group-mates'
former checks (`nestGrowGroup`; the instantiation's own, `nestInstType`,
ran at the occurrence and gave `cty`, the type of its hole), the frame
(`nestFrame`), and the whole group cached — when its parameters mention
no frame hole, the only keys that can hit (`nestContKey`). -/
def nestContNew (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : m (NestFieldKind × NestState) := do
  -- an instantiation whose parameters mention no frame hole is walked at
  -- the EMPTY frame stack: its frame
  -- reads nothing of the frames it was met under, so every cached frame
  -- is derived at the root and a hit's subtree owns all its holes
  let wp := nestWalkStack ctx prog ds
  let grp ← nestGrowGroup ctx ops env (ctx.hiAt wp.length) us ds (nestFrameMates ctx n) [(n, cty)]
  let act := st.active
  let st := { st with active := grp.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey)) ++ act }
  let st ← nestFrame ctx ops env rec wp (ctx.hiAt wp.length) us ds nPc grp st
  -- the group is accepted with it — cached only when its parameters
  -- mention no frame hole: only such a key can ever hit (`nestContKey`)
  return (.nested (kb != 0),
    { st with active := act,
              keys := if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then
                nestAcceptGroup us ds grp st.keys else st.keys })

/-- The instantiation `(n, us, ds)` met (`nestCont` after its checks): IN
PROGRESS (`active`: every frame being walked, the enclosing frames among
them — `Complete/ProgActive.lean`) — met as a CONSTANT, which only
reduction can produce (the frame abstracts its whole group, so a
syntactic occurrence of a group-mate at the key is its hole): official's
"non valid occurrence" (its `check_positivity` reads the reduct, where a
copied type's constant is no member of the auxiliary block); cached — a hit, but only
when its parameters mention no FRAME hole (a frame hole's variable is reused
by a later frame, with other
parameters, so such a key is walked again); else a new frame.  `cty`:
the type of its hole (`nestInstType`, run by the caller). -/
def nestContKey (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : m (NestFieldKind × NestState) :=
  if st.active.contains ⟨n, us, ds⟩ then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  else if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) && st.keys.contains ⟨n, us, ds⟩ then
    pure (.nested (kb != 0), st)
  else nestContNew ctx ops env rec prog kb n us ds nPc cty st

/-- **The container case** of `nestPos`: the reduct `w` is the stored
inductive `n.{us}` applied to `args` (`contApp`), `rec` the walk
itself one fuel lower (at a frame's fields).  The container's
constructors are looked up by the names its record lists
(`nestContainer`); its checks (constructors
exist, enough arguments and hole-free indices, not `Quot`, parameters
without local variables); then the instantiation (`nestContKey`).  Split
off so that the monotonicity theorem can take the container case as its
own lemma. -/
def nestCont (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : m (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainer ctx n) nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) then
    throw nestNonValid
  -- `Quot` is stored as an `.indInfo` but is no inductive for
  -- official (`is_nested_inductive_app` asks `is_inductive()`):
  -- the one name read here.  Every other basis type (`Eq`, `Nat`,
  -- `Empty`, `False`, and `And`) is a container like any stored
  -- inductive.
  if n == quotName then throw nestNonValid
  unless (args.take q.1).all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt prog.length) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  -- the instance is FULLY applied: the container case
  -- compares the container's family at the index tuple, and a partial
  -- application is a function, whose graph does not grow with its values.
  -- A field's domain is a type, so a checked constructor never has one.
  let ni ← nestInstType ctx ops env (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKey ctx ops env rec prog kb n us (args.take q.1) q.1 ni.2 st

/-- **The positivity function** (see the section header): the domain
`e` at depth `dep`, `kb` `Π` binders into the field, `prog` the
instantiations in progress (innermost first; frame `i` from the
outside has its hole at `ctx.hiAt i`).  The block's members are HOLES
(the free variables `nP ..< nP + k`, abstracted by
`nestedBlockPositivity`), and so is each instantiation in progress (its
container abstracted to its frame's hole before its constructors are
instantiated) — so every hole the monotonicity induction varies is a
variable of the term `ops.whnf` reduces.  Throws official's verdict on
a non-positive or non-valid occurrence; returns the field's kind and
the cache. -/
def nestPos (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← ops.whnf env dep e
    -- `const`: the reduct mentions no member and no hole; the normal
    -- form is the input when it mentions none either, else the reduct
    if !w.nestOcc ctx.names ctx.nP hi then
      return (.ordinary, (if e.nestOcc ctx.names ctx.nP hi then w else e), st)
    match w with
    | .forallE a b =>
      -- `pi`: the domain hole-free, the codomain positive
      if a.nestOcc ctx.names ctx.nP hi then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ←
        nestPos ops env ctx fuel prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) st
      pure (k, .forallE a (nb.abstract1 dep), st)
    | _ =>
      let args := w.getAppArgs
      match w.getAppFn with
      | .fvar i _ =>
        -- `holeApp`: a hole (`nestHoleAt`) — a member's, the ROOT frame's,
        -- or a container frame's, its instantiation in progress — standing
        -- for its entry's whole application to the parameters, applied to
        -- hole-free indices, at its full arity (official
        -- `is_valid_ind_app`, :338–341)
        match nestHoleAt ctx prog i with
        | some h =>
          if args.all (fun x => !x.nestOcc ctx.names ctx.nP hi) && args.length == h.nIdx then
            return (if i < ctx.hiAt 0 then
                (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
              else .inProgress, w, st)
          else throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        -- a member constant left after the abstraction (other levels)
        if ctx.names.contains n then throw nestNonValid
        -- `contApp`: a stored inductive at a concrete instantiation
        let (k, st) ← nestCont ctx ops env (nestPos ops env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- The member holes: member `m` is the free variable `nP + m`, typed by
its former's type instantiated at the canonical parameters — a family
over the member's indices (the hole stands for `T_m p⃗`, so it is
well-scoped anywhere above the parameters).  `none` when a member is not
a stored former or its type does not bind the parameters. -/
def nestHoles (ctx : NestCtx) : Option (List Expr) :=
  (List.range ctx.names.length).mapM fun mm =>
    match ctx.formers[mm]? with
    | some cv => (instPisWith ctx.params cv.type).map (.fvar (ctx.nP + mm) ·)
    | none => none

/-- **The root frame's canonical crest** of a member constructor `cv` (at
the block's levels): its whole member applications abstracted
(`nestCanonCrest`) — what the uniform-occurrence check reads; the root
walks it with the canonical parameters and holes put in (`nestCrest`). -/
def nestRootCanon (ctx : NestCtx) (cv : ConstantVal) : Option Expr :=
  nestCanonCrest ctx.names (ctx.lps.map .param) ctx.nP
    (cv.type.instantiateLevelParams cv.levelParams (ctx.lps.map .param))

/-! ### Uniform occurrences: official's `check_uniform_ind_occs`

Official v4.33.1+ (`inductive.cpp` v4.34.1 `check_uniform_ind_occs`,
called first thing by `add_inductive`) walks every constructor type
SYNTACTICALLY — every subterm, `let`s, projections and the parameters'
own domains included — and rejects every occurrence of a member that is
not literally `T.{lps} p⃗`: the declaration's level parameters, applied
to exactly the parameter variables (over-applied, the extra arguments
are walked too; in a parameter's domain every occurrence is rejected).
Reduction never creates such an occurrence (the members are not yet in
the environment), so the syntactic check covers every occurrence a
later reduct could expose or erase.

Here it reads the root frame's canonical crest (`nestRootCanon`): every WHOLE
application `T_m.{lps} p⃗` replaced by the member's hole before the
parameters are instantiated (`nestCanonCrest`) — an over-applied one has its
extra arguments walked — so an occurrence at other levels, or applied to
anything but exactly the parameters, is a member constant left over.
The parameters' domains must be free of members altogether.

The check reads the STORED constructor, which is the declared one,
`let`s included, so an occurrence only in a `let`'s type, or in the
value of a `let` its body never uses, is seen and rejected, as
official does (`uh_let_erase_type`, `uh_let_erase_value`). -/

/-- Does a member or a hole occur in one of the first `n` binder domains
of `e`?  (The parameters' domains, at `n = nP`.) -/
def Expr.piDomsOcc (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE d b => d.nestOcc names lo hi || piDomsOcc names lo hi n b
  | _ + 1, _ => false

/-- **Official's `check_uniform_ind_occs` at one constructor `cv`** (see
the section header): the parameters' domains of its stored type name no
member, and its canonical crest (`nestRootCanon`: every whole application
`T_m.{lps} p⃗` abstracted) has no member constant left.  A type without
`nP` leading binders fails (the constructor stage already declined it). -/
def nestUniformOk (ctx : NestCtx) (cv : ConstantVal) : Bool :=
  !cv.type.piDomsOcc ctx.names ctx.nP (ctx.hiAt 0) ctx.nP &&
    match nestRootCanon ctx cv with
    | some crest => !crest.nestOcc ctx.names 0 0
    | none => false

/-- `nestUniformOk` at every stored constructor of every member, before
the walk (official runs it before anything else): a REJECT with
official's wording. -/
def nestUniform (ctx : NestCtx) (ctorss : List (List (ConstantVal × Nat))) : m Unit :=
  match ctorss.findSome? (·.find? (!nestUniformOk ctx ·.1)) with
  | some c => throw (.invalid s!"invalid occurrence of a datatype being declared in the \
      type of {c.1.name}: it must be applied to the parameters and universe levels of the \
      mutual declaration")
  | none => pure ()

/-! ### The root frame

The block itself is the walk's ROOT frame: its key each member at the
block's own levels and canonical parameters (`NestCtx.rootHoles`), its
holes the member holes, its constructors the block's own — walked by the
one constructor loop (`nestCtors`), exactly as a container frame's are:
instantiated at the key (the members' whole applications abstracted,
`nestCrest`), typed
at the holes' context, every field through `nestPos`, U4, the result,
the normal form recorded (K.53′).  What only the root has is, BEFORE
the walk, official's uniform-occurrence check on its constructors
(`nestUniform`), and — at the install — the fields' universes at the
holes (`checkAbsCtorSorts`, `BlockInstall.lean`). -/

/-- **The root frame**: every member's constructors through `nestCtors`
at the root key (the block's levels `lps`, the canonical parameters, the
holes `nP + t` above them), member by member, sharing the
walk's state; each constructor walked at the input-derived fuel of its
instantiated type (`whnfWalkFuel`: the root has no enclosing walk).
Returns every constructor's kinds and walked normal form
(member-abstracted, at the walk's context), per member. -/
def nestRoot (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestState →
      m (List (List (List NestFieldKind × Expr)) × NestState)
  | [], st => pure ([], st)
  | cs :: css, st => do
    let (o, st) ← nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st
    let (os, st) ← nestRoot ops env ctx holes css st
    pure (o :: os, st)

/-! ### The seeds

The stream's recursor family names the classes it eliminates: every
recursor's major `I.{us} D⃗ ı⃗`.  An outside one — `I` a stored inductive
that is no member and not `Quot` — is official's auxiliary type.  The
install's pass reads and RESOLVES every class before the walk
(`checkBlockClasses`, `GenRec.lean`: the head, the levels, the parameters
`D⃗` over the canonical parameters), and every outside class SEEDS the
walk (`nestSeedOf`): it is walked from the empty frame stack like a
container instance met at the root (`nestContKey`: a cache hit, or its
frame walked), after the members' constructors (the root frame), sharing
the cache — the positivity check is ONE run over the classes.  So every class of the
family is a node by construction — an occurrence whnf erases
(`K (List T)` with `K _ := Nat`) among them — and the walk reads no
syntactic occurrence.

A class is moved to the walk's representation (`nestSeedOf`): its
parameters' whole member applications `T_m.{lps} p⃗` abstracted to the
canonical holes (`replaceApps`, `nestCanonSub`, over the recursor's
parameter binders `0 ..< nP`), then every free variable — a recursor
parameter binder, or a canonical hole — replaced WHOLE by the canonical
parameter variable of its index (`ctx.params`) or the member's hole
(`nestKeyMap`), so the key's leaves are the canonical variables' and the
holes'.  Nothing
here trusts the stream: every seed is walked as the positivity check
walks any container instance, and the proofs read a seed's key only
through its frame's derivation and its leaves. -/

/-- **A resolved class as a seed**: the outside class `I.{us} ds`
(`ds` over the recursor's parameter binders `0 ..< nP`) in the walk's
representation, with its parameter count (see "The seeds"). -/
def nestSeedOf (ctx : NestCtx) (holes : List Expr) (I : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) : NestKey × Nat :=
  (⟨I, us, ds.map fun x =>
      (x.replaceApps (nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0 ctx.nP).replaceFVars
        (nestKeyMap ctx.params holes)⟩,
    nPc)

/-- **The seeds walked**, in order, at the root (see "The seeds"): each
class a container instance met at the empty frame stack
(`nestContKey`).  A seed's parameters are closed and below the frame
holes by construction (`nestSeedOf` of a class whose parameters mention
only the recursor's parameter binders, `targetMajorOf`), so nothing about
them is checked here. -/
def nestSeeds (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → m NestState
  | [], st => pure st
  | (key, nPc) :: ks, st => do
    let F := key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack
    let (_, cty) ← nestInstType ctx ops env (ctx.hiAt 0) key
    let (_, st) ← nestContKey ctx ops env (nestPos ops env ctx F) [] 0 key.cname key.lvls
      key.ds nPc cty st
    nestSeeds ops env ctx ks st

/-- **Positivity through containers, for a whole block** (the unit
tests' entry): official's uniform-occurrence check (`nestUniform`), then
the root frame (`nestRoot`) from the empty state.  `ctorss` are the members'
constructors AS STORED (not normalised: the function reduces itself).
Returns the accepted instantiations, the kinds, every constructor's
NORMALISED type and the recorded normal forms. -/
def nestedBlockPositivity (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let holes ← unwrapOr (nestHoles ctx)
    (.internal "nested positivity: a member is not a stored former")
  nestUniform ctx ctorss
  let (outs, st) ← nestRoot ops env ctx holes ctorss {}
  pure ⟨st.keys, outs.map (·.map (·.1)), outs.map (·.map (·.2)), st.ctorNfs⟩

end Nested

end ConLeche
