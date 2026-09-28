module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Kernel.Inductives.ClassRead
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# The CLASS checker: positivity over the recursor's classes, and the
recursor generated from them (EXPERIMENTAL, not the default route)

The CLASSCHECK design (`_tmp/classcheck/PLAN.md`, DESIGN "CLASSCHECK").
A "class" is a major of the stream's recursor family, `I.{us} D⃗`: the
block's members at their parameters, and — for a nested block — the
containers at the instantiations official's auxiliary types stand for.
The classes are READ off the recursors by an unverified pre-pass
(`ClassRead.lean`); nothing here trusts that reading:

1. **The classes** (`classInfo`): the head is a member (then the class is
   exactly `T p⃗` at the block's levels) or an installed inductive (not
   `Quot`) applied to all its parameters, which mention only the block's
   parameters, some member (official's `is_nested`), every member at the
   block's levels (M2′) and applied to the parameters (M3); its index
   telescope names no member (N2), its sort is the block's (N3), its
   level count is the inductive's, and the class is typed with the
   members abstracted (K.52).  Every member is exactly one class.
2. **The constructors of every class** — a member's own, a container's
   instantiated at the class's levels and parameters (official's
   `instantiate_pi_params`) — with the members abstracted to their holes
   AND every SYNTACTIC occurrence of a class abstracted to the class's
   hole (official's `replace_all_nested`, on the stream's classes):
   a class hole is ATOMIC, a family over the class's INDICES, the
   parameters baked in (official's `_nested.I As` constant; holes applied
   to the parameters falsely reject `corner_keynamed_ctor_occ`).
   Every class is REACHED: it is a member, or its hole occurs in a
   reached class's abstracted constructors (official creates an
   auxiliary type exactly at a syntactic occurrence; a duplicate class
   is never reached).
3. **Positivity** (`classPos`, official's `check_positivity`): every
   field of every abstracted constructor, through whnf: a type naming
   no member and no hole is ordinary; a `Π` needs a hole-free domain; the
   leaf is a member hole at the parameters or a class hole, its indices
   hole-free — anything else is "non valid", in particular a class met
   as a CONSTANT after whnf ("expose, never create": the class
   occurrence must be syntactic before whnf).  U4, the result indices
   hole-free, M3/M2′ on the members' constructors.
4. **Typing with the classes abstracted** (official's auxiliary
   declaration check): every abstracted constructor is inferred to a
   sort at the holes' context; the members' fields' universes are
   bounded there (U2).
5. **The walk against the recursor**: every field has an inductive
   hypothesis in its minor premise exactly when it recurses, at exactly
   the class it lands at.
6. **The recursors GENERATED** from the classes, the prefix layout and
   the walked constructors — type (`classGenRecTy`) and rules
   (`classGenRule`) — and compared with the stream's by `isDefEq`.

The formers, the constructors' own checks (`checkBlockPass`), the index
sorts, the elimination restriction, the capability records and the
projection tables are today's (`BlockInstall.lean`, `BlockTail.lean`).
Written once over `ShadowOps`, like the recursor check it replaces.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Check 1: the classes -/

/-- A checked class. -/
structure ClassInfo where
  /-- the class, concrete: the members as constants, the parameters at
  the block's canonical parameter variables -/
  key : ClassKey
  /-- the parameters with the members abstracted to their holes -/
  dsA : List Expr
  /-- `dsA`, the free variables' annotations erased (the comparisons') -/
  dsE : List Expr := []
  /-- the member it is (`none`: a container instance) -/
  member : Option Nat
  nPc : Nat
  nIdx : Nat
  /-- the constructors of `key.ind`, in order -/
  ctors : List (ConstantVal × Nat)
  /-- a container instance's hole (a free variable over its indices) -/
  hole : Option Expr
  deriving Inhabited

/-- A class's parameters, their variables moved to the canonical ones. -/
def classCanon (params : List Expr) (e : Expr) : Expr :=
  e.replaceFVars fun i => params[i]?

/-- **Check 1 at one class** (see the module header); `a` is the number
of container classes before it (its hole is `fvar (nP + k + a)`). -/
def classInfo (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (a : Nat) (key : ClassKey) : m ClassInfo := do
  let hiM := ctx.hiAt 0
  unless key.ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.nP) do
    throw (.invalid "class check: a class's parameters mention more than the block's \
      parameters (official: nested inductive datatypes parameters cannot contain local \
      variables)")
  let ds ← key.ds.mapM fun d => ops.annotate env ctx.nP (classCanon ctx.params d)
  unless (Expr.mkAppN (.const key.ind key.lvls) ds).allLevelParamsDefined ctx.lps do
    throw (.invalid "class check: a class names a universe parameter the block does not declare")
  match ctx.names.findIdx? (· == key.ind) with
  | some t =>
    unless key.lvls == ctx.lps.map .param && ds == ctx.params do
      throw (.invalid "class check: a member's class is not the member at the block's levels \
        and parameters")
    pure { key := ⟨key.ind, key.lvls, ctx.params⟩, dsA := ctx.params,
           dsE := ctx.params.map Expr.eraseFVarTys, member := some t,
           nPc := ctx.nP, nIdx := ctx.nIdxs.getD t 0, ctors := ctorsAs.getD t [],
           hole := none }
  | none => do
    if key.ind == quotName then
      throw (.invalid "class check: Quot is no inductive (official: non valid occurrence)")
    let some (nPc, ctors) := nestContainer ctx key.ind
      | throw (.invalid "class check: a class is not an installed inductive")
    unless ds.length == nPc do
      throw (.invalid "class check: a class is not applied to all its parameters")
    unless ds.any (·.nestOcc ctx.names 0 0) do
      throw targetNoAuxType
    let dsA := ds.map (nestAbstract ctx holes)
    if dsA.any (·.nestOcc ctx.names 0 0) then
      throw (.invalid "class check: invalid occurrence of a datatype being declared: it must \
        be applied to the parameters and universe levels of the mutual declaration (a member \
        at other universe levels in a class)")
    unless dsA.all (·.holesApplied ctx.names ctx.nP hiM) do
      throw (.invalid "class check: invalid occurrence of a datatype being declared: it must \
        be applied to the parameters and universe levels of the mutual declaration (a member \
        not applied to the parameters, in a class)")
    let (nIdx, fty) ← nestInstType ctx hiM ⟨key.ind, key.lvls, dsA⟩
    -- K.52: the class typed with the members abstracted
    let _ ← ops.inferType env hiM (Expr.mkAppN (.const key.ind key.lvls) dsA)
    let hty ← unwrapOr (instPisWith dsA fty) (.internal "class check: class hole type")
    pure { key := ⟨key.ind, key.lvls, ds⟩, dsA := dsA, dsE := dsA.map Expr.eraseFVarTys,
           member := none, nPc := nPc,
           nIdx := nIdx, ctors := ctors, hole := some (.fvar (hiM + a) hty) }

/-- Check 1 at every class, in order. -/
def classInfos (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (a : Nat) : List ClassKey → m (List ClassInfo)
  | [] => pure []
  | k :: ks => do
    let c ← classInfo ops env ctx holes ctorsAs a k
    let rest ← classInfos ops env ctx holes ctorsAs (if c.member.isSome then a else a + 1) ks
    pure (c :: rest)

/-! ## The class abstraction (official's `replace_all_nested`) -/

/-- Structural equality up to universe levels with equal CANONICAL forms
(`Level.canon`; and free variables' annotations): official's
instantiation simplifies levels (`mk_max`/`mk_imax`: `max 0 0 = 0`,
`max w w = w`, …), ours does not, so a class official spells
`List.{0} R` may occur as `List.{max 0 0} R` — or deep inside another
class's parameters.  The levels are compared by EQUALITY of normal forms,
not by `Level.isEquiv`: that is TRANSITIVE, so two spellings of one class
are recognised alike wherever they occur (the class abstraction's reading
needs this, DESIGN CLASSCHECK / P2B); `canon` subsumes every
simplification official's instantiation performs (DESIGN CLASSCHECK /
LEVELNF).  Binder data (`BinderMeta`, the codomain's zero-condition, which
the reading reads) must be EQUAL.  Equal-up-to terms read alike
(`denoteMeta_semEq`, `Expr.semEq_of_eqUpToLevels`). -/
def Expr.eqUpToLevels : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i _, .fvar j _ => i == j
  | .sort u, .sort v => Level.canon u == Level.canon v
  | .const n us, .const n' us' => n == n' && us.map Level.canon == us'.map Level.canon
  | .lit a, .lit b => a == b
  | .app f a, .app g b => Expr.eqUpToLevels f g && Expr.eqUpToLevels a b
  | .lam t b bm, .lam t' b' bm' => bm == bm' && Expr.eqUpToLevels t t' && Expr.eqUpToLevels b b'
  | .forallE t b bm, .forallE t' b' bm' =>
    bm == bm' && Expr.eqUpToLevels t t' && Expr.eqUpToLevels b b'
  | .letE t v b, .letE t' v' b' =>
    Expr.eqUpToLevels t t' && Expr.eqUpToLevels v v' && Expr.eqUpToLevels b b'
  | .proj s i x, .proj s' i' x' => s == s' && i == i' && Expr.eqUpToLevels x x'
  | _, _ => false

/-- Parameter lists equal: up to annotations, else up to level
equivalence. -/
def classParamsEq (as bs : List Expr) : Bool :=
  as.map Expr.eraseFVarTys == bs.map Expr.eraseFVarTys ||
    (as.length == bs.length && (as.zip bs).all fun (a, b) => a.eqUpToLevels b)

/-- A class occurrence `I.{us} D⃗ ı⃗`: the FIRST class (container classes
only; the members are holes already) whose parameters are `D⃗` up to the
free variables' annotations, at structurally equal levels, else at
levels with equal canonical forms (`Level.canon`), the parameters up to
annotations or `Expr.eqUpToLevels` (official's instantiation simplifies
`max 0 0`, `max w w`; our `Level.subst` does not).  Its hole and the
number of index arguments. -/
def classOcc? (cls : List ClassInfo) (e : Expr) : Option (Expr × Nat) :=
  match e.getAppFn with
  | .const I us =>
    let args := e.getAppArgs
    match cls.filter (fun c => c.hole.isSome && c.key.ind == I && c.nPc ≤ args.length) with
    | [] => none
    | cs@(c0 :: _) =>
      let ps := args.take c0.nPc
      let psE := ps.map Expr.eraseFVarTys
      let pick (c : ClassInfo) : Option (Expr × Nat) := c.hole.map (·, args.length - c.nPc)
      match cs.find? (fun c => us == c.key.lvls && psE == c.dsE) with
      | some c => pick c
      | none =>
        match cs.find? (fun c => us.map Level.canon == c.key.lvls.map Level.canon &&
            (psE == c.dsE || (ps.length == c.dsA.length &&
              (ps.zip c.dsA).all fun (a, b) => a.eqUpToLevels b))) with
        | some c => pick c
        | none => none
  | _ => none

/-- The class abstraction, memoised on the node: every occurrence `occ`
recognises, outermost first, becomes its hole applied to the (abstracted)
indices.  `hd = some (h, n)`: `e` is the head part of an occurrence, the
last `n` arguments to keep. -/
def classAbsGo (occ : Expr → Option (Expr × Nat)) :
    Option (Expr × Nat) → Std.HashMap Expr Expr → Expr → Expr × Std.HashMap Expr Expr
  | some (h, 0), memo, _ => (h, memo)
  | some (h, n + 1), memo, .app f a =>
    let (f', memo) := classAbsGo occ (some (h, n)) memo f
    let (a', memo) := classAbsGo occ none memo a
    (.app f' a', memo)
  | some _, memo, e => (e, memo)
  | none, memo, e@(.bvar _) => (e, memo)
  | none, memo, e@(.fvar ..) => (e, memo)
  | none, memo, e@(.sort _) => (e, memo)
  | none, memo, e@(.const ..) => (e, memo)
  | none, memo, e@(.lit _) => (e, memo)
  | none, memo, e@(.app f a) =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match occ e with
        | some (h, 0) => (h, memo)
        | some (h, n + 1) =>
          let (f', memo) := classAbsGo occ (some (h, n)) memo f
          let (a', memo) := classAbsGo occ none memo a
          (.app f' a', memo)
        | none =>
          let (f', memo) := classAbsGo occ none memo f
          let (a', memo) := classAbsGo occ none memo a
          (.app f' a', memo)
      (r, memo.insert e r)
  | none, memo, e@(.lam ty b bm) =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (t, memo) := classAbsGo occ none memo ty
      let (b', memo) := classAbsGo occ none memo b
      (.lam t b' bm, memo.insert e (.lam t b' bm))
  | none, memo, e@(.forallE ty b bm) =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (t, memo) := classAbsGo occ none memo ty
      let (b', memo) := classAbsGo occ none memo b
      (.forallE t b' bm, memo.insert e (.forallE t b' bm))
  | none, memo, e@(.letE ty v b) =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (t, memo) := classAbsGo occ none memo ty
      let (v', memo) := classAbsGo occ none memo v
      let (b', memo) := classAbsGo occ none memo b
      (.letE t v' b', memo.insert e (.letE t v' b'))
  | none, memo, e@(.proj s i x) =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (x', memo) := classAbsGo occ none memo x
      (.proj s i x', memo.insert e (.proj s i x'))

/-- The class abstraction of one term. -/
def classAbs (cls : List ClassInfo) (e : Expr) : Expr := (classAbsGo (classOcc? cls) none {} e).1

/-- **A class's constructor, abstracted**: a member's at the canonical
parameters with the members abstracted, a container's at the class's
levels and parameters (no β, official's `instantiate_pi_params`); then
every class occurrence abstracted. -/
def classCrest (ctx : NestCtx) (holes : List Expr) (cls : List ClassInfo) (c : ClassInfo)
    (cv : ConstantVal) : m Expr := do
  let crest ← unwrapOr (match c.member with
      | some _ => instPisWith ctx.params (nestAbstract ctx holes cv.type)
      | none => instPisWith c.dsA (cv.type.instantiateLevelParams cv.levelParams c.key.lvls))
    (.invalid "class check: a constructor type does not bind its parameters (official: \
      ill-formed constructor)")
  -- M3 on the constructor's TEXT (official ≥ v4.33.1, `check_uniform_ind_occs`):
  -- every member occurrence is the member applied to exactly the parameters
  -- — the recorded block's syntactic fact a later class's crest reads
  -- (DESIGN CLASSCHECK / P2D3)
  if c.member.isSome && !crest.holesApplied ctx.names ctx.nP (ctx.hiAt 0) then
    throw (.invalid "class check: invalid occurrence of a datatype being declared: it must \
      be applied to the parameters and universe levels of the mutual declaration (official: \
      check_uniform_ind_occs)")
  pure (classAbs cls crest)

/-- The class holes occurring in `e`. -/
def classHolesIn (cls : List ClassInfo) (e : Expr) : List Nat :=
  (List.range cls.length).filter fun c =>
    match (cls.getD c default).hole with
    | some (.fvar h _) => e.mentionsFvar h
    | _ => false

/-- **Two classes are the same instance**: one inductive, equivalent
levels, the parameters equal up to the free variables' annotations — a
FINER identification than official's (a forged stream may split one
auxiliary type into two recursors; official splits nothing it could
merge).  No defeq: coarser identification is not accepted. -/
def ClassInfo.same (c d : ClassInfo) : Bool :=
  c.key.ind == d.key.ind && Level.isEquivList c.key.lvls d.key.lvls == some true &&
    (c.dsE == d.dsE || classParamsEq c.dsA d.dsA)

/-- **Every class is reached** (official's auxiliary types): the members;
every class whose hole occurs in a reached class's abstracted
constructors; every class of a reached container's BLOCK at the same
instantiation (official copies a container's whole mutual block,
`elim_nested_inductive`); every class the same as a reached one.  The
closure, `fuel` rounds; `mates I` is `I`'s block. -/
def classReached (crests : List (List Expr)) (cls : List ClassInfo) (mates : Name → List Name)
    (sameIdx : Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, r => r
  | fuel + 1, r =>
    let occ := r.flatMap fun c => (crests.getD c []).flatMap (classHolesIn cls)
    let grp := (List.range cls.length).filter fun d => r.any fun c =>
      let ci := cls.getD c default
      let di := cls.getD d default
      sameIdx c d || (ci.member.isNone && di.member.isNone && (mates ci.key.ind).contains di.key.ind &&
        Level.isEquivList ci.key.lvls di.key.lvls == some true &&
        (ci.dsE == di.dsE || classParamsEq ci.dsA di.dsA))
    let new := occ ++ grp
    let r' := r ++ (new.filter (!r.contains ·)).eraseDups
    if r'.length == r.length then r else classReached crests cls mates sameIdx fuel r'

/-! ### Coarser identification: per-component defeq, in hole form

A class occurrence the syntactic abstraction does not match, or two
classes it does not identify, may still be the SAME class per component
(PLAN: robust to coarser identification): same inductive, equivalent
levels, every parameter defeq — compared in HOLE FORM (every syntactic
class occurrence inside the parameters already its hole, PROOFPLAN R1′),
both sides inferred first, at the holes' context, so the equation holds at
every value of the holes.  Official identifies syntactically only; this
is the charter's "coarser identification" superset. -/

/-- Parameters per component: equal up to annotations, else inferred and
defeq at depth `d`. -/
def classParamsDefEq (ops : CheckerOps m) (env : Env) (d : Nat) : List Expr → List Expr → m Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if a.eraseFVarTys == b.eraseFVarTys then classParamsDefEq ops env d as bs
    else
      let _ ← ops.inferType env d a
      let _ ← ops.inferType env d b
      if ← ops.isDefEq env d a b then classParamsDefEq ops env d as bs else pure false
  | _, _ => pure false

/-- A class's parameters in hole form. -/
def ClassInfo.holeForm (cls : List ClassInfo) (c : ClassInfo) : List Expr := c.dsA.map (classAbs cls)

/-- An occurrence identified with a class by per-component defeq: its
inductive, levels and hole-form parameters (annotations erased), the
class's hole. -/
structure ClassAlias where
  ind : Name
  lvls : List Level
  ps : List Expr
  nPc : Nat
  hole : Expr

/-- An aliased occurrence. -/
def aliasOcc? (al : List ClassAlias) (e : Expr) : Option (Expr × Nat) :=
  match e.getAppFn with
  | .const I us =>
    let args := e.getAppArgs
    (al.find? fun a => a.ind == I && a.nPc ≤ args.length &&
        Level.isEquivList us a.lvls == some true &&
        (args.take a.nPc).map Expr.eraseFVarTys == a.ps).map fun a =>
      (a.hole, args.length - a.nPc)
  | _ => none

/-- The candidates for an alias in an abstracted term: applications of a
container class's inductive whose closed parameters name a hole (member
or class), every node visited once. -/
def classCandsGo (isCand : Expr → Bool) :
    Std.HashSet Expr × List Expr → Expr → Std.HashSet Expr × List Expr
  | acc, e@(.app f a) =>
    if acc.1.contains e then acc else
    let acc := (acc.1.insert e, if isCand e then e :: acc.2 else acc.2)
    classCandsGo isCand (classCandsGo isCand acc f) a
  | acc, e@(.lam t b _) =>
    if acc.1.contains e then acc else classCandsGo isCand (classCandsGo isCand (acc.1.insert e, acc.2) t) b
  | acc, e@(.forallE t b _) =>
    if acc.1.contains e then acc else classCandsGo isCand (classCandsGo isCand (acc.1.insert e, acc.2) t) b
  | acc, e@(.letE t v b) =>
    if acc.1.contains e then acc else
    classCandsGo isCand (classCandsGo isCand (classCandsGo isCand (acc.1.insert e, acc.2) t) v) b
  | acc, e@(.proj _ _ x) =>
    if acc.1.contains e then acc else classCandsGo isCand (acc.1.insert e, acc.2) x
  | acc, _ => acc

/-- Resolve candidates to classes by per-component defeq. -/
def classAliases (ops : CheckerOps m) (env : Env) (hi : Nat) (cls : List ClassInfo) :
    List Expr → m (List ClassAlias)
  | [] => pure []
  | e :: es => do
    let rest ← classAliases ops env hi cls es
    match e.getAppFn with
    | .const I us =>
      let args := e.getAppArgs
      let mut found : Option ClassAlias := none
      for c in cls do
        if found.isNone && c.key.ind == I && c.nPc ≤ args.length && c.hole.isSome &&
            Level.isEquivList us c.key.lvls == some true then
          if ← classParamsDefEq ops env hi (args.take c.nPc) (c.holeForm cls) then
            found := some ⟨I, us, (args.take c.nPc).map Expr.eraseFVarTys, c.nPc,
              c.hole.getD default⟩
      pure (match found with | some a => a :: rest | none => rest)
    | _ => pure rest

/-- **The aliases a class's crest may use**: a member's, all of them; a
container class's, only those identifying an occurrence with a class of
an inductive strictly OLDER than its own and outside its block — never a
class its class fact keeps as a free hole (its group, or a cyclic inner
class: a younger inductive), which the fact reads at a STAGE value while
the occurrence's spelling reads true (DESIGN CLASSCHECK / P2D).  Official
identifies nothing by defeq. -/
def classAliasesFor (age : Name → Nat) (mates : Name → List Name) (c : ClassInfo)
    (al : List ClassAlias) : List ClassAlias :=
  if c.member.isSome then al else
    al.filter fun a => age a.ind < age c.key.ind && !(mates c.key.ind).contains a.ind

/-- **Class `d` is in class `c`'s group**: its inductive one of the block
mates of `c`'s, at `c`'s levels (canonical forms) and parameters (up to
levels). -/
def classOwn (mates : Name → List Name) (c d : ClassInfo) : Bool :=
  (mates c.key.ind).contains d.key.ind &&
    d.key.lvls.map Level.canon == c.key.lvls.map Level.canon &&
    d.dsA.length == c.dsA.length && (d.dsA.zip c.dsA).all fun (a, b) => a.eqUpToLevels b

/-- **Every block mate of a container class at its instantiation is a
class** (official copies a container's whole mutual block,
`elim_nested_inductive`): each mate at the class's levels and
parameters is recognised as a class occurrence.  The class fact's node is
the container's whole block at the key, every component a walked class
(DESIGN CLASSCHECK / P2D). -/
def classMatesOk (cls : List ClassInfo) (mates : Name → List Name) : Bool :=
  cls.all fun c => c.member.isSome || (mates c.key.ind).all fun I =>
    (classOcc? cls (Expr.mkAppN (.const I c.key.lvls) c.dsA)).isSome

/-! ### The class facts' free holes and their order (DESIGN CLASSCHECK / P2D3)

The proof reads a container class `c` as its container's TRUE carrier at
its key in hole form, a function of its FREE classes `F c`; its own group
`G c` (`classOwn`) is the fact's lfp variable; every other class it reads
COHERENTLY (the class's carrier at its own hole-form key), in an order.
What `c`'s fact reads coherently (`dep c`): the classes its group's crests
mention and, closed, the classes those keep free — none free or in the
group at `c`.  A stage value reaches a class only through such a read:
`y` read coherently at `x` keeps free every class inside its key
(`inn y`, at any depth) that `x` holds at a stage value (`F x ∪ G x`) —
the DEMAND (`classDemandOk`); the free sets are its least solution,
computed here by iteration (unverified) and CHECKED, as are the closures
and four syntactic facts the reading needs (`classFreeOk`):
* the free classes COMMUTE with the instantiation (`classCommutes`): the
  crest with its free classes and its group abstracted is the container's
  own constructor text, group atomised, instantiated at the key with its
  free classes abstracted — so the crest reads as the container's recorded
  clause at every value of the free holes;
* no alias of a container crest targets a free class;
* the key is typed with its free classes abstracted (R6, `classKeysCyclic`);
* the coherent reads are RANKED (acyclic).
None of this is derivable from the recorded blocks' own-name syntax: a
cycle of coherent reads, a free class formed across the instantiation, or
a group occurrence formed through the key each needs a key naming a
container under-applied at its own parameter's kind, excluded by TYPING
only (DESIGN CLASSCHECK / P2D3).  Official has no such notion; for
well-typed input the checks are redundant (`tests/classcheck.sh`). -/

/-- Two container classes are one up to spelling. -/
def classSameKey (c d : ClassInfo) : Bool :=
  c.key.ind == d.key.ind && c.key.lvls.map Level.canon == d.key.lvls.map Level.canon &&
    c.dsA.length == d.dsA.length && (c.dsA.zip d.dsA).all fun (a, b) => a.eqUpToLevels b

/-- The classes recognised at the outermost level of a container class's
key in hole form. -/
def classInner (cls : List ClassInfo) (c : ClassInfo) : List Nat :=
  if c.member.isSome then [] else (c.holeForm cls).flatMap (classHolesIn cls)

/-- A closure by fuelled iteration (unverified; `classClosedOk` checks it). -/
def classClose (step : Nat → List Nat) : Nat → List Nat → List Nat
  | 0, r => r
  | fuel + 1, r =>
    let r' := r ++ ((r.flatMap step).filter (!r.contains ·)).eraseDups
    if r'.length == r.length then r else classClose step fuel r'

/-- `R x` contains `x`'s successors and is closed under them. -/
def classClosedOk (n : Nat) (step R : Nat → List Nat) : Bool :=
  (List.range n).all fun x =>
    (step x).all (R x).contains && (R x).all fun y => (step y).all (R x).contains

/-- The holes of the classes `P` selects. -/
def classHoleOf (cls : List ClassInfo) (P : Nat → Bool) (h : Expr) : Bool :=
  (List.range cls.length).any fun j => (cls.getD j default).hole == some h && P j

/-- The recogniser restricted to the holes `P` keeps. -/
def classOccIf (cls : List ClassInfo) (P : Expr → Bool) (e : Expr) : Option (Expr × Nat) :=
  match classOcc? cls e with
  | some (h, n) => if P h then some (h, n) else none
  | none => none

/-- The class abstraction restricted to the holes `P` keeps. -/
def classAbsIf (cls : List ClassInfo) (P : Expr → Bool) (e : Expr) : Expr :=
  (classAbsGo (classOccIf cls P) none {} e).1

/-- The canonical parameters `fvar 0 … nPc-1` (annotation `Sort 0`). -/
def classCanonParams (nPc : Nat) : List Expr := (List.range nPc).map fun i => .fvar i (.sort .zero)

/-- A container constructor's text at the canonical parameters, its
block's members (`names`, at the constructor's own levels) the holes
`fvar (nPc + m)`: what the recorded clause reads (`canonAbs`). -/
def classCanonText (names : List Name) (nPc : Nat) (cv : ConstantVal) : Option Expr :=
  instPisWith (classCanonParams nPc)
    (nestAbstract ⟨names, cv.levelParams, nPc, [], classCanonParams nPc, .zero, fun _ => none, []⟩
      ((List.range names.length).map fun m => .fvar (nPc + m) (.sort .zero)) cv.type)

/-- The group ATOMISED: a member hole (placeholder `fvar (hi + m)`, above
every hole) applied to exactly the key's parameters `ps` becomes the class
hole `hs m`. -/
def classGrpOcc (hi k : Nat) (ps : List Expr) (hs : Nat → Option Expr) (e : Expr) :
    Option (Expr × Nat) :=
  match e.getAppFn with
  | .fvar i _ =>
    let args := e.getAppArgs
    if hi ≤ i && i < hi + k && ps.length ≤ args.length &&
        (args.take ps.length).map Expr.eraseFVarTys == ps.map Expr.eraseFVarTys then
      (hs (i - hi)).map (·, args.length - ps.length)
    else none
  | _ => none

/-- **The free classes commute with the instantiation** at container
class `c` (free holes `isF`, group holes `isG`, every hole below `hi`),
for the constructor `cv` of a group mate `d`: `d`'s crest (instantiated,
the free classes and the group abstracted) is the container's canonical
text at `c`'s levels and at `c`'s key with its free classes abstracted,
the group atomised. -/
def classCommutes (cls : List ClassInfo) (mates : Name → List Name) (hi : Nat)
    (isF isG : Expr → Bool) (c d : ClassInfo) (cv : ConstantVal) : Bool :=
  let names := mates c.key.ind
  let hs : Nat → Option Expr := fun m =>
    (classOcc? cls (Expr.mkAppN (.const (names.getD m .anonymous) c.key.lvls) c.dsA)).map (·.1)
  let dsF := c.dsA.map (classAbsIf cls isF)
  match instPisWith d.dsA (cv.type.instantiateLevelParams cv.levelParams d.key.lvls),
      classCanonText names c.nPc cv with
  | some e0, some A =>
    let lhs := classAbsIf cls (fun h => isF h || isG h) e0
    let rhs := (classAbsGo (classGrpOcc hi names.length dsF hs) none {}
      ((A.instantiateLevelParams cv.levelParams c.key.lvls).replaceFVars fun i =>
        if i < c.nPc then dsF[i]? else some (.fvar (hi + (i - c.nPc)) (.sort .zero)))).1
    lhs.eraseFVarTys == rhs.eraseFVarTys
  | _, _ => false

/-- The free-set certificate's vocabulary over the class indices: the
free sets `Fl` (up to spelling), and three tables computed once
(`ClassFreeV.build`): the groups, same keys, and the classes each crest
mentions. -/
structure ClassFreeV where
  cls : List ClassInfo
  mates : Name → List Name
  crests : List (List Expr)
  Fl : Nat → List Nat
  ownT : Array (Array Bool)
  skT : Array (Array Bool)
  holesT : Array (List Nat)

namespace ClassFreeV

/-- The vocabulary, its tables computed. -/
def build (cls : List ClassInfo) (mates : Name → List Name) (crests : List (List Expr))
    (Fl : Nat → List Nat) : ClassFreeV :=
  { cls, mates, crests, Fl
    ownT := Array.ofFn (n := cls.length) fun c => Array.ofFn (n := cls.length) fun d =>
      classOwn mates (cls.getD c default) (cls.getD d default)
    skT := Array.ofFn (n := cls.length) fun c => Array.ofFn (n := cls.length) fun d =>
      classSameKey (cls.getD c default) (cls.getD d default)
    holesT := Array.ofFn (n := cls.length) fun j =>
      (crests.getD j []).flatMap (classHolesIn cls) }

variable (V : ClassFreeV)

/-- `d` is in container class `c`'s group. -/
def own (c d : Nat) : Bool := (V.ownT.getD c #[]).getD d false

/-- `d` is free in container class `c`'s fact (up to spelling). -/
def isFree (c d : Nat) : Bool := (V.Fl c).any fun e => (V.skT.getD d #[]).getD e false

/-- `c`'s fact holds `d` at a stage value. -/
def stage (c d : Nat) : Bool := V.isFree c d || V.own c d

/-- What `c`'s group's crests mention. -/
def mentions (c : Nat) : List Nat :=
  ((List.range V.cls.length).filter (V.own c ·)).flatMap fun j => V.holesT.getD j []

/-- The coherent-read step at `c`: a class read coherently brings in the
classes it keeps free that `c` does not hold at a stage value. -/
def depStep (c d : Nat) : List Nat :=
  (List.range V.cls.length).filter fun e => V.isFree d e && !V.stage c e

/-- **The demand**: a class `y` read coherently at `x` keeps free every
class inside its key `x` holds at a stage value. -/
def demandOk (inn dep : Nat → List Nat) : Bool :=
  (List.range V.cls.length).all fun x => (dep x).all fun y =>
    (inn y).all fun e => !V.stage x e || V.isFree y e

end ClassFreeV

/-- **The free-set certificate** (see the section header). -/
def classFreeOk (V : ClassFreeV) (hi : Nat) (aliasesOf : ClassInfo → List ClassAlias)
    (inn dep : Nat → List Nat) (rank : Nat → Nat) : Bool :=
  let n := V.cls.length
  classClosedOk n (fun x => classInner V.cls (V.cls.getD x default)) inn && V.demandOk inn dep &&
    (List.range n).all fun c =>
      let ci := V.cls.getD c default
      ci.member.isSome || (
        -- commuting, at every group mate's constructors
        ((List.range n).all fun j => !V.own c j ||
          ((V.cls.getD j default).ctors.all fun (cv, _) =>
            classCommutes V.cls V.mates hi (classHoleOf V.cls (V.isFree c))
              (classHoleOf V.cls (V.own c)) ci (V.cls.getD j default) cv)) &&
        -- no alias onto a free class
        ((aliasesOf ci).all fun a => !classHoleOf V.cls (V.isFree c) a.hole) &&
        -- the coherent reads: closed, no stage class among them, ranked
        (V.mentions c).all (fun d => V.stage c d || (dep c).contains d) &&
        (dep c).all fun d => !V.stage c d && decide (rank d < rank c) &&
          (V.depStep c d).all (dep c).contains)

/-- Which part of the certificate fails (the error message only). -/
def classFreeDiag (V : ClassFreeV) (hi : Nat) (aliasesOf : ClassInfo → List ClassAlias)
    (inn dep : Nat → List Nat) (rank : Nat → Nat) : String :=
  let n := V.cls.length
  if !classClosedOk n (fun x => classInner V.cls (V.cls.getD x default)) inn then "inner closure" else
  if !V.demandOk inn dep then "demand" else
  let bad := (List.range n).filterMap fun c =>
    let ci := V.cls.getD c default
    if ci.member.isSome then none else
    if !((List.range n).all fun j => !V.own c j ||
          ((V.cls.getD j default).ctors.all fun (cv, _) =>
            classCommutes V.cls V.mates hi (classHoleOf V.cls (V.isFree c))
              (classHoleOf V.cls (V.own c)) ci (V.cls.getD j default) cv)) then
      some s!"class {c}: its free classes do not commute" else
    if !((aliasesOf ci).all fun a => !classHoleOf V.cls (V.isFree c) a.hole) then
      some s!"class {c}: an alias onto a free class" else
    if !((V.mentions c).all fun d => V.stage c d || (dep c).contains d) then
      some s!"class {c}: reads not closed" else
    if !((dep c).all fun d => !V.stage c d) then some s!"class {c}: reads a stage class" else
    if !((dep c).all fun d => decide (rank d < rank c)) then
      some s!"class {c}: the coherent reads are cyclic" else
    if !((dep c).all fun d => (V.depStep c d).all (dep c).contains) then
      some s!"class {c}: reads not closed under free classes" else none
  s!"{bad}; free {(List.range n).map V.Fl}"

/-- The coherent reads at the free sets `Fl`, closed (unverified). -/
def classDeps (V : ClassFreeV) : List (List Nat) :=
  (List.range V.cls.length).map fun r =>
    classClose (V.depStep r) (V.cls.length + 1) ((V.mentions r).filter (!V.stage r ·)).eraseDups

/-- The free sets: the demand's least solution, by fuelled iteration
(unverified). -/
def classFreeGo (V0 : ClassFreeV) (inn : Nat → List Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, fl => fl
  | fuel + 1, fl =>
    let V : ClassFreeV := { V0 with Fl := fun c => fl.getD c [] }
    let depL := classDeps V
    let dep : Nat → List Nat := fun x => depL.getD x []
    let n := V0.cls.length
    let fl' := (List.range n).map fun y =>
      let old := fl.getD y []
      let new := (List.range n).flatMap fun x =>
        if (V0.cls.getD x default).member.isNone && (dep x).contains y then
          (inn y).filter fun e => V.stage x e && !V.isFree y e
        else []
      old ++ new.eraseDups
    if (List.range n).all (fun y => (fl'.getD y []).length == (fl.getD y []).length) then fl
    else classFreeGo V0 inn fuel fl'

/-- The ranks, by fuelled iteration (unverified). -/
def classRankGo (n : Nat) (dep : Nat → List Nat) : Nat → List Nat → List Nat
  | 0, rk => rk
  | fuel + 1, rk => classRankGo n dep fuel ((List.range n).map fun r =>
      (dep r).foldl (fun a d => max a (rk.getD d 0 + 1)) 0)

/-- The certificate's data, computed (unverified): the free sets, the
inner-class closures, the coherent reads, the ranks. -/
def classFreeData (mates : Name → List Name) (cls : List ClassInfo) (crests : List (List Expr)) :
    (Nat → List Nat) × (Nat → List Nat) × (Nat → List Nat) × (Nat → Nat) :=
  let n := cls.length
  let innL := (List.range n).map fun x =>
    classClose (fun y => classInner cls (cls.getD y default)) (n + 1)
      (classInner cls (cls.getD x default))
  let inn : Nat → List Nat := fun x => innL.getD x []
  let V0 := ClassFreeV.build cls mates crests fun _ => []
  let fl := classFreeGo V0 inn (n * n + 1) ((List.range n).map fun _ => [])
  let V : ClassFreeV := { V0 with Fl := fun c => fl.getD c [] }
  let depL := classDeps V
  let dep : Nat → List Nat := fun x => depL.getD x []
  let rankL := classRankGo n dep (n + 1) ((List.range n).map fun _ => 0)
  (fun c => fl.getD c [], inn, dep, fun r => rankL.getD r 0)

/-- Which pairs of container classes are the same class: syntactically
(`ClassInfo.same`), else per component in hole form. -/
def classSamePairs (ops : CheckerOps m) (env : Env) (hi : Nat) (cls : List ClassInfo) :
    m (List (Nat × Nat)) := do
  let mut out := []
  for i in List.range cls.length do
    for j in List.range cls.length do
      let a := cls.getD i default
      let b := cls.getD j default
      if i < j && a.member.isNone && b.member.isNone && a.key.ind == b.key.ind &&
          Level.isEquivList a.key.lvls b.key.lvls == some true then
        if a.same b || (← classParamsDefEq ops env hi (a.holeForm cls) (b.holeForm cls)) then
          out := (i, j) :: (j, i) :: out
  pure out

/-- **R6: every container class's key typed with its FREE classes
abstracted** (`dsF c`; PROOFPLAN R6, DESIGN CLASSCHECK / P2D3), inferred
at the holes' context `hi`.  Official types every auxiliary constructor
with all nested occurrences abstracted, never the keys themselves; this is
the Sat premise the proof needs at the free holes' stage values. -/
def classKeysCyclic (ops : CheckerOps m) (env : Env) (cls : List ClassInfo)
    (dsF : Nat → List Expr) (hi : Nat) : List Nat → m Unit
  | [] => pure ()
  | c :: cs => do
    let ci := cls.getD c default
    if ci.member.isNone then
      -- no `tryCatch` to re-word the error: the verified tiers' monads
      -- (`FueledM`, `PairM`) do not support catching (the bodies never
      -- catch), so a caught error here would break the fueled bridge
      if dsF c != ci.dsA then
        discard <| ops.inferType env hi (Expr.mkAppN (.const ci.key.ind ci.key.lvls) (dsF c))
    classKeysCyclic ops env cls dsF hi cs

/-! ## Check 3: positivity over the classes -/

/-- A walked field: hole-free, or recursive at a class (`tele` binders
under it). -/
inductive ClassField where
  | ordinary
  | recursive (cls : Nat) (tele : Nat)
  deriving DecidableEq, Inhabited

/-- The class a hole variable stands for: member `t`'s hole its class, a
container class's hole that class. -/
def classOfHole (ctx : NestCtx) (cls : List ClassInfo) (i : Nat) : Option Nat :=
  if ctx.nP ≤ i && i < ctx.hiAt 0 then
    cls.findIdx? (·.member == some (i - ctx.nP))
  else
    cls.findIdx? fun c => match c.hole with
      | some (.fvar h _) => h == i
      | _ => false

/-- **Official's `check_positivity` over the classes**, one field type
(abstracted; the holes are `nP … hi-1`), through whnf. -/
def classPos (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (cls : List ClassInfo) (hi : Nat) :
    Nat → Nat → Nat → Expr → m (ClassField × Expr)
  | 0, _, _, _ => throw (.notImplemented "class positivity: fuel")
  | fuel + 1, dep, kb, e => do
    let w ← ops.whnf env dep e
    if !w.nestOcc ctx.names ctx.nP hi then
      return (.ordinary, (if e.nestOcc ctx.names ctx.nP hi then w else e))
    match w with
    | .forallE a b bm =>
      if a.nestOcc ctx.names ctx.nP hi then
        throw (.invalid "class positivity: non positive occurrence of the datatypes being \
          declared")
      let (k, nb) ← classPos ops env ctx cls hi fuel (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a))
      pure (k, .forallE a (nb.abstract1 dep) bm)
    | _ =>
      let args := w.getAppArgs
      match w.getAppFn, classOfHole ctx cls (match w.getAppFn with | .fvar i _ => i | _ => 0) with
      | .fvar i _, some c =>
        let ci := cls.getD c default
        let idxs := if ctx.nP ≤ i && i < ctx.hiAt 0 then
            (if args.take ctx.nP == ctx.params then some (args.drop ctx.nP) else none)
          else some args
        match idxs with
        | some ix =>
          if ix.length == ci.nIdx && ix.all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
            return (.recursive c kb, w)
          else throw nestNonValid
        | none => throw nestNonValid
      | _, _ =>
        throw (.invalid "class positivity: non valid occurrence of the datatypes being declared \
          (no class hole: a nested occurrence official does not see syntactically, or a class \
          created by reduction)")

/-- A constructor's fields walked, the field `j` opened at `base + j`. -/
def classFields (walk : Nat → Expr → m (ClassField × Expr)) (base : Nat) :
    Nat → Nat → Expr → m (List ClassField × List (Expr × BinderMeta) × Expr)
  | 0, _, cur => pure ([], [], cur)
  | nF + 1, j, cur =>
    match cur with
    | .forallE a b bm => do
      let (k, nd) ← walk (base + j) a
      let (ks, nds, res) ← classFields walk base nF (j + 1) (b.instantiate1 (.fvar (base + j) a))
      pure (k :: ks, (nd, bm) :: nds, res)
    | _ => throw (.invalid "class check: a constructor type does not bind its fields \
        (official: ill-formed constructor)")

/-- A walked constructor: its field kinds and its walked telescope,
closed over the fields and READ BACK (holes to the classes they stand
for; only the parameter variables free). -/
structure ClassCtor where
  cv : ConstantVal
  nF : Nat
  kinds : List ClassField
  tyN : Expr
  deriving Inhabited

/-- The holes read back: a member hole to the member, a class hole to
its class. -/
def classReadBack (ctx : NestCtx) (cls : List ClassInfo) (e : Expr) : Expr :=
  e.replaceFVars fun i =>
    if ctx.nP ≤ i && i < ctx.hiAt 0 then
      some (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param))
    else
      match classOfHole ctx cls i with
      | some c =>
        let ci := cls.getD c default
        some (Expr.mkAppN (.const ci.key.ind ci.key.lvls) ci.key.ds)
      | none => none

/-- **Checks 3 and 4 at one constructor** of class `c` (`crest`
abstracted): typed at the holes' context; every field walked
(`classPos`); U4; the result the class's own hole with hole-free indices;
at a member's constructor U2 (field universes at the holes), M3 and M2′. -/
def classCtor (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (cls : List ClassInfo) (hi : Nat) (c : ClassInfo) (cv : ConstantVal) (nF : Nat)
    (crest : Expr) : m ClassCtor := do
  unless Name.nodup cv.levelParams do
    throw (.invalid "class check: a constructor has a duplicate universe level parameter")
  -- check 4: official's auxiliary declaration, typed
  let ty ← ops.inferType env hi crest
  let _ ← ops.ensureSort env hi ty
  -- check 3
  let (ks, nds, cur) ← classFields (fun d e => classPos ops env ctx cls hi (whnfWalkFuel crest) d 0 e)
    hi nF 0 crest
  let tyN := closeTelescope nds hi cur
  if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary && structUsedLater tyN 0 i) then
    throw (.invalid "class positivity: non valid occurrence of the datatypes being declared \
      (a later field or the result depends on a recursive field)")
  let own : Option Nat := match c.member, c.hole with
    | some t, _ => some (ctx.nP + t)
    | none, some (.fvar h _) => some h
    | _, _ => none
  let resOk := match cur.getAppFn, own with
    | .fvar i _, some h => i == h
    | _, _ => false
  unless resOk && (cur.getAppArgs.drop (if c.member.isSome then ctx.nP else 0)).all
      (fun x => !x.nestOcc ctx.names ctx.nP hi) do
    throw (.invalid "class positivity: invalid return type (a constructor's result index \
      mentions the block)")
  if c.member.isSome then
    let xq ← unwrapOr (openPisAtFvars nF tyN hi) (.internal "class check: constructor fields")
    let _ ← checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
      ctx.sort hi xq.1 [] nF
    unless tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) do
      throw (.invalid "class check: invalid occurrence of a datatype being declared: it must \
        be applied to the parameters and universe levels of the mutual declaration (M3)")
    nestNoMemberConst ctx (nestAbstract ctx holes cv.type)
  pure ⟨cv, nF, ks, classReadBack ctx cls tyN⟩

/-- Checks 3 and 4 at every constructor of one class. -/
def classCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (cls : List ClassInfo) (hi : Nat) (c : ClassInfo) :
    List (ConstantVal × Nat) → List Expr → m (List ClassCtor)
  | (cv, nF) :: cs, crest :: crests => do
    let x ← classCtor ops env ctx holes cls hi c cv nF crest
    let xs ← classCtors ops env ctx holes cls hi c cs crests
    pure (x :: xs)
  | _, _ => pure []

/-- Checks 3 and 4 at every class. -/
def classAllCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (cls : List ClassInfo) (hi : Nat) : List ClassInfo → List (List Expr) → m (List (List ClassCtor))
  | c :: cs, cr :: crs => do
    let x ← classCtors ops env ctx holes cls hi c c.ctors cr
    let xs ← classAllCtors ops env ctx holes cls hi cs crs
    pure (x :: xs)
  | _, _ => pure []

/-! ## Check 5: the walk against the recursor's inductive hypotheses -/

/-- The minor premise slot of class `c`'s constructor `C`: exactly one. -/
def classMinorSlot (rd : ClassRead) (c : Nat) (C : Name) : m (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap fun s =>
    match (rd.slots[s]? : Option ClassSlot) with
    | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
    | _ => none
  match hits with
  | [x] => pure x
  | _ => throw (.invalid s!"class check: the recursors' prefix does not have exactly one minor \
      premise for {C} (official: invalid recursor)")

/-- A field's inductive hypothesis agrees with its walk: an ordinary field
has none; a recursive one exactly one, at the class it lands at or one the
same (`ClassInfo.same`).  Returns the kinds at the ih's class (the
generator's calls). -/
def classIhsAgree (sameIdx : Nat → Nat → Bool) (ctor : Name) (ihs : List (Nat × Nat)) :
    Nat → List ClassField → m (List ClassField)
  | _, [] => pure []
  | i, k :: ks => do
    let mine := ihs.filter (·.1 == i)
    let k' ← match k, mine with
      | .ordinary, [] => pure ClassField.ordinary
      | .recursive c tele, [(_, t)] =>
        unless sameIdx c t do
          throw (.invalid s!"class check: field {i} of {ctor} recurses at another class than \
            its inductive hypothesis names (official: invalid recursor)")
        pure (.recursive t tele)
      | _, _ =>
        throw (.invalid s!"class check: the inductive hypotheses of {ctor}'s minor premise \
          are not its recursive fields (official: invalid recursor)")
    let ks' ← classIhsAgree sameIdx ctor ihs (i + 1) ks
    pure (k' :: ks')

/-! ## Check 6: the recursors generated -/

/-- Close a telescope of `λ`s (`closeTelescope`'s twin). -/
def closeLams : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body => .lam dom ((closeLams bs (i + 1) body).abstract1 i 0) bm

/-- What generation reads: the block, the classes, the layout, the
walked constructors, the elimination level. -/
structure ClassGen where
  nP : Nat
  params : List Expr
  cls : List ClassInfo
  /-- per class, the former's type (its own levels instantiated) -/
  formerTys : List Expr
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  elim : Level
  /-- the generated prefix binders (`ClassGen.prefixBinders`), computed once -/
  pre : List (Expr × BinderMeta) := []

/-- The binder of an opened variable. -/
def classBinder (x : Expr) : Expr × BinderMeta := (x.fvarTypeD, default)

/-- The prefix variable of slot `s`. -/
def ClassGen.slotVar (g : ClassGen) (s : Nat) : Expr := .fvar (g.nP + s) (.sort .zero)

/-- Class `c`'s motive variable. -/
def ClassGen.motVar (g : ClassGen) (c : Nat) : Expr :=
  g.slotVar ((ClassRead.motiveSlot ⟨g.slots, []⟩ c).getD 0)

/-- Class `c`'s index telescope opened at `d`, and its major domain. -/
def ClassGen.major (g : ClassGen) (c : Nat) (d : Nat) : Option (List Expr × Expr) := do
  let ci := g.cls.getD c default
  let ty ← instPisWith ci.key.ds (g.formerTys.getD c default)
  let (ifs, _) ← openPisAtFvars ci.nIdx ty d
  pure (ifs, Expr.mkAppN (.const ci.key.ind ci.key.lvls) (ci.key.ds ++ ifs))

/-- Class `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`. -/
def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : Option Expr := do
  let (ifs, maj) ← g.major c d
  pure (closeTelescope (ifs.map classBinder) d (.forallE maj (.sort g.elim) default))

/-- The inductive hypothesis of a recursive field `f` (walked type
`∀ a⃗, J E⃗ e⃗`, landing at class `t`), opened at `d`: its telescope and its
index arguments. -/
def ClassGen.ihParts (g : ClassGen) (t : Nat) (tele : Nat) (f : Expr) (d : Nat) :
    Option (List Expr × List Expr) := do
  let (xs, leaf) ← openPisAtFvars tele f.fvarTypeD d
  pure (xs, leaf.getAppArgs.drop (g.cls.getD t default).nPc)

/-- Constructor `x`'s minor premise type at depth `d`, of class `c`. -/
def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) : Option Expr := do
  let ci := g.cls.getD c default
  let (fvs, res) ← openPisAtFvars x.nF x.tyN d
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let ihs ← (List.range recs.length).mapM fun l => do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let f := fvs.getD i default
    let (xs, idx) ← g.ihParts t tele f e
    pure (closeTelescope (xs.map classBinder) e
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN f xs])), (default : BinderMeta))
  let concl := Expr.mkAppN (g.motVar c)
    (res.getAppArgs.drop ci.nPc ++ [Expr.mkAppN (.const x.cv.name ci.key.lvls) (ci.key.ds ++ fvs)])
  pure (closeTelescope (fvs.map classBinder ++ ihs) d concl)

/-- The prefix binders (parameters, then every slot in the stream's
order). -/
def ClassGen.prefixBinders (g : ClassGen) : Option (List (Expr × BinderMeta)) := do
  let slotBs ← (List.range g.slots.length).mapM fun s => do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      pure ((← g.motiveTy c d), (default : BinderMeta))
    | .minor c C _ =>
      let x ← (g.ctors.getD c []).find? (·.cv.name == C)
      pure ((← g.minorTy c x d), (default : BinderMeta))
  pure (g.params.map classBinder ++ slotBs)

/-- **The generated recursor type** at class `c`. -/
def classGenRecTy (g : ClassGen) (c : Nat) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.major c rP
  let t : Expr := .fvar (rP + ifs.length) maj
  pure (closeTelescope (pre ++ ifs.map classBinder ++ [(maj, default)]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [t])))

/-- **The generated rule** of a recursor at class `c` for its constructor
`x`: `λ p⃗ (prefix) f⃗, minor f⃗ (λ a⃗, rec_t p⃗ (prefix) e⃗ (f a⃗))…`, the
callee `rec_t` the family's recursor at the landing class `t`
(`recOf`). -/
def classGenRule (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level) (c : Nat)
    (x : ClassCtor) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (s, _) ← (List.range g.slots.length).zip g.slots |>.find? fun (_, sl) =>
    match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false
  let (fvs, _) ← openPisAtFvars x.nF x.tyN rP
  let pvars := (List.range rP).map fun i => if i < g.nP then g.params.getD i default else
    g.slotVar (i - g.nP)
  let ihs ← (List.range x.nF).filterMapM fun i =>
    match x.kinds.getD i .ordinary with
    | .ordinary => some none
    | .recursive t tele => do
      let f := fvs.getD i default
      let (xs, idx) ← g.ihParts t tele f (rP + x.nF)
      let r ← recOf t
      pure (some (closeLams (xs.map classBinder) (rP + x.nF)
        (Expr.mkAppN (.const r rlvls) (pvars ++ idx ++ [Expr.mkAppN f xs]))))
  pure (closeLams (pre ++ fvs.map classBinder) 0 (Expr.mkAppN (g.slotVar s) (fvs ++ ihs)))

/-! ## The recursor family, checked against the generated one -/

/-- One stream rule against the generated one: the right-hand side
checked as today's rule stage checks it (scoping, annotation, resolution,
inference at the rule-less recursors' environment `feR`, the λ-binders'
elimination datum), the generated rule annotated and inferred there too,
and the two `isDefEq`.  Returns the annotated stream rule (stored). -/
def classRuleOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (cvR : ConstantVal)
    (pw : PropWhen) (n : Nat) (rhs gen : Expr) : m Expr := do
  unless rhs.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in rule of {cvR.name}")
  if rhs.hasFvar then
    throw (.invalid s!"free variable in rule of {cvR.name}")
  let rhsA ← ops.annotate feR.env 0 rhs
  unless rhsA.allLevelParamsDefined cvR.levelParams do
    throw (.invalid s!"undeclared universe parameter in rule of {cvR.name}")
  unless w.resolve feR rhsA do
    throw (unresolvedConstsError s!"rule of {cvR.name}" rhsA)
  let _ ← ops.inferType feR.env 0 rhsA
  let (rbs, _) ← unwrapOr (rhsA.stripLams n)
    (.invalid s!"class check: a rule of {cvR.name} is not a λ-telescope over the recursor's \
      prefix and the constructor's fields")
  -- the λ-domains name no recursor (they resolve at the constructors'
  -- environment `feT`): a generated rule's domains are the prefix's and
  -- the fields' types
  unless rbs.all (fun b => w.resolve feT b.1) do
    throw (unresolvedConstsError s!"the domains of a rule of {cvR.name}" rhsA)
  unless rbs.all (fun b => b.2.pw == pw) do
    throw (.invalid s!"class check: a rule of {cvR.name} does not annotate its λ-binders with \
      the family's elimination datum")
  let genA ← ops.annotate feR.env 0 gen
  let _ ← ops.inferType feR.env 0 genA
  unless ← ops.isDefEq feR.env 0 rhsA genA do
    throw (.invalid s!"class check: a rule of {cvR.name} is not the generated one (official: \
      invalid recursor)")
  pure rhsA

/-- A recursor's rules, pairwise with its class's walked constructors. -/
def classRulesOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (pw : PropWhen) (c : Nat) :
    List ClassCtor → List Expr → m (List Expr)
  | x :: xs, rhs :: rhss => do
    let gen ← unwrapOr (classGenRule g recOf (cvR.levelParams.map .param) c x)
      (.invalid s!"class check: the rule of {x.cv.name} calls a class whose recursor the \
        stream omits (official: unknown constant)")
    let r ← classRuleOk ops w feT feR cvR pw (g.nP + g.slots.length + x.nF) rhs gen
    let rs ← classRulesOk ops w feT feR g recOf cvR pw c xs rhss
    pure (r :: rs)
  | _, _ => pure []

/-- A class as the install's major record (`tgtStoredRules`). -/
def ClassInfo.toMajor (c : ClassInfo) : TargetMajor :=
  { ind := c.key.ind, lvls := c.key.lvls, ds := c.key.ds, nPc := c.nPc, nIdx := c.nIdx,
    ctors := c.ctors, member := c.member }

/-- **One recursor's type**: its constant checked; its record's member,
rule prefix and major index the generated ones; its type the generated
one (`isDefEq`, the generated type annotated and inferred first, R7); its
rule pins at its class. -/
def classRecTyOk (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (rules : List RecRule) (c : Nat) : m ConstantVal := do
  let cvRi ← checkConstantValF ops fe rc.cvR
  let ci := g.cls.getD c default
  unless rc.tgt == ci.member.getD k do
    throw (.invalid "class check: the recursor record's member is not its major's")
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    throw (.invalid "class check: the recursor record's rule prefix or major index is not the \
      generated one")
  let gty ← unwrapOr (classGenRecTy g c) (.internal "class check: generated recursor type")
  let gtyA ← ops.annotate fe.env 0 gty
  let s ← ops.inferType fe.env 0 gtyA
  let _ ← ops.ensureSort fe.env 0 s
  unless ← ops.isDefEq fe.env 0 cvRi.type gtyA do
    throw (.invalid s!"class check: the type of {rc.cvR.name} is not the generated one \
      (official: invalid recursor)")
  targetRulePins cvRi ci.toMajor rules
  pure cvRi

/-- Every recursor's type, pairwise with its class. -/
def classRecTysOk (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) :
    List RecShape → List (List RecRule) → List Nat → m (List ConstantVal)
  | rc :: rcs, rs :: rss, c :: cs => do
    let x ← classRecTyOk ops fe g k rc rs c
    let xs ← classRecTysOk ops fe g k rcs rss cs
    pure (x :: xs)
  | [], _, _ => pure []
  | _, _, _ => throw (.internal "class check: recursor list")

/-- Every recursor's rules, at the rule-less recursors' environment `feR`. -/
def classRecsRulesOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (pw : PropWhen) :
    List RecShape → List ConstantVal → List Nat → m (List (ConstantVal × TargetMajor × List Expr))
  | rc :: rcs, cvRi :: cvs, c :: cs => do
    let rhss ← classRulesOk ops w feT feR g recOf cvRi pw c (g.ctors.getD c []) rc.rhss
    let xs ← classRecsRulesOk ops w feT feR g recOf pw rcs cvs cs
    pure ((cvRi, (g.cls.getD c default).toMajor, rhss) :: xs)
  | _, _, _ => pure []

/-! ## The whole check -/

/-- **The class check** (checks 1 and 3–6 of the module header), in place of
today's recursor check (`targetRecCheck`): the pins, the pre-pass, the
classes, the abstracted constructors and their reachability, the
constructors typed and walked at the formers' environment (`fe₁`/`env₁`),
the walk against the inductive hypotheses, the elimination guard, and
every recursor against the generated one (types at the constructors'
environment `fe`, rules at the rule-less recursors').  Returns what the
install stores. -/
def classRecCheck (so : ShadowOps m) (fe₁ : FEnv) (env₁ : Env) (fe : FEnv) (p : BlockParts)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr) × List (List ClassCtor)) := do
  let q := p.toBlockShape
  targetRecPins q block
  -- the UNVERIFIED pre-pass (`ClassRead.lean`)
  let nPcOf : Name → Nat := fun I =>
    if q.memberNames.contains I then q.nP else
      match fe₁.find? I with
      | some (.indInfo _ caps) => caps.nparams
      | _ => 0
  let rd ← unwrapOr (classRead q.nP nPcOf q.recs)
    (.invalid "class check: the recursor family is not of the generated shape (official: \
      invalid recursor)")
  -- the context: the canonical parameters, the members' holes
  let cvTa0 ← unwrapOr cvTas.head? (.internal "class check: no type former")
  let pq ← unwrapOr (openPisAtFvars q.nP cvTa0.type 0)
    (.internal "class check: type former telescope")
  let ctx : NestCtx := ⟨q.memberNames, q.lps, q.nP, q.nIdxs, pq.1, q.resSort, fe₁.find?,
    env₁.consts⟩
  let holes ← unwrapOr (nestHoles ctx) (.internal "class check: a member is not a stored former")
  let ops₁ := so.opsAt fe₁
  so.flush
  -- check 1
  let cls ← classInfos ops₁ env₁ ctx holes ctorsAs 0 rd.classes
  unless (List.range q.k).all (fun t => (cls.filter (·.member == some t)).length == 1) do
    throw (.invalid "class check: the recursor family does not have exactly one class per \
      member (official: invalid recursor)")
  let hi := ctx.hiAt 0 + (cls.filter (·.member.isNone)).length
  let age : Name → Nat := fun I => ((fe₁.idx[I]?).map (·.1)).getD 0
  let mates : Name → List Name := fun I => match fe₁.find? I with
    | some (.indInfo _ caps) => caps.all
    | _ => []
  -- the block mates of every container class are classes
  unless classMatesOk cls mates do
    throw (.invalid "class check: a block mate of a container class at its instantiation is no \
      class of the recursor family (official copies the whole block, and generates a recursor \
      for every mate)")
  -- the abstracted constructors, and reachability
  let crests0 ← cls.mapM fun c => c.ctors.mapM fun (cv, _) => classCrest ctx holes cls c cv
  -- coarser identification: aliases for the unmatched occurrences, and
  -- the classes that are the same per component
  let heads := cls.filterMap fun c => if c.member.isNone then some (c.key.ind, c.nPc) else none
  let isCand : Expr → Bool := fun e => match e.getAppFn with
    | .const I _ => match heads.lookup I with
      | some nPc => nPc ≤ e.getAppArgs.length && (e.getAppArgs.take nPc).all fun x =>
          x.bvarB == 0 && x.fvarB ≤ hi
        && (e.getAppArgs.take nPc).any (·.nestOcc ctx.names ctx.nP hi)
      | none => false
    | _ => false
  let cands := (crests0.foldl (fun acc cs => cs.foldl (classCandsGo isCand) acc) ({}, [])).2
  let al ← classAliases ops₁ env₁ hi cls cands
  let crests := (cls.zip crests0).map fun (c, cs) =>
    cs.map fun e => (classAbsGo (aliasOcc? (classAliasesFor age mates c al)) none {} e).1
  let pairs ← classSamePairs ops₁ env₁ hi cls
  let sameIdx : Nat → Nat → Bool := fun i j =>
    i == j || (cls.getD i default).same (cls.getD j default) || pairs.contains (i, j)
  -- the class facts' free holes and their order; R6 at the free holes
  let (Fl, inn, dep, rank) := classFreeData mates cls crests
  let V := ClassFreeV.build cls mates crests Fl
  unless classFreeOk V hi (fun c => classAliasesFor age mates c al) inn dep rank do
    throw (.invalid s!"class check: the class facts' free holes do not commute with their keys, or \
      the classes' coherent reads are cyclic (official: no such notion; ill-typed keys only): \
      {classFreeDiag V hi (fun c => classAliasesFor age mates c al) inn dep rank}")
  classKeysCyclic ops₁ env₁ cls (fun c => (cls.getD c default).dsA.map
    (classAbsIf cls (classHoleOf cls (V.isFree c)))) hi (List.range cls.length)
  let roots := (List.range cls.length).filter fun c => (cls.getD c default).member.isSome
  let reached := classReached crests cls mates sameIdx (cls.length + 1) roots
  unless (List.range cls.length).all reached.contains do
    throw (.invalid "class check: a class of the recursor family is no auxiliary type of the \
      block (not a syntactic nested occurrence, or a duplicate; official generates no such \
      recursor)")
  -- checks 3 and 4
  let ctors ← classAllCtors ops₁ env₁ ctx holes cls hi cls crests
  so.flush
  -- check 5
  let ctors ← (List.range cls.length).mapM fun c => (ctors.getD c []).mapM fun x => do
    let (_, ihs) ← classMinorSlot rd c x.cv.name
    let ks ← classIhsAgree sameIdx x.cv.name ihs 0 x.kinds
    pure { x with kinds := ks }
  unless (rd.slots.filter fun | .minor .. => true | _ => false).length ==
      (ctors.map List.length).sum do
    throw (.invalid "class check: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  -- the elimination guard
  let nested := cls.any (·.member.isNone)
  if q.large && !blockLargeElimAllowed q nested then
    throw (.invalid "class check: large eliminator on a block whose sort may be Prop \
      (official: elim_only_at_universe_zero)")
  -- check 6
  let formerTys ← cls.mapM fun c => match c.member with
    | some t => pure ((cvTas.getD t default).type)
    | none => match fe₁.find? c.key.ind with
      | some (.indInfo cv _) => pure (cv.type.instantiateLevelParams cv.levelParams c.key.lvls)
      | _ => throw (.internal "class check: class former vanished")
  let elim := structElimLevel q.elim q.large
  let g0 : ClassGen := ⟨q.nP, ctx.params, cls, formerTys, rd.slots, ctors, elim, []⟩
  let pre ← unwrapOr g0.prefixBinders (.internal "class check: generated recursor prefix")
  let g := { g0 with pre := pre }
  let recOf : Nat → Option Name := fun t =>
    ((List.range q.recs.length).find? fun r => rd.recCls.getD r 0 == t).map fun r =>
      (q.recs.getD r default).cvR.name
  let cvRis ← classRecTysOk (so.opsAt fe) fe g q.k q.recs (targetRecRules block) rd.recCls
  let feR := consBlockRecsBareF q 0
    ((cvRis.zip rd.recCls).map fun (cv, c) => (cv, (cls.getD c default).nIdx)) fe
  so.flush
  let out ← classRecsRulesOk (so.opsRuleR feR) so.walkers fe feR g recOf (Level.zeronessOf elim)
    q.recs cvRis rd.recCls
  so.flush
  -- R5: the walked constructors (the members' normal forms first)
  pure (out, ctors)

/-! ## The install's tail on the class check (pure) -/

/-- `checkBlockTail` with the class check in place of the recursor check
(and no conformance check: the recursor IS generated and compared). -/
def checkBlockTailClass (ops : CheckerOps m) (block : List ConstantInfo)
    (q : BlockPass Env) : m Env := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSorts ops q.env₁ p.toBlockShape (p.members.zip q.cvTas)
  let env₂ := consBlockCtors p.nP q.ctorsAs q.env₁
  let (out, _) ← classRecCheck (ShadowOps.ofOps ops) (mkFEnv q.env₁) q.env₁ (mkFEnv env₂) p block
    q.cvTas q.ctorsAs
  let env₃ := consBlockRecsT env₂.find? (·.constsResolve env₂) p.toBlockShape 0 out env₂
  checkBlockTables p.toBlockShape (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-- `checkBlock` on the class check (EXPERIMENTAL, not the default). -/
def checkBlockClass (ops : CheckerOps m) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) : m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let q ← checkBlockPass ops env p₀ (blockRawRec p₀)
  checkBlockTailClass ops block q

end ConLeche
