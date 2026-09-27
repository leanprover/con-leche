module

public import ConLeche.Kernel.Inductives.FieldNf

@[expose] public section

/-!
# Positivity through containers, KEY-NAMED (PRIMREC/NESTKN §2′, PROTOTYPE)

A kernel prototype of the NESTKN design of record (`_tmp/primrec/NESTKN/DESIGN.md`
§2′, §2′.1 and §5): a node of the positivity check is a function of its CANONICAL KEY
alone (`C.{us} Ds`, `Ds` over the block's parameters and member holes only).

* **Contained keys** (`containedK`, R3): EVERY key occurrence in `Ds` at any depth,
  inner-first, merged up to defeq (KN5: same container, `Level.isEquivList` levels,
  parameters pairwise `isDefEq`; the first in scan order is the representative).
* **Flexibility** (`flexK`): a contained key is FLEXIBLE when the node's key, the group's
  formers at `DsF` (K-a) and its crests type-check with every occurrence of it abstracted
  to a family over its indices — the family typed by its container's former at the key's
  parameters with the inner flexible families abstracted (R3); the flexible keys are then
  abstracted JOINTLY — a joint failure is an internal error (§2′.1), never a reject.
  `nestLayoutK` is the ONE layout function (K-f).
* **The layout** (VARIANT E): flexible families at `hiAt0 + j` (over the indices, typed
  at their concrete key), then the own group's HOLES exactly as today's frames: each
  container constant at `us` abstracted (`replaceConsts`) BEFORE the constructor is
  instantiated at `DsF`, the hole `y_g` typed by the container's former at `us` (generic
  in the parameters) and met as `y_g DsF is` (today's frame-hole rule) — so an own
  occurrence reached only through a redex still reduces to the hole.
* **USE** (`useK`): the used key's former checks at the site (K-c) and K.52 at the user's
  layout, the node walked once (cached by its key), the user's parameters matched against
  `DsF` and CHECKED (`matchK`, K-d), and the node's MET flexible
  families propagated to the user: a family of the user is met there, a concrete key is
  used in turn (the pending walk, while the user is still active; an in-progress target
  rejects, K-g).  A rigid key the user holds at stage is an internal error (§2′.1).

Everything recurses on explicit fuel (`posK`, `synK`, `useK`, `nodeK`, one mutual block).
UNWIRED: nothing in the install calls it; `nestedBlockPositivityK` / `nestBlockCtorsK`
have the result shapes of `nestedBlockPositivity` / `nestBlockCtors`.
-/

namespace ConLeche

section NestedK

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Layouts and the readback -/

/-- A node's layout: its families — the flexible contained keys first (`nF` of them),
then the own group — family `j` the variable `hiAt0 + j`, each with its key (canonical)
and its index count; `hi` the first variable above them. -/
structure LayoutK where
  fams : List (NestKey × Nat) := []
  nF : Nat := 0
  /-- the flexible families' types (`fvar (hiAt0 + j) famTys[j]`), aligned with `fams` -/
  famTys : List Expr := []
  /-- VARIANT E: the own group's HOLES (today's frame holes), at `hiAt0 + nF + g`, each
  the container's former at `lvls` applied to `dsF` and then its indices -/
  grp : List Name := []
  lvls : List Level := []
  dsF : List Expr := []
  hi : Nat
  deriving Inhabited

/-- The expression a key stands for. -/
def NestKey.expr (k : NestKey) : Expr := Expr.mkAppN (.const k.cname k.lvls) k.ds

/-- The root's layout: the members only. -/
def rootLayoutK (ctx : NestCtx) : LayoutK := { hi := ctx.hiAt 0 }

/-- **The readback** at a layout: every family variable to its key (canonical; the
member holes stay). -/
def rbK (ctx : NestCtx) (L : LayoutK) (e : Expr) : Expr :=
  e.replaceFVars fun i =>
    if ctx.hiAt 0 ≤ i && i < ctx.hiAt 0 + L.nF then (L.fams[i - ctx.hiAt 0]?).map (·.1.expr)
    else if ctx.hiAt 0 + L.nF ≤ i && i < L.hi then
      (L.grp[i - ctx.hiAt 0 - L.nF]?).map fun g => .const g L.lvls
    else none

/-! ## Top-down replacement of exactly-applied spines (memoised) -/

/-- Replace top-down: at every node `f` answers first (a hit is not descended into). -/
def Expr.replaceTopGo (f : Expr → Option Expr) (memo : Std.HashMap Expr Expr) :
    Expr → Expr × Std.HashMap Expr Expr
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | e@(.fvar ..) => (e, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match f e with
        | some r => (r, memo)
        | none =>
          match e with
          | .app a b =>
            let (a', memo) := replaceTopGo f memo a
            let (b', memo) := replaceTopGo f memo b
            (.app a' b', memo)
          | .lam ty body bm =>
            let (t, memo) := replaceTopGo f memo ty
            let (b, memo) := replaceTopGo f memo body
            (.lam t b bm, memo)
          | .forallE ty body bm =>
            let (t, memo) := replaceTopGo f memo ty
            let (b, memo) := replaceTopGo f memo body
            (.forallE t b bm, memo)
          | .letE ty v body =>
            let (t, memo) := replaceTopGo f memo ty
            let (v', memo) := replaceTopGo f memo v
            let (b, memo) := replaceTopGo f memo body
            (.letE t v' b, memo)
          | .proj s i sub =>
            let (u, memo) := replaceTopGo f memo sub
            (.proj s i u, memo)
          | e => (e, memo)
      (r, memo.insert e r)

/-- `replaceTopGo` from an empty memo. -/
def Expr.replaceTop (f : Expr → Option Expr) (e : Expr) : Expr := (e.replaceTopGo f {}).1

/-- `e` is exactly the key `k` (its constant at its levels applied to its parameters). -/
def spineIsK (k : NestKey) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n us => n == k.cname && us == k.lvls && e.getAppArgs == k.ds
  | _ => false

/-- **The abstraction** `absKeys S e`: every occurrence, at any depth, of a key of `S`
becomes its family (applied to whatever indices followed it, which are descended into). -/
def absKeysK (S : List (NestKey × Expr)) (e : Expr) : Expr :=
  e.replaceTop fun x => (S.find? fun (k, _) => spineIsK k x).map (·.2)

/-! ## Key occurrences and contained keys -/

/-- **A key occurrence** of the block `[lo, hi)`: a stored inductive (no member, not
`Quot`) applied to at least its parameters, some parameter mentioning the block. -/
def keyOccK? (ctx : NestCtx) (lo hi : Nat) (e : Expr) : Option NestKey :=
  match e.getAppFn with
  | .const n us =>
    if ctx.names.contains n || n == quotName then none else
    match ctx.find? n with
    | some (.indInfo _ caps) =>
      let args := e.getAppArgs
      if caps.nparams ≤ args.length &&
          (args.take caps.nparams).any (·.nestOcc ctx.names lo hi) then
        some ⟨n, us, args.take caps.nparams⟩
      else none
    | _ => none
  | _ => none

/-- The contained-key scan (R3): EVERY key occurrence at any depth (block = the members)
with bvar-closed parameters, each once, INNER-FIRST (a key after the keys inside it). -/
def containedGoK (ctx : NestCtx) (e : Expr) (acc : NestSynAcc) : NestSynAcc :=
  if acc.seen.contains e then acc else
  let acc := { acc with seen := acc.seen.insert e }
  match e with
  | .app f a =>
    let inner := containedGoK ctx a (containedGoK ctx f acc)
    match keyOccK? ctx ctx.nP (ctx.hiAt 0) e with
    | some k =>
      if k.ds.all (·.bvarB == 0) && !inner.keys.contains k then
        { inner with keys := inner.keys.push k }
      else inner
    | none => inner
  | .lam t b _ | .forallE t b _ => containedGoK ctx b (containedGoK ctx t acc)
  | .letE t v b => containedGoK ctx b (containedGoK ctx v (containedGoK ctx t acc))
  | .proj _ _ x => containedGoK ctx x acc
  | _ => acc

/-- A key's contained keys (all depths, inner-first, syntactically deduplicated). -/
def containedK (ctx : NestCtx) (ds : List Expr) : List NestKey :=
  (ds.foldl (fun acc d => containedGoK ctx d acc) {}).keys.toList

/-- Fuel errors are never caught (a fuel-indexed family is monotone in its success). -/
def isFuelErrK : CheckError → Bool
  | .notImplemented msg => (msg.splitOn "fuel").length > 1
  | _ => false

/-- Parameters pairwise defeq at `d` (an `.invalid` failure reads as `false`). -/
def dsDefEqK (ops : CheckerOps m) (env : Env) (d : Nat) : List Expr → List Expr → m Bool
  | a :: as, b :: bs => do
    let r ← tryCatchThe CheckError (ops.isDefEq env d a b) fun err =>
      match err with
      | .invalid _ => pure false
      | e => throw e
    if r then dsDefEqK ops env d as bs else pure false
  | [], [] => pure true
  | _, _ => pure false

/-- KN5: the first representative (index) that `k` merges into. -/
def findRepK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (k : NestKey) :
    List NestKey → Nat → m (Option Nat)
  | [], _ => pure none
  | r :: rs, j => do
    if r.cname == k.cname && (Level.isEquivList r.lvls k.lvls).getD false &&
        r.ds.length == k.ds.length then
      if ← dsDefEqK ops env (ctx.hiAt 0) r.ds k.ds then return some j
    findRepK ops env ctx k rs (j + 1)

/-- KN5: the contained keys split into representatives and aliases (alias ↦ rep index). -/
def mergeK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List NestKey → List NestKey → List (NestKey × Nat) → m (List NestKey × List (NestKey × Nat))
  | [], reps, als => pure (reps, als)
  | k :: ks, reps, als => do
    match ← findRepK ops env ctx k reps 0 with
    | some j => mergeK ops env ctx ks reps (als ++ [(k, j)])
    | none => mergeK ops env ctx ks (reps ++ [k]) als

/-- A contained key's family type (R3): its container's former at the key's parameters
with the EARLIER (inner) flexible families `Sin` abstracted, with its index count. -/
def famTypeK (ctx : NestCtx) (Sin : List (NestKey × Expr)) (k : NestKey) :
    Option (Expr × Nat) :=
  match ctx.find? k.cname with
  | some (.indInfo cv _) =>
    (instPisWith (k.ds.map (absKeysK Sin))
      (cv.type.instantiateLevelParams cv.levelParams k.lvls)).map
      fun t => (t, t.piBinders.1.length)
  | _ => none

/-! ## The layout's typing -/

/-- A typing step of a layout: a `.notImplemented` that is not fuel (a projection out of a
family-typed value) is a reject. -/
def typeAtK (ops : CheckerOps m) (env : Env) (d : Nat) (e : Expr) (sort : Bool) : m Unit :=
  tryCatchThe CheckError (do
      let ty ← ops.inferType env d e
      if sort then
        let _ ← ops.ensureSort env d ty
      pure ())
    fun err =>
      match err with
      | .notImplemented msg =>
        if isFuelErrK err then throw err
        else throw (.invalid s!"nested positivity: a container instance is ill-typed at its \
          layout ({msg}) (official: the auxiliary constructor does not type-check)")
      | e => throw e

/-- The group's crests at `dsF`, the own occurrences abstracted to the group's families. -/
def crestsK (us : List Level) (dsF : List Expr) (grp : List (Name × Expr)) :
    List (ConstantVal × Nat) → Option (List Expr)
  | [] => some []
  | (cv, _) :: cs => do
    let t ← instPisWith dsF ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      fun c us' => if us' == us then grp.lookup c else none)
    let rest ← crestsK us dsF grp cs
    pure (t :: rest)

/-- Type each crest at `hi` (into a sort). -/
def typeCrestsK (ops : CheckerOps m) (env : Env) (hi : Nat) : List Expr → m Unit
  | [] => pure ()
  | c :: cs => do
    typeAtK ops env hi c true
    typeCrestsK ops env hi cs

/-- K-a: the group's formers at `DsF`, at the layout depth `hiK` (`nestInstType`: levels,
N2 with the flexible families as holes, N3): each member's index count and its hole's type
(the container's former at `us`, generic in the parameters — today's frame hole). -/
def groupInfoK (ctx : NestCtx) (us : List Level) (dsF : List Expr) (hiK : Nat) :
    List Name → m (List (Name × Nat × Expr))
  | [] => pure []
  | g :: gs => do
    let (nI, ty) ← nestInstType ctx hiK ⟨g, us, dsF⟩
    let rest ← groupInfoK ctx us dsF hiK gs
    pure ((g, nI, ty) :: rest)

/-- **A layout, built and typed**: the families `S` (key or alias ↦ family variable, the
`nF` flexible ones below `hiAt0 + nF`), the group's holes above them; the group's formers
at `DsF` (K-a), the key `C us DsF` typed at `hiAt0 + nF`, every crest at `hi`.  Returns
`DsF`, the group's information and the crests. -/
def layoutTypeK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (kc : NestKey)
    (gnames : List Name) (ctors : List (ConstantVal × Nat))
    (S : List (NestKey × Expr)) (nF : Nat) :
    m (List Expr × List (Name × Nat × Expr) × List Expr) := do
  let hiK := ctx.hiAt 0 + nF
  let dsF := kc.ds.map (absKeysK S)
  let ginfo ← groupInfoK ctx kc.lvls dsF hiK gnames
  let grp := ginfo.mapIdx fun g (n, _, ty) => (n, Expr.fvar (hiK + g) ty)
  let crests ← unwrapOr (crestsK kc.lvls dsF grp ctors)
    (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
      does not bind the parameters (official: ill-formed constructor)")
  typeAtK ops env hiK (Expr.mkAppN (.const kc.cname kc.lvls) dsF) false
  typeCrestsK ops env (hiK + ginfo.length) crests
  pure (dsF, ginfo, crests)

/-- The substitution of the flexible families found so far (`fl`: representative index,
type, index count; family `i` at `hiAt0 + i`), aliases included. -/
def flexSubstK (ctx : NestCtx) (reps : List NestKey) (als : List (NestKey × Nat))
    (fl : List (Nat × Expr × Nat)) : List (NestKey × Expr) :=
  (fl.mapIdx fun i (r, ty, _) => (r, Expr.fvar (ctx.hiAt 0 + i) ty)).flatMap fun (r, z) =>
    ((reps[r]?).toList.map fun k => (k, z)) ++ (als.filter (·.2 == r)).map fun a => (a.1, z)

/-- **Flexibility**, inner-first: a representative is flexible iff the layout with IT
alone abstracted everywhere (its aliases with it) types — its family typed over the inner
flexible families found so far (declared below it, `famTypeK`).  Returns the flexible ones
in order (representative index, family type, index count). -/
def flexK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (kc : NestKey)
    (gnames : List Name) (ctors : List (ConstantVal × Nat))
    (reps : List NestKey) (als : List (NestKey × Nat)) :
    List Nat → List (Nat × Expr × Nat) → m (List (Nat × Expr × Nat))
  | [], fl => pure fl
  | r :: rs, fl => do
    match reps[r]?, (reps[r]?).bind (famTypeK ctx (flexSubstK ctx reps als fl)) with
    | some k, some (ty, nI) =>
      let z := Expr.fvar (ctx.hiAt 0 + fl.length) ty
      let S := (k, z) :: (als.filter (·.2 == r)).map (fun a => (a.1, z))
      let ok ← tryCatchThe CheckError
        (do let _ ← layoutTypeK ops env ctx kc gnames ctors S (fl.length + 1); pure true)
        fun err =>
          match err with
          | .invalid _ => pure false
          | e => throw e
      flexK ops env ctx kc gnames ctors reps als rs (if ok then fl ++ [(r, ty, nI)] else fl)
    | _, _ => flexK ops env ctx kc gnames ctors reps als rs fl

/-- The constructors of the containers `cs` (one parameter count), through a lookup that
reads `nestContainer`. -/
def groupCtorsK (look : Name → Option (Nat × List (ConstantVal × Nat))) (nPc : Nat) :
    List Name → m (List (ConstantVal × Nat))
  | [] => pure []
  | c :: cs => do
    let (nPc', ctors) ← unwrapOr (look c) nestNonValid
    unless nPc' == nPc || ctors.isEmpty do
      throw (.invalid "nested positivity: number of parameters mismatch in inductive \
        datatype declaration (a container's group)")
    let rest ← groupCtorsK look nPc cs
    pure (ctors ++ rest)

/-- **A container's group in its recorded block order** (`IndCaps.all`, deduplicated;
the container itself first when it is not recorded there).  Its HEAD is the node's
canonical key: every mate's node is the head's. -/
def groupOfK (ctx : NestCtx) (C : Name) : List Name :=
  let g := (nestBlockOf ctx C).eraseDups
  if g.contains C then g else C :: g

/-- **A hook check** (NESTKN-K3, the model's `UseOkK`): a failure is an internal error —
the check guards an invariant of the key-named construction, never the input's
validity; a decline (`.notImplemented`, e.g. fuel) passes through. -/
def asInternalK (what : String) (x : m α) : m α :=
  tryCatchThe CheckError x fun err =>
    match err with
    | .invalid msg => throw (.internal s!"NESTKN-K3: {what} ({msg})")
    | e => throw e

/-- **U3**: each flexible family's type inferred into a sort at its family's depth
(family `j` at `d + j`). -/
def famTysSortK (ops : CheckerOps m) (env : Env) (d : Nat) : List Expr → m Unit
  | [] => pure ()
  | t :: ts => do
    let ty ← ops.inferType env d t
    let _ ← ops.ensureSort env d ty
    famTysSortK ops env (d + 1) ts

/-- **U5** (NESTKN-M3B): each flexible family's KEY typed at the members' depth (the
key is concrete: a bvar-closed key subterm of the node's key). -/
def keysTypedK (ops : CheckerOps m) (env : Env) (d : Nat) : List NestKey → m Unit
  | [] => pure ()
  | k :: ks => do
    let _ ← ops.inferType env d k.expr
    keysTypedK ops env d ks

/-- What `nestLayoutK` computes for a key. -/
structure LayoutOutK where
  L : LayoutK
  ctors : List (ConstantVal × Nat)
  crests : List Expr
  ginfo : List (Name × Nat × Expr)
  /-- the flexible families whose representative has KN5 aliases -/
  merged : List Nat
  /-- statistics: contained representatives -/
  nReps : Nat
  /-- each flexible family's key parameters with the INNER flexible families abstracted
  (the parameters its type is instantiated at), aligned with `L.fams` -/
  famPs : List (List Expr) := []
  deriving Inhabited

/-- **The layout of a key** (K-f: ONE deterministic function of the key and the
environment, for the positivity check and, later, the recursor check): the group and its
constructors, the contained keys (all depths, inner-first, KN5), the flexible ones
(individual, then JOINT — a joint failure is `.internal` unless nothing is flexible), the
group's formers at `DsF` and the crests typed.  `look` reads `nestContainer`. -/
def nestLayoutK (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (look : Name → Option (Nat × List (ConstantVal × Nat))) (kc0 : NestKey) :
    m LayoutOutK := do
  -- the canonical head: any mate's layout is the head's
  let gnames := groupOfK ctx kc0.cname
  let kc : NestKey := { kc0 with cname := gnames.headD kc0.cname }
  let q ← unwrapOr (look kc.cname) nestNonValid
  let ctors ← groupCtorsK look q.1 gnames
  unless ctors.all (fun c => Name.nodup c.1.levelParams) do
    throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
      has a duplicate universe level parameter (official: duplicate universe level \
      parameter)")
  let (reps, als) ← mergeK ops env ctx (containedK ctx kc.ds) [] []
  let fl ← flexK ops env ctx kc gnames ctors reps als (List.range reps.length) []
  let nF := fl.length
  let (dsF, ginfo, crests) ← tryCatchThe CheckError
    (layoutTypeK ops env ctx kc gnames ctors (flexSubstK ctx reps als fl) nF)
    fun err =>
      match err with
      | .invalid msg =>
        if nF == 0 then throw err
        else throw (.internal s!"NESTKN-K: the flexible keys are individually flexible \
          but not jointly ({msg})")
      | e => throw e
  let fams := fl.filterMap fun (r, _, nI) => (reps[r]?).map fun k => (k, nI)
  -- U3 (NESTKN-K3): every family's type is a type at its depth, once per layout
  asInternalK "a flexible family's type is not a type at its depth"
    (famTysSortK ops env (ctx.hiAt 0) (fl.map (·.2.1)))
  -- U5 (NESTKN-M3B): every family's key a term at the members' depth, once per layout
  asInternalK "a flexible family's key is ill-typed at the members' depth"
    (keysTypedK ops env (ctx.hiAt 0) (fams.map (·.1)))
  pure { L := { fams := fams, nF := nF, famTys := fl.map (·.2.1), grp := gnames,
                lvls := kc.lvls, dsF := dsF, hi := ctx.hiAt 0 + nF + ginfo.length },
         ctors := ctors, crests := crests, ginfo := ginfo,
         merged := (List.range nF).filter fun i =>
           match fl[i]? with
           | some (r, _, _) => als.any (·.2 == r)
           | none => false,
         nReps := reps.length,
         famPs := (List.range nF).map fun i =>
           match fl[i]? with
           | some (r, _, _) =>
             ((reps[r]?).map fun k => k.ds.map (absKeysK (flexSubstK ctx reps als (fl.take i))))
               |>.getD []
           | none => [] }

/-! ## State and nodes -/

/-- A walked node: its key, its table index, `DsF` (the flexible families the pattern
variables `hiAt0 + j`, `j < nF`), and the flexible families it MET. -/
structure NodeK where
  key : NestKey
  q : Nat
  dsF : List Expr
  nF : Nat
  met : List Nat
  merged : List Nat := []
  /-- the flexible families' keys and their parameters with the inner families abstracted
  (`LayoutOutK.famPs`), aligned -/
  famKeys : List NestKey := []
  famPs : List (List Expr) := []
  /-- the flexible families' types and index counts (`LayoutK.famTys`, `LayoutK.fams`'
  counts), aligned — the use's hook checks read them (NESTKN-K3) -/
  famTys : List Expr := []
  famNIs : List Nat := []
  deriving Inhabited

/-- The run's state: today's (`NestState`: table, lookups, classes, active keys, ctor
normal forms), the node cache, and the current node's met set. -/
structure NestStK where
  base : NestState := {}
  cache : Array NodeK := #[]
  met : List Nat := []
  deriving Inhabited

/-- The cached node of a key. -/
def NestStK.node? (st : NestStK) (k : NestKey) : Option NodeK :=
  st.cache.find? (·.key == k)

/-- Record a node's group: table entries, classes, cache entries. -/
def recordK (ctx : NestCtx) (kc : NestKey) (lo : LayoutOutK) (met : List Nat) :
    List (Name × Nat × Expr) → NestStK → NestStK
  | [], st => st
  | (g, nI, _) :: gs, st =>
    let k : NestKey := ⟨g, kc.lvls, kc.ds⟩
    let (q, keys) := match st.base.keys.findIdx? (·.key == k) with
      | some q => (q, st.base.keys)
      | none => (st.base.keys.size, st.base.keys.push ⟨k, nI⟩)
    let base : NestState :=
      { st.base with keys := keys, nodes := st.base.nodes.push (ctx.concreteKey [] g k) }
    let nd : NodeK := ⟨k, q, lo.L.dsF, lo.L.nF, met, lo.merged, lo.L.fams.map (·.1), lo.famPs,
      lo.L.famTys, lo.L.fams.map (·.2)⟩
    let st : NestStK := { st with base := base, cache := st.cache.push nd }
    recordK ctx kc lo met gs st

/-! ## Matching a user's parameters against `DsF` -/

/-- **The match** (§5 USE): the pattern `p` (a piece of the node's `DsF`, the pattern
variables `lo ..< lo + nF`) against the user's target `t` (at the user's layout `L`).
At a pattern variable applied to `k` indices, the target minus its last `k` arguments is
bound (and the indices matched).  Where the pattern is free of pattern variables the
target must not mention a family of the user (§2′.1's rigid-at-stage invariant). -/
def matchGoK (ctx : NestCtx) (L : LayoutK) (lo nF : Nat) :
    Nat → Expr → Expr → Except String (List (Nat × Expr))
  | 0, _, _ => .error "match: fuel"
  | fuel + 1, p, t =>
    if !p.nestOcc [] lo (lo + nF) then
      if t.nestOcc [] (ctx.hiAt 0) L.hi then
        .error "a RIGID key of the node is at stage in its user (a family of the user where \
          the node's layout keeps the key concrete)"
      else .ok []
    else
      let pvar : Option Nat := match p.getAppFn with
        | .fvar i _ => if lo ≤ i && i < lo + nF then some (i - lo) else none
        | _ => none
      match pvar with
      | some j =>
        let pa := p.getAppArgs
        let ta := t.getAppArgs
        if ta.length < pa.length then .error "match: a family bound to a shorter spine" else
        let b := Expr.mkAppN t.getAppFn (ta.take (ta.length - pa.length))
        match (pa.zip (ta.drop (ta.length - pa.length))).mapM
            (fun (x, y) => matchGoK ctx L lo nF fuel x y) with
        | .ok rs => .ok ((j, b) :: rs.flatten)
        | .error e => .error e
      | none =>
        match p, t with
        | .app f a, .app f' a' => do
          let x ← matchGoK ctx L lo nF fuel f f'
          let y ← matchGoK ctx L lo nF fuel a a'
          pure (x ++ y)
        | .lam ty b _, .lam ty' b' _ | .forallE ty b _, .forallE ty' b' _ => do
          let x ← matchGoK ctx L lo nF fuel ty ty'
          let y ← matchGoK ctx L lo nF fuel b b'
          pure (x ++ y)
        | .letE ty v b, .letE ty' v' b' => do
          let x ← matchGoK ctx L lo nF fuel ty ty'
          let y ← matchGoK ctx L lo nF fuel v v'
          let z ← matchGoK ctx L lo nF fuel b b'
          pure (x ++ y ++ z)
        | .proj _ _ x, .proj _ _ x' => matchGoK ctx L lo nF fuel x x'
        | _, _ => .error "match: the user's parameters differ in shape from the node's layout"

/-- K-d: each parameter CHECKED against the pattern instantiated at the bindings `θ`:
syntactically, else — only where the pattern holds a KN5-merged family — `isDefEq` at the
user's depth, both sides inferred.  A failure is `.internal`. -/
def checkParamsK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK)
    (θ : Nat → Option Expr) : List (Expr × Expr) → m Unit
  | [] => pure ()
  | (p, t) :: rest => do
    let inst := p.replaceFVars θ
    unless inst == t do
      unless nd.merged.any (fun j => p.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1)) do
        throw (.internal "NESTKN-K: match: a parameter differs syntactically from the node's \
          layout at its bindings, at a position without a merged family")
      typeAtK ops env L.hi inst false
      typeAtK ops env L.hi t false
      unless ← ops.isDefEq env L.hi inst t do
        throw (.internal "NESTKN-K: match: a merged position is not defeq at its bindings")
    checkParamsK ops env ctx L nd θ rest

/-- **Every flexible family bound** (round 4 (b)): an inner family that occurs only inside
an outer family's key (hence only in its type) is bound from the outer binding — the
outer key's parameters with the inner families abstracted (`famPs`) matched against the
binding's parameters (a key application or an own hole at its parameters); when the
outer binding is itself a flexible family of the user, the inner key's family in the
user if it has one, else the concrete key.  Outer first (descending), so an inner one is
bound before it is itself used. -/
def bindInnerK (ctx : NestCtx) (L : LayoutK) (nd : NodeK) :
    List Nat → List (Nat × Expr) → Except String (List (Nat × Expr))
  | [], bs => .ok bs
  | j :: js, bs =>
    let ps := nd.famPs.getD j []
    let bound (i : Nat) : Bool := bs.any (·.1 == i)
    let add (new : List (Nat × Expr)) : List (Nat × Expr) :=
      bs ++ new.filter fun (i, _) => !bound i
    let lo := ctx.hiAt 0
    match bs.find? (·.1 == j) with
    | none => bindInnerK ctx L nd js bs
    | some (_, b) =>
      if !ps.any (·.nestOcc [] lo (lo + nd.nF)) then bindInnerK ctx L nd js bs else
      let viaArgs : Except String (List (Nat × Expr)) := do
        let args := b.getAppArgs
        if args.length != ps.length then
          .error "bind: an outer family's binding has another parameter count"
        let rs ← (ps.zip args).mapM fun (p, t) =>
          matchGoK ctx L lo nd.nF (whnfWalkFuel p + whnfWalkFuel t) p t
        pure rs.flatten
      let r : Except String (List (Nat × Expr)) :=
        match b.getAppFn with
        | .const .. => viaArgs
        | .fvar i _ =>
          if lo + L.nF ≤ i && i < L.hi then viaArgs
          else if lo ≤ i && i < lo + L.nF && b.getAppArgs.isEmpty then
            -- the user's family: each inner key by the user's family for it, else concrete
            .ok ((List.range nd.nF).filterMap fun i' =>
              if ps.any (·.nestOcc [] (lo + i') (lo + i' + 1)) then
                (nd.famKeys[i']?).map fun k =>
                  match L.fams.findIdx? (·.1 == k) with
                  | some x => (i', Expr.fvar (lo + x) (L.famTys.getD x (.sort .zero)))
                  | none => (i', k.expr)
              else none)
          else .error "bind: an outer family bound to a non-family variable"
        | _ => .error "bind: an outer family bound to a non-key"
      match r with
      | .ok new => bindInnerK ctx L nd js (add new)
      | .error e => .error e

/-- **U7, a met family's arity** (`BindArityK`): its binding is read at the family's
index count `nI` — a family of the user of that count; the user's own hole at exactly
`DsF`, its remaining arity `nI`; a key whose former at the user counts `nI` indices and
which has a parameter (U8). -/
def bindArityK (ctx : NestCtx) (L : LayoutK) (b : Expr) (nI : Nat) : m Unit := do
  let lo := ctx.hiAt 0
  match b.getAppFn with
  | .fvar i _ =>
    if b.getAppArgs.isEmpty && lo ≤ i && i < lo + L.nF then
      match L.fams[i - lo]? with
      | some (_, n) =>
        unless n == nI do
          throw (.internal "NESTKN-K3: a met family bound to a family of another arity")
      | none => throw (.internal "NESTKN-K3: a met family bound to a family without an entry")
    else if lo + L.nF ≤ i && i < L.hi then
      unless b.getAppArgs == L.dsF do
        throw (.internal "NESTKN-K3: a met family bound to an own hole not at DsF")
      match L.grp[i - lo - L.nF]? with
      | some g =>
        unless nI + L.dsF.length == nestArity ctx g do
          throw (.internal "NESTKN-K3: a met family bound to an own hole of another arity")
      | none => throw (.internal "NESTKN-K3: a met family bound to an own hole without a member")
  | .const n us =>
    -- U8 (NESTKN-M4): a key occurrence has a parameter (never fires on a valid run)
    if b.getAppArgs.isEmpty then
      throw (.internal "NESTKN-K3: a met family bound to a key occurrence without parameters")
    let r ← asInternalK "a met family's key binding" (nestInstType ctx L.hi ⟨n, us, b.getAppArgs⟩)
    unless r.1 == nI do
      throw (.internal "NESTKN-K3: a met family bound to a key of another arity")
  | _ => pure ()

/-- **U7, every family's binding** (met or not): bound, bvar-closed, and HAS its family's
type at the bindings (`famTys[j]` at `θ`, both inferred at the user, defeq); a MET
family's binding at the family's arity (`bindArityK`). -/
def bindsOkK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK)
    (θ : Nat → Option Expr) : List Nat → m Unit
  | [] => pure ()
  | j :: js => do
    let b ← unwrapOr (θ (ctx.hiAt 0 + j)) (.internal "NESTKN-K3: a family unbound at a use")
    unless b.looseBVarsBounded 0 do
      throw (.internal "NESTKN-K3: a family's binding has a loose bound variable")
    let fty := (nd.famTys.getD j default).replaceFVars θ
    asInternalK "a family's binding against its type" do
      let T ← ops.inferType env L.hi b
      let _ ← ops.inferType env L.hi fty
      unless ← ops.isDefEq env L.hi T fty do
        throw (.internal "NESTKN-K3: a family's binding does not have its family's type")
    if nd.met.contains j then
      bindArityK ctx L b (nd.famNIs.getD j 0)
    bindsOkK ops env ctx L nd θ js

/-- The match over the parameter lists, then checked (K-d); returns the bindings. -/
def matchK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK)
    (ps : List Expr) : m (List (Nat × Expr)) := do
  if nd.dsF.length != ps.length then
    throw (.internal "NESTKN-K: match: parameter count")
  let bs ← match (nd.dsF.zip ps).mapM (fun (p, t) =>
        matchGoK ctx L (ctx.hiAt 0) nd.nF (whnfWalkFuel p + whnfWalkFuel t) p t) with
    | .ok rs => pure rs.flatten
    | .error e => throw (.internal s!"NESTKN-K: {e}")
  let bs ← match bindInnerK ctx L nd (List.range nd.nF).reverse bs with
    | .ok bs => pure bs
    | .error e => throw (.internal s!"NESTKN-K: {e}")
  unless (List.range nd.nF).all (fun j => bs.any (·.1 == j)) do
    throw (.internal "NESTKN-K: a flexible family left unbound at a use")
  let θ : Nat → Option Expr := fun x =>
    if ctx.hiAt 0 ≤ x && x < ctx.hiAt 0 + nd.nF then
      (bs.find? (·.1 == x - ctx.hiAt 0)).map (·.2)
    else none
  checkParamsK ops env ctx L nd θ (nd.dsF.zip ps)
  bindsOkK ops env ctx L nd θ (List.range nd.nF)
  pure bs

/-- **Met-propagation**: every MET flexible family of the node, at its binding in the
user `L`: a flexible family of `L` is met in `L`; `L`'s own group is in progress there;
a concrete key is USED in turn (the pending walk, `L` still active). -/
def metK (ctx : NestCtx) (L : LayoutK)
    (use : LayoutK → NestKey → List Expr → NestStK → m (Nat × NestStK)) (met : List Nat) :
    List (Nat × Expr) → NestStK → m NestStK
  | [], st => pure st
  | (j, b) :: bs, st => do
    if !met.contains j then metK ctx L use met bs st else
    let st ← match b with
      | .fvar i _ =>
        if ctx.hiAt 0 ≤ i && i < ctx.hiAt 0 + L.nF then
          let j' := i - ctx.hiAt 0
          pure (if st.met.contains j' then st else { st with met := st.met ++ [j'] })
        else if ctx.hiAt 0 + L.nF ≤ i && i < L.hi then pure st
        else throw (.internal "NESTKN-K: a met family bound to a non-family variable")
      | _ =>
        match b.getAppFn with
        | .fvar i _ =>
          -- VARIANT E: the user's own hole at its parameters: in progress there
          if ctx.hiAt 0 + L.nF ≤ i && i < L.hi then pure st
          else throw (.internal "NESTKN-K: a met family bound to a non-family application")
        | .const n us =>
          let ps := b.getAppArgs
          let kc : NestKey := ⟨n, us, ps.map (rbK ctx L)⟩
          if st.base.active.contains kc then
            throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
              declared (an instantiation in progress, reached through reduction)")
          else do
            let (_, st) ← use L kc ps st
            pure st
        | _ => throw (.internal "NESTKN-K: a met family bound to a non-key")
    metK ctx L use met bs st

/-! ## The container case, the syntactic pass, the constructors -/

/-- **The container case** after whnf: today's checks, the canonical key read back;
in progress → "reached through reduction"; else USE. -/
def contK (ctx : NestCtx)
    (use : LayoutK → NestKey → List Expr → NestStK → m (Nat × NestStK))
    (L : LayoutK) (kb : Nat) (n : Name) (us : List Level) (args : List Expr) (st : NestStK) :
    m (NestFieldKind × NestStK) := do
  let (q?, base) := nestContainerC ctx st.base n
  let st := { st with base := base }
  let q ← unwrapOr q? nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !x.nestOcc ctx.names ctx.nP L.hi) then
    throw nestNonValid
  if n == quotName then throw nestNonValid
  let ps := args.take q.1
  unless ps.all (fun x => x.bvarB == 0 && x.fvarB ≤ L.hi) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  let ni ← nestInstType ctx L.hi ⟨n, us, ps⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  let kc : NestKey := ⟨n, us, ps.map (rbK ctx L)⟩
  if st.base.active.contains kc then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  let (qi, st) ← use L kc ps st
  pure (.nested qi (kb != 0), st)

/-- **The syntactic pass**' occurrences (official's `replace_all_nested`), each USED
unless it is the field's own post-whnf key or in progress. -/
def synKeysK (ctx : NestCtx) (L : LayoutK)
    (use : LayoutK → NestKey → List Expr → NestStK → m (Nat × NestStK))
    (skip : Option NestKey) : List NestKey → NestStK → m NestStK
  | [], st => pure st
  | key :: ks, st => do
    unless key.ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ L.hi) do
      throw (.invalid "nested positivity: nested inductive datatypes parameters \
        cannot contain local variables")
    if ctx.names.contains key.cname || key.cname == quotName then
      throw (.internal "nested positivity: a syntactic occurrence headed by a member")
    let kc : NestKey := ⟨key.cname, key.lvls, key.ds.map (rbK ctx L)⟩
    let st ← if skip == some kc || st.base.active.contains kc then pure st else do
      let (q?, base) := nestContainerC ctx st.base key.cname
      let st := { st with base := base }
      match q? with
      | none => throw nestNonValid
      | some q =>
        if key.ds.length != q.1 then
          throw (.internal "nested positivity: a container's recorded parameter count \
            disagrees with its constructors'")
        let (_, st) ← use L kc key.ds st
        pure st
    synKeysK ctx L use skip ks st

/-- A constructor's field telescope (`nF` fields from field `j`), each field through
`rec` at `L.hi + j` and then `syn`. -/
def fieldsK
    (rec : LayoutK → Nat → Nat → Expr → NestStK → m (NestFieldKind × Expr × NestStK))
    (syn : LayoutK → Option NestKey → Expr → NestStK → m NestStK)
    (L : LayoutK) (err : CheckError) :
    Nat → Nat → Expr → NestStK →
      m (List NestFieldKind × List (Expr × BinderMeta) × Expr × NestStK)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, j, cur, st =>
    match cur with
    | .forallE a b bm => do
      let (k, nd, st) ← rec L (L.hi + j) 0 a st
      let skip : Option NestKey := match k with
        | .nested q _ => st.base.keys[q]?.map (·.key)
        | _ => none
      let st ← syn L skip a st
      let (ks, nds, res, st) ← fieldsK rec syn L err nF (j + 1)
        (b.instantiate1 (.fvar (L.hi + j) a)) st
      pure (k :: ks, (nd, bm) :: nds, res, st)
    | _ => throw err

/-- **A node's constructors** (its crests), each walked at the layout: U4 on the walked
telescope, the result headed by an own hole with hole-free indices (the records are
`frameNfsK`'s). -/
def ctorsK (ctx : NestCtx)
    (rec : LayoutK → Nat → Nat → Expr → NestStK → m (NestFieldKind × Expr × NestStK))
    (syn : LayoutK → Option NestKey → Expr → NestStK → m NestStK)
    (L : LayoutK) :
    List ((ConstantVal × Nat) × Expr) → NestStK → m NestStK
  | [], st => pure st
  | ((_, nF), crest) :: cs, st => do
    let (ks, nds, cur, st) ← fieldsK rec syn L
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds L.hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result of an instantiated container constructor \
        depends on a recursive or nested field)")
    unless nestResHead cur && (cur.getAppArgs.drop L.dsF.length).all
        (fun x => !x.nestOcc ctx.names ctx.nP L.hi) do
      throw (.invalid "nested positivity: invalid return type of an instantiated \
        container constructor (an index mentions the block)")
    ctorsK ctx rec syn L cs st

/-- **A node's constructor records** (legacy K.53′, the recursor stage's `NestNodes`):
today's record at the concrete key (`nestFrameCtorNf`, the frame at the EMPTY stack),
NOT read back from the layout — a KN5-merged family would read every spelling of its
key as the representative's, where official keeps one auxiliary type per spelling. -/
def frameNfsK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (us : List Level)
    (ds : List Expr) (grp : List (Name × Expr)) :
    List (ConstantVal × Nat) → m (List NestCtorNf)
  | [] => pure []
  | (cv, nF) :: cs => do
    let r ← nestFrameCtorNf ops env ctx us ds grp cv nF
    let rest ← frameNfsK ops env ctx us ds grp cs
    pure (r.entry :: rest)

/-! ## The mutual block -/

mutual

/-- **The positivity check** at a layout `L` (`nestPos`' cases, the frame holes replaced
by the layout's families). -/
def posK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → LayoutK → Nat → Nat → Expr → NestStK → m (NestFieldKind × Expr × NestStK)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, L, dep, kb, e, st => do
    let hi := L.hi
    let w ← ops.whnf env dep e
    if !w.nestOcc ctx.names ctx.nP hi then
      return (.ordinary, (if e.nestOcc ctx.names ctx.nP hi then w else e), st)
    match w with
    | .forallE a b bm =>
      if a.nestOcc ctx.names ctx.nP hi then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ← posK ops env ctx fuel L (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) st
      pure (k, .forallE a (nb.abstract1 dep) bm, st)
    | _ =>
      let args := w.getAppArgs
      match w.getAppFn with
      | .fvar i _ =>
        if ctx.nP ≤ i && i < ctx.hiAt 0 then
          let t := i - ctx.nP
          if args.length == ctx.nP + ctx.nIdxs.getD t 0 &&
              args.take ctx.nP == ctx.params &&
              args.all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
            return (if kb == 0 then .recursive t else .reflexive t, w, st)
          else throw nestNonValid
        else if ctx.hiAt 0 ≤ i && i < hi then
          -- a FAMILY of the layout, applied to exactly its indices, hole-free
          let j := i - ctx.hiAt 0
          if j < L.nF then
            -- a FLEXIBLE family, applied to exactly its indices, hole-free
            match L.fams[j]? with
            | none => throw (.internal "NESTKN-K: family without a layout entry")
            | some (_, nI) =>
              if args.length == nI && args.all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
                let st := if !st.met.contains j then { st with met := st.met ++ [j] } else st
                return (.inProgress, w, st)
              else throw nestNonValid
          else
            -- VARIANT E: an OWN hole (today's frame hole) at `DsF`, hole-free indices, at
            -- its full arity
            match L.grp[j - L.nF]? with
            | none => throw (.internal "NESTKN-K: own hole without a group member")
            | some g =>
              if L.dsF.length ≤ args.length && args.take L.dsF.length == L.dsF then
                if (args.drop L.dsF.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) &&
                    args.length == nestArity ctx g then
                  return (.inProgress, w, st)
                else throw nestNonValid
              else
                throw (.invalid "nested positivity: non valid occurrence of the datatypes \
                  being declared (a container's own occurrence at other parameters)")
        else throw nestNonValid
      | .const n us =>
        if ctx.names.contains n then throw nestNonValid
        let (k, st) ← contK ctx (useK ops env ctx fuel) L kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- **The syntactic pass** of a field's domain at the layout `L`. -/
def synK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → LayoutK → Option NestKey → Expr → NestStK → m NestStK
  | 0, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, L, skip, e, st =>
    synKeysK ctx L (useK ops env ctx fuel) skip (nestSynOccs ctx L.hi e) st

/-- **USE** of the canonical key `kc`, spelled `ps` at the user's layout `L`: K.52, the
node walked once, the match, the met families propagated.  Returns the table index. -/
def useK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → LayoutK → NestKey → List Expr → NestStK → m (Nat × NestStK)
  | 0, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, L, kc, ps, st => do
    -- U0/U1 (NESTKN-K3): the used container is no member and not `Quot`, and takes the
    -- spelling's parameter count — at EVERY use, the pending ones from `metK` included
    if ctx.names.contains kc.cname || kc.cname == quotName then
      throw (.internal "NESTKN-K3: a use of a member or of Quot")
    let (q?, base) := nestContainerC ctx st.base kc.cname
    let st := { st with base := base }
    match q? with
    | some q =>
      unless q.1 == ps.length do
        throw (.internal "NESTKN-K3: a use at another parameter count than its container's")
    | none => throw (.internal "NESTKN-K3: a use of a non-container")
    -- K-c: the used key's former checks at the site (levels, N2, N3)
    let _ ← nestInstType ctx L.hi ⟨kc.cname, kc.lvls, ps⟩
    -- K.52: the key typed at the user's layout
    let _ ← ops.inferType env L.hi (Expr.mkAppN (.const kc.cname kc.lvls) ps)
    let st ← match st.node? kc with
      | some _ => pure st
      | none =>
        if st.base.active.contains kc then
          throw (.internal "NESTKN-K: USE of an in-progress key that is not cached")
        else nodeK ops env ctx fuel kc st
    let nd ← unwrapOr (st.node? kc) (.internal "NESTKN-K: a node not cached after its walk")
    let bs ← matchK ops env ctx L nd ps
    let st ← metK ctx L (useK ops env ctx fuel) nd.met bs st
    pure (nd.q, st)

/-- **A node** (the canonical key `kc`): the group, the contained keys (KN5), the
flexible ones, the joint layout, every group crest walked with the group active, then
the node recorded (table, classes, cache with its met set). -/
def nodeK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → NestKey → NestStK → m NestStK
  | 0, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, kc, st => do
    -- warm the container lookups (a reading of the environment, `nestContainer`'s)
    let (q?, base) := nestContainerC ctx st.base kc.cname
    let st := { st with base := base }
    let q ← unwrapOr q? nestNonValid
    let (_, base) ← nestGroupCtors ctx q.1 (groupOfK ctx kc.cname) st.base
    let st := { st with base := base }
    let look (c : Name) : Option (Nat × List (ConstantVal × Nat)) :=
      match st.base.ctorsOf.lookup c with
      | some r => r
      | none => nestContainer ctx c
    let lo ← nestLayoutK ops env ctx look kc
    let L := lo.L
    let act := st.base.active
    let met0 := st.met
    let st := { st with
      base := { st.base with active := L.grp.map (fun g => ⟨g, kc.lvls, kc.ds⟩) ++ act },
      met := [] }
    let st ← ctorsK ctx (posK ops env ctx fuel) (synK ops env ctx fuel) L
      (lo.ctors.zip lo.crests) st
    let met := st.met
    let st := { st with base := { st.base with active := act }, met := met0 }
    let grp ← nestClassGroup ctx (L.grp.headD kc.cname) kc.lvls kc.ds
    let nfs ← frameNfsK ops env ctx kc.lvls kc.ds grp lo.ctors
    let st := { st with base := { st.base with ctorNfs := st.base.ctorNfs ++ nfs.toArray } }
    pure (recordK ctx kc lo met lo.ginfo st)

end

/-! ## The root -/

/-- One member constructor at the root layout (`nestMemberCtor`'s checks). -/
def nestMemberCtorK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (nF : Nat) (crest : Expr)
    (st : NestStK) : m (List NestFieldKind × Expr × NestStK) := do
  let base := ctx.hiAt 0
  let L := rootLayoutK ctx
  let (ks, nds, cur, st) ← fieldsK (posK ops env ctx (whnfWalkFuel crest))
    (synK ops env ctx (whnfWalkFuel crest)) L
    (.invalid "nested positivity: a constructor type does not bind its fields (official: \
      ill-formed constructor)") nF 0 crest st
  let tyN := closeTelescope nds base cur
  if (List.range nF).any (fun i =>
      (match ks.getD i .ordinary with
        | .recursive _ | .reflexive _ | .nested _ _ => true
        | _ => false) && structUsedLater tyN 0 i) then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (a later field or the result depends on a recursive or nested field)")
  unless nestResHead cur && (cur.getAppArgs.drop ctx.nP).all
      (fun a => !a.nestOcc ctx.names ctx.nP base) do
    throw (.invalid "nested positivity: invalid return type — a constructor's result \
      index mentions the block")
  unless tyN.holesApplied ctx.names ctx.nP base do
    throw (.invalid "nested positivity: invalid occurrence of a datatype being declared: it \
      must be applied to the parameters and universe levels of the mutual declaration (a \
      member not applied to the parameters, in a container's parameter)")
  pure (ks, tyN, st)

/-- One member's constructors (`nestMemberCtors`). -/
def nestMemberCtorsK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (ConstantVal × Nat) → NestStK → m (List (List NestFieldKind) × List Expr × NestStK)
  | [], st => pure ([], [], st)
  | c :: cs, st => do
    let crest ← unwrapOr (instPisWith ctx.params (nestAbstract ctx holes c.1.type))
      (.invalid "nested positivity: a constructor type does not bind the parameters \
        (official: ill-formed constructor)")
    let (ks, tyN, st) ← nestMemberCtorK ops env ctx c.2 crest st
    nestNoMemberConst ctx (nestAbstract ctx holes c.1.type)
    let (kss, nss, st) ← nestMemberCtorsK ops env ctx holes cs st
    pure (ks :: kss, tyN :: nss, st)

/-- Every member's constructors, sharing the cache. -/
def nestBlockCtorsGoK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestStK →
      m (List (List (List NestFieldKind)) × List (List Expr) × NestStK)
  | [], st => pure ([], [], st)
  | cs :: css, st => do
    let (kss, nss, st) ← nestMemberCtorsK ops env ctx holes cs st
    let (ksss, nsss, st) ← nestBlockCtorsGoK ops env ctx holes css st
    pure (kss :: ksss, nss :: nsss, st)

/-- **`nestBlockCtors`' shape**: the kinds, the normal forms and today's state record
(keys, classes, constructor normal forms). -/
def nestBlockCtorsK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorss : List (List (ConstantVal × Nat))) :
    m (List (List (List NestFieldKind)) × List (List Expr) × NestState) := do
  let (kinds, nfs, st) ← nestBlockCtorsGoK ops env ctx holes ctorss {}
  pure (kinds, nfs, st.base)

/-- **Positivity through containers, key-named, for a whole block** (the result shape of
`nestedBlockPositivity`). -/
def nestedBlockPositivityK (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let holes ← unwrapOr (nestHoles ctx)
    (.internal "nested positivity: a member is not a stored former")
  let (kinds, nfs, st) ← nestBlockCtorsK ops env ctx holes ctorss
  pure ⟨st.keys, kinds, (ctorss.zip nfs).map fun (cs, ns) =>
    (cs.zip ns).map fun (c, n) => (nestConcreteCtor ctx c.1.type n).getD n, st.nodes,
    (nestMemberNfs ctx ctorss nfs).toArray ++ st.ctorNfs⟩

end NestedK

end ConLeche
