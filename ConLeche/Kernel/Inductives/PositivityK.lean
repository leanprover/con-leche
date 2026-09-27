module

public import ConLeche.Kernel.Inductives.Positivity

@[expose] public section

/-!
# Positivity through containers, KEY-NAMED (PRIMREC/NESTKN §2′, PROTOTYPE)

A kernel prototype of the NESTKN design of record (`_tmp/primrec/NESTKN/DESIGN.md`
§2′, §2′.1 and §5): a node of the positivity check is a function of its CANONICAL KEY
alone (`C.{us} Ds`, `Ds` over the block's parameters and member holes only).

* **Contained keys** (`containedK`): the outermost key occurrences in `Ds`, merged up to
  defeq (KN5: same container, `Level.isEquivList` levels, parameters pairwise `isDefEq`;
  the first in scan order is the representative).
* **Flexibility** (`layoutTypeK`): a contained key is FLEXIBLE when the node's key and its
  group's crests type-check with every occurrence of it abstracted to a family over its
  indices (typed at the concrete key); the flexible keys are then abstracted JOINTLY —
  a joint failure is an internal error (§2′.1), never a reject.
* **The layout**: flexible families at `hiAt0 + j`, then the own group's families (each
  typed at its concrete key); the group's crests are the constructors instantiated at
  `DsF` with the own occurrences `C_g us DsF is ↦ z_g is`.
* **USE** (`useK`): K.52 at the user's layout, the node walked once (cached by its key),
  the user's parameters matched against `DsF` (`matchK`), and the node's MET flexible
  families propagated to the user: a family of the user is met there, a concrete key is
  used in turn (the pending walk, while the user is still active).  A rigid key the user
  holds at stage is an internal error (§2′.1).

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
    if ctx.hiAt 0 ≤ i && i < L.hi then (L.fams[i - ctx.hiAt 0]?).map (·.1.expr) else none

/-- The readback, then the member holes to the members (the recursor's representation). -/
def rbFullK (ctx : NestCtx) (L : LayoutK) (e : Expr) : Expr :=
  (rbK ctx L e).replaceFVars (nestHoleConst ctx [])

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

/-- The contained-key scan: outermost key occurrences (block = the members) with
bvar-closed parameters, each once, in scan order. -/
def containedGoK (ctx : NestCtx) (e : Expr) (acc : NestSynAcc) : NestSynAcc :=
  if acc.seen.contains e then acc else
  let acc := { acc with seen := acc.seen.insert e }
  match e with
  | .app f a =>
    match keyOccK? ctx ctx.nP (ctx.hiAt 0) e with
    | some k =>
      if k.ds.all (·.bvarB == 0) then
        if acc.keys.contains k then acc else { acc with keys := acc.keys.push k }
      else containedGoK ctx a (containedGoK ctx f acc)
    | none => containedGoK ctx a (containedGoK ctx f acc)
  | .lam t b _ | .forallE t b _ => containedGoK ctx b (containedGoK ctx t acc)
  | .letE t v b => containedGoK ctx b (containedGoK ctx v (containedGoK ctx t acc))
  | .proj _ _ x => containedGoK ctx x acc
  | _ => acc

/-- A key's contained keys (scan order, syntactically deduplicated). -/
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

/-- A contained key's family type: its container's former at the concrete key (the
indices' telescope into the sort), with its index count. -/
def famTypeK (ctx : NestCtx) (k : NestKey) : Option (Expr × Nat) :=
  match ctx.find? k.cname with
  | some (.indInfo cv _) =>
    (instPisWith k.ds (cv.type.instantiateLevelParams cv.levelParams k.lvls)).map
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
    let t ← instPisWith dsF (cv.type.instantiateLevelParams cv.levelParams us)
    let t := t.replaceTop fun x => (grp.find? fun (g, _) => spineIsK ⟨g, us, dsF⟩ x).map (·.2)
    let rest ← crestsK us dsF grp cs
    pure (t :: rest)

/-- Type each crest at `hi` (into a sort). -/
def typeCrestsK (ops : CheckerOps m) (env : Env) (hi : Nat) : List Expr → m Unit
  | [] => pure ()
  | c :: cs => do
    typeAtK ops env hi c true
    typeCrestsK ops env hi cs

/-- **A layout, built and typed**: the families `S` (key or alias ↦ family variable, the
`nF` flexible ones below `hiAt0 + nF`), the group's families above them (`ginfo`: name,
index count, type at the concrete key); the key `C us DsF` typed at `hiAt0 + nF`, every
crest at `hi`.  Returns `DsF`, the group's variables and the crests. -/
def layoutTypeK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (kc : NestKey)
    (ginfo : List (Name × Nat × Expr)) (ctors : List (ConstantVal × Nat))
    (S : List (NestKey × Expr)) (nF : Nat) :
    m (List Expr × List (Name × Expr) × List Expr) := do
  let hiK := ctx.hiAt 0 + nF
  let dsF := kc.ds.map (absKeysK S)
  let grp := ginfo.mapIdx fun g (n, _, ty) => (n, Expr.fvar (hiK + g) ty)
  let crests ← unwrapOr (crestsK kc.lvls dsF grp ctors)
    (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
      does not bind the parameters (official: ill-formed constructor)")
  typeAtK ops env hiK (Expr.mkAppN (.const kc.cname kc.lvls) dsF) false
  typeCrestsK ops env (hiK + ginfo.length) crests
  pure (dsF, grp, crests)

/-- **Individual flexibility** of each representative (`reps`, index `r`): the layout
with it alone abstracted (its aliases with it) types.  Returns the flexible ones' indices
with their family types and index counts. -/
def flexK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (kc : NestKey)
    (ginfo : List (Name × Nat × Expr)) (ctors : List (ConstantVal × Nat))
    (reps : List NestKey) (als : List (NestKey × Nat)) :
    List Nat → m (List (Nat × Expr × Nat))
  | [] => pure []
  | r :: rs => do
    let rest ← flexK ops env ctx kc ginfo ctors reps als rs
    match reps[r]?, (reps[r]?).bind (famTypeK ctx) with
    | some k, some (ty, nI) =>
      let z := Expr.fvar (ctx.hiAt 0) ty
      let S := (k, z) :: (als.filter (·.2 == r)).map (fun a => (a.1, z))
      let ok ← tryCatchThe CheckError
        (do let _ ← layoutTypeK ops env ctx kc ginfo ctors S 1; pure true)
        fun err =>
          match err with
          | .invalid _ => pure false
          | e => throw e
      pure (if ok then (r, ty, nI) :: rest else rest)
    | _, _ => pure rest

/-- The group's information at the concrete key: each member's index count (its former's
checks, `nestInstType`) and its family type. -/
def groupInfoK (ctx : NestCtx) (kc : NestKey) : List Name → m (List (Name × Nat × Expr))
  | [] => pure []
  | g :: gs => do
    let (nI, former) ← nestInstType ctx (ctx.hiAt 0) ⟨g, kc.lvls, kc.ds⟩
    let ty ← unwrapOr (instPisWith kc.ds former)
      (.invalid "nested positivity: invalid nested inductive datatype, its type does not \
        bind its parameters (official: ill-formed inductive type)")
    let rest ← groupInfoK ctx kc gs
    pure ((g, nI, ty) :: rest)

/-! ## State and nodes -/

/-- A walked node: its key, its table index, `DsF` (the flexible families the pattern
variables `hiAt0 + j`, `j < nF`), and the flexible families it MET. -/
structure NodeK where
  key : NestKey
  q : Nat
  dsF : List Expr
  nF : Nat
  met : List Nat
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
def recordK (ctx : NestCtx) (kc : NestKey) (dsF : List Expr) (nF : Nat) (met : List Nat) :
    List (Name × Nat × Expr) → NestStK → NestStK
  | [], st => st
  | (g, nI, _) :: gs, st =>
    let k : NestKey := ⟨g, kc.lvls, kc.ds⟩
    let (q, keys) := match st.base.keys.findIdx? (·.key == k) with
      | some q => (q, st.base.keys)
      | none => (st.base.keys.size, st.base.keys.push ⟨k, nI⟩)
    let base : NestState :=
      { st.base with keys := keys, nodes := st.base.nodes.push (ctx.concreteKey [] g k) }
    let st : NestStK := { st with base := base, cache := st.cache.push ⟨k, q, dsF, nF, met⟩ }
    recordK ctx kc dsF nF met gs st

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

/-- The match over the parameter lists. -/
def matchK (ctx : NestCtx) (L : LayoutK) (nd : NodeK) (ps : List Expr) :
    m (List (Nat × Expr)) :=
  if nd.dsF.length != ps.length then
    throw (.internal "NESTKN-K: match: parameter count")
  else
    match (nd.dsF.zip ps).mapM (fun (p, t) =>
        matchGoK ctx L (ctx.hiAt 0) nd.nF (whnfWalkFuel p + whnfWalkFuel t) p t) with
    | .ok rs => pure rs.flatten
    | .error e => throw (.internal s!"NESTKN-K: {e}")

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
        | .const n us =>
          let ps := b.getAppArgs
          let kc : NestKey := ⟨n, us, ps.map (rbK ctx L)⟩
          if st.base.active.contains kc then
            throw (.internal "NESTKN-K: a pending walk reached an in-progress key (a rigid \
              ancestor at stage)")
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
telescope, the result headed by a family with hole-free indices, the normal form recorded
read back (K.53′). -/
def ctorsK (ctx : NestCtx)
    (rec : LayoutK → Nat → Nat → Expr → NestStK → m (NestFieldKind × Expr × NestStK))
    (syn : LayoutK → Option NestKey → Expr → NestStK → m NestStK)
    (L : LayoutK) (kc : NestKey) :
    List ((ConstantVal × Nat) × Expr) → NestStK → m NestStK
  | [], st => pure st
  | ((cv, nF), crest) :: cs, st => do
    let (ks, nds, cur, st) ← fieldsK rec syn L
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds L.hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result of an instantiated container constructor \
        depends on a recursive or nested field)")
    unless nestResHead cur && cur.getAppArgs.all
        (fun x => !x.nestOcc ctx.names ctx.nP L.hi) do
      throw (.invalid "nested positivity: invalid return type of an instantiated \
        container constructor (an index mentions the block)")
    let nf : NestCtorNf := ⟨cv.name, kc.lvls, kc.ds.map (·.replaceFVars (nestHoleConst ctx [])),
      rbFullK ctx L (closeTelescope nds L.hi cur)⟩
    let st := { st with base := { st.base with ctorNfs := st.base.ctorNfs.push nf } }
    ctorsK ctx rec syn L kc cs st

/-- The flexible families' substitution (`S`) and the layout's families. -/
def flexSubstK (ctx : NestCtx) (reps : List NestKey) (als : List (NestKey × Nat))
    (flex : List (Nat × Expr × Nat)) : List (NestKey × Expr) × List (NestKey × Nat) :=
  let zs := flex.mapIdx fun i (r, ty, nI) => (r, Expr.fvar (ctx.hiAt 0 + i) ty, nI)
  let S := zs.flatMap fun (r, z, _) =>
    ((reps[r]?).toList.map fun k => (k, z)) ++ (als.filter (·.2 == r)).map fun a => (a.1, z)
  let fams := zs.filterMap fun (r, _, nI) => (reps[r]?).map fun k => (k, nI)
  (S, fams)

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
          match L.fams[j]? with
          | none => throw (.internal "NESTKN-K: family without a layout entry")
          | some (_, nI) =>
            if args.length == nI && args.all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
              let st := if j < L.nF && !st.met.contains j then
                { st with met := st.met ++ [j] } else st
              return (.inProgress, w, st)
            else throw nestNonValid
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
    -- K.52: the key typed at the user's layout
    let _ ← ops.inferType env L.hi (Expr.mkAppN (.const kc.cname kc.lvls) ps)
    let st ← match st.node? kc with
      | some _ => pure st
      | none =>
        if st.base.active.contains kc then
          throw (.internal "NESTKN-K: USE of an in-progress key that is not cached")
        else nodeK ops env ctx fuel kc st
    let nd ← unwrapOr (st.node? kc) (.internal "NESTKN-K: a node not cached after its walk")
    let bs ← matchK ctx L nd ps
    let st ← metK ctx L (useK ops env ctx fuel) nd.met bs st
    pure (nd.q, st)

/-- **A node** (the canonical key `kc`): the group, the contained keys (KN5), the
flexible ones, the joint layout, every group crest walked with the group active, then
the node recorded (table, classes, cache with its met set). -/
def nodeK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → NestKey → NestStK → m NestStK
  | 0, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, kc, st => do
    let (q?, base) := nestContainerC ctx st.base kc.cname
    let st := { st with base := base }
    let q ← unwrapOr q? nestNonValid
    let gnames := kc.cname :: nestFrameMates ctx kc.cname
    let ginfo ← groupInfoK ctx kc gnames
    let (ctors, base) ← nestGroupCtors ctx q.1 gnames st.base
    let st := { st with base := base }
    unless ctors.all (fun c => Name.nodup c.1.levelParams) do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    let (reps, als) ← mergeK ops env ctx (containedK ctx kc.ds) [] []
    let flex ← flexK ops env ctx kc ginfo ctors reps als (List.range reps.length)
    let (S, ffams) := flexSubstK ctx reps als flex
    let nF := flex.length
    let (dsF, _, crests) ← tryCatchThe CheckError
      (layoutTypeK ops env ctx kc ginfo ctors S nF)
      fun err =>
        match err with
        | .invalid msg =>
          if nF == 0 then throw err
          else throw (.internal s!"NESTKN-K: the flexible keys are individually flexible \
            but not jointly ({msg})")
        | e => throw e
    let L : LayoutK :=
      { fams := ffams ++ ginfo.map (fun (g, nI, _) => (⟨g, kc.lvls, kc.ds⟩, nI)),
        nF := nF, hi := ctx.hiAt 0 + nF + ginfo.length }
    let act := st.base.active
    let met0 := st.met
    let st := { st with
      base := { st.base with active := gnames.map (fun g => ⟨g, kc.lvls, kc.ds⟩) ++ act },
      met := [] }
    let st ← ctorsK ctx (posK ops env ctx fuel) (synK ops env ctx fuel) L kc
      (ctors.zip crests) st
    let met := st.met
    let st := { st with base := { st.base with active := act }, met := met0 }
    pure (recordK ctx kc dsF nF met ginfo st)

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
