module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Kernel.Inductives.PositivityK

@[expose] public section

/-!
# The recursor check's nested route, key-named (PRIMREC / NESTKN-R, PROTOTYPE)

A HOT class of a recursor family (`hotRK`: its strongly connected component of the call
graph has a call that is not flat, `targetFlatEdge`) lies on a cycle through a nested home's
members and the container instances its constructors reach.  This route checks every call
inside such a component WITHOUT the positivity check's data and without a table: it
generates PAIRS (class, node) itself, from the installing block's member classes along the
family's own calls, and matches each call against the called field's normal form at the node
(`_tmp/primrec/NESTKN/DESIGN.md` §0, §3; DESIGN.md "PRIMREC / NESTKN-R").

* **Homes** (`homeRK`): a block read at its OWN context (the positivity check's: parameters
  opened at the first former, members as holes) — the installing block, or an OLDER block
  (`IndCaps.all`).  An INSTANCE (`InstRK`) is a home at the levels and parameters of the
  class that seeds it.
* **Nodes** (`layIdxRK`): a layout of the home — the ROOT (the members' constructors, members
  abstracted) or a container key's `nestLayoutK`, the ONE layout function the key-named
  positivity check uses (determinism tie) — and one member of its group.  Every
  constructor's field normal forms are `nestTeleNf` at the layout.
* **The instance map** (`relocRK`): a node's terms live at the home's context, a call at its
  rule's (prefix, fields).  `θ`: the home's level parameters to the instance's levels, its
  parameters to the instance's parameters, and the node's holes (members, flexible
  families, own group) RELOCATED above the rule's fields (`base …`), each typed by its own
  type under `θ`.
* **A call at a pair** (`callRK`) — caller class `K`, field `f`, callee `K''`: the field's
  normal form's `Π`-leaf at the node (`leafRK`) is a member hole, a flexible family, an
  own-group hole or a container key; `K''` must match it PER COMPONENT (`matchRK`: same
  inductive, `Level.isEquivList` levels, each parameter `isDefEq` at the relocated hole
  context with both sides inferred, under one symmetric abstraction `absRK`).  The leaf
  names the callee's node: the root at a member hole, the family's key node at a family, a
  group-mate at an own hole, the key's canonical node at a container key.
  - A call INSIDE a hot component is STRICT: the match, the call's TYPING (the node's crest
    field, holes relocated, at the rule's field variables, defeq to the leaf's head at the
    callee's abstracted parameters and the call's indices, under the call's telescope — at
    every value of the holes), K.53 (reject-only, `Conformance/K53.lean`: the normal form
    read back at the instance), the callee's pair; every failure rejects.
  - A call INTO another component is SOFT: the match alone (an `.invalid` means no pair);
    a hot component need not hold a member class (`corner_nestkn_noseed`).
  - A flat component's own calls are the flat route's (`targetIntraCallOk`).
* **Seeds**: the installing block's member classes, then — for the hot classes they do not
  reach — an older home's root at the class's own instance (`olderSeedRK`).
* **Coverage**: every hot class is in a pair.  Nothing is read from the positivity run.

UNWIRED: `_tmp/primrec/NESTKN/wire-R.patch` runs `targetNestRouteK` after the rules.
-/

namespace ConLeche

section NestRouteK

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Homes, instances, layouts -/

/-- A home, at its own context: the positivity check's context of its block, the member
holes, and each member's constructors. -/
structure HomeRK where
  ctx : NestCtx
  holes : List Expr
  ctors : List (List (ConstantVal × Nat))

/-- An instance of a home: the levels and parameters (at the rule's parameter variables)
its nodes are read at. -/
structure InstRK where
  home : Nat
  us : List Level
  ds : List Expr
  deriving Inhabited

/-- A layout of a home: the root (`key = none`) or a container key's (`nestLayoutK`); its
group's members, their constructors and crests, the types of its holes (`[nP, L.hi)`, in
order: members, flexible families, own group) and every constructor's field normal forms
(fields at `L.hi + j`). -/
structure LayRK where
  home : Nat
  key : Option NestKey
  L : LayoutK
  mems : List Name
  ctors : List (List (ConstantVal × Nat))
  crests : List (List Expr)
  holeTys : List Expr
  nfs : List (List (List Expr))
  deriving Inhabited

/-- A pair: a class of the family, an instance, a layout and one member of its group. -/
structure PairRK where
  cls : Nat
  inst : Nat
  lay : Nat
  mem : Nat
  deriving DecidableEq, Inhabited

/-- One call of a class's rule, with the rule's frame (`targetRule`'s). -/
structure CallRK where
  ctor : Nat
  cn : Name
  fvsPref : List Expr
  fvsF : List Expr
  teles : List (List (Expr × BinderMeta))
  base : Nat
  ih : TargetIh
  deriving Inhabited

/-- The route's state. -/
structure RouteRK where
  homes : Array HomeRK := #[]
  homeNames : Array (List Name) := #[]
  insts : Array InstRK := #[]
  lays : Array LayRK := #[]
  pairs : Array PairRK := #[]
  next : Nat := 0

/-- **A home, read off the environment** at a class `M`: the installing block at a member
class (the recursor stage's own context, `homeTableRec`'s), else `M`'s recorded block
(`IndCaps.all`) at its first former's telescope. -/
def homeRK (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (M : TargetMajor) : m HomeRK := do
  match M.member with
  | some _ =>
    let cvTa0 ← unwrapOr cvTas.head? (.internal "nested route: no type former")
    let pq ← unwrapOr (openPisAtFvars p.nP cvTa0.type 0)
      (.internal "nested route: type former telescope")
    let ctx := p.nestCtx pq.1 fe.find? fe.env.consts
    let holes ← unwrapOr (nestHoles ctx) (.internal "nested route: a member is no former")
    pure ⟨ctx, holes, ctorsAs⟩
  | none =>
    let some (.indInfo _ caps) := fe.find? M.ind
      | throw (.invalid "target rec (nested route): a class's inductive is not stored")
    let names := if caps.all.eraseDups.contains M.ind then caps.all.eraseDups else [M.ind]
    let n0 ← unwrapOr names.head? (.internal "nested route: empty home")
    let some (.indInfo cv0 caps0) := fe.find? n0
      | throw (.invalid "target rec (nested route): a home's member is not stored")
    let nPH := caps0.nparams
    let pq ← unwrapOr (openPisAtFvars nPH cv0.type 0)
      (.invalid "target rec (nested route): a home's former does not bind its parameters")
    let sort ← unwrapOr (match cv0.type.piBinders.2 with
        | .sort s => some s
        | _ => none)
      (.invalid "target rec (nested route): a home's former is not a telescope into a sort")
    let nIdxs := names.map fun n => match fe.find? n with
      | some (.indInfo cv _) => cv.type.piBinders.1.length - nPH
      | _ => 0
    let ctx : NestCtx := ⟨names, cv0.levelParams, nPH, nIdxs, pq.1, sort, fe.find?,
      fe.env.consts⟩
    let holes ← unwrapOr (nestHoles ctx)
      (.invalid "target rec (nested route): a home's member is no former")
    let ctors ← names.mapM fun n => unwrapOr ((nestContainer ctx n).map (·.2))
      (.invalid "target rec (nested route): a home's member is no inductive")
    pure ⟨ctx, holes, ctors⟩

/-- Every constructor's field normal forms at a layout (`nestTeleNf`, fields at `hi`). -/
def layNfsRK (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (hi : Nat) :
    List (ConstantVal × Nat) → List Expr → m (List (List Expr))
  | (_, nF) :: cs, crest :: crests => do
    let (nds, _) ← nestTeleNf ops env ctx.names ctx.nP hi (whnfWalkFuel crest) hi nF 0 crest
    let rest ← layNfsRK ops env ctx hi cs crests
    pure (nds.map (·.1) :: rest)
  | _, _ => pure []

/-- Split a list by the lengths of `xs`. -/
def splitByRK {α β : Type} : List (List α) → List β → List (List β)
  | [], _ => []
  | x :: xs, ys => ys.take x.length :: splitByRK xs (ys.drop x.length)

/-- **The root layout** of a home: its members' constructors, the members abstracted. -/
def rootLayRK (ops : CheckerOps m) (env : Env) (h : Nat) (H : HomeRK) : m LayRK := do
  let ctx := H.ctx
  let L := rootLayoutK ctx
  let crests ← H.ctors.mapM fun cs => cs.mapM fun (cv, _) =>
    unwrapOr (instPisWith ctx.params (nestAbstract ctx H.holes cv.type))
      (.invalid "target rec (nested route): a constructor type does not bind the parameters")
  let nfs ← (H.ctors.zip crests).mapM fun (cs, crs) => layNfsRK ops env ctx L.hi cs crs
  pure { home := h, key := none, L := L, mems := ctx.names, ctors := H.ctors,
         crests := crests, holeTys := H.holes.map Expr.fvarTypeD, nfs := nfs }

/-- **A container key's layout** (`nestLayoutK`, the positivity check's). -/
def contLayRK (ops : CheckerOps m) (env : Env) (h : Nat) (H : HomeRK) (kc : NestKey) :
    m LayRK := do
  let ctx := H.ctx
  let look := nestContainer ctx
  let lo ← nestLayoutK ops env ctx look kc
  let ctorsG ← lo.L.grp.mapM fun g => unwrapOr ((look g).map (·.2)) nestNonValid
  let crests := splitByRK ctorsG lo.crests
  let nfs ← (ctorsG.zip crests).mapM fun (cs, crs) => layNfsRK ops env ctx lo.L.hi cs crs
  pure { home := h, key := some kc, L := lo.L, mems := lo.L.grp, ctors := ctorsG,
         crests := crests,
         holeTys := H.holes.map Expr.fvarTypeD ++ lo.famTys ++ lo.ginfo.map (·.2.2),
         nfs := nfs }

/-- The home of a class's block, found or read. -/
def homeIdxRK (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (M : TargetMajor) (st : RouteRK) :
    m (Nat × RouteRK) := do
  let H ← homeRK fe p cvTas ctorsAs M
  match st.homeNames.findIdx? (· == H.ctx.names) with
  | some h => pure (h, st)
  | none => pure (st.homes.size,
      { st with homes := st.homes.push H, homeNames := st.homeNames.push H.ctx.names })

/-- A layout of home `h`, found or built: the root at `none`, a container key's layout at
`some kc` (a layout of `kc`'s group at its levels and parameters is shared by its members). -/
def layIdxRK (ops : CheckerOps m) (env : Env) (h : Nat) (key : Option NestKey)
    (st : RouteRK) : m (Nat × RouteRK) := do
  let H ← unwrapOr st.homes[h]? (.internal "nested route: home")
  let hit := st.lays.findIdx? fun l => l.home == h &&
    match l.key, key with
    | none, none => true
    | some k', some kc => k'.lvls == kc.lvls && k'.ds == kc.ds && l.mems.contains kc.cname
    | _, _ => false
  match hit with
  | some i => pure (i, st)
  | none =>
    let lay ← match key with
      | none => rootLayRK ops env h H
      | some kc => contLayRK ops env h H kc
    pure (st.lays.size, { st with lays := st.lays.push lay })

/-! ## The instance map -/

/-- A term of the home's context at the instance's levels. -/
def lvlRK (H : HomeRK) (I : InstRK) (e : Expr) : Expr :=
  if I.us == H.ctx.lps.map .param then e else e.instantiateLevelParams H.ctx.lps I.us

/-- The relocated holes of a layout at `base`: hole `i` (the variable `nP + i` of the home's
context) becomes `.fvar (base + i)`, typed by its type under the map so far. -/
def relocHolesRK (H : HomeRK) (I : InstRK) (base : Nat) : List Expr → List Expr → List Expr
  | [], acc => acc
  | ty :: tys, acc =>
    let nP := H.ctx.nP
    let θ : Nat → Option Expr := fun i =>
      if i < nP then I.ds[i]? else if i < nP + acc.length then acc[i - nP]? else none
    relocHolesRK H I base tys (acc ++ [.fvar (base + acc.length) ((lvlRK H I ty).replaceFVars θ)])

/-- **The instance map** `θ` of a layout's terms (see the module docstring), the relocated
holes `hs`. -/
def relocRK (H : HomeRK) (I : InstRK) (hs : List Expr) (e : Expr) : Expr :=
  let nP := H.ctx.nP
  (lvlRK H I e).replaceFVars fun i =>
    if i < nP then I.ds[i]? else if i < nP + hs.length then hs[i - nP]? else none

/-- A level of the home's context at the instance. -/
def lvl1RK (H : HomeRK) (I : InstRK) (u : Level) : Level :=
  if I.us == H.ctx.lps.map .param then u else Level.subst H.ctx.lps I.us u

/-- The flexible families' keys under `θ`, to their relocated holes (the callee side's
abstraction of the keys a node holds as families). -/
def famSubstRK (H : HomeRK) (I : InstRK) (lay : LayRK) (hs : List Expr) :
    List (NestKey × Expr) :=
  lay.L.fams.mapIdx fun j (k, _) =>
    (⟨k.cname, k.lvls.map (lvl1RK H I), k.ds.map (relocRK H I hs)⟩,
      hs.getD (H.ctx.names.length + j) default)

/-- **The abstraction both sides of a match are compared under**: the home's members at the
instance's levels to their relocated holes, the node's flexible keys to their relocated
families, then the node's own group at its levels to its relocated own holes (the crest
abstracts them before instantiating, so a leaf's parameters carry them as holes). -/
def absRK (H : HomeRK) (I : InstRK) (lay : LayRK) (S : List (NestKey × Expr)) (hs : List Expr)
    (e : Expr) : Expr :=
  let nM := H.ctx.names.length
  let own := (hs.drop (nM + lay.L.nF))
  targetAbs lay.L.grp (lay.L.lvls.map (lvl1RK H I)) own
    (absKeysK S (targetAbs H.ctx.names I.us (hs.take nM) e))

/-- **The read-back at the instance** (K.53's): the node's holes to their constants (a
family to its key's), the home's parameters to the instance's, the fields `hi + j` to the
rule's `fvsF`. -/
def rbInstRK (H : HomeRK) (I : InstRK) (lay : LayRK) (fvsF : List Expr) (e : Expr) : Expr :=
  let ctx := H.ctx
  let nP := ctx.nP
  let k := ctx.names.length
  let L := lay.L
  let base : Nat → Option Expr := fun i =>
    if i < nP then I.ds[i]?
    else if i < nP + k then some (.const (ctx.names.getD (i - nP) .anonymous) I.us)
    else none
  (lvlRK H I e).replaceFVars fun i =>
    if i < nP + k then base i
    else if i < nP + k + L.nF then
      (L.fams[i - nP - k]?).map fun (kk, _) => (lvlRK H I kk.expr).replaceFVars base
    else if i < L.hi then
      (L.grp[i - nP - k - L.nF]?).map fun g => .const g (L.lvls.map (lvl1RK H I))
    else if L.hi ≤ i && i < L.hi + fvsF.length then fvsF[i - L.hi]?
    else none

/-! ## The leaf and the per-component match -/

/-- What a field's `Π`-leaf at a node is: a member hole, a flexible family, an own-group
hole (each by index), or a container key; with the inductive it names, its levels and its
parameters (all at the home's context). -/
inductive LeafRK where
  | mem (t : Nat)
  | fam (j : Nat)
  | own (g : Nat)
  | key (kc : NestKey)
  deriving Inhabited

/-- **The leaf of a field's normal form at a layout**: its kind, inductive, levels and
parameters; `none` when it is none of the four (the call cannot be a nested one). -/
def leafRK (H : HomeRK) (lay : LayRK) (nf : Expr) :
    Option (LeafRK × Name × List Level × List Expr) :=
  let ctx := H.ctx
  let L := lay.L
  let lf := nf.piLeaf
  let args := lf.getAppArgs
  let ok (ps : List Expr) : Bool := ps.all fun x => x.bvarB == 0 && x.fvarB ≤ L.hi
  match lf.getAppFn with
  | .fvar i _ =>
    if ctx.nP ≤ i && i < ctx.hiAt 0 then
      let t := i - ctx.nP
      let ps := args.take ctx.nP
      if ps.length == ctx.nP && ok ps then
        some (.mem t, ctx.names.getD t .anonymous, ctx.lps.map .param, ps)
      else none
    else if ctx.hiAt 0 ≤ i && i < ctx.hiAt 0 + L.nF then
      let j := i - ctx.hiAt 0
      (L.fams[j]?).map fun (kj, _) => (.fam j, kj.cname, kj.lvls, kj.ds)
    else if ctx.hiAt 0 + L.nF ≤ i && i < L.hi then
      let g := i - ctx.hiAt 0 - L.nF
      let ps := args.take L.dsF.length
      if ps.length == L.dsF.length && ok ps then
        (L.grp[g]?).map fun n => (.own g, n, L.lvls, ps)
      else none
    else none
  | .const _ _ =>
    match keyOccK? ctx ctx.nP L.hi lf with
    | some k =>
      if ok k.ds then some (.key ⟨k.cname, k.lvls, k.ds.map (rbK ctx L)⟩, k.cname, k.lvls, k.ds)
      else none
    | none => none
  | _ => none

/-- Parameters pairwise defeq at `d`, each side inferred first (the per-component match). -/
def paramsDefEqRK (ops : CheckerOps m) (env : Env) (d : Nat) (cn : Name) :
    List Expr → List Expr → m Unit
  | a :: as, b :: bs => do
    let _ ← ops.inferType env d a
    let _ ← ops.inferType env d b
    unless ← ops.isDefEq env d a b do
      throw (.invalid s!"target rec (nested route): the rule of {cn} calls a recursor whose \
        major's parameters are not the called field's at its node")
    paramsDefEqRK ops env d cn as bs
  | [], [] => pure ()
  | _, _ => throw (.invalid s!"target rec (nested route): the rule of {cn} calls a recursor \
      whose major's parameter count is not the called field's")

/-- The constructors of a class and of a node's member agree (names and field counts). -/
def ctorsAgreeRK : List (ConstantVal × Nat) → List (ConstantVal × Nat) → Bool
  | a :: as, b :: bs => a.1.name == b.1.name && a.2 == b.2 && ctorsAgreeRK as bs
  | [], [] => true
  | _, _ => false

/-- Add a pair (once), its class's constructors checked against the node's member's: a
mismatch rejects when `strict`, else adds nothing. -/
def addPairRK (Ms : List TargetMajor) (strict : Bool) (q : PairRK) (st : RouteRK) :
    m RouteRK := do
  if st.pairs.contains q then return st
  let lay ← unwrapOr st.lays[q.lay]? (.internal "nested route: layout")
  let M := Ms.getD q.cls default
  if ctorsAgreeRK M.ctors (lay.ctors.getD q.mem []) then
    pure { st with pairs := st.pairs.push q }
  else if strict then
    throw (.invalid s!"target rec (nested route): the class {M.ind} is matched to a node whose \
      constructors are not its own")
  else pure st

/-! ## One call -/

/-- **The per-component match** of a callee `M''` against the leaf of the field normal form
`nf` at a layout (the relocated holes `hs`, their families `S`, depth `d`): the leaf, the
inductive, `Level.isEquivList` levels, the parameters defeq at the holes (both inferred).
Returns the leaf's kind and inductive and the callee's abstracted parameters. -/
def matchRK (ops : CheckerOps m) (env : Env) (H : HomeRK) (I : InstRK) (lay : LayRK)
    (hs : List Expr) (S : List (NestKey × Expr)) (d : Nat) (rn : Expr → Expr) (cnR : Name)
    (M'' : TargetMajor) (nf : Expr) : m (LeafRK × Name × List Expr) := do
  let some (kind, cn, lvls, ps) := leafRK H lay nf
    | throw (.invalid s!"target rec (nested route): the rule of {cnR} calls around a nested \
        cycle on a field whose normal form at its node is no member, family or container \
        instance")
  unless M''.ind == cn && (Level.isEquivList M''.lvls (lvls.map (lvl1RK H I))).getD false do
    throw (.invalid s!"target rec (nested route): the rule of {cnR} calls a recursor whose \
      major is not the called field's inductive at its node")
  let dsC := M''.ds.map fun x => absRK H I lay S hs (rn x)
  let dsL := ps.map fun x => absRK H I lay S hs (relocRK H I hs x)
  paramsDefEqRK ops env d cnR dsC dsL
  pure (kind, cn, dsC)

/-- **The callee's node** a leaf gives: the root at a member hole, the family's key node at
a family, the same layout at an own hole, the key's canonical node at a container key. -/
def childRK (ops : CheckerOps m) (env : Env) (I : InstRK) (q : PairRK) (lay : LayRK)
    (kind : LeafRK) (cn : Name) (st : RouteRK) : m (Nat × Nat × RouteRK) := do
  let (li, st) ← match kind with
    | .mem _ => layIdxRK ops env I.home none st
    | .fam j => do
      let kj ← unwrapOr ((lay.L.fams[j]?).map (·.1)) (.internal "nested route: family")
      layIdxRK ops env I.home (some kj) st
    | .own _ => pure (q.lay, st)
    | .key kc => layIdxRK ops env I.home (some kc) st
  let lay' ← unwrapOr st.lays[li]? (.internal "nested route: layout")
  let mi ← unwrapOr (lay'.mems.findIdx? (· == cn)) (.internal "nested route: node member")
  pure (li, mi, st)

/-- **One call at a pair** (see the module docstring).  `strict` (an intra-component call of
a hot class): the per-component match, the call's typing at the relocated holes, K.53, and
the callee's pair — every failure rejects.  Otherwise (a call INTO another component): only
the match, and the callee's pair where it succeeds (its own component's calls are checked
at that pair). `pc` are the canonical parameter variables (every class's parameters are
read at them). -/
def callRK (ops : CheckerOps m) (env : Env) (fam : TargetFamily) (Ms : List TargetMajor)
    (pc : List Expr) (strict : Bool) (q : PairRK) (c : CallRK) (st : RouteRK) : m RouteRK := do
  let rn : Expr → Expr := fun e => e.replaceFVars fun i => pc[i]?
  let I ← unwrapOr st.insts[q.inst]? (.internal "nested route: instance")
  let H ← unwrapOr st.homes[I.home]? (.internal "nested route: home")
  let lay ← unwrapOr st.lays[q.lay]? (.internal "nested route: layout")
  let M'' := Ms.getD c.ih.callee default
  let nds := (lay.nfs.getD q.mem []).getD c.ctor []
  let nf ← unwrapOr nds[c.ih.field]? (.internal "nested route: field normal form")
  -- the relocated context
  let hs := relocHolesRK H I c.base lay.holeTys []
  let S := famSubstRK H I lay hs
  let d := c.base + hs.length
  if !strict then
    let r ← tryCatchThe CheckError
      (do let x ← matchRK ops env H I lay hs S d rn c.cn M'' nf; pure (some x))
      fun err => match err with
        | .invalid _ => pure none
        | e => throw e
    match r with
    | none => return st
    | some (kind, cn, _) =>
      let (li, mi, st) ← childRK ops env I q lay kind cn st
      return ← addPairRK Ms false ⟨c.ih.callee, q.inst, li, mi⟩ st
  let (kind, cn, dsC) ← matchRK ops env H I lay hs S d rn c.cn M'' nf
  -- the call's typing, at every value of the relocated holes
  let crest ← unwrapOr ((lay.crests.getD q.mem []))[c.ctor]? (.internal "nested route: crest")
  let fldH ← unwrapOr (((targetPiDomsWith c.fvsF (relocRK H I hs crest)).getD [])[c.ih.field]?)
    (.internal "nested route: a node's crest does not bind the rule's fields")
  let nM := H.ctx.names.length
  let (hd, psR) : Expr × List Expr := match kind with
    | .mem t => (hs.getD t default, dsC)
    | .fam j => (hs.getD (nM + j) default, [])
    | .own g => (hs.getD (nM + lay.L.nF + g) default, dsC)
    | .key _ => (.const M''.ind M''.lvls, dsC)
  let tele := c.teles.getD c.ih.field []
  let wantH := Expr.mkPisOf tele (Expr.mkAppN hd (psR ++ c.ih.idx))
  let _ ← ops.inferType env d fldH
  let _ ← ops.inferType env d wantH
  unless ← ops.isDefEq env d fldH wantH do
    throw (.invalid s!"target rec (nested route): the rule of {c.cn} calls around a nested \
      cycle on a field that is not a value of the callee's major type at every value of its \
      node's holes")
  -- K.53 (conformance): the callee's major is the field's normal form, read back
  let some calleeAt := Expr.instPisAtLift (c.fvsPref ++ c.ih.idx)
      (fam.recTys.getD c.ih.callee (.sort .zero))
    | throw (.invalid s!"target rec: the rule of {c.cn} recurses into a recursor whose type \
        does not bind the call's arguments")
  let .forallE majDom _ _ := calleeAt
    | throw (.invalid s!"target rec: the rule of {c.cn} recurses into a recursor whose type \
        does not bind the call's major")
  targetK53ConformK c.cn (rbInstRK H I lay c.fvsF nf) (Expr.mkPisOf tele majDom)
  let (li, mi, st) ← childRK ops env I q lay kind cn st
  addPairRK Ms true ⟨c.ih.callee, q.inst, li, mi⟩ st

/-! ## The calls of a class -/

/-- **A rule's calls**, its frame recomputed as `targetRule` computes it (the
rule already passed that check; `rhsA` is its annotated right-hand side). -/
def ruleCallsRK (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (cvRi : ConstantVal) (rP ci : Nat) (M : TargetMajor)
    (c : ConstantVal × Nat) (rhsA : Expr) : m (List CallRK) := do
  let nF := c.2
  let (_, body) ← unwrapOr (rhsA.stripLams (rP + nF)) (.internal "nested route: rule")
  let (fvsPref, _) ← unwrapOr (openPisAtFvars rP cvRi.type 0) (.internal "nested route: prefix")
  let crest ← unwrapOr (instPisWith M.ds (targetCtorAt M c.1)) (.internal "nested route: crest")
  let (fvsF, _) ← unwrapOr (openPisAtFvars nF crest rP) (.internal "nested route: fields")
  let base := rP + nF
  let k := formerTys.length
  let absM := targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys base)
  let fnorm ← targetFieldNorms ops fe.env (base + k) absM fvsF
  let fr : TargetFrame :=
    { recNames := fam.recNames, rlvls := fam.rlvls, recTys := fam.recTys, mIs := fam.mIs,
      rPs := fam.rPs, rP := rP, pref := fvsPref, fields := fvsF,
      teles := fnorm.map fun t => t.piBinders.1,
      pw := Level.zeronessOf (structElimLevel p.elim p.large) }
  let bodyF := body.instantiateList (fvsPref ++ fvsF).reverse
  let (_, ihs) ← unwrapOr (targetAbstract fr base 0 bodyF #[]) (.internal "nested route: calls")
  pure (ihs.toList.map fun ih => ⟨ci, c.1.name, fvsPref, fvsF, fr.teles, base, ih⟩)

/-- Every rule's calls of one recursor. -/
def recCallsRK (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (cvRi : ConstantVal) (rP : Nat) (M : TargetMajor) :
    Nat → List (ConstantVal × Nat) → List Expr → m (List CallRK)
  | ci, c :: cs, r :: rs => do
    let a ← ruleCallsRK ops fe p formerTys fam cvRi rP ci M c r
    let b ← recCallsRK ops fe p formerTys fam cvRi rP M (ci + 1) cs rs
    pure (a ++ b)
  | _, _, _ => pure []

/-! ## The traversal -/

/-- Every call of the pair's class, at the pair: an intra-component call STRICTLY where the
class is hot (a flat component's own calls are the flat route's, `targetIntraCallOk`), a call
into another component softly. -/
def pairCallsRK (ops : CheckerOps m) (env : Env) (fam : TargetFamily) (Ms : List TargetMajor)
    (pc : List Expr) (rk : List Nat) (hs : List Bool) (q : PairRK) :
    List CallRK → RouteRK → m RouteRK
  | [], st => pure st
  | c :: cs, st => do
    let intra := rk.getD c.ih.callee 0 == rk.getD q.cls 0
    let st ← if intra && !hs.getD q.cls false then pure st
      else callRK ops env fam Ms pc intra q c st
    pairCallsRK ops env fam Ms pc rk hs q cs st

/-- The worklist over the pairs, in order of creation. -/
def routeLoopRK (ops : CheckerOps m) (env : Env) (fam : TargetFamily) (Ms : List TargetMajor)
    (pc : List Expr) (rk : List Nat) (hs : List Bool) (calls : List (List CallRK)) :
    Nat → RouteRK → m RouteRK
  | 0, _ => throw (.notImplemented "target rec (nested route): fuel")
  | fuel + 1, st =>
    match st.pairs[st.next]? with
    | none => pure st
    | some q => do
      let st ← pairCallsRK ops env fam Ms pc rk hs q (calls.getD q.cls [])
        { st with next := st.next + 1 }
      routeLoopRK ops env fam Ms pc rk hs calls fuel st

/-- The traversal's fuel: pairs processed. -/
def routeFuelRK : Nat := 65536

/-- **The strongly connected components** of the family's call graph: row `c` marks the
classes in `c`'s component (mutual reachability; `targetHots` marks whole RANK layers, which
may hold several components of one rank). -/
def sccRK (g : List (List Nat)) : List (List Bool) :=
  let n := g.length
  match reachFix g (n * n + 1) ((List.range n).map fun c => (List.range n).map (· == c)) with
  | some R => (List.range n).map fun c => (List.range n).map fun c' =>
      (R.getD c []).getD c' false && (R.getD c' []).getD c false
  | none => (List.range n).map fun c => (List.range n).map (· == c)

/-- **A hot class** (NESTKN-R): its component has a call that is not flat
(`targetFlatEdge`) — a cycle through a nested home. -/
def hotRK (g : List (List Nat)) (scc : List (List Bool)) (Ms : List TargetMajor) (c : Nat) :
    Bool :=
  let inC : Nat → Bool := fun x => (scc.getD c []).getD x false
  (List.range g.length).any fun c1 => inC c1 &&
    (g.getD c1 []).any fun c2 => inC c2 &&
      !targetFlatEdge (Ms.getD c1 default) (Ms.getD c2 default)

/-- **An older seed**: a hot class whose parameters name no inductive of its component — an
OLDER home's member at an instance, the root of its tree.  Used only for the hot classes the
installing block's members do not reach along calls (`targetNestRouteK`), so a class reached
from the block is read in the block's own tree. -/
def olderSeedRK (Ms : List TargetMajor) (scc : List (List Bool)) (hs : List Bool) (c : Nat) :
    Bool :=
  hs.getD c false &&
    let inds := (List.range Ms.length).filterMap fun c' =>
      if (scc.getD c []).getD c' false then some (Ms.getD c' default).ind else none
    !(Ms.getD c default).ds.any (·.mentionsAnyConst inds)

/-- The seeds' pairs: each at its home's root, at the seed's own instance. -/
def seedsRK (ops : CheckerOps m) (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (Ms : List TargetMajor) (pc : List Expr) :
    List Nat → RouteRK → m RouteRK
  | [], st => pure st
  | c :: cs, st => do
    let M := Ms.getD c default
    let (h, st) ← homeIdxRK fe p cvTas ctorsAs M st
    let ds := M.ds.map fun e => e.replaceFVars fun i => pc[i]?
    let (ii, st) : Nat × RouteRK :=
      match st.insts.findIdx? (fun I => I.home == h && I.us == M.lvls &&
          I.ds.map Expr.eraseFVarTys == ds.map Expr.eraseFVarTys) with
      | some ii => (ii, st)
      | none => (st.insts.size, { st with insts := st.insts.push ⟨h, M.lvls, ds⟩ })
    let (li, st) ← layIdxRK ops fe.env h none st
    let H ← unwrapOr st.homes[h]? (.internal "nested route: home")
    let t ← unwrapOr (H.ctx.names.findIdx? (· == M.ind)) (.internal "nested route: seed member")
    let st ← addPairRK Ms true ⟨c, ii, li, t⟩ st
    seedsRK ops fe p cvTas ctorsAs Ms pc cs st

/-- **The nested route** (see the module docstring), after the family's rules passed
(`out`: every recursor with its major and annotated rules): nothing without a hot class;
else the pairs from the seeds along the family's calls (strict inside a hot component,
soft into another), and every hot class covered. -/
def targetNestRouteK (so : ShadowOps m) (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : m Unit := do
  let Ms := out.map (·.2.1)
  let g := targetGraphOf p
  let scc := sccRK g
  let hs := (List.range Ms.length).map (hotRK g scc Ms)
  if !hs.any id then return
  let ops := so.opsAt fe
  let rk := graphRank g
  let fam : TargetFamily :=
    { recNames := p.recs.map (·.cvR.name),
      rlvls := (p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [],
      recTys := out.map (·.1.type), mIs := p.recs.map (·.mI), rPs := p.recs.map (·.rP),
      ranks := some rk, majors := Ms }
  let cv0 ← unwrapOr (out.head?.map (·.1)) (.internal "nested route: empty family")
  let (pc, _) ← unwrapOr (openPisAtFvars p.nP cv0.type 0) (.internal "nested route: parameters")
  let formerTys := cvTas.map (·.type)
  let calls ← (out.zip p.recs).mapM fun ((cvRi, M, rhss), rc) =>
    recCallsRK ops fe p formerTys fam cvRi rc.rP M 0 M.ctors rhss
  -- the installing block's member classes first, then the older homes' roots of the hot
  -- classes they do not reach
  let seeds := (List.range Ms.length).filter fun c => (Ms.getD c default).member.isSome
  let st ← seedsRK ops fe p cvTas ctorsAs Ms pc seeds {}
  let st ← routeLoopRK ops fe.env fam Ms pc rk hs calls routeFuelRK st
  let seeds2 := (List.range Ms.length).filter fun c =>
    olderSeedRK Ms scc hs c && !st.pairs.any (·.cls == c)
  let st ← seedsRK ops fe p cvTas ctorsAs Ms pc seeds2 st
  let st ← routeLoopRK ops fe.env fam Ms pc rk hs calls routeFuelRK st
  unless (List.range Ms.length).all (fun c => !hs.getD c false || st.pairs.any (·.cls == c)) do
    throw (.invalid "target rec (nested route): a class of a nested cycle is reached from no \
      member of its home along the family's calls (no auxiliary type official generates)")
  so.flush

end NestRouteK

end ConLeche
