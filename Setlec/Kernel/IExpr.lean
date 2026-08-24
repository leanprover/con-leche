import Std.Data.HashMap
import Setlec.Kernel.Env
import Setlec.Kernel.Basis.Names
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level

/-!
# Interned (cons-hashed) expressions

An arena of expression nodes whose children are plain indices (`EIdx`),
together with a cons-table mapping each node to its index: structurally
equal terms receive the *same* index, so equality and hashing of interned
expressions are O(1) index operations (nanoda's `ExprPtr` design).

`EStore.intern` adds a single node (reusing an existing index when the
node is already present); `EStore.internExpr` interns a whole `Expr`
bottom-up.  The syntactic operations (`instantiate1I`, `abstract1I`,
`instantiateLevelParamsI`, and the pure queries) mirror the corresponding
`Setlec.Expr` operations exactly, but traverse the DAG with a per-call
memo table keyed by node index (plus the traversal cursor where there is
one), so shared subterms are visited once.

Verification (denotation into `Expr`, well-formedness of stores,
commutation of every operation with the denotation) lives in
`Setlec/Verify/IExpr.lean`; this module is implementation-only.
-/

namespace Setlec

/-- Index of an interned expression node in an `EStore` arena. -/
abbrev EIdx := Nat

/-- Index of an interned level node in an `EStore` arena's level table
(task #62). -/
abbrev LIdx := Nat

/-- Index of an interned name node in an `EStore` arena's name table
(task #88). -/
abbrev NIdx := Nat

/-- The tier-two index tag (task #64): a tier-two arena index is
`tierTag + offset`, keeping tier-one indices the *identity* embedding
(index = table position), so the pre-tier code paths and their proofs
are untouched.  The value is the high bit of the scalar-`Nat` range.
It must stay behind this single definition: large `Nat` literals
compile to a per-use GMP string parse in the generated C (measured
landmine, task #64 experiments); a top-level constant is parsed once
at initialization. -/
def tierTag : Nat := 2 ^ 62

/-- One interned name node: the constructors of `Setlec.Name` with the
prefix replaced by an arena index (task #88: `O(1)` node
hashing/equality — every intern probe hashes a `Nat` and a leaf
component instead of a whole cons-list name). -/
inductive NNode where
  | anonymous
  | str (pre : NIdx) (s : String)
  | num (pre : NIdx) (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- One interned level node: the constructors of `Setlec.Level` with
sublevels replaced by arena indices. -/
inductive LNode where
  | zero
  | succ (u : LIdx)
  | max (u v : LIdx)
  | imax (u v : LIdx)
  | param (n : Name)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Interned binder metadata: `BinderMeta` with the codomain sort
annotation as a level index. -/
structure IBinderMeta where
  bi : BinderInfo
  cod : Option LIdx := none
  deriving DecidableEq, Repr, Hashable

instance : Inhabited IBinderMeta := ⟨⟨.default, none⟩⟩

/-- One interned expression node: the constructors of `Setlec.Expr` with
subexpressions replaced by arena indices and levels by level indices
(task #62: `O(1)` node hashing/equality even for level-deep terms).
Leaf data (names, binder infos, literals) is carried unchanged. -/
inductive ENode where
  | bvar (i : Nat)
  | fvar (idx : Nat) (name : NIdx) (type : EIdx)
  | sort (u : LIdx)
  | const (n : NIdx) (us : List LIdx)
  | app (f a : EIdx)
  | lam (n : NIdx) (type body : EIdx) (m : IBinderMeta)
  | forallE (n : NIdx) (type body : EIdx) (m : IBinderMeta)
  | letE (n : NIdx) (type value body : EIdx)
  | lit (l : Literal)
  | proj (structName : NIdx) (idx : Nat) (e : EIdx)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The name references of an expression node (task #88: constant
name, binder/fvar display name, projection type name). -/
@[inline] def ENode.names : ENode → List NIdx
  | .bvar _ | .sort _ | .app _ _ | .lit _ => []
  | .fvar _ n _ | .const n _ | .lam n _ _ _ | .forallE n _ _ _
  | .letE n _ _ _ | .proj n _ _ => [n]

/-! ### Eager derived per-node fields (task #87)

Each node carries derived data computed at intern time from its
children's already-present entries (the arena is append-only and
children are interned before parents, so the recurrence reads are
`O(1)` `Array.getD`s).  The fields live in parallel arrays beside
`nodes` — a derived field is a function of the cons key and must not
pollute the node (or its hash).  Current fields: the loose-bvar
*bound* (least `k` with `looseBVarsBounded k`; instantiation at or
above the bound is the identity — nanoda's per-node `num_loose_bvars`,
tasks #72/#84) and the fvar *range* (max fvar index + 1, `0` =
fvar-free, `fvar` type annotations not descended — matching the
abstraction traversals; abstraction at or above the range is the
identity, task #86). -/

/-- The loose-bvar-bound recurrence of one node over its children's
entries (`bs` is the bound array; children of a stored node are in
range, so the `getD` default is never hit on well-formed stores). -/
@[inline] def ENode.bvarBoundOf (bs : Array Nat) : ENode → Nat
  | .bvar i => i + 1
  | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max (bs.getD f 0) (bs.getD a 0)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max (bs.getD ty 0) (bs.getD body 0 - 1)
  | .letE _ ty val body =>
    max (max (bs.getD ty 0) (bs.getD val 0)) (bs.getD body 0 - 1)
  | .proj _ _ sub => bs.getD sub 0

/-- The fvar-range recurrence of one node over its children's entries
(`fvar` type annotations are not descended, matching the abstraction
traversals). -/
@[inline] def ENode.fvarRangeOf (fs : Array Nat) : ENode → Nat
  | .fvar idx _ _ => idx + 1
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max (fs.getD f 0) (fs.getD a 0)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max (fs.getD ty 0) (fs.getD body 0)
  | .letE _ ty val body =>
    max (max (fs.getD ty 0) (fs.getD val 0)) (fs.getD body 0)
  | .proj _ _ sub => fs.getD sub 0

/-- The has-level-param recurrence of one level node over its
children's entries (official kernel `level.cpp` `has_param` flag,
task #87). -/
@[inline] def LNode.hasParamOf (bs : Array Bool) : LNode → Bool
  | .param _ => true
  | .zero => false
  | .succ u => bs.getD u false
  | .max u v | .imax u v => bs.getD u false || bs.getD v false

/-- The has-level-param recurrence of one expression node over the
derived arrays (official kernel `instantiate.cpp:232`'s
`has_univ_param` mechanism, task #87): reads the level array (`lbs`)
at `.sort`/`.const` levels and binder-cod annotations, else the
disjunction of the children's entries (`ebs`; `fvar` type annotations
included, matching the level-instantiation traversal). -/
@[inline] def ENode.hasLParamOf (ebs lbs : Array Bool) : ENode → Bool
  | .bvar _ | .lit _ => false
  | .sort u => lbs.getD u false
  | .const _ us => us.any (lbs.getD · false)
  | .fvar _ _ ty => ebs.getD ty false
  | .app f a => ebs.getD f false || ebs.getD a false
  | .lam _ ty body m | .forallE _ ty body m =>
    ebs.getD ty false || ebs.getD body false ||
      (match m.cod with
       | some u => lbs.getD u false
       | none => false)
  | .letE _ ty val body =>
    ebs.getD ty false || ebs.getD val false || ebs.getD body false
  | .proj _ _ sub => ebs.getD sub false

/-- The eager readback recurrence of one name node over its
children's entries (task #88): the parent's `Name` is built from the
prefix's already-cached `Name`, so every distinct name is materialized
once and shared. -/
@[inline] def NNode.nameOf (rs : Array Name) : NNode → Name
  | .anonymous => .anonymous
  | .str p s => .str (rs.getD p .anonymous) s
  | .num p k => .num (rs.getD p .anonymous) k

/-- The interning arena: the expression node table (index = position)
with its cons-table, the level node table with its cons-table, and the
eager derived-field arrays kept congruent with `nodes` (task #87).
Invariant (stated and maintained in `Setlec/Verify/IExpr.lean`):
children of a node are strictly smaller indices, level references of
expression nodes are in range, each cons-table is exactly the graph
of its node table, and each derived-field array has one entry per node
satisfying its recurrence. -/
structure EStore where
  nodes : Array ENode
  cons : Std.HashMap ENode EIdx
  lnodes : Array LNode
  lcons : Std.HashMap LNode LIdx
  /-- Eager per-node loose-bvar bound (`bvarBs.size = nodes.size`). -/
  bvarBs : Array Nat
  /-- Eager per-node fvar range (`fvarBs.size = nodes.size`). -/
  fvarBs : Array Nat
  /-- Eager per-level-node has-param flag
  (`lparamBs.size = lnodes.size`). -/
  lparamBs : Array Bool
  /-- Eager per-node has-level-param flag
  (`eparamBs.size = nodes.size`). -/
  eparamBs : Array Bool
  /-- The name node table (task #88). -/
  nnodes : Array NNode
  /-- The name cons-table (graph of `nnodes`). -/
  ncons : Std.HashMap NNode NIdx
  /-- Eager per-name-node readback (`rbNames.size = nnodes.size`):
  the node's `Name`, shared structurally with its prefix's entry, so
  `readbackN` is an `O(1)` read of a shared value (task #88). -/
  rbNames : Array Name
  /-- Tier-two mode flag (task #64).  Entirely internal: while set,
  `intern` appends to the tier-two tables and tier one is frozen;
  consumers stay tier-blind and only `enableTierTwo` /
  `truncateTierTwo` touch the flag. -/
  tierTwo : Bool
  /-- The tier-two expression node table (task #64; a node at position
  `j` has index `tierTag + j`).  Names and levels stay single-tier. -/
  tnodes : Array ENode
  /-- The tier-two cons-table (graph of `tnodes` under tagged
  indices).  Disjoint from `cons` by the probe order: `internT` probes
  the frozen tier-one table first. -/
  tcons : Std.HashMap ENode EIdx
  /-- Tier-two eager loose-bvar bounds (`tbvarBs.size = tnodes.size`). -/
  tbvarBs : Array Nat
  /-- Tier-two eager fvar ranges (`tfvarBs.size = tnodes.size`). -/
  tfvarBs : Array Nat
  /-- Tier-two eager has-level-param flags
  (`teparamBs.size = tnodes.size`). -/
  teparamBs : Array Bool

namespace EStore

/-- The empty arena. -/
def empty : EStore :=
  ⟨#[], {}, #[], {}, #[], #[], #[], #[], #[], {}, #[],
    false, #[], {}, #[], #[], #[]⟩

instance : Inhabited EStore := ⟨empty⟩

/-- Tier-one intern (the pre-tier `intern`, task #64): the existing
index when the node is already in the cons-table, else the next fresh
index (pushing the node and recording it, and pushing its derived-field
entries computed from the children's).  The store is destructured
before updating so the tables are uniquely referenced during
`push`/`insert` (avoiding whole-table copies). -/
def internP (st : EStore) (n : ENode) : EIdx × EStore :=
  match st.cons[n]? with
  | some i => (i, st)
  | none =>
    match st with
    | ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
        nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs,
        tfvarBs, teparamBs⟩ =>
      let i := nodes.size
      let bb := n.bvarBoundOf bvarBs
      let fb := n.fvarRangeOf fvarBs
      let pb := n.hasLParamOf eparamBs lparamBs
      (i, ⟨nodes.push n, cons.insert n i, lnodes, lcons,
        bvarBs.push bb, fvarBs.push fb, lparamBs, eparamBs.push pb,
        nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs,
        tfvarBs, teparamBs⟩)

/-- The eager per-node loose-bvar bound (task #87): the least `k` with
`looseBVarsBounded k` for the node's denotation; `0` (also the
out-of-range default) means bvar-closed.  Tier dispatch (task #64):
a tier-one position reads the tier-one array exactly as before;
anything else falls through to the tier-two array at offset
`e - tierTag` (empty on a flag-off store, so the fallback is the old
default `0`). -/
@[inline] def bvarBoundD (st : EStore) (e : EIdx) : Nat :=
  if h : e < st.bvarBs.size then st.bvarBs[e]
  else st.tbvarBs.getD (e - tierTag) 0

/-- The eager per-node fvar range (task #87): max fvar index + 1 of
the node's denotation (annotations not descended); `0` (also the
out-of-range default) means fvar-free.  Tier dispatch as
`bvarBoundD` (task #64). -/
@[inline] def fvarRangeD (st : EStore) (e : EIdx) : Nat :=
  if h : e < st.fvarBs.size then st.fvarBs[e]
  else st.tfvarBs.getD (e - tierTag) 0

/-- The eager per-level-node has-param flag (task #87; `false` is
also the out-of-range default).  Levels are single-tier (task #64). -/
@[inline] def lhasParamD (st : EStore) (u : LIdx) : Bool :=
  st.lparamBs.getD u false

/-- The eager per-node has-level-param flag (task #87; `false` is
also the out-of-range default).  Tier dispatch as `bvarBoundD`
(task #64). -/
@[inline] def ehasParamD (st : EStore) (e : EIdx) : Bool :=
  if h : e < st.eparamBs.size then st.eparamBs[e]
  else st.teparamBs.getD (e - tierTag) false

/-! ### Tier two (task #64)

The structure carries a second expression tier so the eventual wiring
can drop a declaration's reduction temporaries wholesale: while the
internal flag is on, fresh nodes go to the tier-two tables (indices
`tierTag + offset`), tier one is frozen, and `truncateTierTwo` later
discards tier two without touching a single tier-one observation
(`Setlec/Kernel/ArenaWF.lean`, `truncateTierTwo_*`).  Consumers stay
tier-blind: `intern` and the derived reads dispatch internally, and
tier-one indices remain the identity embedding. -/

/-- Tier-dispatched node read (task #64): a tier-one position reads
the tier-one table at the identity index; anything else falls through
to the tier-two table at offset `i - tierTag`.  On a flag-off store
(tier two empty) this is exactly `st.getNode i`; with tier two live,
the split is a theorem (`TWF.flag_bound`: tier-one indices sit below
`tierTag`, tier-two indices at or above it). -/
def getNode (st : EStore) (i : EIdx) : Option ENode :=
  if h : i < st.nodes.size then some st.nodes[i]
  else st.tnodes[i - tierTag]?

/-- Tier-blind loose-bvar-bound recurrence of one node over the
dispatching derived reads (the tier-two intern's entry computation,
task #64; the tier-one intern keeps the array-local
`ENode.bvarBoundOf` — same values, uniquely-referenced reads). -/
def nodeBvarBound (st : EStore) : ENode → Nat
  | .bvar i => i + 1
  | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max (st.bvarBoundD f) (st.bvarBoundD a)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max (st.bvarBoundD ty) (st.bvarBoundD body - 1)
  | .letE _ ty val body =>
    max (max (st.bvarBoundD ty) (st.bvarBoundD val))
      (st.bvarBoundD body - 1)
  | .proj _ _ sub => st.bvarBoundD sub

/-- Tier-blind fvar-range recurrence (see `nodeBvarBound`). -/
def nodeFvarRange (st : EStore) : ENode → Nat
  | .fvar idx _ _ => idx + 1
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max (st.fvarRangeD f) (st.fvarRangeD a)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max (st.fvarRangeD ty) (st.fvarRangeD body)
  | .letE _ ty val body =>
    max (max (st.fvarRangeD ty) (st.fvarRangeD val))
      (st.fvarRangeD body)
  | .proj _ _ sub => st.fvarRangeD sub

/-- Tier-blind has-level-param recurrence (see `nodeBvarBound`;
levels are single-tier, so the level reads are the plain
`lhasParamD`). -/
def nodeHasLParam (st : EStore) : ENode → Bool
  | .bvar _ | .lit _ => false
  | .sort u => st.lhasParamD u
  | .const _ us => us.any st.lhasParamD
  | .fvar _ _ ty => st.ehasParamD ty
  | .app f a => st.ehasParamD f || st.ehasParamD a
  | .lam _ ty body m | .forallE _ ty body m =>
    st.ehasParamD ty || st.ehasParamD body ||
      (match m.cod with
       | some u => st.lhasParamD u
       | none => false)
  | .letE _ ty val body =>
    st.ehasParamD ty || st.ehasParamD val || st.ehasParamD body
  | .proj _ _ sub => st.ehasParamD sub

/-- Tier-two intern (task #64): probe the tier-one cons-table first —
tier one is frozen while the flag is on, so a hit resolves to the
node's canonical tier-one index and the tier-one table is never
polluted — then the tier-two cons-table; a fresh node is pushed onto
the tier-two tables at index `tierTag + tnodes.size`, its derived
entries computed by the tier-blind recurrences. -/
def internT (st : EStore) (n : ENode) : EIdx × EStore :=
  match st.cons[n]? with
  | some i => (i, st)
  | none =>
    match st.tcons[n]? with
    | some i => (i, st)
    | none =>
      let bb := st.nodeBvarBound n
      let fb := st.nodeFvarRange n
      let pb := st.nodeHasLParam n
      match st with
      | ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
          nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs,
          tfvarBs, teparamBs⟩ =>
        let i := tierTag + tnodes.size
        (i, ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs,
          eparamBs, nnodes, ncons, rbNames, tierTwo, tnodes.push n,
          tcons.insert n i, tbvarBs.push bb, tfvarBs.push fb,
          teparamBs.push pb⟩)

/-- Intern one node (task #64: internal tier dispatch): with the flag
off — the ordinary state — the tier-one intern `internP`, the pre-tier
code path bit for bit; with it on, the tier-two intern `internT`. -/
def intern (st : EStore) (n : ENode) : EIdx × EStore :=
  if st.tierTwo then st.internT n else st.internP n

/-- Enable tier two (task #64): set the internal flag; subsequent
interns append to the tier-two tables and tier one is frozen.  Guarded
by the tag bound `nodes.size ≤ tierTag`, the invariant that makes the
high-bit index split a theorem (`TWF.flag_bound`,
`Setlec/Kernel/ArenaWF.lean`) — the validate-at-insertion pattern
(task #42): one comparison per enable, no per-access reasoning.  If
the guard ever failed (a tier-one table of `2 ^ 62` nodes), the flag
stays off and the store keeps operating in the fully verified
single-tier mode — graceful degradation (only truncation's memory
reclamation is lost), not an error. -/
def enableTierTwo (st : EStore) : EStore :=
  if st.nodes.size ≤ tierTag then { st with tierTwo := true } else st

/-- Drop tier two wholesale and clear the flag (task #64):
`Array.shrink 0` keeps the tier-two arrays' capacity for the next
enable round; the tier-two cons-table is dropped.  The identity on
every tier-one observation (`truncateTierTwo_*`,
`Setlec/Kernel/ArenaWF.lean`). -/
def truncateTierTwo (st : EStore) : EStore :=
  match st with
  | ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
      nnodes, ncons, rbNames, _tierTwo, tnodes, _tcons, tbvarBs,
      tfvarBs, teparamBs⟩ =>
    ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
      nnodes, ncons, rbNames, false, tnodes.shrink 0, {},
      tbvarBs.shrink 0, tfvarBs.shrink 0, teparamBs.shrink 0⟩

/-- Intern one level node (the level-table analog of `intern`; pushes
the node's has-param entry computed from the children's). -/
def internL (st : EStore) (n : LNode) : LIdx × EStore :=
  match st.lcons[n]? with
  | some i => (i, st)
  | none =>
    match st with
    | ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
        nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs,
        tfvarBs, teparamBs⟩ =>
      let i := lnodes.size
      let pb := n.hasParamOf lparamBs
      (i, ⟨nodes, cons, lnodes.push n, lcons.insert n i, bvarBs, fvarBs,
        lparamBs.push pb, eparamBs, nnodes, ncons, rbNames, tierTwo,
        tnodes, tcons, tbvarBs, tfvarBs, teparamBs⟩)

/-- Intern one name node (the name-table analog of `intern`,
task #88). -/
def internN (st : EStore) (n : NNode) : NIdx × EStore :=
  match st.ncons[n]? with
  | some i => (i, st)
  | none =>
    match st with
    | ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
        nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs,
        tfvarBs, teparamBs⟩ =>
      let i := nnodes.size
      let rb := n.nameOf rbNames
      (i, ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
        nnodes.push n, ncons.insert n i, rbNames.push rb, tierTwo,
        tnodes, tcons, tbvarBs, tfvarBs, teparamBs⟩)

/-- Intern a whole name bottom-up (names are short cons-lists, so no
memoization is needed — the walk is linear in the name's depth). -/
def internName (st : EStore) : Name → NIdx × EStore
  | .anonymous => st.internN .anonymous
  | .str p s =>
    let (p', st) := st.internName p
    st.internN (.str p' s)
  | .num p n =>
    let (p', st) := st.internName p
    st.internN (.num p' n)

/-- Alloc-free comparison of an interned name against a `Name` tree
(structural walk; on a canonical arena equals `readbackN i == some nm`,
`Setlec/Verify/IExpr.lean`).  Used for the fixed-name dispatch tests of
the interned checker core. -/
def beqNameI (st : EStore) (i : NIdx) : Name → Bool
  | .anonymous => st.nnodes[i]? == some .anonymous
  | .str p s =>
    match st.nnodes[i]? with
    | some (.str pi s') => s' == s && st.beqNameI pi p
    | _ => false
  | .num p n =>
    match st.nnodes[i]? with
    | some (.num pi n') => n' == n && st.beqNameI pi p
    | _ => false

/-- Read an interned name back — an `O(1)` read of the eager
per-node readback array (task #88; the returned `Name` is the shared
value built at intern time).  Agrees with the verification's name
denotation on well-formed stores (`WF.readbackN_eq_denoteN`). -/
@[inline] def readbackN (st : EStore) (i : NIdx) : Option Name :=
  st.rbNames[i]?

/-- Intern a whole level bottom-up. -/
def internLevel (st : EStore) : Level → LIdx × EStore
  | .zero => st.internL .zero
  | .succ u =>
    let (u', st) := st.internLevel u
    st.internL (.succ u')
  | .max u v =>
    let (u', st) := st.internLevel u
    let (v', st) := st.internLevel v
    st.internL (.max u' v')
  | .imax u v =>
    let (u', st) := st.internLevel u
    let (v', st) := st.internLevel v
    st.internL (.imax u' v')
  | .param n => st.internL (.param n)

/-- Intern a list of levels. -/
def internLevels (st : EStore) : List Level → List LIdx × EStore
  | [] => ([], st)
  | u :: us =>
    let (u', st) := st.internLevel u
    let (us', st) := st.internLevels us
    (u' :: us', st)

/-- Intern binder metadata (the codomain annotation level, if any). -/
def internBM (st : EStore) (m : BinderMeta) : IBinderMeta × EStore :=
  match m.cod with
  | none => (⟨m.bi, none⟩, st)
  | some u =>
    let (u', st) := st.internLevel u
    (⟨m.bi, some u'⟩, st)

/-- Intern a whole expression bottom-up. -/
def internExpr (st : EStore) : Expr → EIdx × EStore
  | .bvar i => st.intern (.bvar i)
  | .fvar idx n ty =>
    let (t, st) := st.internExpr ty
    let (n', st) := st.internName n
    st.intern (.fvar idx n' t)
  | .sort u =>
    let (u', st) := st.internLevel u
    st.intern (.sort u')
  | .const n us =>
    let (us', st) := st.internLevels us
    let (n', st) := st.internName n
    st.intern (.const n' us')
  | .app f a =>
    let (f', st) := st.internExpr f
    let (a', st) := st.internExpr a
    st.intern (.app f' a')
  | .lam n ty body m =>
    let (t, st) := st.internExpr ty
    let (b, st) := st.internExpr body
    let (m', st) := st.internBM m
    let (n', st) := st.internName n
    st.intern (.lam n' t b m')
  | .forallE n ty body m =>
    let (t, st) := st.internExpr ty
    let (b, st) := st.internExpr body
    let (m', st) := st.internBM m
    let (n', st) := st.internName n
    st.intern (.forallE n' t b m')
  | .letE n ty val body =>
    let (t, st) := st.internExpr ty
    let (v, st) := st.internExpr val
    let (b, st) := st.internExpr body
    let (n', st) := st.internName n
    st.intern (.letE n' t v b)
  | .lit l => st.intern (.lit l)
  | .proj s i e =>
    let (e', st) := st.internExpr e
    let (s', st) := st.internName s
    st.intern (.proj s' i e')

/-! ### Boundary interning with the codomain-chain fast path (task #72)

An annotated binder telescope of depth `n` carries codomain-sort
annotations `vᵢ = imax uᵢ₊₁ vᵢ₊₁` — level *trees* of depth `O(n)`, so
structurally re-interning an annotated expression at the entry-runner
boundary costs `O(n²)` even though the readback shares the chains in
memory (one level memo per `readbackI`).  `internExprFast` exploits
exactly that sharing: at a binder node whose annotation is
`imax _ (child's cod)` — pointer-checked via `withPtrEq`, which is
definitionally its structural continuation, so proofs see plain
equality — the already-interned child index is reused instead of
walking the tail again.  Function-equal to `internExpr`
(`internExprFast_eq`, `Setlec/Verify/IExpr.lean`). -/

/-- Structural level equality with a physical-equality shortcut
(`withPtrEq` is definitionally its continuation `a == b`). -/
@[inline] def levelPtrBEq (a b : Level) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by subst h; simp)

/-- Structural expression equality with a physical-equality shortcut
(definitionally `a == b`).  Used to validate interned-environment
entries against the stored constant they cache: the entry was created
from the very object stored in the environment, so the pointer test
succeeds without walking either expression. -/
@[inline] def exprPtrBEq (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by subst h; simp)

/-- `internBM` reusing the direct child binder's codomain index when
this binder's annotation is `imax _ (child's cod)` — the shape
`annotate` produces on a binder telescope. -/
def internBMFast (st : EStore) (m : BinderMeta)
    (child : Option (Level × LIdx)) : IBinderMeta × EStore :=
  match m.cod with
  | none => (⟨m.bi, none⟩, st)
  | some v =>
    match child, v with
    | some (vc, ic), .imax u vtail =>
      if levelPtrBEq vtail vc then
        let (u', st) := st.internLevel u
        let (i, st) := st.internL (.imax u' ic)
        (⟨m.bi, some i⟩, st)
      else
        let (i, st) := st.internLevel v
        (⟨m.bi, some i⟩, st)
    | _, _ =>
      let (i, st) := st.internLevel v
      (⟨m.bi, some i⟩, st)

/-- Core of `internExprFast`: returns the interned index and, for a
binder node, its codomain annotation (tree and interned index) for the
parent's `internBMFast`. -/
def internExprFastGo (st : EStore) :
    Expr → (EIdx × EStore) × Option (Level × LIdx)
  | .bvar i => (st.intern (.bvar i), none)
  | .fvar idx n ty =>
    let ((t, st), _) := st.internExprFastGo ty
    let (n', st) := st.internName n
    (st.intern (.fvar idx n' t), none)
  | .sort u =>
    let (u', st) := st.internLevel u
    (st.intern (.sort u'), none)
  | .const n us =>
    let (us', st) := st.internLevels us
    let (n', st) := st.internName n
    (st.intern (.const n' us'), none)
  | .app f a =>
    let ((f', st), _) := st.internExprFastGo f
    let ((a', st), _) := st.internExprFastGo a
    (st.intern (.app f' a'), none)
  | .lam n ty body m =>
    let ((t, st), _) := st.internExprFastGo ty
    let ((b, st), child) := st.internExprFastGo body
    let (m', st) := st.internBMFast m child
    let (n', st) := st.internName n
    let cod := match m.cod, m'.cod with
      | some v, some i => some (v, i)
      | _, _ => none
    (st.intern (.lam n' t b m'), cod)
  | .forallE n ty body m =>
    let ((t, st), _) := st.internExprFastGo ty
    let ((b, st), child) := st.internExprFastGo body
    let (m', st) := st.internBMFast m child
    let (n', st) := st.internName n
    let cod := match m.cod, m'.cod with
      | some v, some i => some (v, i)
      | _, _ => none
    (st.intern (.forallE n' t b m'), cod)
  | .letE n ty val body =>
    let ((t, st), _) := st.internExprFastGo ty
    let ((v, st), _) := st.internExprFastGo val
    let ((b, st), _) := st.internExprFastGo body
    let (n', st) := st.internName n
    (st.intern (.letE n' t v b), none)
  | .lit l => (st.intern (.lit l), none)
  | .proj s i e =>
    let ((e', st), _) := st.internExprFastGo e
    let (s', st) := st.internName s
    (st.intern (.proj s' i e'), none)

/-- `internExpr` with the codomain-chain fast path (task #72; equal to
`internExpr` by `internExprFast_eq`).  Used by the entry runners, whose
inputs are readbacks of a previous arena. -/
def internExprFast (st : EStore) (e : Expr) : EIdx × EStore :=
  (st.internExprFastGo e).1

/-!
## Level operations on indices (task #62)

Each mirrors its `Setlec.Level` counterpart; recursive traversals into
child indices use `if _h : c < u` guards for unconditional termination
(the guards never fail on well-formed stores), and the DAG-shaped
recursions thread a memo table so shared sublevels are visited once.
-/

/-- Core of `readbackL` (memoized level readback). -/
def readbackLGo (st : EStore) (memo : Std.HashMap LIdx Level) (u : LIdx) :
    Option Level × Std.HashMap LIdx Level :=
  match memo[u]? with
  | some x => (some x, memo)
  | none =>
    match st.lnodes[u]? with
    | none => (none, memo)
    | some n =>
      let (r, memo) : Option Level × Std.HashMap LIdx Level :=
        match n with
        | .zero => (some .zero, memo)
        | .param p => (some (.param p), memo)
        | .succ l =>
          if _h : l < u then
            match readbackLGo st memo l with
            | (some x, memo) => (some (.succ x), memo)
            | (none, memo) => (none, memo)
          else (none, memo)
        | .max l r =>
          if _h : l < u ∧ r < u then
            match readbackLGo st memo l with
            | (some x, memo) =>
              match readbackLGo st memo r with
              | (some y, memo) => (some (.max x y), memo)
              | (none, memo) => (none, memo)
            | (none, memo) => (none, memo)
          else (none, memo)
        | .imax l r =>
          if _h : l < u ∧ r < u then
            match readbackLGo st memo l with
            | (some x, memo) =>
              match readbackLGo st memo r with
              | (some y, memo) => (some (.imax x y), memo)
              | (none, memo) => (none, memo)
            | (none, memo) => (none, memo)
          else (none, memo)
      match r with
      | some x => (some x, memo.insert u x)
      | none => (none, memo)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Read an interned level back as a `Level` tree (memoized: rebuilt
sublevels are shared in memory).  Agrees with the verification's
structural level denotation on well-formed stores. -/
def readbackL (st : EStore) (u : LIdx) : Option Level :=
  (readbackLGo st {} u).1

/-- Memo table for level index→index traversals. -/
abbrev LMemo := Std.HashMap LIdx LIdx

/-- Parameter lookup of `Level.subst.go` with interned replacement
levels: the replacement index for `n`, or `none` when `n` is unlisted
(the caller keeps the `param` node unchanged). -/
def substLGo? : List Name → List LIdx → Name → Option LIdx
  | k :: ks, v :: vs, n => if k = n then some v else substLGo? ks vs n
  | _, _, _ => none

/-- Core of `substLI` (interned `Level.subst`, memoized per call).
A param-free level (eager has-param entry `false`, task #87) is
returned unchanged without traversal — the official kernel's
`has_param` shortcut in `level.cpp:319`'s replace loop. -/
def substLIGo (ks : List Name) (us : List LIdx) (st : EStore)
    (memo : LMemo) (u : LIdx) : LIdx × EStore × LMemo :=
  if !st.lhasParamD u then (u, st, memo) else
  match memo[u]? with
  | some r => (r, st, memo)
  | none =>
    match st.lnodes[u]? with
    | none => (u, st, memo)
    | some n =>
      let (r, st, memo) : LIdx × EStore × LMemo :=
        match n with
        | .zero => (u, st, memo)
        | .param p =>
          match substLGo? ks us p with
          | some v => (v, st, memo)
          | none => (u, st, memo)
        | .succ l =>
          if _h : l < u then
            let (l', st, memo) := substLIGo ks us st memo l
            let (r, st) := st.internL (.succ l')
            (r, st, memo)
          else (u, st, memo)
        | .max l r =>
          if _h : l < u ∧ r < u then
            let (l', st, memo) := substLIGo ks us st memo l
            let (r', st, memo) := substLIGo ks us st memo r
            let (x, st) := st.internL (.max l' r')
            (x, st, memo)
          else (u, st, memo)
        | .imax l r =>
          if _h : l < u ∧ r < u then
            let (l', st, memo) := substLIGo ks us st memo l
            let (r', st, memo) := substLIGo ks us st memo r
            let (x, st) := st.internL (.imax l' r')
            (x, st, memo)
          else (u, st, memo)
      (r, st, memo.insert u r)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Interned counterpart of `Level.subst ks us` on a level index
(fresh memo). -/
def substLI (st : EStore) (ks : List Name) (us : List LIdx) (u : LIdx) :
    LIdx × EStore :=
  let (r, st, _) := substLIGo ks us st {} u
  (r, st)

/-- Interned `Level.subst ks us` applied to a level *tree* (stored
levels enter the arena through this; parameters hit the interned
replacements directly). -/
def internLevelSubst (st : EStore) (ks : List Name) (us : List LIdx) :
    Level → LIdx × EStore
  | .zero => st.internL .zero
  | .succ u =>
    let (u', st) := st.internLevelSubst ks us u
    st.internL (.succ u')
  | .max u v =>
    let (u', st) := st.internLevelSubst ks us u
    let (v', st) := st.internLevelSubst ks us v
    st.internL (.max u' v')
  | .imax u v =>
    let (u', st) := st.internLevelSubst ks us u
    let (v', st) := st.internLevelSubst ks us v
    st.internL (.imax u' v')
  | .param n =>
    match substLGo? ks us n with
    | some v => (v, st)
    | none => st.internL (.param n)

/-- `internLevelSubst` over a list of stored level trees. -/
def internLevelSubsts (st : EStore) (ks : List Name) (us : List LIdx) :
    List Level → List LIdx × EStore
  | [] => ([], st)
  | l :: ls =>
    let (r, st) := st.internLevelSubst ks us l
    let (rs, st) := st.internLevelSubsts ks us ls
    (r :: rs, st)

/-- Interned counterpart of `Level.combining` (pull common `succ`s out
of a `max` of simplified levels). -/
def combiningLI (st : EStore) (a b : LIdx) : LIdx × EStore :=
  match st.lnodes[a]?, st.lnodes[b]? with
  | some .zero, _ => (b, st)
  | _, some .zero => (a, st)
  | some (.succ l), some (.succ r) =>
    if _h : l < a then
      let (c, st) := st.combiningLI l r
      st.internL (.succ c)
    else st.internL (.max a b)
  | _, _ => st.internL (.max a b)
termination_by a

/-- The non-collapsing `imax` result of `simplifyLIGo`: dispatch on the
simplified right side's node. -/
def simplifyImax (st : EStore) (memo : LMemo) (ls rs : LIdx) :
    LIdx × EStore × LMemo :=
  match st.lnodes[rs]? with
  | some .zero => (rs, st, memo)
  | some (.succ _) =>
    let (x, st) := st.combiningLI ls rs
    (x, st, memo)
  | _ =>
    let (x, st) := st.internL (.imax ls rs)
    (x, st, memo)

/-- Core of `simplifyLI` (interned `Level.simplify`, memoized; the memo
is parameter-free, so callers may share it across calls — the
persistent simplify cache of `Setlec/Kernel/CoreI.lean`). -/
def simplifyLIGo (st : EStore) (memo : LMemo) (u : LIdx) :
    LIdx × EStore × LMemo :=
  match memo[u]? with
  | some r => (r, st, memo)
  | none =>
    match st.lnodes[u]? with
    | none => (u, st, memo)
    | some n =>
      let (r, st, memo) : LIdx × EStore × LMemo :=
        match n with
        | .zero => (u, st, memo)
        | .param _ => (u, st, memo)
        | .succ l =>
          if _h : l < u then
            let (l', st, memo) := simplifyLIGo st memo l
            let (r, st) := st.internL (.succ l')
            (r, st, memo)
          else (u, st, memo)
        | .max l r =>
          if _h : l < u ∧ r < u then
            let (l', st, memo) := simplifyLIGo st memo l
            let (r', st, memo) := simplifyLIGo st memo r
            let (x, st) := st.combiningLI l' r'
            (x, st, memo)
          else (u, st, memo)
        | .imax l r =>
          if _h : l < u ∧ r < u then
            let (ls, st, memo) := simplifyLIGo st memo l
            let (rs, st, memo) := simplifyLIGo st memo r
            let lsIsOne : Bool :=
              match st.lnodes[ls]? with
              | some (.succ z) => st.lnodes[z]? == some .zero
              | _ => false
            if st.lnodes[ls]? == some .zero || lsIsOne then (rs, st, memo)
            else simplifyImax st memo ls rs
          else (u, st, memo)
      (r, st, memo.insert u r)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Interned counterpart of `Level.simplify` (fresh memo). -/
def simplifyLI (st : EStore) (u : LIdx) : LIdx × EStore :=
  let (r, st, _) := simplifyLIGo st {} u
  (r, st)

/-- Core of `isNonZeroLI` (memoized; the memo is shareable across
calls, like `simplifyLIGo`'s). -/
def isNonZeroLIGo (st : EStore) (memo : Std.HashMap LIdx Bool) (u : LIdx) :
    Bool × Std.HashMap LIdx Bool :=
  match memo[u]? with
  | some r => (r, memo)
  | none =>
    match st.lnodes[u]? with
    | none => (false, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap LIdx Bool :=
        match n with
        | .zero => (false, memo)
        | .param _ => (false, memo)
        | .succ _ => (true, memo)
        | .max a b =>
          if _h : a < u ∧ b < u then
            let (ra, memo) := isNonZeroLIGo st memo a
            if ra then (true, memo) else isNonZeroLIGo st memo b
          else (false, memo)
        | .imax _ b =>
          if _h : b < u then isNonZeroLIGo st memo b
          else (false, memo)
      (r, memo.insert u r)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Interned counterpart of `Level.isNonZero` (fresh memo). -/
def isNonZeroLI (st : EStore) (u : LIdx) : Bool :=
  (isNonZeroLIGo st {} u).1

/-!
## Syntactic operations on indices

Each operation mirrors its `Setlec.Expr` counterpart exactly (same
recursion structure, same semantics) and threads a per-call memo table
keyed by the node index plus the traversal cursor, so DAG traversals are
linear in the number of distinct (node, cursor) pairs.

The traversals recurse on child indices, which are strictly smaller than
the parent's for well-formed stores; the `if _h : c < e` guards make
termination unconditional (on an ill-formed store a guard can fail, and
the operation returns the child unchanged — garbage in, garbage out; the
verification only speaks about well-formed stores).
-/

/-- Memo table for index→index traversals with a `Nat` cursor. -/
abbrev MemoN := Std.HashMap (EIdx × Nat) EIdx

/-- Core of `instantiate1I`; `v` is the replacement index, `d` the
binder depth cursor (mirrors `Expr.instantiate1 e v d`).  A node whose
eager bound entry is at or below the cursor has no loose bvar the
substitution could touch, so it is returned unchanged without
traversal (nanoda's per-node `num_loose_bvars <= offset` shortcut,
tasks #84/#87; on a canonical arena the traversal would rebuild the
same index node by node). -/
def instantiate1IGo (v : EIdx) (st : EStore) (memo : MemoN)
    (e : EIdx) (d : Nat) : EIdx × EStore × MemoN :=
  if st.bvarBoundD e ≤ d then (e, st, memo) else
  match memo[(e, d)]? with
  | some r => (r, st, memo)
  | none =>
    match st.getNode e with
    | none => (e, st, memo)
    | some n =>
      let (r, st, memo) : EIdx × EStore × MemoN :=
        match n with
        | .bvar i =>
          if i = d then (v, st, memo)
          else if i > d then
            let (r, st) := st.intern (.bvar (i - 1))
            (r, st, memo)
          else (e, st, memo)
        | .fvar _ _ _ => (e, st, memo)
        | .sort _ => (e, st, memo)
        | .const _ _ => (e, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := instantiate1IGo v st memo f d
            let (a', st, memo) := instantiate1IGo v st memo a d
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.lam n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.forallE n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (val', st, memo) := instantiate1IGo v st memo val d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := instantiate1IGo v st memo sub d
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
      (r, st, memo.insert (e, d) r)
termination_by (e, d)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.instantiate1 e v d`: replace `bvar d`
by `v` (which must denote a `bvar`-closed expression; it is not shifted),
lowering loose `bvar`s above `d` by one. -/
def instantiate1I (st : EStore) (e v : EIdx) (d : Nat := 0) :
    EIdx × EStore :=
  let (r, st, _) := instantiate1IGo v st {} e d
  (r, st)

/-- Memo table for the bulk-instantiation traversal, keyed by the node
index, the live prefix length of the replacement array, and the binder
cursor (nanoda's `ExprCache` discipline: a shared subterm is
substituted once per distinct (node, prefix, cursor) triple). -/
abbrev MemoNL := Std.HashMap (EIdx × Nat × Nat) EIdx

/-- Core of `instantiateListI` (task #50): `vs` holds the replacement
indices innermost binder first, `k ≤ vs.size` the live prefix length —
the call implements `Expr.instantiateList e (ws.take k) d` on the
denotations in **one** DAG traversal, where an `instantiate1` fold
would traverse once per replacement.  A `bvar` hit recurses into its
replacement with the shorter prefix `i - d`, mirroring the `Expr`
fold's semantics on open replacements; on `bvar`-closed replacements
(every call site) that recursion is the identity, memoized like any
other node.  `k > vs.size` (never produced by the wrapper) degrades to
the identity on the missing entries — garbage in, garbage out.
Nodes whose eager bound entry is at or below the cursor are returned
unchanged (see `instantiate1IGo`). -/
def instantiateListIGo (vs : Array EIdx) (st : EStore)
    (memo : MemoNL) (e : EIdx) (k : Nat) (d : Nat) :
    EIdx × EStore × MemoNL :=
  if k = 0 then (e, st, memo)
  else if st.bvarBoundD e ≤ d then (e, st, memo)
  else
    match memo[(e, k, d)]? with
    | some r => (r, st, memo)
    | none =>
      match st.getNode e with
      | none => (e, st, memo)
      | some n =>
        let (r, st, memo) : EIdx × EStore × MemoNL :=
          match n with
          | .bvar i =>
            if i < d then (e, st, memo)
            else if _h : i - d < k then
              if _h2 : i - d < vs.size then
                instantiateListIGo vs st memo vs[i - d] (i - d) d
              else (e, st, memo)
            else
              let (r, st) := st.intern (.bvar (i - k))
              (r, st, memo)
          | .fvar _ _ _ => (e, st, memo)
          | .sort _ => (e, st, memo)
          | .const _ _ => (e, st, memo)
          | .app f a =>
            if _h : f < e ∧ a < e then
              let (f', st, memo) := instantiateListIGo vs st memo f k d
              let (a', st, memo) := instantiateListIGo vs st memo a k d
              let (r, st) := st.intern (.app f' a')
              (r, st, memo)
            else (e, st, memo)
          | .lam n ty body m =>
            if _h : ty < e ∧ body < e then
              let (ty', st, memo) := instantiateListIGo vs st memo ty k d
              let (body', st, memo) :=
                instantiateListIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.lam n ty' body' m)
              (r, st, memo)
            else (e, st, memo)
          | .forallE n ty body m =>
            if _h : ty < e ∧ body < e then
              let (ty', st, memo) := instantiateListIGo vs st memo ty k d
              let (body', st, memo) :=
                instantiateListIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.forallE n ty' body' m)
              (r, st, memo)
            else (e, st, memo)
          | .letE n ty val body =>
            if _h : ty < e ∧ val < e ∧ body < e then
              let (ty', st, memo) := instantiateListIGo vs st memo ty k d
              let (val', st, memo) := instantiateListIGo vs st memo val k d
              let (body', st, memo) :=
                instantiateListIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.letE n ty' val' body')
              (r, st, memo)
            else (e, st, memo)
          | .lit _ => (e, st, memo)
          | .proj s i sub =>
            if _h : sub < e then
              let (sub', st, memo) := instantiateListIGo vs st memo sub k d
              let (r, st) := st.intern (.proj s i sub')
              (r, st, memo)
            else (e, st, memo)
        (r, st, memo.insert (e, k, d) r)
termination_by (k, e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; first
        | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.instantiateList e ws d` (bulk
instantiation, task #50): substitute a whole replacement list —
innermost binder first, `vs[0]` for `bvar d` — in one memoized DAG
traversal.  Equal, under the denotation, to the `instantiate1I` chain
(`Expr.instantiateList_cons`). -/
def instantiateListI (st : EStore) (e : EIdx) (vs : List EIdx)
    (d : Nat := 0) : EIdx × EStore :=
  match vs with
  | [] => (e, st)
  | _ :: _ =>
    let a := vs.toArray
    let (r, st, _) := instantiateListIGo a st {} e a.size d
    (r, st)

/-- Reversed-array core of `instantiateRevI` (task #97): as
`instantiateListIGo`, but the replacement array holds the innermost
binder **last** (`vs[vs.size - 1]` for `bvar d`) — the push order of a
telescope-walking accumulator (lean4lean's `instantiateRev`
discipline).  Pointwise equal to `instantiateListIGo vs.reverse`
(`instantiateRevIGo_eq`, `Setlec/Verify/IExprOps.lean`); keeping the
array un-reversed removes the per-call `O(k)` accumulator conversion
that made telescope walks quadratic. -/
def instantiateRevIGo (vs : Array EIdx) (st : EStore)
    (memo : MemoNL) (e : EIdx) (k : Nat) (d : Nat) :
    EIdx × EStore × MemoNL :=
  if k = 0 then (e, st, memo)
  else if st.bvarBoundD e ≤ d then (e, st, memo)
  else
    match memo[(e, k, d)]? with
    | some r => (r, st, memo)
    | none =>
      match st.getNode e with
      | none => (e, st, memo)
      | some n =>
        let (r, st, memo) : EIdx × EStore × MemoNL :=
          match n with
          | .bvar i =>
            if i < d then (e, st, memo)
            else if _h : i - d < k then
              if _h2 : i - d < vs.size then
                instantiateRevIGo vs st memo
                  (vs[vs.size - 1 - (i - d)]'(by omega)) (i - d) d
              else (e, st, memo)
            else
              let (r, st) := st.intern (.bvar (i - k))
              (r, st, memo)
          | .fvar _ _ _ => (e, st, memo)
          | .sort _ => (e, st, memo)
          | .const _ _ => (e, st, memo)
          | .app f a =>
            if _h : f < e ∧ a < e then
              let (f', st, memo) := instantiateRevIGo vs st memo f k d
              let (a', st, memo) := instantiateRevIGo vs st memo a k d
              let (r, st) := st.intern (.app f' a')
              (r, st, memo)
            else (e, st, memo)
          | .lam n ty body m =>
            if _h : ty < e ∧ body < e then
              let (ty', st, memo) := instantiateRevIGo vs st memo ty k d
              let (body', st, memo) :=
                instantiateRevIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.lam n ty' body' m)
              (r, st, memo)
            else (e, st, memo)
          | .forallE n ty body m =>
            if _h : ty < e ∧ body < e then
              let (ty', st, memo) := instantiateRevIGo vs st memo ty k d
              let (body', st, memo) :=
                instantiateRevIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.forallE n ty' body' m)
              (r, st, memo)
            else (e, st, memo)
          | .letE n ty val body =>
            if _h : ty < e ∧ val < e ∧ body < e then
              let (ty', st, memo) := instantiateRevIGo vs st memo ty k d
              let (val', st, memo) := instantiateRevIGo vs st memo val k d
              let (body', st, memo) :=
                instantiateRevIGo vs st memo body k (d + 1)
              let (r, st) := st.intern (.letE n ty' val' body')
              (r, st, memo)
            else (e, st, memo)
          | .lit _ => (e, st, memo)
          | .proj s i sub =>
            if _h : sub < e then
              let (sub', st, memo) := instantiateRevIGo vs st memo sub k d
              let (r, st) := st.intern (.proj s i sub')
              (r, st, memo)
            else (e, st, memo)
        (r, st, memo.insert (e, k, d) r)
termination_by (k, e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; first
        | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of lean4lean's `Expr.instantiateRev` shape:
bulk-substitute a whole accumulator array with the innermost binder
last (the push order of the binder-telescope loops), in one memoized
DAG traversal.  Equal to `instantiateListI e vs.toList.reverse d`
(`instantiateRevI_eq`), with no per-call accumulator conversion
(task #97). -/
def instantiateRevI (st : EStore) (e : EIdx) (vs : Array EIdx)
    (d : Nat := 0) : EIdx × EStore :=
  if vs.size = 0 then (e, st)
  else
    let (r, st, _) := instantiateRevIGo vs st {} e vs.size d
    (r, st)

/-- Core of `abstract1I`; `d` is the abstracted fvar's de Bruijn level
(fixed), `k` the binder cursor (mirrors `Expr.abstract1 e d k`). -/
def abstract1IGo (d : Nat) (st : EStore) (memo : MemoN) (e : EIdx) (k : Nat) :
    EIdx × EStore × MemoN :=
  match memo[(e, k)]? with
  | some r => (r, st, memo)
  | none =>
    match st.getNode e with
    | none => (e, st, memo)
    | some n =>
      let (r, st, memo) : EIdx × EStore × MemoN :=
        match n with
        | .bvar _ => (e, st, memo)
        | .fvar idx _ _ =>
          if idx = d then
            let (r, st) := st.intern (.bvar k)
            (r, st, memo)
          else (e, st, memo)
        | .sort _ => (e, st, memo)
        | .const _ _ => (e, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := abstract1IGo d st memo f k
            let (a', st, memo) := abstract1IGo d st memo a k
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.lam n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.forallE n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (val', st, memo) := abstract1IGo d st memo val k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := abstract1IGo d st memo sub k
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
      (r, st, memo.insert (e, k) r)
termination_by (e, k)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.abstract1 e d k`: replace `fvar d …`
leaves by `bvar k`, bumping `k` under binders (`fvar` type annotations
are not descended into). -/
def abstract1I (st : EStore) (e : EIdx) (d : Nat) (k : Nat := 0) : EIdx × EStore :=
  let (r, st, _) := abstract1IGo d st {} e k
  (r, st)

/-- Core of `abstractRangeI` (task #72); `d`/`k` fix the abstracted
fvar-level range `[d, d + k)`, `c` is the binder cursor (mirrors
`Expr.abstractRange e d k c`).  A node whose eager range entry is at
or below `d` has no fvar the abstraction could touch, so it is
returned unchanged without traversal (nanoda's per-node `!has_fvars`
shortcut in `abstr_aux`, tasks #86/#87; on a canonical arena the
traversal would rebuild the same index node by node). -/
def abstractRangeIGo (d k : Nat) (st : EStore)
    (memo : MemoN) (e : EIdx) (c : Nat) : EIdx × EStore × MemoN :=
  if st.fvarRangeD e ≤ d then (e, st, memo) else
  match memo[(e, c)]? with
  | some r => (r, st, memo)
  | none =>
    match st.getNode e with
    | none => (e, st, memo)
    | some n =>
      let (r, st, memo) : EIdx × EStore × MemoN :=
        match n with
        | .bvar _ => (e, st, memo)
        | .fvar idx _ _ =>
          if d ≤ idx ∧ idx < d + k then
            let (r, st) := st.intern (.bvar (c + (d + k - 1 - idx)))
            (r, st, memo)
          else (e, st, memo)
        | .sort _ => (e, st, memo)
        | .const _ _ => (e, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := abstractRangeIGo d k st memo f c
            let (a', st, memo) := abstractRangeIGo d k st memo a c
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstractRangeIGo d k st memo ty c
            let (body', st, memo) := abstractRangeIGo d k st memo body (c + 1)
            let (r, st) := st.intern (.lam n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstractRangeIGo d k st memo ty c
            let (body', st, memo) := abstractRangeIGo d k st memo body (c + 1)
            let (r, st) := st.intern (.forallE n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := abstractRangeIGo d k st memo ty c
            let (val', st, memo) := abstractRangeIGo d k st memo val c
            let (body', st, memo) := abstractRangeIGo d k st memo body (c + 1)
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := abstractRangeIGo d k st memo sub c
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
      (r, st, memo.insert (e, c) r)
termination_by (e, c)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.abstractRange e d k c` (bulk
abstraction, task #72): close the `k` fvar levels `[d, d + k)` —
innermost bound tightest — in one memoized DAG traversal.  Equal,
under the denotation, to the innermost-first `abstract1I` chain
(`Expr.abstractRange_succ`).  `k = 0` is the identity and skips the
traversal.  Nodes whose eager range entry is at or below `d` are
returned unchanged (see `abstractRangeIGo`). -/
def abstractRangeI (st : EStore) (e : EIdx) (d k : Nat) (c : Nat := 0) :
    EIdx × EStore :=
  match k with
  | 0 => (e, st)
  | _ + 1 =>
    let (r, st, _) := abstractRangeIGo d k st {} e c
    (r, st)

/-- Memo table for cursor-free index→index traversals. -/
abbrev Memo0 := Std.HashMap EIdx EIdx

/-- Interned level-list substitution (shared level memo). -/
def substLIList (ks : List Name) (us : List LIdx) (st : EStore)
    (memo : LMemo) : List LIdx → List LIdx × EStore × LMemo
  | [] => ([], st, memo)
  | v :: vs =>
    let (v', st, memo) := substLIGo ks us st memo v
    let (vs', st, memo) := substLIList ks us st memo vs
    (v' :: vs', st, memo)

/-- Interned binder-meta level substitution (shared level memo). -/
def substLIBM (ks : List Name) (us : List LIdx) (st : EStore)
    (memo : LMemo) (m : IBinderMeta) : IBinderMeta × EStore × LMemo :=
  match m.cod with
  | none => (⟨m.bi, none⟩, st, memo)
  | some u =>
    let (u', st, memo) := substLIGo ks us st memo u
    (⟨m.bi, some u'⟩, st, memo)

/-- Core of `instantiateLevelParamsI` (no cursor; mirrors
`Expr.instantiateLevelParams ks us`; the replacement levels are
interned, and one level memo is shared across the expression
traversal). -/
def instantiateLevelParamsIGo (ks : List Name) (us : List LIdx)
    (st : EStore) (memo : Memo0) (lmemo : LMemo) (e : EIdx) :
    EIdx × EStore × Memo0 × LMemo :=
  if !st.ehasParamD e then (e, st, memo, lmemo) else
  match memo[e]? with
  | some r => (r, st, memo, lmemo)
  | none =>
    match st.getNode e with
    | none => (e, st, memo, lmemo)
    | some n =>
      let (r, st, memo, lmemo) : EIdx × EStore × Memo0 × LMemo :=
        match n with
        | .bvar _ => (e, st, memo, lmemo)
        | .fvar idx nm ty =>
          if _h : ty < e then
            let (ty', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo ty
            let (r, st) := st.intern (.fvar idx nm ty')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
        | .sort u =>
          let (u', st, lmemo) := substLIGo ks us st lmemo u
          let (r, st) := st.intern (.sort u')
          (r, st, memo, lmemo)
        | .const n vs =>
          let (vs', st, lmemo) := substLIList ks us st lmemo vs
          let (r, st) := st.intern (.const n vs')
          (r, st, memo, lmemo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo f
            let (a', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo a
            let (r, st) := st.intern (.app f' a')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo ty
            let (body', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo body
            let (m', st, lmemo) := substLIBM ks us st lmemo m
            let (r, st) := st.intern (.lam n ty' body' m')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo ty
            let (body', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo body
            let (m', st, lmemo) := substLIBM ks us st lmemo m
            let (r, st) := st.intern (.forallE n ty' body' m')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo ty
            let (val', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo val
            let (body', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo body
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
        | .lit _ => (e, st, memo, lmemo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo, lmemo) :=
              instantiateLevelParamsIGo ks us st memo lmemo sub
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo, lmemo)
          else (e, st, memo, lmemo)
      (r, st, memo.insert e r, lmemo)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.instantiateLevelParams ks us`:
substitute level parameters throughout (sorts, constant level arguments,
binder codomain annotations, and `fvar` type annotations); the
replacement levels are interned. -/
def instantiateLevelParamsI (st : EStore) (ks : List Name) (us : List LIdx)
    (e : EIdx) : EIdx × EStore :=
  let (r, st, _) := instantiateLevelParamsIGo ks us st {} {} e
  (r, st)

/-!
## Pure queries (no store change)

Boolean/list queries mirror their `Expr` counterparts; each threads a
per-call memo where the recursion can revisit shared children.
-/

/-- Interned counterpart of `Expr.hasFvar` — an `O(1)` read of the
eager fvar-range entry (task #87; a node has a reachable fvar leaf iff
its range is nonzero: `hasFvar` and the range both treat `fvar` leaves
as hits without descending into their annotations). -/
def hasFvarI (st : EStore) (e : EIdx) : Bool :=
  st.fvarRangeD e != 0

/-- Core of `looseBVarsBoundedI`; `k` is the bound cursor (mirrors
`Expr.looseBVarsBounded k`). -/
def looseBVarsBoundedIGo (st : EStore) (memo : Std.HashMap (EIdx × Nat) Bool)
    (k : Nat) (e : EIdx) : Bool × Std.HashMap (EIdx × Nat) Bool :=
  match memo[(e, k)]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => (false, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap (EIdx × Nat) Bool :=
        match n with
        | .bvar i => (decide (i < k), memo)
        | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => (true, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := looseBVarsBoundedIGo st memo k f
            if rf then looseBVarsBoundedIGo st memo k a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := looseBVarsBoundedIGo st memo k ty
            if rt then looseBVarsBoundedIGo st memo (k + 1) body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := looseBVarsBoundedIGo st memo k ty
            if rt then
              let (rv, memo) := looseBVarsBoundedIGo st memo k val
              if rv then looseBVarsBoundedIGo st memo (k + 1) body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj _ _ sub =>
          if _h : sub < e then looseBVarsBoundedIGo st memo k sub
          else (false, memo)
      (r, memo.insert (e, k) r)
termination_by (e, k)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.looseBVarsBounded k`. -/
def looseBVarsBoundedI (st : EStore) (k : Nat) (e : EIdx) : Bool :=
  (looseBVarsBoundedIGo st {} k e).1

/-- Level-parameter definedness of an interned level, DAG-memoized
(the memo is per call: the predicate depends on `params`).  Mirrors
`Level.allParamsDefined params`. -/
def lparamsDefinedLIGo (st : EStore) (params : List Name)
    (memo : Std.HashMap LIdx Bool) (u : LIdx) :
    Bool × Std.HashMap LIdx Bool :=
  if !st.lhasParamD u then (true, memo) else
  match memo[u]? with
  | some r => (r, memo)
  | none =>
    match st.lnodes[u]? with
    | none => (false, memo)
    | some m =>
      let (r, memo) : Bool × Std.HashMap LIdx Bool :=
        match m with
        | .zero => (true, memo)
        | .param n => (params.contains n, memo)
        | .succ v =>
          if _h : v < u then lparamsDefinedLIGo st params memo v
          else (false, memo)
        | .max v w | .imax v w =>
          if _h : v < u ∧ w < u then
            let (rv, memo) := lparamsDefinedLIGo st params memo v
            if rv then lparamsDefinedLIGo st params memo w
            else (false, memo)
          else (false, memo)
      (r, memo.insert u r)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- `lparamsDefinedLIGo` over a list (a `const` node's levels). -/
def lparamsDefinedListLI (st : EStore) (params : List Name)
    (memo : Std.HashMap LIdx Bool) :
    List LIdx → Bool × Std.HashMap LIdx Bool
  | [] => (true, memo)
  | u :: us =>
    let (r, memo) := lparamsDefinedLIGo st params memo u
    if r then lparamsDefinedListLI st params memo us else (false, memo)

/-- Core of `allLevelParamsDefinedI`: one DAG-memoized walk (per-call
memos, keyed by node index — the parameters are fixed for the call).
Mirrors `Expr.allLevelParamsDefined params`. -/
def allLevelParamsDefinedIGo (st : EStore) (params : List Name)
    (lmemo : Std.HashMap LIdx Bool) (memo : Std.HashMap EIdx Bool)
    (e : EIdx) :
    Bool × Std.HashMap LIdx Bool × Std.HashMap EIdx Bool :=
  if !st.ehasParamD e then (true, lmemo, memo) else
  match memo[e]? with
  | some r => (r, lmemo, memo)
  | none =>
    match st.getNode e with
    | none => (false, lmemo, memo)
    | some n =>
      let (r, lmemo, memo) :
          Bool × Std.HashMap LIdx Bool × Std.HashMap EIdx Bool :=
        match n with
        | .bvar _ | .lit _ => (true, lmemo, memo)
        | .sort u =>
          let (r, lmemo) := lparamsDefinedLIGo st params lmemo u
          (r, lmemo, memo)
        | .const _ us =>
          let (r, lmemo) := lparamsDefinedListLI st params lmemo us
          (r, lmemo, memo)
        | .fvar _ _ ty =>
          if _h : ty < e then allLevelParamsDefinedIGo st params lmemo memo ty
          else (false, lmemo, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, lmemo, memo) :=
              allLevelParamsDefinedIGo st params lmemo memo f
            if rf then allLevelParamsDefinedIGo st params lmemo memo a
            else (false, lmemo, memo)
          else (false, lmemo, memo)
        | .lam _ ty body m | .forallE _ ty body m =>
          if _h : ty < e ∧ body < e then
            let (rt, lmemo, memo) :=
              allLevelParamsDefinedIGo st params lmemo memo ty
            if rt then
              let (rb, lmemo, memo) :=
                allLevelParamsDefinedIGo st params lmemo memo body
              if rb then
                match m.cod with
                | some v =>
                  let (rc, lmemo) := lparamsDefinedLIGo st params lmemo v
                  (rc, lmemo, memo)
                | none => (true, lmemo, memo)
              else (false, lmemo, memo)
            else (false, lmemo, memo)
          else (false, lmemo, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, lmemo, memo) :=
              allLevelParamsDefinedIGo st params lmemo memo ty
            if rt then
              let (rv, lmemo, memo) :=
                allLevelParamsDefinedIGo st params lmemo memo val
              if rv then allLevelParamsDefinedIGo st params lmemo memo body
              else (false, lmemo, memo)
            else (false, lmemo, memo)
          else (false, lmemo, memo)
        | .proj _ _ sub =>
          if _h : sub < e then allLevelParamsDefinedIGo st params lmemo memo sub
          else (false, lmemo, memo)
      (r, lmemo, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.allLevelParamsDefined params`. -/
def allLevelParamsDefinedI (st : EStore) (params : List Name) (e : EIdx) :
    Bool :=
  (allLevelParamsDefinedIGo st params {} {} e).1

/-- Core of `wscopedBI`; `d` is the scope cursor (mirrors
`Expr.wscopedB d`; an `fvar idx _ ty` leaf checks `idx < d` and recurses
into the annotation at cutoff `idx`). -/
def wscopedBIGo (st : EStore) (memo : Std.HashMap (EIdx × Nat) Bool)
    (d : Nat) (e : EIdx) : Bool × Std.HashMap (EIdx × Nat) Bool :=
  match memo[(e, d)]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => (false, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap (EIdx × Nat) Bool :=
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => (true, memo)
        | .fvar idx _ ty =>
          if _h : ty < e then
            if idx < d then wscopedBIGo st memo idx ty else (false, memo)
          else (false, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := wscopedBIGo st memo d f
            if rf then wscopedBIGo st memo d a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := wscopedBIGo st memo d ty
            if rt then wscopedBIGo st memo d body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := wscopedBIGo st memo d ty
            if rt then
              let (rv, memo) := wscopedBIGo st memo d val
              if rv then wscopedBIGo st memo d body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj _ _ sub =>
          if _h : sub < e then wscopedBIGo st memo d sub
          else (false, memo)
      (r, memo.insert (e, d) r)
termination_by (e, d)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.wscopedB d`. -/
def wscopedBI (st : EStore) (d : Nat) (e : EIdx) : Bool :=
  (wscopedBIGo st {} d e).1

/-- Core of `fvarLeavesI` (mirrors `Expr.fvarLeaves`: reachable `fvar`
leaves including, hereditarily, those inside their type annotations; the
annotation component of each triple is an index).  The memo shares the
sub-lists, so the traversal is linear in the number of distinct nodes
(the *resulting list* can still repeat leaves, exactly as the `Expr`
version does). -/
def fvarLeavesIGo (st : EStore)
    (memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))) (e : EIdx) :
    List (Nat × NIdx × EIdx) × Std.HashMap EIdx (List (Nat × NIdx × EIdx)) :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => ([], memo)
    | some n =>
      let (r, memo) : List (Nat × NIdx × EIdx) × Std.HashMap EIdx (List (Nat × NIdx × EIdx)) :=
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => ([], memo)
        | .fvar idx nm ty =>
          if _h : ty < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            ((idx, nm, ty) :: rt, memo)
          else ([(idx, nm, ty)], memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := fvarLeavesIGo st memo f
            let (ra, memo) := fvarLeavesIGo st memo a
            (rf ++ ra, memo)
          else ([], memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            let (rb, memo) := fvarLeavesIGo st memo body
            (rt ++ rb, memo)
          else ([], memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            let (rv, memo) := fvarLeavesIGo st memo val
            let (rb, memo) := fvarLeavesIGo st memo body
            (rt ++ rv ++ rb, memo)
          else ([], memo)
        | .proj _ _ sub =>
          if _h : sub < e then fvarLeavesIGo st memo sub
          else ([], memo)
      (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.fvarLeaves`: the reachable `fvar`
leaves as `(idx, name, type-index)` triples. -/
def fvarLeavesI (st : EStore) (e : EIdx) : List (Nat × NIdx × EIdx) :=
  (fvarLeavesIGo st {} e).1

/-- Core of the fabrication-side leaf-subset test (task #86): is
every fvar leaf of `e` — hereditarily including annotation leaves,
exactly `fvarLeavesI`'s notion — contained in `bl`?  One memoized
Bool DAG walk; the previous `.all` over the materialized
`fvarLeavesI e` list was tree-sized on shared fabrications (the
residual exponential case noted at task #84). -/
def leavesSubIGo (st : EStore) (bl : List (Nat × NIdx × EIdx))
    (memo : Std.HashMap EIdx Bool) (e : EIdx) :
    Bool × Std.HashMap EIdx Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => (true, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap EIdx Bool :=
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => (true, memo)
        | .fvar idx nm ty =>
          if bl.contains (idx, nm, ty) then
            if _h : ty < e then leavesSubIGo st bl memo ty
            else (true, memo)
          else (false, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := leavesSubIGo st bl memo f
            if rf then leavesSubIGo st bl memo a else (false, memo)
          else (true, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := leavesSubIGo st bl memo ty
            if rt then leavesSubIGo st bl memo body else (false, memo)
          else (true, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := leavesSubIGo st bl memo ty
            if rt then
              let (rv, memo) := leavesSubIGo st bl memo val
              if rv then leavesSubIGo st bl memo body else (false, memo)
            else (false, memo)
          else (true, memo)
        | .proj _ _ sub =>
          if _h : sub < e then leavesSubIGo st bl memo sub
          else (true, memo)
      (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- The fabrication leaf guard (scoped call discipline): every fvar
leaf of `fab` is an fvar leaf of `base`.  Equal to the `Expr`-level
`fab.fvarLeaves.all (base.fvarLeaves.contains ·)` on well-formed
stores (`leafGuardI_spec`); evaluation short-circuits — a term with no
fvar at all passes trivially (`hasFvarI`, one memoized DAG walk), and
the fabrication side is the memoized Bool walk `leavesSubIGo` instead
of a tree-sized leaf-list materialization (tasks #84/#86; the base's
leaf list is still materialized, once). -/
def leafGuardI (st : EStore) (fab base : EIdx) : Bool :=
  !st.hasFvarI fab ||
    (leavesSubIGo st (st.fvarLeavesI base) {} fab).1

/-- Core of `constsResolveI` (mirrors `Expr.constsResolve env`; no
cursor). -/
def constsResolveIGo (st : EStore) (env : Env)
    (memo : Std.HashMap EIdx Bool) (e : EIdx) : Bool × Std.HashMap EIdx Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => (false, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap EIdx Bool :=
        match n with
        | .bvar _ | .sort _ => (true, memo)
        | .lit (.natVal _) =>
          ((env.find? natName).isSome && (env.find? natZeroName).isSome &&
            (env.find? natSuccName).isSome, memo)
        | .lit (.strVal _) =>
          ((env.find? natName).isSome && (env.find? natZeroName).isSome &&
            (env.find? natSuccName).isSome && (env.find? stringName).isSome &&
            (env.find? stringOfListName).isSome &&
            (env.find? listName).isSome && (env.find? listNilName).isSome &&
            (env.find? listConsName).isSome && (env.find? charName).isSome &&
            (env.find? charOfNatName).isSome, memo)
        | .const n _ =>
          (match st.readbackN n with
           | some nm => (env.find? nm).isSome
           | none => false, memo)
        | .fvar _ _ ty =>
          if _h : ty < e then constsResolveIGo st env memo ty
          else (false, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := constsResolveIGo st env memo f
            if rf then constsResolveIGo st env memo a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := constsResolveIGo st env memo ty
            if rt then constsResolveIGo st env memo body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := constsResolveIGo st env memo ty
            if rt then
              let (rv, memo) := constsResolveIGo st env memo val
              if rv then constsResolveIGo st env memo body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj s _ sub =>
          if _h : sub < e then
            match st.readbackN s with
            | some sn =>
              if (env.find? sn).isSome then constsResolveIGo st env memo sub
              else (false, memo)
            | none => (false, memo)
          else (false, memo)
      (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.constsResolve env`. -/
def constsResolveI (st : EStore) (env : Env) (e : EIdx) : Bool :=
  (constsResolveIGo st env {} e).1

/-!
## Spine and telescope operations (task #26)

The remaining `Expr` operations the interned checker core
(`Setlec/Kernel/CoreI.lean`) needs.  Each mirrors its `Setlec.Expr`
counterpart exactly; traversals into child indices use the
`if _h : c < e` guards for unconditional termination (the guards never
fail on well-formed stores — `Setlec/Verify/IExprOps.lean`).
-/

/-- Interned counterpart of `Expr.getAppFn`. -/
def getAppFnI (st : EStore) (e : EIdx) : EIdx :=
  match st.getNode e with
  | some (.app f _) => if _h : f < e then getAppFnI st f else e
  | _ => e
termination_by e

/-- Core of `getAppArgsI`: prepend the spine arguments of `e`
(outermost last) to `acc` — linear in the spine length (task #50; the
previous append-per-node form was quadratic). -/
def getAppArgsAccI (st : EStore) : EIdx → List EIdx → List EIdx
  | e, acc =>
    match st.getNode e with
    | some (.app f a) =>
      if _h : f < e then getAppArgsAccI st f (a :: acc) else acc
    | _ => acc
termination_by e _ => e

/-- Interned counterpart of `Expr.getAppArgs` (outermost last). -/
def getAppArgsI (st : EStore) (e : EIdx) : List EIdx :=
  getAppArgsAccI st e []

/-- Interned counterpart of `Expr.mkAppN`. -/
def mkAppNI (st : EStore) (f : EIdx) : List EIdx → EIdx × EStore
  | [] => (f, st)
  | a :: as =>
    let (fa, st) := st.intern (.app f a)
    mkAppNI st fa as

/-- The `instantiate1I` chain of `Expr.instSpine` — the fallback for
argument lists that do not span the whole telescope context (`t + 1`
entries); the spanning case is bulk-instantiated (`instSpineI`). -/
def instSpineChainI (st : EStore) :
    List EIdx → Nat → EIdx → EIdx × EStore
  | [], _, e => (e, st)
  | a :: as, t, e =>
    let (e', st) := st.instantiate1I e a t
    instSpineChainI st as (t - 1) e'

/-- Interned counterpart of `Expr.instSpine`.  When the arguments span
the whole telescope context (`t + 1` of them, the only shape the
checker produces) this is one bulk instantiation of the reversed spine
(`Expr.instSpine_eq_instantiateList`, task #50); otherwise the
`instantiate1I` chain. -/
def instSpineI (st : EStore) (args : List EIdx) (t : Nat) (e : EIdx) :
    EIdx × EStore :=
  if args.length = t + 1 then
    st.instantiateListI e args.reverse 0
  else instSpineChainI st args t e

/-- Interned counterpart of `Expr.piResidual` (= `Expr.instPis`: the
two `Expr` functions have identical equations).  Bulk form (task #50):
peel the syntactic `∀`-binders while accumulating the arguments and
substitute once at the end — one traversal, where the fold copied the
residual telescope per argument.  A `bvar` telescope body (whose
substitution could itself expose `∀`-binders — never produced by the
checker, but the fold semantics allows it) substitutes the accumulator
and re-enters. -/
def piResidualAccI (st : EStore) : List EIdx → EIdx → List EIdx →
    Option EIdx × EStore
  | acc, e, [] =>
    let (r, st) := st.instantiateListI e acc 0
    (some r, st)
  | acc, e, a :: as =>
    match st.getNode e with
    | some (.forallE _ _ b _) => piResidualAccI st (a :: acc) b as
    | some (.bvar _) =>
      match acc with
      | [] => (none, st)
      | _ :: _ =>
        let (e', st) := st.instantiateListI e acc 0
        piResidualAccI st [] e' (a :: as)
    | _ => (none, st)
termination_by acc _e as => (as.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

@[inherit_doc piResidualAccI]
def piResidualI (st : EStore) (e : EIdx) (args : List EIdx) :
    Option EIdx × EStore :=
  piResidualAccI st [] e args

/-- Interned counterpart of `Expr.pisToLams`. -/
def pisToLamsI (st : EStore) : Nat → EIdx → EIdx → Option EIdx × EStore
  | 0, _, body => (some body, st)
  | k + 1, e, body =>
    match st.getNode e with
    | some (.forallE n ty rest mb) =>
      match pisToLamsI st k rest body with
      | (some b, st) =>
        let (r, st) := st.intern (.lam n ty b ⟨mb.bi, none⟩)
        (some r, st)
      | (none, st) => (none, st)
    | _ => (none, st)

/-- The body after `k` leading `∀`-binders (the second component of
`Expr.stripPis k`; the interned iota step only tests `isSome` and reads
the body). -/
def stripPisBodyI (st : EStore) : Nat → EIdx → Option EIdx
  | 0, e => some e
  | k + 1, e =>
    match st.getNode e with
    | some (.forallE _ _ b _) => stripPisBodyI st k b
    | _ => none

/-- Memoized level-list readback (shared level memo). -/
def readbackLList (st : EStore) (memo : Std.HashMap LIdx Level) :
    List LIdx → Option (List Level) × Std.HashMap LIdx Level
  | [] => (some [], memo)
  | u :: us =>
    match readbackLGo st memo u with
    | (some l, memo) =>
      match readbackLList st memo us with
      | (some ls, memo) => (some (l :: ls), memo)
      | (none, memo) => (none, memo)
    | (none, memo) => (none, memo)

/-- Memoized binder-meta readback (shared level memo). -/
def readbackBM (st : EStore) (memo : Std.HashMap LIdx Level)
    (m : IBinderMeta) : Option BinderMeta × Std.HashMap LIdx Level :=
  match m.cod with
  | none => (some ⟨m.bi, none⟩, memo)
  | some u =>
    match readbackLGo st memo u with
    | (some l, memo) => (some ⟨m.bi, some l⟩, memo)
    | (none, memo) => (none, memo)

/-- Core of `readbackI` (memoized, so shared subterms are rebuilt once
and share the resulting `Expr` values in memory; one level memo is
shared across the traversal). -/
def readbackGo (st : EStore) (memo : Std.HashMap EIdx Expr)
    (lmemo : Std.HashMap LIdx Level) (e : EIdx) :
    Option Expr × Std.HashMap EIdx Expr × Std.HashMap LIdx Level :=
  match memo[e]? with
  | some x => (some x, memo, lmemo)
  | none =>
    match st.getNode e with
    | none => (none, memo, lmemo)
    | some n =>
      let (r, memo, lmemo) :
          Option Expr × Std.HashMap EIdx Expr × Std.HashMap LIdx Level :=
        match n with
        | .bvar i => (some (.bvar i), memo, lmemo)
        | .fvar idx nm ty =>
          if _h : ty < e then
            match readbackGo st memo lmemo ty with
            | (some t, memo, lmemo) =>
              match st.readbackN nm with
              | some n => (some (.fvar idx n t), memo, lmemo)
              | none => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .sort u =>
          match readbackLGo st lmemo u with
          | (some l, lmemo) => (some (.sort l), memo, lmemo)
          | (none, lmemo) => (none, memo, lmemo)
        | .const n us =>
          match readbackLList st lmemo us with
          | (some ls, lmemo) =>
            match st.readbackN n with
            | some nm => (some (.const nm ls), memo, lmemo)
            | none => (none, memo, lmemo)
          | (none, lmemo) => (none, memo, lmemo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            match readbackGo st memo lmemo f with
            | (some xf, memo, lmemo) =>
              match readbackGo st memo lmemo a with
              | (some xa, memo, lmemo) => (some (.app xf xa), memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .lam n ty body mb =>
          if _h : ty < e ∧ body < e then
            match readbackGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match readbackGo st memo lmemo body with
              | (some xb, memo, lmemo) =>
                match readbackBM st lmemo mb with
                | (some m, lmemo) =>
                  match st.readbackN n with
                  | some nm => (some (.lam nm xt xb m), memo, lmemo)
                  | none => (none, memo, lmemo)
                | (none, lmemo) => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .forallE n ty body mb =>
          if _h : ty < e ∧ body < e then
            match readbackGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match readbackGo st memo lmemo body with
              | (some xb, memo, lmemo) =>
                match readbackBM st lmemo mb with
                | (some m, lmemo) =>
                  match st.readbackN n with
                  | some nm => (some (.forallE nm xt xb m), memo, lmemo)
                  | none => (none, memo, lmemo)
                | (none, lmemo) => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            match readbackGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match readbackGo st memo lmemo val with
              | (some xv, memo, lmemo) =>
                match readbackGo st memo lmemo body with
                | (some xb, memo, lmemo) =>
                  match st.readbackN n with
                  | some nm => (some (.letE nm xt xv xb), memo, lmemo)
                  | none => (none, memo, lmemo)
                | (none, memo, lmemo) => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .lit l => (some (.lit l), memo, lmemo)
        | .proj s i sub =>
          if _h : sub < e then
            match readbackGo st memo lmemo sub with
            | (some xs, memo, lmemo) =>
              match st.readbackN s with
              | some sn => (some (.proj sn i xs), memo, lmemo)
              | none => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
      match r with
      | some x => (some x, memo.insert e x, lmemo)
      | none => (none, memo, lmemo)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Read an interned expression back as an `Expr` tree (memoized: the
rebuilt subtrees are shared in memory).  Agrees with the verification's
structural denotation on well-formed stores
(`Setlec/Verify/IExprOps.lean`). -/
def readbackI (st : EStore) (e : EIdx) : Option Expr :=
  (readbackGo st {} {} e).1

end EStore

end Setlec
