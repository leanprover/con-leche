module

public import ConLeche.Cached.ExprNodes
public import ConLeche.Kernel.Core
public import ConLeche.Kernel.Exclusive

@[expose] public section

/-!
# The cached syntactic operations on `Expr`

The **executed** counterparts of the arena operations in
`ConLeche/Kernel/IExpr.lean` — same clauses, same memo discipline, same
cutoffs; the mechanism differs only in where the derived data lives (a
field of the node instead of a parallel array indexed by the node's
arena position) and in how a rebuilt node is obtained (allocation
instead of a cons-table probe).

Two structural consequences of dropping the arena, both load-bearing
for the pilot's numbers:

* every traversal memo is keyed on `Expr` itself (`O(1)` hashing off
  the cached field, pointer-first equality), so shared sub-DAGs are
  still visited once — a `Std.HashMap Expr α` replaces the arena's
  `Std.HashMap EIdx α` one for one;
* a cutoff (`bvarB ≤ d`, `fvarB ≤ d`, `!hasLP`) returns the node
  **itself**, so the result shares memory with the input and later
  pointer comparisons on it are `O(1)` — the analogue of the arena
  returning the same index.

## The memo discipline of the substitution walks (task #177)

The retired arena's memo key was an `EIdx` — a scalar.  This tier's is
a *constructed* key, so the probe costs allocations, and profiling put
`instantiate*Go`/`abstract*Go` plus their `Std.DHashMap` spec sites at
roughly half of every `--trusted` run.  Three shape rules cut that,
and each is a property of the walks alone (the values are unchanged —
`ConLeche/Verify/Cached/OpsC.lean` proves each walk equal to its
`ConLeche.Expr` counterpart exactly as before):

1. **The key is built once per node.**  `let key := …` is shared by the
   probe and the insert, instead of the same tuple being allocated for
   each.
2. **The bulk key carries no live prefix.**  `k` is invariant over the
   life of a table (see `MemoNL`), so it moved from the key into the
   memo *invariant* (`MemoLInv ws k memo`), and the `bvar` arm's
   re-entry — the one place `k` shrinks — runs under a fresh table.
3. **Only compound nodes are memoized.**  The memo probe and insert sit
   inside the `app`/`lam`/`forallE`/`letE`/`proj` arms; a node with no
   children to descend into is answered on the spot.  This matters most
   for the loose `bvar`s, which the cutoff lets through by
   construction and which are the most numerous nodes a substitution
   touches — recording a one-word answer under a two-word key was pure
   loss.  It is why the arms carry the probe rather than the head of
   the function.
-/

namespace ConLeche.Expr

/-! ## Spines -/

/-- Prepend the spine arguments of `e` to `acc` (outermost last). -/
def getAppArgsAccC : Expr → List Expr → List Expr
  | .app f a .., acc => getAppArgsAccC f (a :: acc)
  | _, acc => acc

/-- The arguments of an application spine, outermost last. -/
@[inline] def getAppArgsC (e : Expr) : List Expr := getAppArgsAccC e []

/-! ## Instantiation -/

/-! ## The exclusivity-oracle memo discipline (task #314)

The second memo discipline, selectable by `walkMemoMode`: ONE walk
per operation that asks, at every compound node, whether the node is
an EXCLUSIVE object — single-threaded, reference count 1
(`ConLeche/Kernel/Exclusive.lean`) — and rebuilds an exclusive node
without touching the memo (no key, no probe, no insert), while a
shared node (count `> 1`, multi-threaded, or persistent — the
installed environment) is probed and, on a miss, recorded after the
rebuild.  The table is created at the first shared compound node
(`none` until then); the root is never probed (it cannot be reached
again within its own walk).  The official kernel's `replace_fn`
caches exactly the `!is_likely_unshared(e)` nodes.

**The node is borrowed** (`@&`) all the way down, and so is the
replacement.  An owned parameter is a reference of its own, and the
count the oracle reads would then be "in-tree references + 1" — every
child of a held root would answer shared.  Borrowed, the count is the
number of references INSIDE the term (plus the caller's at the root,
which is never asked), which is the question the memo exists to
answer.  The task #314 record reads the generated C.

**Verification is intrinsic** (the `Expr.beqGo` shape): a walk
returns a `Squash` of the rebuilt term with its proof of equality to
the PLAIN descent (`*P`, the reference — `Verify/Cached/OpsC.lean`
proves each `*P` equal to the specification) beside the memo, whose
type carries its own invariant (`MemoXInv`).  The result is a
`Subsingleton`, which is the obligation `withExclusive` asks of its
continuation — so the wrapper's theorem holds whatever the oracle
answers, by the primitive's contract, never by a case analysis on
reference counts.  Each walk's `enter*` is the child step: the cutoff,
the compound test, then the oracle; its `rec` argument is the descent
itself, inlined, so the recursive call is applied to the subterm and
termination is the walk's own. -/

/-- The nodes a memo entry can save a descent of. -/
@[inline] def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

/-- The term of a walk's result (the quotient lifts: the term is fixed
by its subtype). -/
@[inline] def resTerm {c : Expr} {M : Type} (s : Squash ({ r : Expr // r = c } × M)) : Expr :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s

/-- What the term of a walk's result is: the value its subtype names.
Whatever the oracle answered along the way. -/
theorem resTerm_eq {c : Expr} {M : Type} (s : Squash ({ r : Expr // r = c } × M)) :
    resTerm s = c := by
  induction s using Quotient.ind with
  | _ p => exact p.1.2

/-! ## The pointer-keyed memo (task #316)

The oracle memo above (`MemoX`) records a shared node under the
STRUCTURAL key `(e, c)`: one `Prod` allocation per entry, the node's
cached hash mixed with the cursor, a `beq` on every probe (pointer
identity first, then the data word, then the descent), a bucket cons
cell per insert and the rehash train of a table grown from eight
buckets.  The task #314/#315 records attribute what remains of the
oracle's gap against the budget on `magma-list-pair-n21` (+13.6 …
+17.9 %) to exactly that per-entry price on the shared nodes of small
walks.  The C++ kernel's `replace_fn` pays none of it: its cache is an
`unordered_map` keyed on the raw `expr` pointer and the offset.

This is that memo in Lean: the key is the node's ADDRESS (`withPtrAddr`,
`Init.Util`) packed with the cursor into one `Nat` (`pkey`: addresses
are 8-byte aligned, so `addr / 8`, then the cursor modulo `2^16` in
the low bits — a scalar, no allocation), and a hit is VALIDATED by
pointer identity of the stored node with the current one
(`Expr.ptrDec`, i.e. `withPtrEqDecEq`: one comparison at runtime, the
structural decision in the model) plus a cursor compare.  **No table
invariant**: every entry (`PEnt`) carries its own proof that its value
is the plain descent of its node at its cursor — the `BeqMap`/`EqPair`
shape of `Expr.beqGo` — so a validated hit yields the proof the walk's
result type demands by rewriting along the two equalities, and the
address is never trusted: a key collision (an address reused within
one walk cannot happen — every recorded node is held by the table —
but nothing here depends on that) fails validation and is a miss.
That is what discharges `withPtrAddr`'s obligation: the continuation
returns a `Squash`, and its value is the plain descent whatever the
address (`Subsingleton.elim`, as `Expr.withAddr` already asks).

Two tables behind one switch (`walkPtrTable`): `.hash`, a
`Std.HashMap` on the packed key under a mixing hash (the address bits
are dense; `hash64` is what `Lean.Ptr` uses) — the incumbent's table
with the key changed, one `Prod`-free insert; and `.flat`, an
open-addressing table of two parallel arrays (`keys : Array Nat`,
tagged scalars, `0` = empty; `ents : Array (PEnt s)`), power-of-two
capacity from 16, Fibonacci hashing on the packed key, linear probing,
doubled at half load by re-probing every entry — no bucket cells, no
per-key allocation beyond the entry itself, no cutoff, growth only.
The walks (`*XP`) are the oracle walks (`*X`) verbatim over `MemoXP`
in place of `MemoX`; the memo is `none` until the first shared
compound node, as before, and the switch is a compile-time constant
the wrappers fold.  Nothing here adds to the trust surface: the two
address primitives are `Init.Util`'s and the oracle's is task #314's. -/

/-- The packed key: the node's address over its 8-byte alignment,
then the cursor modulo `2^16` in the low bits.  Pure `UInt64` register
arithmetic; a tagged scalar as a `Nat` (addresses are below `2^47`).
In the model the address is `0` and the key is the cursor — the
tables never rely on the key: an entry validates itself. -/
@[inline] def pkey (addr : USize) (c : Nat) : Nat :=
  (addr.toUInt64 / 8 * 65536 + (UInt64.ofNat c &&& 65535)).toNat

/-- A memo entry: the node it was made for, its rebuild, the cursor,
and the proof — the entry is its own invariant. -/
structure PEnt (s : Expr → Nat → Expr) where
  node : Expr
  val : Expr
  depth : Nat
  eq : val = s node depth

/-- A validated hit: the cursor compares equal and the stored node IS
the current one (by pointer at runtime — `Expr.ptrDec` — structurally
in the model); then the entry's proof is the walk's. -/
@[inline] def PEnt.hit {s : Expr → Nat → Expr} {β : Sort u} (p : PEnt s) (e : Expr) (c : Nat)
    (k : { r : Expr // r = s e c } → β) (miss : Unit → β) : β :=
  if hd : p.depth = c then
    match Expr.ptrDec p.node e with
    | isTrue hn => k ⟨p.val, by rw [p.eq, hn, hd]⟩
    | isFalse _ => miss ()
  else miss ()

/-- The hash-map variant's key: the packed `Nat` under a MIXING hash —
the identity hash of `Nat` clusters dense address bits after Std's
fold (the intern table's lesson, task #89). -/
structure PKey where
  val : Nat

instance : BEq PKey := ⟨fun a b => a.val == b.val⟩
instance : Hashable PKey := ⟨fun k => hash64 (UInt64.ofNat k.val)⟩

/-- The hash-map table: the incumbent's `Std.HashMap`, keyed by the
packed address instead of the structural pair. -/
abbrev HTab (s : Expr → Nat → Expr) := Std.HashMap PKey (PEnt s)

/-- The pointer-keyed memo: absent until the first shared compound
node. -/
abbrev MemoXP (s : Expr → Nat → Expr) := Option (HTab s)

/-- A pointer-keyed walk's result: the term, fixed by its proof,
beside the memo. -/
abbrev ResXP (s : Expr → Nat → Expr) (e : Expr) (c : Nat) :=
  { r : Expr // r = s e c } × MemoXP s

/-- The record: the entry under its packed key, in the table or in a
fresh one. -/
@[inline] def MemoXP.insert {s : Expr → Nat → Expr} (memo : MemoXP s) (key : Nat)
    (p : PEnt s) : MemoXP s :=
  match memo with
  | none => some (({} : HTab s).insert ⟨key⟩ p)
  | some m => some (m.insert ⟨key⟩ p)

/-- The shared-node step over the pointer-keyed memo: the address
read, the probe, the validated hit — else the descent and the record
under the key read BEFORE the descent (the result is a `Squash`, so
the address is unobservable: `withAddr`). -/
@[inline] def MemoXP.shared {s : Expr → Nat → Expr} (memo : MemoXP s) (e : Expr) (c : Nat)
    (rec : Unit → Squash (ResXP s e c)) : Squash (ResXP s e c) :=
  withAddr e fun addr =>
  let key := pkey addr c
  match memo with
  | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
      Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)
  | some m =>
    match m[(⟨key⟩ : PKey)]? with
    | some p => p.hit e c (fun r => Squash.mk (r, memo)) fun _ =>
        Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
          Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)
    | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
        Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, r, c, hr⟩)

/-- The cursor-free instance (`instLevelParams`): the cursored memo at
cursor `0`. -/
abbrev MemoXP0 (s : Expr → Expr) := MemoXP (fun e _ => s e)

abbrev ResXP0 (s : Expr → Expr) (e : Expr) := { r : Expr // r = s e } × MemoXP0 s

@[inline] def MemoXP0.shared {s : Expr → Expr} (memo : MemoXP0 s) (e : Expr)
    (rec : Unit → Squash (ResXP0 s e)) : Squash (ResXP0 s e) :=
  MemoXP.shared (s := fun e _ => s e) memo e 0 rec

/-! ### `instantiate1LiftC` (task #214, P4)

The capture-avoiding substitution `Expr.instantiate1Lift` — the one
substitution on the direct install's executed path with no memoised
twin: `structProjBodies` runs it once per field over the constructor
telescope, turning a DAG-shared field type into an unshared tree each
time.  The twin has the `bvarB` cutoff (a node bounded at or below the
cursor is returned unchanged), a BUDGETED plain descent first (4096
nodes, allocation-free of any memo table — the memo would be a tax on
the small terms that are the common case, cf. the +33 % an
unconditional instantiate memo cost on init-prelude), and the memoised
descent only past the budget.  `instantiate1LiftC_spec`
(`ConLeche/Verify/Cached/OpsC.lean`) reads it as `Expr.instantiate1Lift`. -/

/-- The plain descent of `instantiate1LiftC` (task #314; the reference
of `instantiate1LiftX`). -/
def instantiate1LiftP (v : Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. =>
    if i = d then Expr.liftLooseBVars d 0 v else if i > d then Expr.mkBvar (i - 1) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiate1LiftP v f d) (instantiate1LiftP v a d)
  | .lam ty body m .. =>
    mkLam (instantiate1LiftP v ty d) (instantiate1LiftP v body (d + 1)) m
  | .forallE ty body m .. =>
    mkForallE (instantiate1LiftP v ty d) (instantiate1LiftP v body (d + 1)) m
  | .letE ty val body .. =>
    mkLetE (instantiate1LiftP v ty d) (instantiate1LiftP v val d)
      (instantiate1LiftP v body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiate1LiftP v sub d)

theorem instantiate1LiftP_cut {v e : Expr} {d : Nat} (h : e.bvarB ≤ d) :
    instantiate1LiftP v e d = e := by
  rw [instantiate1LiftP.eq_def]; simp [h]

/-- (Task #316.) The child step of `instantiate1LiftXP`: the pointer-keyed twin of `enterLift`. -/
@[inline] def enterLiftP (v : @& Expr) (e : @& Expr) (d : Nat)
    (memo : MemoXP (instantiate1LiftP v))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiate1LiftP v) e d)) :
    Squash (ResXP (instantiate1LiftP v) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiate1LiftP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The oracle walk of `instantiate1LiftC`. -/
def instantiate1LiftXP (v : @& Expr) (memo : MemoXP (instantiate1LiftP v)) (e : @& Expr)
    (d : Nat) (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiate1LiftP v) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i = d then Expr.liftLooseBVars d 0 v
        else if i > d then Expr.mkBvar (i - 1) else .bvar i,
      by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiate1LiftP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLiftP v f d memo (fun h => instantiate1LiftXP v memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLiftP v a d memo (fun h => instantiate1LiftXP v memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiate1LiftP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [instantiate1LiftP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [instantiate1LiftP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLiftP v ty d memo (fun h => instantiate1LiftXP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP v val d memo (fun h => instantiate1LiftXP v memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLiftP v body (d + 1) memo (fun h => instantiate1LiftXP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiate1LiftP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLiftP v sub d memo (fun h => instantiate1LiftXP v memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiate1LiftP]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiate1Lift`: the cutoff, then the walk. -/
def instantiate1LiftC (e : @& Expr) (v : Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiate1LiftXP v none e d hcut)

/-- The plain descent of `instantiate1C`: the reference the oracle
walk is verified against (`instantiate1P_spec`, `Verify/Cached/OpsC.lean`,
is the equation to `Expr.instantiate1`). -/
def instantiate1P (v : Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. => if i = d then v else if i > d then Expr.mkBvar (i - 1) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiate1P v f d) (instantiate1P v a d)
  | .lam ty body m .. => mkLam (instantiate1P v ty d) (instantiate1P v body (d + 1)) m
  | .forallE ty body m .. =>
    mkForallE (instantiate1P v ty d) (instantiate1P v body (d + 1)) m
  | .letE ty val body .. =>
    mkLetE (instantiate1P v ty d) (instantiate1P v val d) (instantiate1P v body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiate1P v sub d)

theorem instantiate1P_cut {v e : Expr} {d : Nat} (h : e.bvarB ≤ d) :
    instantiate1P v e d = e := by
  rw [instantiate1P.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instantiate1XP`: the cutoff, the compound test,
the oracle. -/
@[inline] def enter1P (v : @& Expr) (e : @& Expr) (d : Nat) (memo : MemoXP (instantiate1P v))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiate1P v) e d)) :
    Squash (ResXP (instantiate1P v) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiate1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The oracle walk of `instantiate1C` (the node is past the cutoff:
the wrapper and `enter1P` test it). -/
def instantiate1XP (v : @& Expr) (memo : MemoXP (instantiate1P v)) (e : @& Expr) (d : Nat)
    (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiate1P v) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i = d then v else if i > d then Expr.mkBvar (i - 1) else .bvar i,
      by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enter1P v f d memo (fun h => instantiate1XP v memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enter1P v a d memo (fun h => instantiate1XP v memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiate1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [instantiate1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [instantiate1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v val d memo (fun h => instantiate1XP v memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiate1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enter1P v sub d memo (fun h => instantiate1XP v memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiate1P]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiate1`: the cutoff, then the walk. -/
def instantiate1C (e : @& Expr) (v : Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiate1XP v none e d hcut)

/-- The plain descent of `instantiateListC` (task #314; the reference of
`instantiateListX`, `instantiateListBC` without the fuel). -/
def instantiateListP (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then w
          else instantiateListP vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => mkApp (instantiateListP vs f k d) (instantiateListP vs a k d)
    | .lam ty body m .. => mkLam (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1)) m
    | .forallE ty body m .. =>
      mkForallE (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1)) m
    | .letE ty val body .. =>
      mkLetE (instantiateListP vs ty k d) (instantiateListP vs val k d) (instantiateListP vs body k (d + 1))
    | .proj sn i sub .. => mkProj sn i (instantiateListP vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instantiateListP_cut {vs : Array Expr} {e : Expr} {k d : Nat} (h : e.bvarB ≤ d) :
    instantiateListP vs e k d = e := by
  rw [instantiateListP.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instantiateListXP` (`k` is the parent's live prefix). -/
@[inline] def enterListP (vs : @& Array Expr) (e : @& Expr) (k d : Nat)
    (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (fun e d => instantiateListP vs e k d) e d)) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateListP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The oracle walk of the bulk instantiation (the `bvar` arm's
re-entry at a replacement runs under a fresh memo, as the memoised
walk's does — `MemoNL`). -/
def instantiateListXP (vs : @& Array Expr) (k : Nat) (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (e : @& Expr) (d : Nat) (hk : ¬ k = 0) (hcut : ¬ e.bvarB ≤ d) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  match e with
  | .bvar i .. =>
    if hi : i < d then Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi]⟩, memo)
    else if _h : i - d < k then
      if h : i - d < vs.size then
        let w := vs[i - d]
        if h0 : i - d = 0 || w.bvarB ≤ d then
          Squash.mk (⟨w, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0]⟩, memo)
        else
          have h0' : ¬ i - d = 0 ∧ ¬ w.bvarB ≤ d := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or] using h0
          instantiateListXP vs (i - d) none w d h0'.1 h0'.2 |>.lift fun (⟨r, hr⟩, _) =>
          Squash.mk (⟨r, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0, hr]⟩, memo)
      else Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h]⟩, memo)
    else Squash.mk (⟨Expr.mkBvar (i - k), by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut]⟩, memo)
  | .app f a .. =>
    enterListP vs f k d memo (fun h => instantiateListXP vs k memo f d hk h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterListP vs a k d memo (fun h => instantiateListXP vs k memo a d hk h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterListP vs ty k d memo (fun h => instantiateListXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs val k d memo (fun h => instantiateListXP vs k memo val d hk h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterListP vs body k (d + 1) memo (fun h => instantiateListXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterListP vs sub k d memo (fun h => instantiateListXP vs k memo sub d hk h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hs, mkProj]⟩, memo)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- The cached `Expr.instantiateList` (bulk): the cutoff, then the walk. -/
def instantiateListC (e : @& Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match vs with
  | [] => e
  | v :: vs' =>
    let a := (v :: vs').toArray
    if hcut : e.bvarB ≤ d then e
    else resTerm (instantiateListXP a a.size none e d (by simp [a]) hcut)

/-- The plain descent of `instantiateRev` (task #314; as `instantiateListP`
on the reversed array). -/
def instantiateRevP (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[vs.size - 1 - (i - d)]'(by omega)
          if i - d = 0 || w.bvarB ≤ d then w
          else instantiateRevP vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => mkApp (instantiateRevP vs f k d) (instantiateRevP vs a k d)
    | .lam ty body m .. => mkLam (instantiateRevP vs ty k d) (instantiateRevP vs body k (d + 1)) m
    | .forallE ty body m .. =>
      mkForallE (instantiateRevP vs ty k d) (instantiateRevP vs body k (d + 1)) m
    | .letE ty val body .. =>
      mkLetE (instantiateRevP vs ty k d) (instantiateRevP vs val k d) (instantiateRevP vs body k (d + 1))
    | .proj sn i sub .. => mkProj sn i (instantiateRevP vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instantiateRevP_cut {vs : Array Expr} {e : Expr} {k d : Nat} (h : e.bvarB ≤ d) :
    instantiateRevP vs e k d = e := by
  rw [instantiateRevP.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instantiateRevXP` (`k` is the parent's live prefix). -/
@[inline] def enterRevP (vs : @& Array Expr) (e : @& Expr) (k d : Nat)
    (memo : MemoXP (fun e d => instantiateRevP vs e k d))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (fun e d => instantiateRevP vs e k d) e d)) :
    Squash (ResXP (fun e d => instantiateRevP vs e k d) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateRevP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut

/-- The oracle walk of the bulk instantiation (the `bvar` arm's
re-entry at a replacement runs under a fresh memo, as the memoised
walk's does — `MemoNL`). -/
def instantiateRevXP (vs : @& Array Expr) (k : Nat) (memo : MemoXP (fun e d => instantiateRevP vs e k d))
    (e : @& Expr) (d : Nat) (hk : ¬ k = 0) (hcut : ¬ e.bvarB ≤ d) :
    Squash (ResXP (fun e d => instantiateRevP vs e k d) e d) :=
  match e with
  | .bvar i .. =>
    if hi : i < d then Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi]⟩, memo)
    else if _h : i - d < k then
      if h : i - d < vs.size then
        let w := vs[vs.size - 1 - (i - d)]'(by omega)
        if h0 : i - d = 0 || w.bvarB ≤ d then
          Squash.mk (⟨w, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0]⟩, memo)
        else
          have h0' : ¬ i - d = 0 ∧ ¬ w.bvarB ≤ d := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or] using h0
          instantiateRevXP vs (i - d) none w d h0'.1 h0'.2 |>.lift fun (⟨r, hr⟩, _) =>
          Squash.mk (⟨r, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0, hr]⟩, memo)
      else Squash.mk (⟨.bvar i, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h, h]⟩, memo)
    else Squash.mk (⟨Expr.mkBvar (i - k), by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hi, _h]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut]⟩, memo)
  | .app f a .. =>
    enterRevP vs f k d memo (fun h => instantiateRevXP vs k memo f d hk h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterRevP vs a k d memo (fun h => instantiateRevXP vs k memo a d hk h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterRevP vs ty k d memo (fun h => instantiateRevXP vs k memo ty d hk h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRevP vs val k d memo (fun h => instantiateRevXP vs k memo val d hk h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterRevP vs body k (d + 1) memo (fun h => instantiateRevXP vs k memo body (d + 1) hk h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterRevP vs sub k d memo (fun h => instantiateRevXP vs k memo sub d hk h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by dsimp only; rw [instantiateRevP.eq_def]; simp [hk, hcut, hs, mkProj]⟩, memo)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- Bulk instantiation on a reversed accumulator array: the cutoffs,
then the walk. -/
def instantiateRev (e : @& Expr) (vs : Array Expr) (d : Nat := 0) : Expr :=
  if hk : vs.size = 0 then e
  else if hcut : e.bvarB ≤ d then e
  else resTerm (instantiateRevXP vs vs.size none e d hk hcut)

/-! ## Abstraction -/

/-- The plain descent of `abstract1C` (task #314; the reference of
`abstract1X`). -/
def abstract1P (d : Nat) (e : Expr) (k : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. => if idx = d then Expr.mkBvar k else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstract1P d f k) (abstract1P d a k)
  | .lam ty body m .. => mkLam (abstract1P d ty k) (abstract1P d body (k + 1)) m
  | .forallE ty body m .. => mkForallE (abstract1P d ty k) (abstract1P d body (k + 1)) m
  | .letE ty val body .. =>
    mkLetE (abstract1P d ty k) (abstract1P d val k) (abstract1P d body (k + 1))
  | .proj sn i sub .. => mkProj sn i (abstract1P d sub k)

theorem abstract1P_cut {d : Nat} {e : Expr} {k : Nat} (h : e.fvarB ≤ d) :
    abstract1P d e k = e := by
  rw [abstract1P.eq_def]; simp [h]

/-- (Task #316.) The child step of `abstract1XP`: the pointer-keyed twin of `enterAbs1`. -/
@[inline] def enterAbs1P (d : Nat) (e : @& Expr) (k : Nat) (memo : MemoXP (abstract1P d))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstract1P d) e k)) :
    Squash (ResXP (abstract1P d) e k) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstract1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e k fun _ => rec hcut

/-- The oracle walk of `abstract1C`. -/
def abstract1XP (d : Nat) (memo : MemoXP (abstract1P d)) (e : @& Expr) (k : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstract1P d) e k) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if idx = d then Expr.mkBvar k else .fvar idx ty,
      by rw [abstract1P]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbs1P d f k memo (fun h => abstract1XP d memo f k h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbs1P d a k memo (fun h => abstract1XP d memo a k h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstract1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [abstract1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [abstract1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d val k memo (fun h => abstract1XP d memo val k h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstract1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbs1P d sub k memo (fun h => abstract1XP d memo sub k h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstract1P]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.abstract1`: the cutoff, then the walk. -/
def abstract1C (e : @& Expr) (d : Nat) (k : Nat := 0) : Expr :=
  if hcut : e.fvarB ≤ d then e else
  resTerm (abstract1XP d none e k hcut)

/-- The plain descent of `abstractRangeC` (task #314; the reference of
`abstractRangeX`). -/
def abstractRangeP (d k : Nat) (e : Expr) (c : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. =>
    if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstractRangeP d k f c) (abstractRangeP d k a c)
  | .lam ty body m .. =>
    mkLam (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1)) m
  | .forallE ty body m .. =>
    mkForallE (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1)) m
  | .letE ty val body .. =>
    mkLetE (abstractRangeP d k ty c) (abstractRangeP d k val c)
      (abstractRangeP d k body (c + 1))
  | .proj sn i sub .. => mkProj sn i (abstractRangeP d k sub c)

theorem abstractRangeP_cut {d k : Nat} {e : Expr} {c : Nat} (h : e.fvarB ≤ d) :
    abstractRangeP d k e c = e := by
  rw [abstractRangeP.eq_def]; simp [h]

/-- (Task #316.) The child step of `abstractRangeXP`: the pointer-keyed twin of `enterAbsR`. -/
@[inline] def enterAbsRP (d k : Nat) (e : @& Expr) (c : Nat) (memo : MemoXP (abstractRangeP d k))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstractRangeP d k) e c)) :
    Squash (ResXP (abstractRangeP d k) e c) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstractRangeP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e c fun _ => rec hcut

/-- The oracle walk of `abstractRangeC`. -/
def abstractRangeXP (d k : Nat) (memo : MemoXP (abstractRangeP d k)) (e : @& Expr) (c : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstractRangeP d k) e c) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx))
        else .fvar idx ty,
      by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbsRP d k f c memo (fun h => abstractRangeXP d k memo f c h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbsRP d k a c memo (fun h => abstractRangeXP d k memo a c h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstractRangeP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' m, by rw [abstractRangeP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' m, by rw [abstractRangeP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k val c memo (fun h => abstractRangeXP d k memo val c h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstractRangeP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbsRP d k sub c memo (fun h => abstractRangeXP d k memo sub c h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstractRangeP]; simp [hcut, hs, mkProj]⟩, memo)

/-- The cached `Expr.abstractRange` (`k = 0` is the identity and skips
the traversal, as in the arena): the cutoff, then the walk. -/
def abstractRangeC (e : @& Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match k with
  | 0 => e
  | _ + 1 =>
    if hcut : e.fvarB ≤ d then e else
    resTerm (abstractRangeXP d k none e c hcut)

/-! ## Level instantiation -/

/-- The plain descent of `instLevelParams` (task #314; the reference of
`instLevelParamsX`). -/
def instLevelParamsP (ks : List Name) (us : List Level) (e : Expr) : Expr :=
  if !e.hasLP then e else
  match e with
  | .bvar .. | .lit .. => e
  | .sort u .. => mkSort (Level.subst ks us u)
  | .const n vs .. => mkConst n (vs.map (Level.subst ks us))
  | .fvar idx ty .. => mkFVar idx (instLevelParamsP ks us ty)
  | .app f a .. => mkApp (instLevelParamsP ks us f) (instLevelParamsP ks us a)
  | .lam ty body m .. =>
    mkLam (instLevelParamsP ks us ty) (instLevelParamsP ks us body) ⟨Level.substPW ks us m.pw⟩
  | .forallE ty body m .. =>
    mkForallE (instLevelParamsP ks us ty) (instLevelParamsP ks us body)
      ⟨Level.substPW ks us m.pw⟩
  | .letE ty val body .. =>
    mkLetE (instLevelParamsP ks us ty) (instLevelParamsP ks us val)
      (instLevelParamsP ks us body)
  | .proj s i sub .. => mkProj s i (instLevelParamsP ks us sub)

theorem instLevelParamsP_cut {ks : List Name} {us : List Level} {e : Expr}
    (h : (!e.hasLP) = true) : instLevelParamsP ks us e = e := by
  rw [instLevelParamsP.eq_def]; simp [h]

/-- (Task #316, the pointer-keyed twin.) The child step of `instLevelParamsXP`: the cutoff, then the oracle —
on EVERY node past the cutoff, as the memoised walk records every one
(a `const` with level parameters is a `Level.subst` per occurrence). -/
@[inline] def enterLPP (ks : @& List Name) (us : @& List Level) (e : @& Expr)
    (memo : MemoXP0 (instLevelParamsP ks us))
    (rec : (hcut : ¬ (!e.hasLP) = true) → Squash (ResXP0 (instLevelParamsP ks us) e)) :
    Squash (ResXP0 (instLevelParamsP ks us) e) :=
  if hcut : (!e.hasLP) = true then Squash.mk (⟨e, (instLevelParamsP_cut hcut).symm⟩, memo)
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e fun _ => rec hcut

/-- The oracle walk of `instLevelParams`. -/
def instLevelParamsXP (ks : @& List Name) (us : @& List Level)
    (memo : MemoXP0 (instLevelParamsP ks us)) (e : @& Expr) (hcut : ¬ (!e.hasLP) = true) :
    Squash (ResXP0 (instLevelParamsP ks us) e) :=
  match e with
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .sort u .. =>
    Squash.mk (⟨mkSort (Level.subst ks us u), by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .const n vs .. =>
    Squash.mk (⟨mkConst n (vs.map (Level.subst ks us)),
      by rw [instLevelParamsP.eq_def, if_neg hcut]⟩, memo)
  | .fvar idx ty .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨t, ht⟩, memo) =>
    Squash.mk (⟨mkFVar idx t, by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, mkFVar]⟩, memo)
  | .app f a .. =>
    enterLPP ks us f memo (fun h => instLevelParamsXP ks us memo f h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLPP ks us a memo (fun h => instLevelParamsXP ks us memo a h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [hf, ha, mkApp]⟩, memo)
  | .lam ty body m .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b' ⟨Level.substPW ks us m.pw⟩,
      by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hb, mkLam]⟩, memo)
  | .forallE ty body m .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b' ⟨Level.substPW ks us m.pw⟩,
      by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLPP ks us ty memo (fun h => instLevelParamsXP ks us memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLPP ks us val memo (fun h => instLevelParamsXP ks us memo val h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLPP ks us body memo (fun h => instLevelParamsXP ks us memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLPP ks us sub memo (fun h => instLevelParamsXP ks us memo sub h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instLevelParamsP.eq_def, if_neg hcut]; simp only [hs, mkProj]⟩, memo)

/-- The cached `Expr.instantiateLevelParams`: the cutoff, then the
walk. -/
def instLevelParams (ks : List Name) (us : List Level) (e : @& Expr) : Expr :=
  if hcut : (!e.hasLP) = true then e else
  resTerm (instLevelParamsXP ks us none e hcut)

/-- The cached `ProjEntry.typeAt`: the same two instantiations through
the memoized, **sharing-preserving** `instLevelParams` and
`instantiateListC` (`ProjEntry.typeAtI_eq`, `ConLeche/Verify/Cached/
OpsC.lean`, is the equation).

The executable `.proj` inference clause used to call the spec's
`ProjEntry.typeAt` directly — legitimate as a *value* (`Expr = Expr`)
but not as a *computation*: `Expr.instantiateList` is the unmemoized
tree walk, and its `bvar` arm re-traverses the replacement (`vs[j - d]`
under `vs.take (j - d)`), so every occurrence of the subject and of
every parameter in the field type came back as a fresh **tree copy**
of a term that was a DAG.  On a projection chain over a Mathlib
carrier (`(Classical.choice …).ColimitCocone.0.Cocone.0.CommRingCat.0`)
the copies nest, and at `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`
(subject tree 3.9 · 10⁸ nodes on a 3 106-node DAG) the copy alone is
the out-of-memory — DESIGN.md "The affine frontier". -/
def _root_.ConLeche.ProjEntry.typeAtI (entry : ProjEntry) (us : List Level)
    (targs : List Expr) (pe : Expr) : Expr :=
  instantiateListC (instLevelParams entry.levelParams us entry.body)
    (pe :: targs.reverse)

/-! ## Scope queries -/

/-- Core of `wscopedBC` (memoized; `fvar` annotations are descended,
so the cached fvar range does not decide it). -/
def wscopedBGoC (memo : Std.HashMap (Expr × Nat) Bool) (d : Nat)
    (e : Expr) : Bool × Std.HashMap (Expr × Nat) Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[(e, d)]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap (Expr × Nat) Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx ty .. =>
        if idx < d then wscopedBGoC memo idx ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := wscopedBGoC memo d f
        if rf then wscopedBGoC memo d a else (false, memo)
      | .lam ty body _ .. | .forallE ty body _ .. =>
        let (rt, memo) := wscopedBGoC memo d ty
        if rt then wscopedBGoC memo d body else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := wscopedBGoC memo d ty
        if rt then
          let (rv, memo) := wscopedBGoC memo d val
          if rv then wscopedBGoC memo d body else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => wscopedBGoC memo d sub
    (r, memo.insert (e, d) r)

/-- The cached `Expr.wscopedB d` (one memoized DAG walk). -/
def wscopedBC (d : Nat) (e : Expr) : Bool := (wscopedBGoC {} d e).1

/-- Core of `fvarLeavesC` (memoized set accumulation). -/
def fvarLeavesGoC (acc : List (Nat × Expr))
    (seen : Std.HashMap Expr Unit) (e : Expr) :
    List (Nat × Expr) × Std.HashMap Expr Unit :=
  if e.fvarB == 0 then (acc, seen) else
  match seen[e]? with
  | some _ => (acc, seen)
  | none =>
    let seen := seen.insert e ()
    match e with
    | .bvar .. | .sort .. | .const .. | .lit .. => (acc, seen)
    | .fvar idx ty .. => fvarLeavesGoC ((idx, ty) :: acc) seen ty
    | .app f a .. =>
      let (acc, seen) := fvarLeavesGoC acc seen f
      fvarLeavesGoC acc seen a
    | .lam ty body _ .. | .forallE ty body _ .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      fvarLeavesGoC acc seen body
    | .letE ty val body .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      let (acc, seen) := fvarLeavesGoC acc seen val
      fvarLeavesGoC acc seen body
    | .proj _ _ sub .. => fvarLeavesGoC acc seen sub

/-- The reachable `fvar` leaves (hereditarily through annotations). -/
def fvarLeavesC (e : Expr) : List (Nat × Expr) :=
  (fvarLeavesGoC [] {} e).1

/-- Is `(idx, ty)` in the base leaf list?  Compares the annotation
with `Expr.beq` (pointer-first). -/
def leafMem : List (Nat × Expr) → Nat → Expr → Bool
  | [], _, _ => false
  | (i, t) :: rest, idx, ty =>
    (i == idx && t == ty) || leafMem rest idx ty

/-- Core of the fabrication-side leaf-subset test (task #86). -/
def leavesSubGo (bl : List (Nat × Expr))
    (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap Expr Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx ty .. =>
        if leafMem bl idx ty then leavesSubGo bl memo ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := leavesSubGo bl memo f
        if rf then leavesSubGo bl memo a else (false, memo)
      | .lam ty body _ .. | .forallE ty body _ .. =>
        let (rt, memo) := leavesSubGo bl memo ty
        if rt then leavesSubGo bl memo body else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := leavesSubGo bl memo ty
        if rt then
          let (rv, memo) := leavesSubGo bl memo val
          if rv then leavesSubGo bl memo body else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => leavesSubGo bl memo sub
    (r, memo.insert e r)

/-- The fabrication leaf guard: every `fvar` leaf of `fab` is one of
`base` (short-circuits on `fvar`-free fabrications, `O(1)` off the
cached range). -/
def leafGuard (fab base : Expr) : Bool :=
  !fab.hasFvar || (leavesSubGo (fvarLeavesC base) {} fab).1

/-! ## Telescope operations -/

/-- The `instantiate1C` chain of `Expr.instSpine`. -/
def instSpineChainC : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpineChainC as (t - 1) (instantiate1C e a t)

/-- The cached `Expr.instSpine` (bulk when the spine spans the
telescope context, the chain otherwise). -/
def instSpineC (args : List Expr) (t : Nat) (e : Expr) : Expr :=
  if args.length = t + 1 then instantiateListC e args.reverse 0
  else instSpineChainC args t e

/-- Core of `piResidual` (bulk form, task #50).

Not structural: the `bvar` arm re-enters on the same argument list with
the accumulator flushed.  Measure `(as.length, acc.length)` — the
`forallE` arm consumes an argument, the `bvar` arm keeps the arguments
and empties a nonempty accumulator. -/
def piResidualAcc : List Expr → Expr → List Expr → Option Expr
  | acc, e, [] => some (instantiateListC e acc 0)
  | acc, e, a :: as =>
    match e with
    | .forallE _ b _ .. => piResidualAcc (a :: acc) b as
    | .bvar .. =>
      match acc with
      | [] => none
      | _ :: _ => piResidualAcc [] (instantiateListC e acc 0) (a :: as)
    | _ => none
termination_by acc _ as => (as.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)

@[inherit_doc piResidualAcc]
def piResidual (e : Expr) (args : List Expr) : Option Expr :=
  piResidualAcc [] e args

/-! ## Level-parameter definedness (the parsed-index driver's guard) -/

/-- Core of `allLevelParamsDefinedC` (memoized; nodes without a level
parameter are `true` without traversal — the `hasLP` cutoff). -/
def allLevelParamsDefinedGoC (params : List Name)
    (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  if !e.hasLP then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap Expr Bool :=
      match e with
      | .bvar .. | .lit .. => (true, memo)
      | .sort u .. => (Level.allParamsDefined params u, memo)
      | .const _ us .. => (us.all (Level.allParamsDefined params), memo)
      | .fvar _ ty .. => allLevelParamsDefinedGoC params memo ty
      | .app f a .. =>
        let (rf, memo) := allLevelParamsDefinedGoC params memo f
        if rf then allLevelParamsDefinedGoC params memo a else (false, memo)
      | .lam ty body m .. | .forallE ty body m .. =>
        let (rt, memo) := allLevelParamsDefinedGoC params memo ty
        if rt then
          let (rb, memo) := allLevelParamsDefinedGoC params memo body
          (rb && m.pw.paramsDefined params, memo)
        else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := allLevelParamsDefinedGoC params memo ty
        if rt then
          let (rv, memo) := allLevelParamsDefinedGoC params memo val
          if rv then allLevelParamsDefinedGoC params memo body
          else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => allLevelParamsDefinedGoC params memo sub
    (r, memo.insert e r)

/-- The cached `Expr.allLevelParamsDefined params` (one memoized DAG
walk). -/
def allLevelParamsDefinedC (params : List Name) (e : Expr) : Bool :=
  (allLevelParamsDefinedGoC params {} e).1

end ConLeche.Expr
