module

public import Std.Data.HashSet.Basic
public import ConLeche.Kernel.Core

@[expose] public section

/-!
# Hoisting a pinned `Nat` operation's stream-certified ground (task #191)

The second half of the order-insensitivity fix, beside the built-in
prelude (`ConLeche/Frontend/Prelude.lean`).

A pin-certified operation's certificate *statements* are spelled over
the structural `Nat` operations (`natOpDeps`: `Nat.shiftLeft`'s over
`Nat.ble` and `Nat.sub`, `Nat.land`'s over `Nat.mul`, …), and the
install guard `divModEnvGuard` requires those stored — they are what
the model reads the statements through.  They are NOT in the
operation's own dependency closure, so an export that orders
declarations by a DFS from arbitrary roots (`lean4export` walks
`env.constants` in hash order; the raw export of
`tests/e2e/src/natop_order.lean` emits `Nat.shiftLeft` before
`Nat.ble`/`Nat.sub`/`Bool`) declined at the install.

They cannot go into the prelude: the structural operations are
certified at install by *definitional* recurrence equations
(`certifyNatEqs`) — deliberately not by a syntactic pin, so that a
stream from another toolchain still installs them (`Nat.add` gained a
separate `._f` functional between the 4.29 fixtures and the 4.33
build; a syntactic prelude copy would decline every 4.29 stream,
`good/init-prelude` included).  So instead the parsed stream is
REORDERED: for every pinned operation record whose `natOpDeps` ground
is declared LATER in the stream, the ground's transitive dependency
closure (within the stream) is moved ahead of the operation.  A
dependency-closed set moved earlier is still a valid stream — every
record still follows everything it references, and the moved records
see exactly their own closure (plus the prelude) — so the checker's
verdict on a valid stream is the official kernel's, whatever order the
export chose.  Like the prelude prepend it sits beside, this is a pure transformation
of the parsed list below the verified fold — a step of
`preparePrelude` (`ConLeche/Frontend/Prepare.lean`), not of the parse:
nothing in the kernel or the proofs knows it happened.

The pass is a no-op — the array is returned as it is, no sort — on
every stream whose ground precedes its operations (the toolchain's own
export order: `init-full`, Mathlib), so it costs one name-index build
and nothing else there.
-/

namespace ConLeche.Frontend

open ConLeche

/-- The constants an `Expr` DAG references, each node visited once
(`Std.HashSet Expr`: pointer-first equality, computed hash). -/
def usedConstsGo (seen : Std.HashSet Expr) (acc : Array Name) (e : Expr) :
    Std.HashSet Expr × Array Name :=
  if seen.contains e then (seen, acc) else
  let seen := seen.insert e
  match e with
  | .const n _ .. => (seen, acc.push n)
  | .app f a .. =>
    let (seen, acc) := usedConstsGo seen acc f
    usedConstsGo seen acc a
  | .lam ty b _ .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    usedConstsGo seen acc b
  | .forallE ty b _ .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    usedConstsGo seen acc b
  | .letE ty v b .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    let (seen, acc) := usedConstsGo seen acc v
    usedConstsGo seen acc b
  | .proj sn _ x .. => usedConstsGo seen (acc.push sn) x
  | .fvar _ ty .. => usedConstsGo seen acc ty
  | _ => (seen, acc)

/-- The constants a parsed record references (types, values, recursor
rule right-hand sides; a basis block references nothing the stream
declares). -/
def _root_.ConLeche.Declaration.usedConsts : Declaration → Array Name
  | .axiomDecl cv => (usedConstsGo {} #[] cv.type).2
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    let (seen, acc) := usedConstsGo {} #[] cv.type
    (usedConstsGo seen acc v).2
  | .indDecl block _ =>
    (block.foldl (init := (({} : Std.HashSet Expr), (#[] : Array Name)))
      fun (seen, acc) ci =>
        let (seen, acc) := usedConstsGo seen acc ci.toConstantVal.type
        match ci with
        | .recInfo _ _ _ rules =>
          rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) (seen, acc)
        | _ => (seen, acc)).2
  | .basisDecl _ | .quotDecl .. => #[]

/-- The pinned `Nat` operation records whose ground the pass serves:
the pin-certified WF operations and the structural ones (whose
`natOpDeps` are in their own closures already — kept uniform). -/
def isNatOpRecord : Declaration → Option Name
  | .defnDecl cv .. =>
    if natDivModNames.contains cv.name || natOpNames.contains cv.name then some cv.name
    else none
  | _ => none

/-- What the hoist's gate reads of a record: the names it declares and
whether it is a pinned operation's. -/
def declShape (d : Declaration) : List Name × Option Name := (d.names, isNatOpRecord d)

/-- Name ↦ the index of the first record declaring it (the first, on a
duplicate — the fold rejects the second anyway). -/
def nameIdx (sh : Array (List Name × Option Name)) : Std.HashMap Name Nat := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:sh.size] do
    for n in sh[i]!.1 do
      if !idx.contains n then idx := idx.insert n i
  return idx

/-- **The hoist's gate, from names alone** (task #329): some pinned
operation's ground name is declared by a LATER record.  Without it the
hoist is the identity, and nothing reads a record's types or values to
know it. -/
def lateI (idx : Std.HashMap Name Nat) (sh : Array (List Name × Option Name)) : Bool := Id.run do
  let mut late := false
  for i in [0:sh.size] do
    let some c := sh[i]!.2 | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      if j > i then late := true
  return late

/-- The gate on the records' shapes. -/
def groundLateS (sh : Array (List Name × Option Name)) : Bool := lateI (nameIdx sh) sh

/-- The gate on a record array. -/
def groundLate (ds : Array Declaration) : Bool := groundLateS (ds.map declShape)

/-! ### The targets, over a lookup of the records' constants

The walk reads the constants of the records it moves through `uc`
(record index ↦ its constants, `none` when they are not known), and
nothing else of a record: the serial preparation hands it every
record's `usedConsts`; the lazy driver's records leave a theorem's
unknown (its value is not built), and a walk that meets one does not
finish (`none`).  A walk that finishes reads only records whose
constants are known, so it is the serial walk (`hoistTargetsU_mono`,
`ConLeche/Verify/Frontend/LazyPrepare.lean`). -/

/-- The records record `k`'s constants bring into the walk (those
declared after the operation at `i`), pushed onto the stack. -/
def hoistPushes (idx : Std.HashMap Name Nat) (i k : Nat) (us : Array Name) (st : List Nat) :
    List Nat :=
  us.foldl (fun st n => match idx[n]? with
    | some m => if m > i && m != k then m :: st else st
    | none => st) st

/-- Record `k` already moves at least as far as the operation at `i`. -/
@[inline] def movedBy (t : Std.HashMap Nat Nat) (k i : Nat) : Bool :=
  match t[k]? with
  | some tk => decide (tk ≤ i)
  | none => false

/-- The closure of the operation at `i`, within the records after it:
each record popped is moved to `i` unless it already moves at least as
far, and its constants' records are pushed. -/
def hoistWalk (idx : Std.HashMap Name Nat) (uc : Nat → Option (Array Name)) (i : Nat) :
    Nat → List Nat → Std.HashMap Nat Nat → Option (Std.HashMap Nat Nat)
  | 0, _, _ => none
  | _ + 1, [], t => some t
  | fuel + 1, k :: st, t =>
    if movedBy t k i then hoistWalk idx uc i fuel st t
    else
      match uc k with
      | some us => hoistWalk idx uc i fuel (hoistPushes idx i k us st) (t.insert k i)
      | none => none

/-- The walk's step budget: far beyond any stream. -/
@[noinline] def hoistFuel : Nat := 1 <<< 62

/-- The ground names of the operation at `i`, each declared after it,
walked. -/
def hoistDeps (idx : Std.HashMap Name Nat) (uc : Nat → Option (Array Name)) (i : Nat) :
    List Name → Std.HashMap Nat Nat → Option (Std.HashMap Nat Nat)
  | [], t => some t
  | g :: gs, t =>
    match idx[g]? with
    | some j =>
      if j > i then
        match hoistWalk idx uc i hoistFuel [j] t with
        | some t => hoistDeps idx uc i gs t
        | none => none
      else hoistDeps idx uc i gs t
    | none => hoistDeps idx uc i gs t

/-- Every pinned operation from record `i` on. -/
def hoistOps (sh : Array (List Name × Option Name)) (idx : Std.HashMap Name Nat)
    (uc : Nat → Option (Array Name)) (i : Nat) (t : Std.HashMap Nat Nat) :
    Option (Std.HashMap Nat Nat) :=
  if i < sh.size then
    match sh[i]!.2 with
    | some c =>
      match hoistDeps idx uc i (natOpDeps c) t with
      | some t => hoistOps sh idx uc (i + 1) t
      | none => none
    | none => hoistOps sh idx uc (i + 1) t
  else some t
termination_by sh.size - i

/-- **Which records must move, and how far**, over a lookup of the
records' constants: the map from a record's index to the earliest
pinned-operation index it must precede — empty, without reading `uc`,
when the names-only gate is closed. -/
def hoistPlan (sh : Array (List Name × Option Name)) (uc : Nat → Option (Array Name)) :
    Option (Std.HashMap Nat Nat) :=
  let idx := nameIdx sh
  if lateI idx sh then hoistOps sh idx uc 0 {} else some {}

/-- **Which records must move, and how far**: the map from a record's
index to the earliest pinned-operation index it must precede.  Empty —
and then the hoist is the identity — on every stream whose ground
precedes its operations, which the names-only gate decides first. -/
def hoistTargets (ds : Array Declaration) : Std.HashMap Nat Nat :=
  (hoistPlan (ds.map declShape) (fun k => some ds[k]!.usedConsts)).getD {}

/-- **The reorder**: a moved record sorts at its target, just ahead of
the operation record there (key `(t, 0, k)` against the operation's
`(t, 1, t)`); everything else keeps its position (`(k, 1, k)`).  Moved
records with the same target keep their relative order, which is
dependency order.

The sort is `List.mergeSort` and not `Array.qsort` for one reason: the
result is a PERMUTATION of the input, and that is a property the
prepared list's shape lemma states (`mergeSort_perm`,
`ConLeche/Verify/Frontend/Prepare.lean`).  The keys are pairwise
distinct (each carries its own index), so the order is the same one
`qsort` produced. -/
def applyHoist (ds : Array Declaration) (target : Std.HashMap Nat Nat) :
    Array Declaration × Array Name :=
  let key : Nat → Nat × Nat × Nat := fun k =>
    match target[k]? with
    | some t => (t, 0, k)
    | none => (k, 1, k)
  let lt : Nat → Nat → Bool := fun a b =>
    let (ta, sa, ka) := key a
    let (tb, sb, kb) := key b
    ta < tb || (ta == tb && (sa < sb || (sa == sb && ka < kb)))
  let order := (List.range ds.size).mergeSort (fun a b => !lt b a)
  let moved := (Array.range ds.size).filter (target.contains ·)
  ((order.map (ds[·]!)).toArray, moved.flatMap fun k => (ds[k]!.names).toArray)

/-- **The hoist.**  Returns the reordered records and the names of the
records moved (empty, and the array untouched, when no operation's
ground is declared after it). -/
def hoistNatOpGround (ds : Array Declaration) : Array Declaration × Array Name :=
  let target := hoistTargets ds
  if target.isEmpty then (ds, #[]) else applyHoist ds target

end ConLeche.Frontend
