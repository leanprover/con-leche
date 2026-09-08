module

public import Std.Data.HashSet.Basic
public import ConLeche.Cached.ParsedC

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
export chose.  Like the prelude and the projection rewrite
(`ConLeche/Frontend/ProjRec.lean`), this is a pure transformation of the
parsed list below the verified fold: nothing in the kernel or the
proofs knows it happened.

The pass is a no-op — the array is returned as it is, no sort — on
every stream whose ground precedes its operations (the toolchain's own
export order: `init-full`, Mathlib), so it costs one name-index build
and nothing else there.
-/

namespace ConLeche.Frontend

open ConLeche ConLeche.Cached

/-- For the array indexing below (`ds[i]!`); never observed. -/
instance : Inhabited DeclC := ⟨.basisDecl .eqK⟩

/-- The names a parsed declaration declares (the prelude index and the
hoist's name index; basis blocks are indexed by kind instead). -/
def _root_.ConLeche.Cached.DeclC.names : DeclC → List Name
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

/-- The constants an `ExprC` DAG references, each node visited once
(`Std.HashSet ExprC`: pointer-first equality, computed hash). -/
def usedConstsGo (seen : Std.HashSet ExprC) (acc : Array Name) (e : ExprC) :
    Std.HashSet ExprC × Array Name :=
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
def _root_.ConLeche.Cached.DeclC.usedConsts : DeclC → Array Name
  | .axiomDecl cv => (usedConstsGo {} #[] cv.type).2
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    let (seen, acc) := usedConstsGo {} #[] cv.type
    (usedConstsGo seen acc v).2
  | .indDecl block _ =>
    (block.foldl (init := (({} : Std.HashSet ExprC), (#[] : Array Name)))
      fun (seen, acc) ci =>
        let (seen, acc) := usedConstsGo seen acc ci.toConstantVal.type
        match ci with
        | .recInfo _ _ _ rules =>
          rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) (seen, acc)
        | _ => (seen, acc)).2
  | .basisDecl _ => #[]

/-- The pinned `Nat` operation records whose ground the pass serves:
the pin-certified WF operations and the structural ones (whose
`natOpDeps` are in their own closures already — kept uniform). -/
def isNatOpRecord : DeclC → Option Name
  | .defnDecl cv .. =>
    if natDivModNames.contains cv.name || natOpNames.contains cv.name then some cv.name
    else none
  | _ => none

/-- **The hoist.**  Returns the reordered records and the names of the
records moved (empty, and the array untouched, when no operation's
ground is declared after it). -/
def hoistNatOpGround (ds : Array DeclC) : Array DeclC × Array Name := Id.run do
  -- name ↦ the index of the record declaring it (the first, on a
  -- duplicate — the fold rejects the second anyway)
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:ds.size] do
    for n in ds[i]!.names do
      if !idx.contains n then idx := idx.insert n i
  -- moved record ↦ the earliest operation index it must precede
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:ds.size] do
    let some c := isNatOpRecord ds[i]! | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      unless j > i do continue
      -- the closure of `j` within the records after `i`
      let mut stack : Array Nat := #[j]
      while h : stack.size > 0 do
        let k := stack[stack.size - 1]
        stack := stack.pop
        match target[k]? with
        | some t => if t ≤ i then continue
        | none => pure ()
        target := target.insert k i
        for n in ds[k]!.usedConsts do
          if let some m := idx[n]? then
            if m > i && m != k then stack := stack.push m
  if target.isEmpty then return (ds, #[])
  -- the order: a moved record sorts at its target, just ahead of the
  -- operation record there (key `(t, 0, k)` against the operation's
  -- `(t, 1, t)`); everything else keeps its position (`(k, 1, k)`).
  -- Moved records with the same target keep their relative order,
  -- which is dependency order.
  let key : Nat → Nat × Nat × Nat := fun k =>
    match target[k]? with
    | some t => (t, 0, k)
    | none => (k, 1, k)
  let lt : Nat → Nat → Bool := fun a b =>
    let (ta, sa, ka) := key a
    let (tb, sb, kb) := key b
    ta < tb || (ta == tb && (sa < sb || (sa == sb && ka < kb)))
  let order := (Array.range ds.size).qsort lt
  let moved := (Array.range ds.size).filter (target.contains ·)
  return (order.map (ds[·]!), moved.flatMap fun k => (ds[k]!.names).toArray)

end ConLeche.Frontend
