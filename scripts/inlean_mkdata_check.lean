import Lean
import InLeanProof.MkDataAxioms

/-!
# Checking the stop-gap axioms against C (task #451, lane G)

Run: `lake env lean --run scripts/inlean_mkdata_check.lean` (after `lake build
InLeanProof.MkDataAxioms`).  Compares the C functions `Expr.mkData`,
`Expr.mkAppData` and `Level.mkData` with the statements of
`InLeanProof/MkDataAxioms.lean`:

1. on the cross product of boundary values of every argument, at and below the
   bounds (above them C aborts the process, and nothing is claimed);
2. on pseudo-random arguments (a fixed seed);
3. on every node of `Init`'s constants, with the arguments `Expr.data`'s
   definition passes for that node's constructor.
-/

open Lean InLeanProof

/-- xorshift64: a fixed sequence. -/
def nextRand (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

structure Tally where
  checked : Nat := 0
  failed : Nat := 0

def Tally.add (t : Tally) (ok : Bool) : Tally :=
  { checked := t.checked + 1, failed := if ok then t.failed else t.failed + 1 }

def checkMkData (h : UInt64) (r : Nat) (d : UInt32) (a b c e : Bool) : Bool :=
  (Expr.mkData h r d a b c e : UInt64) == UInt64.ofNat (mkDataNat h r d a b c e)

def checkLevelMkData (h : UInt64) (d : Nat) (m p : Bool) : Bool :=
  (Level.mkData h d m p : UInt64) == UInt64.ofNat (levelMkDataNat h d m p)

def checkAppData (f a : Expr.Data) : Bool :=
  let x := Expr.mkAppData f a
  x.looseBVarRange.toNat == max f.looseBVarRange.toNat a.looseBVarRange.toNat &&
  x.hasFVar == (f.hasFVar || a.hasFVar) &&
  x.hasExprMVar == (f.hasExprMVar || a.hasExprMVar) &&
  x.hasLevelMVar == (f.hasLevelMVar || a.hasLevelMVar) &&
  x.hasLevelParam == (f.hasLevelParam || a.hasLevelParam)

def bools : List Bool := [false, true]
def hashes : List UInt64 := [0, 1, 0xFFFFFFFF, 0x100000000, 0xFFFFFFFFFFFFFFFF, 0x123456789ABCDEF0]
def ranges : List Nat := [0, 1, 2, 1048574, 1048575]
def depths : List UInt32 := [0, 1, 254, 255, 256, 0xFFFFFFFF]
def ldepths : List Nat := [0, 1, 16777214, 16777215]

def boundary : Tally × Tally × Tally := Id.run do
  let mut t : Tally := {}
  for h in hashes do for r in ranges do for d in depths do
    for a in bools do for b in bools do for c in bools do for e in bools do
      t := t.add (checkMkData h r d a b c e)
  let mut l : Tally := {}
  for h in hashes do for d in ldepths do for m in bools do for p in bools do
    l := l.add (checkLevelMkData h d m p)
  let words : List UInt64 := [0, 1, 0xFFFFFFFF, 0xFF00000000, 0xF0000000000, 0x10000000000,
    0x80000000000, 0xFFFFF00000000000, 0x7FFFF00000000000, 0xFFFFFFFFFFFFFFFF]
  let mut ap : Tally := {}
  for f in words do for a in words do
    ap := ap.add (checkAppData f a)
  return (t, l, ap)

def random (n : Nat) : Tally × Tally × Tally := Id.run do
  let mut x : UInt64 := 0x9E3779B97F4A7C15
  let mut t : Tally := {}
  let mut l : Tally := {}
  let mut ap : Tally := {}
  for _ in [0:n] do
    x := nextRand x
    let h := x
    x := nextRand x
    let f := x
    x := nextRand x
    let g := x
    let r := (f >>> 44).toNat
    let d := g.toUInt32
    let fl (i : UInt64) : Bool := ((f >>> i) &&& 1) == 1
    t := t.add (checkMkData h r d (fl 0) (fl 1) (fl 2) (fl 3))
    l := l.add (checkLevelMkData h (g >>> 40).toNat (fl 4) (fl 5))
    ap := ap.add (checkAppData f g)
  return (t, l, ap)

/-- One node's data against the axioms, with the arguments of `Expr.data`. -/
def checkNode (e : Expr) : Bool :=
  let D (x : Expr) : Expr.Data := x.data
  let word (h : UInt64) (r : Nat) (d : UInt32) (a b c x : Bool) : Bool :=
    (e.data : UInt64) == UInt64.ofNat (mkDataNat h r d a b c x)
  let R (x : Expr) : Nat := (D x).looseBVarRange.toNat
  let A (x : Expr) : UInt32 := (D x).approxDepth.toUInt32
  match e with
  | .const n lvls => word (mixHash 5 <| mixHash (hash n) (hash lvls)) 0 0 false false
      (lvls.any Level.hasMVar) (lvls.any Level.hasParam)
  | .bvar idx => word (mixHash 7 <| hash idx) (idx + 1) 0 false false false false
  | .sort lvl => word (mixHash 11 <| hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam
  | .fvar id => word (mixHash 13 <| hash id) 0 0 true false false false
  | .mvar id => word (mixHash 17 <| hash id) 0 0 false true false false
  | .mdata _ x =>
    let d := A x + 1
    word (mixHash d.toUInt64 <| (D x).hash) (R x) d (D x).hasFVar (D x).hasExprMVar
      (D x).hasLevelMVar (D x).hasLevelParam
  | .proj s i x =>
    let d := A x + 1
    word (mixHash d.toUInt64 <| mixHash (hash s) <| mixHash (hash i) (D x).hash) (R x) d
      (D x).hasFVar (D x).hasExprMVar (D x).hasLevelMVar (D x).hasLevelParam
  | .app f a => checkAppData (D f) (D a) &&
      (let x := D e; x.looseBVarRange == Expr.Data.looseBVarRange (Expr.mkAppData (D f) (D a)))
  | .lam _ t b _ | .forallE _ t b _ =>
    let d := (max (A t) (A b)) + 1
    word (mixHash d.toUInt64 <| mixHash (D t).hash (D b).hash) (max (R t) (R b - 1)) d
      ((D t).hasFVar || (D b).hasFVar) ((D t).hasExprMVar || (D b).hasExprMVar)
      ((D t).hasLevelMVar || (D b).hasLevelMVar) ((D t).hasLevelParam || (D b).hasLevelParam)
  | .letE _ t v b _ =>
    let d := (max (max (A t) (A v)) (A b)) + 1
    word (mixHash d.toUInt64 <| mixHash (D t).hash <| mixHash (D v).hash (D b).hash)
      (max (max (R t) (R v)) (R b - 1)) d
      ((D t).hasFVar || (D v).hasFVar || (D b).hasFVar)
      ((D t).hasExprMVar || (D v).hasExprMVar || (D b).hasExprMVar)
      ((D t).hasLevelMVar || (D v).hasLevelMVar || (D b).hasLevelMVar)
      ((D t).hasLevelParam || (D v).hasLevelParam || (D b).hasLevelParam)
  | .lit l => word (mixHash 3 (hash l)) 0 0 false false false false

/-- One level node against the axiom, with the arguments of `Level.data`. -/
def checkLevelNode (l : Level) : Bool :=
  let word (h : UInt64) (d : Nat) (m p : Bool) : Bool :=
    (l.data : UInt64) == UInt64.ofNat (levelMkDataNat h d m p)
  let D (u : Level) : Level.Data := u.data
  match l with
  | .zero => word 2221 0 false false
  | .mvar id => word (mixHash 2237 <| hash id) 0 true false
  | .param n => word (mixHash 2239 <| hash n) 0 false true
  | .succ u => word (mixHash 2243 <| (D u).hash) ((D u).depth.toNat + 1) (D u).hasMVar (D u).hasParam
  | .max u v => word (mixHash 2251 <| mixHash (D u).hash (D v).hash)
      (Nat.max (D u).depth.toNat (D v).depth.toNat + 1)
      ((D u).hasMVar || (D v).hasMVar) ((D u).hasParam || (D v).hasParam)
  | .imax u v => word (mixHash 2267 <| mixHash (D u).hash (D v).hash)
      (Nat.max (D u).depth.toNat (D v).depth.toNat + 1)
      ((D u).hasMVar || (D v).hasMVar) ((D u).hasParam || (D v).hasParam)

partial def checkLevels (l : Level) (seen : Std.HashSet Level) (t : Tally) : Std.HashSet Level × Tally :=
  if seen.contains l then (seen, t) else
  let seen := seen.insert l
  let t := t.add (checkLevelNode l)
  match l with
  | .succ u => checkLevels u seen t
  | .max u v | .imax u v =>
    let (seen, t) := checkLevels u seen t
    checkLevels v seen t
  | _ => (seen, t)

structure Walk where
  seen : Std.HashSet USize := {}
  lseen : Std.HashSet Level := {}
  nodes : Tally := {}
  levels : Tally := {}
  bad : Array String := #[]

/-- Every node once, by address: `ptrAddrUnsafe` needs `unsafe`, so the walk is
keyed by `Expr` itself. -/
partial def walk (e : Expr) (seen : Std.HashSet Expr) (w : Walk) : Std.HashSet Expr × Walk :=
  if seen.contains e then (seen, w) else
  let seen := seen.insert e
  let ok := checkNode e
  let w := { w with nodes := w.nodes.add ok,
                    bad := if ok || w.bad.size ≥ 20 then w.bad else w.bad.push (toString e) }
  let w := match e with
    | .sort u =>
      let (ls, t) := checkLevels u w.lseen w.levels
      { w with lseen := ls, levels := t }
    | .const _ us => us.foldl (fun w u =>
        let (ls, t) := checkLevels u w.lseen w.levels
        { w with lseen := ls, levels := t }) w
    | _ => w
  match e with
  | .app f a =>
    let (seen, w) := walk f seen w
    walk a seen w
  | .lam _ t b _ | .forallE _ t b _ =>
    let (seen, w) := walk t seen w
    walk b seen w
  | .letE _ t v b _ =>
    let (seen, w) := walk t seen w
    let (seen, w) := walk v seen w
    walk b seen w
  | .mdata _ x | .proj _ _ x => walk x seen w
  | _ => (seen, w)

def report (name : String) (t : Tally) : IO Unit :=
  IO.println s!"{name}: {t.checked} checked, {t.failed} failed"

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (t, l, ap) := boundary
  report "boundary Expr.mkData" t
  report "boundary Level.mkData" l
  report "boundary Expr.mkAppData" ap
  let (t', l', ap') := random 200000
  report "random Expr.mkData" t'
  report "random Level.mkData" l'
  report "random Expr.mkAppData" ap'
  let env ← importModules #[{ module := `Init }] {} (loadExts := false)
  let mut seen : Std.HashSet Expr := {}
  let mut w : Walk := {}
  for (_, ci) in env.constants.map₁.toList do
    let (s, w') := walk ci.type seen w
    seen := s; w := w'
    if let some v := ci.value? (allowOpaque := true) then
      let (s, w') := walk v seen w
      seen := s; w := w'
    if let .recInfo rv := ci then
      for r in rv.rules do
        let (s, w') := walk r.rhs seen w
        seen := s; w := w'
  report "Init Expr nodes" w.nodes
  report "Init Level nodes" w.levels
  for b in w.bad do IO.println s!"BAD {b}"
  let bad := t.failed + l.failed + ap.failed + t'.failed + l'.failed + ap'.failed +
    w.nodes.failed + w.levels.failed
  return if bad == 0 then 0 else 1
