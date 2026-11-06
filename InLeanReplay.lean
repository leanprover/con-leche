module

import Lean
public import InLean

/-!
# `inlean-replay` (task #451)

Loads the environment of the given modules with `importModules`, then replays
every constant of the import closure into a fresh kernel environment in
dependency order through the selected kernel, optionally comparing every
constant the kernel added with the imported one.  Adapted from core's
`Lean.Kernel.Environment.replay`, with the kernel as a parameter and with
unsafe/partial constants included.

Exit codes: 0 all accepted, 1 a reject or a compare mismatch, 3 internal error.
-/

open Lean

namespace InLeanReplay

inductive KernelSel | inlean | official | none
  deriving BEq

structure Config where
  kernel : KernelSel := .official
  compare : Bool := false
  keepGoing : Bool := false
  quiet : Bool := false
  mods : Array Name := #[]

def addWith (k : KernelSel) (env : Kernel.Environment) (d : Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  match k with
  | .inlean => InLean.addDecl env d
  | _ => env.addDeclCore 0 0 d none

/-! ## Comparison -/

/-- Differences of two expressions: none if `Expr.equal`, cosmetic if only `Expr.eqv`
(binder names/infos), exact otherwise.  Both are pointer-first C++ walks with a cache. -/
def exprDiff (f : String) (a b : Expr) : Array (String × Bool) :=
  if a.equal b then #[] else if a.eqv b then #[(f, true)] else #[(f, false)]

def beqDiff {α} [BEq α] (f : String) (a b : α) : Array (String × Bool) :=
  if a == b then #[] else #[(f, false)]

def ruleDiffs (a b : List RecursorRule) : Array (String × Bool) := Id.run do
  if a.length != b.length then return #[("rules.length", false)]
  let mut r := #[]
  for (x, y) in a.zip b do
    r := r ++ beqDiff s!"rule {x.ctor}.ctor" x.ctor y.ctor
      ++ beqDiff s!"rule {x.ctor}.nfields" x.nfields y.nfields
      ++ exprDiff s!"rule {x.ctor}.rhs" x.rhs y.rhs
  return r

def valDiffs (a b : ConstantInfo) : Array (String × Bool) :=
  let c := beqDiff "levelParams" a.levelParams b.levelParams ++ exprDiff "type" a.type b.type
  match a, b with
  | .axiomInfo x, .axiomInfo y => c ++ beqDiff "isUnsafe" x.isUnsafe y.isUnsafe
  | .defnInfo x, .defnInfo y =>
    c ++ exprDiff "value" x.value y.value ++ beqDiff "hints" x.hints y.hints
      ++ beqDiff "safety" x.safety y.safety ++ beqDiff "all" x.all y.all
  | .thmInfo x, .thmInfo y => c ++ exprDiff "value" x.value y.value ++ beqDiff "all" x.all y.all
  | .opaqueInfo x, .opaqueInfo y =>
    c ++ exprDiff "value" x.value y.value ++ beqDiff "isUnsafe" x.isUnsafe y.isUnsafe
      ++ beqDiff "all" x.all y.all
  | .quotInfo x, .quotInfo y => c ++ beqDiff "kind" x.kind y.kind
  | .inductInfo x, .inductInfo y =>
    c ++ beqDiff "numParams" x.numParams y.numParams ++ beqDiff "numIndices" x.numIndices y.numIndices
      ++ beqDiff "all" x.all y.all ++ beqDiff "ctors" x.ctors y.ctors
      ++ beqDiff "numNested" x.numNested y.numNested ++ beqDiff "isRec" x.isRec y.isRec
      ++ beqDiff "isUnsafe" x.isUnsafe y.isUnsafe ++ beqDiff "isReflexive" x.isReflexive y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
    c ++ beqDiff "induct" x.induct y.induct ++ beqDiff "cidx" x.cidx y.cidx
      ++ beqDiff "numParams" x.numParams y.numParams ++ beqDiff "numFields" x.numFields y.numFields
      ++ beqDiff "isUnsafe" x.isUnsafe y.isUnsafe
  | .recInfo x, .recInfo y =>
    c ++ beqDiff "all" x.all y.all ++ beqDiff "numParams" x.numParams y.numParams
      ++ beqDiff "numIndices" x.numIndices y.numIndices ++ beqDiff "numMotives" x.numMotives y.numMotives
      ++ beqDiff "numMinors" x.numMinors y.numMinors ++ beqDiff "k" x.k y.k
      ++ beqDiff "isUnsafe" x.isUnsafe y.isUnsafe ++ ruleDiffs x.rules y.rules
  | _, _ => #[("kind", false)]

/-! ## Replay -/

structure Ctx where
  cfg : Config
  consts : Std.HashMap Name ConstantInfo

structure St where
  env : Kernel.Environment
  remaining : Std.HashSet Name
  pending : Std.HashSet Name := {}
  bad : Std.HashSet Name := {}
  compared : Std.HashSet Name := {}
  stop : Bool := false
  sent : Nat := 0
  accepted : Nat := 0
  rejected : Nat := 0
  skipped : Nat := 0
  dups : Nat := 0
  compareCount : Nat := 0
  exact : Nat := 0
  cosmetic : Nat := 0
  mismatchLines : Nat := 0

abbrev M := ReaderT Ctx <| StateRefT St IO

def say (s : String) : M Unit := do
  unless (← read).cfg.quiet do IO.println s

def isTodo (n : Name) : M Bool := do
  let s ← get
  if s.remaining.contains n then
    set { s with remaining := s.remaining.erase n, pending := s.pending.insert n }
    return true
  return false

def lookup (n : Name) : M ConstantInfo := do
  let some ci := (← read).consts[n]? | throw <| .userError s!"internal: unknown constant {n}"
  return ci

/-- Compare the kernel's constant `n` with the imported one. -/
def compareConst (n : Name) : M Unit := do
  let ci ← lookup n
  modify fun s => { s with compared := s.compared.insert n, compareCount := s.compareCount + 1 }
  let diffs := match (← get).env.find? n with
    | none => #[("missing in kernel env", false)]
    | some ci' => valDiffs ci' ci
  if diffs.isEmpty then return
  let isExact := diffs.any (!·.2)
  let desc := ", ".intercalate (diffs.toList.map fun (f, c) => if c then s!"{f} (cosmetic)" else f)
  modify fun s =>
    { s with exact := s.exact + (if isExact then 1 else 0)
             cosmetic := s.cosmetic + (if isExact then 0 else 1) }
  if isExact || !(← read).cfg.quiet then
    if (← get).mismatchLines < 200 then
      IO.println s!"MISMATCH{if isExact then "" else " (cosmetic)"} {n}: {desc}"
      modify fun s => { s with mismatchLines := s.mismatchLines + 1 }

/-- Names produced by an inductive block: types, constructors, `rec`, `rec_N`. -/
def blockNames (all : List Name) : M (Array Name) := do
  let consts := (← read).consts
  let mut r := #[]
  for n in all do
    r := r.push n
    if let some (.inductInfo v) := consts[n]? then
      r := r ++ v.ctors.toArray
    let recN := n ++ `rec
    if consts.contains recN then r := r.push recN
  -- nested auxiliary recursors `rec_1`, ... are named after the first type
  if let n :: _ := all then
    let mut i := 1
    while consts.contains (n ++ Name.mkSimple s!"rec_{i}") do
      r := r.push (n ++ Name.mkSimple s!"rec_{i}")
      i := i + 1
  return r

def sendDecl (d : Declaration) (group : List Name) (produced : Array Name) : M Unit := do
  modify fun s => { s with sent := s.sent + 1 }
  match addWith (← read).cfg.kernel (← get).env d with
  | .ok env =>
    modify fun s => { s with env, accepted := s.accepted + 1 }
    if (← read).cfg.compare then
      for n in produced do compareConst n
  | .error ex =>
    let msg ← (ex.toMessageData {}).toString
    IO.println s!"REJECT {group}: {msg}"
    let keep := (← read).cfg.keepGoing
    modify fun s => { s with rejected := s.rejected + 1, bad := group.foldl (·.insert ·) s.bad,
                             stop := !keep }

mutual
partial def replayConstant (name : Name) : M Unit := do
  if (← get).stop then return
  unless ← isTodo name do return
  let ci ← lookup name
  let consts := (← read).consts
  -- the block this constant belongs to
  let group : List Name ← match ci with
    | .defnInfo v =>
      if v.safety == .safe then pure [name]
      else pure (v.all.filter fun n => match consts[n]? with | some (.defnInfo _) => true | _ => false)
    | .inductInfo v => pure v.all
    | .quotInfo _ => pure [`Quot, `Quot.mk, `Quot.lift, `Quot.ind]
    | _ => pure [name]
  let group := if group.contains name then group else name :: group
  for o in group do
    modify fun s => { s with remaining := s.remaining.erase o, pending := s.pending.insert o }
  -- dependencies
  let mut members : List ConstantInfo := []
  for o in group do members := members ++ [← lookup o]
  let ctorInfos : List ConstantInfo ← match ci with
    | .inductInfo _ => do
      let mut r := []
      for m in members do
        if let .inductInfo v := m then
          for c in v.ctors do r := r ++ [← lookup c]
      pure r
    | _ => pure []
  let deps : Std.HashSet Name := (members ++ ctorInfos).foldl
    (fun acc m => m.getUsedConstantsAsSet.foldl (·.insert ·) acc) {}
  let deps := if let .quotInfo _ := ci then deps.insert `Eq else deps
  for d in deps do
    unless group.contains d do replayConstant d
  if (← get).stop then return
  let bad := (← get).bad
  if deps.any fun d => !group.contains d && bad.contains d then
    modify fun s => { s with skipped := s.skipped + group.length, bad := group.foldl (·.insert ·) s.bad }
    say s!"skip {group} (depends on a rejected constant)"
    return
  match ci with
  | .defnInfo v =>
    if v.safety == .safe then sendDecl (.defnDecl v) group #[name]
    else
      let defs := members.filterMap fun | .defnInfo d => some d | _ => none
      sendDecl (.mutualDefnDecl defs) group group.toArray
  | .thmInfo v =>
    -- core's special case: duplicate private theorems are ignored
    if let some (.thmInfo v') := (← get).env.find? name then
      if v.name == v'.name && v.type == v'.type && v.levelParams == v'.levelParams && v.all == v'.all then
        modify fun s => { s with dups := s.dups + 1 }
        return
    sendDecl (.thmDecl v) group #[name]
  | .axiomInfo v => sendDecl (.axiomDecl v) group #[name]
  | .opaqueInfo v => sendDecl (.opaqueDecl v) group #[name]
  | .quotInfo _ =>
    if (← get).env.quotInit then
      -- quotient already installed: nothing to send
      pure ()
    else sendDecl .quotDecl group group.toArray
  | .inductInfo v =>
    let types : List InductiveType := members.filterMap fun
      | .inductInfo iv => some
          { name := iv.name, type := iv.type
            ctors := iv.ctors.filterMap fun c => match consts[c]? with
              | some ctor => some { name := c, type := ctor.type }
              | none => none }
      | _ => none
    sendDecl (.inductDecl v.levelParams v.numParams types v.isUnsafe) group (← blockNames group)
  -- constructors and recursors are not sent: they are compared with the block's output
  | .ctorInfo _ | .recInfo _ => pure ()
end

def run : M Unit := do
  let names := (← get).remaining.toList
  for n in names do replayConstant n
  if (← read).cfg.compare then
    -- postponed constructors and recursors must have been produced and compared
    for (n, ci) in (← read).consts.toList do
      if (← get).compared.contains n || (← get).bad.contains n then continue
      match ci with
      | .ctorInfo _ | .recInfo _ => compareConst n
      | _ => pure ()

end InLeanReplay

open InLeanReplay

def usage : String :=
  "usage: inlean-replay [--kernel=inlean|official|none] [--compare] [--mode=verified|trusted] \
   [--keep-going] [--quiet] MOD..."

def parseArgs (args : List String) : Except String Config := do
  let mut cfg : Config := {}
  for a in args do
    match a with
    | "--kernel=inlean" => cfg := { cfg with kernel := .inlean }
    | "--kernel=official" => cfg := { cfg with kernel := .official }
    | "--kernel=none" => cfg := { cfg with kernel := .none }
    | "--compare" => cfg := { cfg with compare := true }
    | "--keep-going" => cfg := { cfg with keepGoing := true }
    | "--quiet" => cfg := { cfg with quiet := true }
    | "--mode=verified" | "--mode=trusted" => pure ()
    | _ =>
      if a.startsWith "--" then throw s!"unknown option {a}"
      else cfg := { cfg with mods := cfg.mods.push a.toName }
  if cfg.mods.isEmpty then throw "no modules given"
  return cfg

public def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"{e}\n{usage}"; return 3
  if args.any (·.startsWith "--mode=") then
    IO.eprintln "note: --mode is ignored (InLean provides no mode switch yet)"
  if cfg.compare && cfg.kernel == .none then
    IO.eprintln "--compare needs a kernel"; return 3
  try
    initSearchPath (← findSysroot)
    let env ← importModules (cfg.mods.map ({ module := · })) {} (loadExts := false)
    let consts := env.constants.map₁
    IO.println s!"imported {consts.size} constants"
    if cfg.kernel == .none then return 0
    let kenv := (← mkEmptyEnvironment).toKernelEnv
    let remaining : Std.HashSet Name := consts.fold (fun acc n _ => acc.insert n) {}
    let ((), s) ← (InLeanReplay.run.run { cfg, consts }).run { env := kenv, remaining }
    IO.println s!"constants {consts.size}; declarations sent {s.sent}, accepted {s.accepted}, \
      rejected {s.rejected}, skipped {s.skipped}, duplicate theorems {s.dups}"
    if cfg.compare then
      IO.println s!"compared {s.compareCount}; mismatches exact {s.exact}, cosmetic {s.cosmetic}"
    return if s.rejected > 0 || s.exact > 0 then 1 else 0
  catch e =>
    IO.eprintln s!"internal error: {e}"
    return 3
