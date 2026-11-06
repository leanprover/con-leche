import Lean
import InLean

/-!
# Opaque-surface audit of InLean (task #451, lane F)

Run: `lake env lean scripts/inlean_opaque_audit.lean` (after `lake build
InLean`).  Starting from InLean's entry points, walks the VALUES of the
definitions they reach (instances included; theorem values and types are
not followed: only executed code matters) and lists every reached
constant a proof cannot see through:

* `opaque` (no usable body: core's `@[extern] opaque`, `partial def`s,
  `implemented_by` targets' sources),
* definitions with `@[implemented_by]` (the body is a spec the compiled
  code is trusted to meet),
* definitions with `@[extern]` and a body (likewise),
* axioms other than the three standard ones.

Expected since lane G: `Expr.mkData`, `Expr.mkAppData`, `Level.mkData` and the
readers of the cached fields, covered by the stop-gap axioms of
`InLeanProof/MkDataAxioms.lean` on terms in range.  Anything else in the opaque
list is the JSON pin parse, core's `PersistentHashMap` (the premise `EnvLaws`)
or message formatting.

Each line names the constant and one reached-from path element, grouped
by module prefix.
-/

open Lean

def roots : List Name :=
  [`InLean.addDecl, `InLean.kernelWhnf, `InLean.kernelIsDefEq]

/-- Prefixes whose constants are the generator (unverified by design). -/
def genPrefixes : List Name := [`InLean.Ind]

/-- Hash functions: only key memo maps whose equality is `=` (any function
is a lawful hash then); not followed. -/
def hashLeaves : List Name := [``Expr.hash, ``Level.hash, ``Name.hash, ``mixHash]

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isUnder (p n : Name) : Bool := p.isPrefixOf n

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `InLean }] {} (loadExts := false)
  let mut seen : Std.HashSet Name := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut todo : Array Name := roots.toArray
  let mut opq : Array Name := #[]
  let mut implBy : Array (Name × Name) := #[]
  let mut ext : Array Name := #[]
  let mut axs : Array Name := #[]
  let mut gen : Std.HashSet Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    -- the generator is outside the theorem: record, do not descend
    if hashLeaves.contains n then continue
    if genPrefixes.any (isUnder · n) then
      gen := gen.insert n
      continue
    let some ci := env.find? n | continue
    if let some tgt := Compiler.getImplementedBy? env n then
      implBy := implBy.push (n, tgt)
    if (getExternAttrData? env n).isSome then
      match ci with
      | .opaqueInfo _ => pure ()
      | _ => ext := ext.push n
    match ci with
    | .opaqueInfo _ => opq := opq.push n
    | .axiomInfo _ => unless stdAxioms.contains n do axs := axs.push n
    | .defnInfo v =>
      for c in v.value.getUsedConstants do
        unless seen.contains c do
          unless parent.contains c do parent := parent.insert c n
          todo := todo.push c
    | _ => pure ()
  let fmt (n : Name) : String := Id.run do
    let mut chain : Array Name := #[]
    let mut cur := n
    for _ in [0:40] do
      match parent.get? cur with
      | some p =>
        chain := chain.push p
        if p.getRoot == `InLean then break
        cur := p
      | none => break
    return s!"{n}  <- {" <- ".intercalate (chain.toList.map toString)}"
  IO.println s!"reached {seen.size} constants ({gen.size} generator constants not followed)"
  let covered : List Name := [``Expr.mkData, ``Expr.mkAppData, ``Level.mkData]
  IO.println s!"\n## opaque ({opq.size})"
  for n in opq.qsort (·.toString < ·.toString) do
    IO.println ((if covered.contains n then "[stop-gap axiom] " else "") ++ fmt n)
  IO.println s!"\n## implemented_by ({implBy.size})"
  for (n, t) in implBy.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{fmt n} -> {t}"
  IO.println s!"\n## extern with body ({ext.size})"
  for n in ext.qsort (·.toString < ·.toString) do IO.println (fmt n)
  let fields : List Name := [``Expr.looseBVarRange, ``Expr.hasFVar, ``Expr.hasExprMVar,
    ``Expr.hasLevelMVar, ``Expr.hasLevelParam, ``Expr.hasMVar, ``Expr.hasLooseBVars,
    ``Expr.approxDepth, ``Expr.Data.looseBVarRange, ``Expr.Data.hasFVar,
    ``Expr.Data.hasLevelParam, ``Expr.Data.hasExprMVar, ``Expr.Data.hasLevelMVar,
    ``Expr.Data.approxDepth, ``Level.hasParam, ``Level.hasMVar, ``Level.depth]
  let hit := fields.filter seen.contains
  IO.println s!"\n## cached-field readers reached ({hit.length}; expected, see the header)"
  for n in hit do IO.println (fmt n)
  IO.println s!"\n## generator constants reached ({gen.size}; not followed)"
  for n in gen.toArray.qsort (·.toString < ·.toString) do IO.println (fmt n)
  IO.println s!"\n## non-standard axioms ({axs.size})"
  for n in axs do IO.println (fmt n)
