import Lean
open Lean

/-!
# `scripts/executed-decls.lean` — the IR declarations the binary can run

The instrument behind `scripts/code-stats.py --executed`.  In the
environment of the executable's root module (`Main`, the `con-leche`
exe of `lakefile.toml`), it walks the **compiled IR** from `main`: a
declaration is reached when a reached IR body names it in a full
application (`fap`), a partial application (`pap`, a closure), or as
a constant.  The IR is what the binary links, so `@[implemented_by]`,
`@[csimp]` and `@[extern]` are already resolved in it: the walk follows
what the compiler emitted, not the kernel terms.  A body the binary
never runs — the pure specification checker, a proof, a subtype's
predicate — has no path from `main` here, however many kernel terms
mention it.

**Output.**  One line per reached IR declaration declared by one of
our own modules (`ConLeche*`, `Main`):

    <ir name> \t <source decl> \t <module> \t <start line> \t <end line>

The source declaration is the IR name with compiler-generated
components stripped (`foo._lambda_1`, `foo._closed_3`, `foo._redArg`,
`foo._boxed`, `foo.match_1`, `foo._at_.bar.spec_2` ↦ `foo`, …) until a
name with declaration ranges remains; its range is the source range of
the whole declaration (`Lean.declRangeExt`).  A reached name of ours
with no range is printed with `?` for the lines and counted by the
driver as unattributed.

Usage (normally through `scripts/code-stats.py --executed`):

    lake env lean --run scripts/executed-decls.lean [--edges] [ROOT [ENTRY]]

with defaults `Main` and `main`.

**`--edges`** (task #497, the plain-tier reach audit `scripts/plain-reach.py`)
prints instead the reached IR call graph: one line

    <caller IR> \t <caller source> \t <caller module> \t <callee IR> \t <callee source> \t <callee module>

for every reached IR body (ours or not) and every IR declaration it
names, with the source declaration resolved as above (a name without
ranges stands for itself, its module that of the IR name).
-/

def isOurModule (m : String) : Bool :=
  m == "ConLeche" || "ConLeche.".isPrefixOf m || m == "Main"

def moduleOf? (env : Environment) (n : Name) : Option String :=
  (env.getModuleIdxFor? n).map fun i => (env.header.moduleNames[i.toNat]!).toString

/-- The functions an IR expression names. -/
def exprRefs : IR.Expr → Array Name
  | .fap c _ => #[c]
  | .pap c _ => #[c]
  | _ => #[]

/-- The functions an IR body names. -/
partial def bodyRefs (b : IR.FnBody) (acc : Array Name := #[]) : Array Name :=
  match b with
  | .vdecl _ _ e k => bodyRefs k (acc ++ exprRefs e)
  | .jdecl _ _ v k => bodyRefs k (bodyRefs v acc)
  | .case _ _ _ alts => alts.foldl (fun acc alt => bodyRefs alt.body acc) acc
  | .set _ _ _ k | .setTag _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k
  | .inc _ _ _ _ k | .dec _ _ _ _ k | .del _ k => bodyRefs k acc
  | .ret _ | .jmp _ _ | .unreachable => acc

/-- Is `s` a component the compiler generates (as opposed to a source name)? -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_"
    || s.startsWith "spec_" || s.startsWith "eq_"

/-- The declaration ranges of `n`, if it was declared in source. -/
def rangeOf? (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .server) env n <|> declRangeExt.find? env n

/-- The source declaration an IR name belongs to: drop a specialization's
`_at_` suffix (the code is the callee's), then strip generated components
until a name with ranges remains. -/
partial def sourceOf (env : Environment) (n : Name) : Option Name :=
  let comps := n.componentsRev.reverse
  -- `callee._at_.caller.spec_k`: the specialized code is the callee's
  let comps := match comps.idxOf? (Name.mkSimple "_at_") with
    | some i => comps.take i
    | none => comps
  let base := comps.foldl (fun acc c => match c with
    | .str _ s => .str acc s
    | .num _ k => .num acc k
    | .anonymous => acc) Name.anonymous
  go base
where
  go (m : Name) : Option Name :=
    if (rangeOf? env m).isSome then some m else
    match m with
    | .str p s => if isAuxComponent s then go p else none
    | .num p _ => go p
    | .anonymous => none

/-- The source declaration and module an IR name is attributed to. -/
def attributeTo (env : Environment) (n : Name) : String × String :=
  let m := (moduleOf? env n).getD "?"
  match sourceOf env n with
  | some s => (s.toString, (moduleOf? env s).getD m)
  | none => (n.toString, m)

def main (args : List String) : IO UInt32 := do
  let edges := args.contains "--edges"
  let args := args.filter (· != "--edges")
  let root := (args.getD 0 "Main").toName
  let entry := (args.getD 1 "main").toName
  initSearchPath (← findSysroot)
  -- `.private` (the default) imports every module's full `.ir`, so
  -- `findEnvDecl` sees the bodies of private and non-exposed
  -- declarations too.
  let env ← importModules #[{ module := root }] {}
  if (IR.findEnvDecl env entry).isNone then
    IO.eprintln s!"executed-decls: no IR declaration {entry} in {root}"
    return 3
  let mut seen : NameSet := ({} : NameSet).insert entry
  let mut todo : Array Name := #[entry]
  let mut out : Array String := #[]
  let mut missing := 0
  let mut edgeSet : Std.HashSet String := {}
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    match IR.findEnvDecl env n with
    | none => missing := missing + 1
    | some d =>
      if let .fdecl _ _ _ body _ := d then
        for c in bodyRefs body do
          if edges then
            let (fs, fm) := attributeTo env n
            let (ts, tm) := attributeTo env c
            edgeSet := edgeSet.insert s!"{n}\t{fs}\t{fm}\t{c}\t{ts}\t{tm}"
          if !seen.contains c then
            seen := seen.insert c
            todo := todo.push c
    if let some m := moduleOf? env n then
      if isOurModule m then
        match sourceOf env n with
        | some s =>
          let r := (rangeOf? env s).get!.range
          let sm := (moduleOf? env s).getD m
          out := out.push s!"{n}\t{s}\t{sm}\t{r.pos.line}\t{r.endPos.line}"
        | none => out := out.push s!"{n}\t?\t{m}\t?\t?"
  IO.eprintln s!"executed-decls: {seen.size} IR declarations reached, {missing} without IR"
  let lines := if edges then edgeSet.toArray else out
  for l in lines.qsort (· < ·) do IO.println l
  return 0
