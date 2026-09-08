import Lean
open Lean

/-!
# `scripts/dead-census.lean` — the per-constant dependency dump (task #221)

Half of the census instrument task #210 Part C built in `_tmp` and did
not keep; it is committed here so the next census is a *re-run*, not a
re-derivation.  This file dumps the graph; `scripts/dead-census.py`
chooses the seeds and walks it.

**What it dumps.**  In an environment obtained by importing the given
modules, one line per constant declared by con-leche's own modules
(`ConLeche`, `ConLeche.*`, `Main`, `PinDump`, `ConLecheTests*`):

    <name> \t <module> \t <kind> \t <dep> <dep> …

The dependencies are the constants of the declaration's **type and its
proof term or body**, restricted to our own — a constant of the Lean
prelude cannot mention one of ours, so the restriction loses no path —
plus two edges a `getUsedConstants` walk does not have:

* `@[implemented_by impl]` on `n` ⟶ `impl` (the compiled body);
* `n` is a `@[csimp]` replacement's `fromDeclName` ⟶ its `toDeclName`
  and the theorem (a live function drags in the fast twin the compiler
  swaps in for it).

A theorem's proof term is reached by matching `.thmInfo` **directly**:
`ConstantInfo.value?` returns `none` for theorems, which would silently
make the walk report the empty set (`tests/ProofDeps.lean`'s note, the
same trap).

The `@[csimp]` theorem names are dumped too, as `#csimp <name>` lines:
a csimp theorem is reached by nothing and is what makes its fast twin
reachable at all, so the driver seeds them.

Usage (normally through the driver):

    lake env lean --run scripts/dead-census.lean MODULE...
-/

/-- Is `n` declared by one of our own modules? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i =>
    let m := (env.header.moduleNames[i.toNat]!).toString
    m == "ConLeche" || "ConLeche.".isPrefixOf m
      || m == "Main" || m == "PinDump"
      || m == "ConLecheTests" || "ConLecheTests.".isPrefixOf m

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | none => "?"
  | some i => (env.header.moduleNames[i.toNat]!).toString

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/dead-census.lean MODULE..."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => ({ module := m.toName } : Import)) {}
  let st := Lean.Compiler.CSimp.ext.getState env
  let csimpTo : Std.HashMap Name (Name × Name) :=
    st.map.fold (fun acc k e => acc.insert k (e.toDeclName, e.thmName)) {}
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if isOurs env n then
      let vcs : Array Name := match ci with
        | .thmInfo v => v.value.getUsedConstants
        | .defnInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | _ => #[]
      let extra : Array Name :=
        (match Lean.Compiler.getImplementedBy? env n with
         | some i => #[i]
         | none => #[]) ++
        (match csimpTo[n]? with
         | some (t, thm) => #[t, thm]
         | none => #[])
      let deps := (ci.type.getUsedConstants ++ vcs ++ extra).filter
        (fun d => d != n && isOurs env d)
      let mut seen : NameSet := {}
      let mut uniq : Array Name := #[]
      for d in deps do
        if !seen.contains d then
          seen := seen.insert d
          uniq := uniq.push d
      out := out.push
        s!"{n}\t{moduleOf env n}\t{kindOf ci}\t{String.intercalate " " (uniq.toList.map toString)}"
  for n in st.thmNames.toList do
    if isOurs env n then out := out.push s!"#csimp\t{n}"
  for l in out.qsort (· < ·) do IO.println l
  return 0
