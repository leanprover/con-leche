import Lean
open Lean

/-!
# `scripts/SelfcheckDecls.lean` — the self-check's declaration list (task #199)

Prints, one per line, every **non-internal constant declared by one of
lech's own modules** in the environment obtained by importing the given
root modules.  `scripts/selfcheck.sh` feeds that list to `lean4export`
after a `--`, so the exported stream is exactly *our declarations plus
their transitive dependency cone* — the honest reading of "an export of
the lech code base".  Exporting the whole imported environment instead
would drag in the ~200k constants of the Lean elaborator that nothing of
ours depends on.

    lake env lean --run scripts/SelfcheckDecls.lean Lech Lech.SetP ...

A constant counts as ours when the module that declares it is `Lech`,
`Lech.*`, or one of the executable roots (`Main`).  Internal names
(`_private.…`, `….\_unsafe_rec`, `….\_override`, macro scopes) are not
listed: they are not stable API, and `lean4export` reaches the ones that
matter through the dependency walk anyway.
-/

def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i =>
    let m := (env.header.moduleNames[i.toNat]!).toString
    m == "Lech" || "Lech.".isPrefixOf m || m == "Main"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/SelfcheckDecls.lean MODULE..."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => ({ module := m.toName } : Import)) {}
  let all := env.constants.toList
  let mut out : Array Name := #[]
  for (n, _) in all do
    if isOurs env n && !n.isInternal then out := out.push n
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println n
  IO.eprintln s!"SelfcheckDecls: {out.size} own declarations \
    (environment holds {all.length} constants \
    from {env.header.moduleNames.size} modules)"
  return 0
