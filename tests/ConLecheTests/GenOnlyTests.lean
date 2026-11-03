module

public import ConLeche.Frontend.Prepare
public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.ExportC
public import ConLeche.Cached.Installed
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Prepare
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Frontend.ExportC
meta import ConLeche.Cached.Installed

public section

/-!
# The generate-only install of an inductive block (task #410)

`genIndStep` pushes, wherever the checked step `installDeclStep`
accepts a block, what that step pushed (`genIndStep_eq`,
`ConLeche/Verify/Cached/GenOnly.lean`).  Here on values: streams with
mutual, nested, indexed and structure-like blocks, folded by the
checked step; at every inductive block the generate-only step at the
same index pushes the same constants and tables.
-/

namespace ConLecheTests.GenOnly

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The fold over the prepared stream; at every inductive block, the
generate-only step at the same index compared with the checked one
(at least one block compared). -/
def genAgrees (path : System.FilePath) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let some pre := builtinPreludeE.toOption | throw <| IO.userError "prelude"
  let .ok r := parseBytes b | throw <| IO.userError s!"{path}: does not parse"
  let ds := preparePrelude pre r.decls
  let rec go : List Declaration → Nat × FEnv × Array PendingCheck → Nat → IO Nat
    | [], _, n => pure n
    | d :: ds, acc, n =>
      match installDeclStep .verified natOpPinSets acc d with
      | .error _ => throw <| IO.userError s!"{path}: the checked fold rejects"
      | .ok acc' =>
        match d with
        | .indDecl block nP =>
          match genIndStep .verified acc.2.1 block nP with
          | .ok fe' =>
            if fe'.env.consts == acc'.2.1.env.consts && fe'.env.tables == acc'.2.1.env.tables
            then go ds acc' (n + 1)
            else throw <| IO.userError s!"{path}: the generate-only step differs"
          | .error _ => throw <| IO.userError s!"{path}: the generate-only step fails"
        | _ => go ds acc' n
  if (← go ds.toList (0, mkFEnv Env.empty, #[]) 0) == 0 then
    throw <| IO.userError s!"{path}: no inductive block"

-- mutual, nested (through a container, a list rose tree, mutual
-- nesting), indexed, structure-like (projection tables) and reflexive
-- blocks
#eval genAgrees "tests/e2e/inmodel_mutual.ndjson"
#eval genAgrees "tests/e2e/inmodel_mutual_idx.ndjson"
#eval genAgrees "tests/e2e/mutual_struct_proj.ndjson"
#eval genAgrees "tests/e2e/corner_nestind_f13_listrose.ndjson"
#eval genAgrees "tests/e2e/corner_nestind_d_mutual.ndjson"
#eval genAgrees "tests/e2e/indexed_vec.ndjson"

end ConLecheTests.GenOnly
