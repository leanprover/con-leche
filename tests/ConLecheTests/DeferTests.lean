module

public import ConLeche.Frontend.Prepare
public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.ExportC
public import ConLeche.Verify.Cached.Defer
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Prepare
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Frontend.ExportC
meta import ConLeche.Verify.Cached.Defer

public section

/-!
# Inductive blocks checked in the check phase (tasks #411, #431)

The install with its blocks pushed as stored (`storedInstall`) and their
checked installs deferred (the install's commit loop, here as
a pure serial fold over the prepared stream, each block checked at a
view of the index it was installed at), against the checked fold
`installDeclStep`: on accepted streams the same environment, and every
deferred check passes; on rejected streams with a faulty block the
same verdict at the same fold position — the first failure among the
fold's own errors and the deferred checks below it.  And a stored
install that is not the checked one's (a tampered capability record)
fails its job as an internal error.
-/

namespace ConLecheTests.Defer

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The index as a view: its lookups, an empty environment of its own
(as the worker view's), so that a step's pushes are its environment. -/
def viewOf (fe : FEnv) : FEnv := { fe with env := Env.empty }

/-- The deferring fold: every inductive block as stored with its check
recorded at the view of its index, every other record by the checked
step; a failure reported, as the driver does, after the deferred checks
below it. -/
def deferFold : List Declaration → Nat × FEnv × Array PendingCheck → Array BlockCheck →
    Except (CheckError × Nat) (FEnv × Array BlockCheck)
  | [], acc, D => .ok (acc.2.1, D)
  | d :: ds, acc, D =>
    match deferredBlock? d with
    | some (block, nP) =>
      let v := viewOf acc.2.1
      let (L, Q) := storedInstall .verified v block nP
      deferFold ds (acc.1 + 1, FEnv.pushDelta L Q acc.2.1, acc.2.2)
        (D.push ⟨v, block, nP, acc.1, L, Q⟩)
    | none =>
      match installDeclStep .verified natOpPinSets acc d with
      | .ok acc' => deferFold ds acc' D
      | .error e => .error ((blockFailure .verified natOpPinSets D).getD e)

/-- The fold's verdict with every deferred check run: the environment,
or the first failure in fold order. -/
def deferVerdict (ds : List Declaration) : Except (CheckError × Nat) Env :=
  match deferFold ds (0, mkFEnv Env.empty, #[]) #[] with
  | .ok (fe, D) =>
    match blockFailure .verified natOpPinSets D with
    | some e => .error e
    | none => .ok fe.env
  | .error e => .error e

/-- The checked fold's phase A: the environment, or the failure. -/
def checkedA (ds : List Declaration) : Except (CheckError × Nat) Env :=
  match ds.foldlM (installDeclStep .verified natOpPinSets) (0, mkFEnv Env.empty, #[]) with
  | .ok p => .ok p.2.1.env
  | .error e => .error e

def prepared (path : System.FilePath) : IO (List Declaration) := do
  let b ← IO.FS.readBinFile path
  let some pre := builtinPreludeE.toOption | throw <| IO.userError "prelude"
  let .ok r := parseBytes b | throw <| IO.userError s!"{path}: does not parse"
  return (preparePrelude pre r.decls).toList

/-- An accepted stream: the same environment (at least one block deferred). -/
def sameAccept (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  match deferFold ds (0, mkFEnv Env.empty, #[]) #[], checkedA ds with
  | .ok (fe, D), .ok env =>
    if D.isEmpty then throw <| IO.userError s!"{path}: no block deferred"
    if (blockFailure .verified natOpPinSets D).isSome then
      throw <| IO.userError s!"{path}: a deferred check fails"
    unless fe.env.consts == env.consts && fe.env.tables == env.tables do
      throw <| IO.userError s!"{path}: the environments differ"
  | _, _ => throw <| IO.userError s!"{path}: a fold rejects"

/-- A stream rejected at an inductive block: rejected at the same fold
position, as invalid. -/
def sameReject (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  match deferVerdict ds, checkedA ds with
  | .error (.invalid _, p), .error (.invalid _, q) =>
    unless p == q do throw <| IO.userError s!"{path}: rejected at {p}, the checked fold at {q}"
  | _, _ => throw <| IO.userError s!"{path}: not both rejected as invalid"

-- accepted: mutual, indexed mutual, mutual structures with projections,
-- nested (a list rose tree, mutual nesting), an indexed family
#eval sameAccept "tests/e2e/inmodel_mutual.ndjson"
#eval sameAccept "tests/e2e/inmodel_mutual_idx.ndjson"
#eval sameAccept "tests/e2e/mutual_struct_proj.ndjson"
#eval sameAccept "tests/e2e/corner_nestind_f13_listrose.ndjson"
#eval sameAccept "tests/e2e/corner_nestind_d_mutual.ndjson"
#eval sameAccept "tests/e2e/indexed_vec.ndjson"
-- def-headed formers (installed at the reduced telescope), a pinned
-- basis block (the pin's constants)
#eval sameAccept "tests/e2e/direct_idx_defhead.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_struct.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_k.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_mutual.ndjson"
#eval sameAccept "tests/e2e/ind_former_redex.ndjson"

/-- A tampered stored install (the first block's first former's
capability record with its unit-likeness flipped) fails its job, as an
internal error. -/
def tamperedFails (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  match deferFold ds (0, mkFEnv Env.empty, #[]) #[] with
  | .ok (_, D) =>
    let some b := D[0]? | throw <| IO.userError s!"{path}: no block deferred"
    let L' := match b.L with
      | .indInfo cv caps :: rest => .indInfo cv { caps with unitlike := !caps.unitlike } :: rest
      | L => L
    match blockCheck .verified natOpPinSets { b with L := L' } with
    | .error (.internal _) => pure ()
    | _ => throw <| IO.userError s!"{path}: the tampered install passed its job"
  | .error _ => throw <| IO.userError s!"{path}: the fold rejects"

#eval tamperedFails "tests/e2e/inmodel_mutual.ndjson"
#eval tamperedFails "tests/e2e/mutual_struct_proj.ndjson"

-- rejected at a block: a large eliminator out of a proposition, a bad
-- index, a negative occurrence, a stub recursor, a stub's positivity,
-- universes, the recursor's name and levels, the parameter count
#eval sameReject "tests/e2e/direct_sum_or_large_bad.ndjson"
-- #eval sameReject "tests/e2e/direct_idx_prop_idx_bad.ndjson"
#eval sameReject "tests/e2e/direct_fix_nat_neg_bad.ndjson"
#eval sameReject "tests/e2e/direct_fix_vec_idx_occ_bad.ndjson"
#eval sameReject "tests/e2e/ind_stub_recname.ndjson"
#eval sameReject "tests/e2e/ind_stub_reclps.ndjson"
#eval sameReject "tests/e2e/zero_ctor_bad_rec.ndjson"
#eval sameReject "tests/e2e/ind_mutual_param_bad.ndjson"
#eval sameReject "tests/e2e/ind_mutual_sort_bad.ndjson"
#eval sameReject "tests/e2e/nested_nonuniform_param.ndjson"
#eval sameReject "tests/e2e/direct_fix_wtype_neg_bad.ndjson"

end ConLecheTests.Defer
