module

public import ConLeche.Frontend.Prepare
public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.ExportC
public import ConLeche.Verify.Cached.StreamIndex
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Prepare
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Frontend.ExportC
meta import ConLeche.Verify.Cached.StreamIndex

public section

/-!
# The jobs against the fold

Every record's job at the frozen index (`buildIndex`, `recordJob`), walked
in position order as the driver walks them, against the fold `checkDecls`:
on accepted streams both accept and the fold's environment is
`streamEnv`, what the records say; on rejected streams the same failure at
the same position.  That is `checkDecls_of_jobs` for the accepts; for the
rejects the verdict the binary prints is the walk's, so it is pinned here.
-/

namespace ConLecheTests.Jobs

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The driver's walk over the jobs: the first failure in position order. -/
def jobsVerdict (ds : Array Declaration) : Option (CheckError × Nat) :=
  let I := buildIndex ds
  (List.range ds.size).findSome? fun k =>
    if hk : k < ds.size then
      match recordJob .verified natOpPinSets maxNatSizeDefault I k ds[k] with
      | .ok () => none
      | .error e => some (e, k)
    else none

def prepared (path : System.FilePath) : IO (Array Declaration) := do
  let b ← IO.FS.readBinFile path
  let some pre := builtinPreludeE.toOption | throw <| IO.userError "prelude"
  let .ok r := parseBytes b | throw <| IO.userError s!"{path}: does not parse"
  return preparePrelude pre r.decls

/-- An accepted stream: every job passes, the fold accepts, and its
environment is what the records say. -/
def sameAccept (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  if let some (e, k) := jobsVerdict ds then
    throw <| IO.userError s!"{path}: job {k} fails: {e}"
  match checkDecls .verified natOpPinSets maxNatSizeDefault ds with
  | .ok env =>
    let s := streamEnv ds.toList
    unless env.consts == s.consts && env.tables == s.tables do
      throw <| IO.userError s!"{path}: the environments differ"
  | .error _ => throw <| IO.userError s!"{path}: the fold rejects"

/-- A stream rejected as invalid: at the same position by the walk and
the fold. -/
def sameReject (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  match jobsVerdict ds, checkDecls .verified natOpPinSets maxNatSizeDefault ds with
  | some (.invalid _, p), .error (.invalid _, q) =>
    unless p == q do throw <| IO.userError s!"{path}: rejected at {p}, the fold at {q}"
  | _, _ => throw <| IO.userError s!"{path}: not both rejected as invalid"

-- accepted: mutual, indexed mutual, mutual structures with projections,
-- nested (a list rose tree, mutual nesting), an indexed family
#eval sameAccept "tests/e2e/inmodel_mutual.ndjson"
#eval sameAccept "tests/e2e/inmodel_mutual_idx.ndjson"
#eval sameAccept "tests/e2e/mutual_struct_proj.ndjson"
#eval sameAccept "tests/e2e/corner_nestind_f13_listrose.ndjson"
#eval sameAccept "tests/e2e/corner_nestind_d_mutual.ndjson"
#eval sameAccept "tests/e2e/indexed_vec.ndjson"
-- def-headed formers, a pinned basis block
#eval sameAccept "tests/e2e/direct_idx_defhead.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_struct.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_k.ndjson"
#eval sameAccept "tests/e2e/ind_defhead_mutual.ndjson"
#eval sameAccept "tests/e2e/ind_former_redex.ndjson"

-- rejected at a block: a large eliminator out of a proposition, a
-- negative occurrence, a stub recursor, a stub's positivity, universes,
-- the recursor's name and levels, the parameter count
#eval sameReject "tests/e2e/direct_sum_or_large_bad.ndjson"
#eval sameReject "tests/e2e/direct_fix_nat_neg_bad.ndjson"
#eval sameReject "tests/e2e/direct_fix_vec_idx_occ_bad.ndjson"
#eval sameReject "tests/e2e/ind_stub_recname.ndjson"
#eval sameReject "tests/e2e/ind_stub_reclps.ndjson"
#eval sameReject "tests/e2e/zero_ctor_bad_rec.ndjson"
#eval sameReject "tests/e2e/ind_mutual_param_bad.ndjson"
#eval sameReject "tests/e2e/ind_mutual_sort_bad.ndjson"
#eval sameReject "tests/e2e/nested_nonuniform_param.ndjson"
#eval sameReject "tests/e2e/direct_fix_wtype_neg_bad.ndjson"

-- rejected at a value record, in the middle of the stream
#eval sameReject "tests/e2e/wide_reject_mid.ndjson"
-- a name's second declaration: the index keeps the first entry, and the
-- later record's job fails on it, at that record
#eval sameReject "tests/e2e/wide_dup.ndjson"

/-- A pinned operation's job on its own: `natop_typepin_foreign`'s
`Nat.gcd` declines (no pin variant matches, its type pins not
definitionally equal), whatever fails before it in the fold. -/
def natopForeignDeclines (path : System.FilePath) : IO Unit := do
  let ds ← prepared path
  let some k := ds.findIdx? (fun d => declCLabel d == "def Nat.gcd")
    | throw <| IO.userError s!"{path}: no record Nat.gcd"
  match recordJob .verified natOpPinSets maxNatSizeDefault (buildIndex ds) k ds[k]! with
  | .error (.notImplemented m) =>
    unless (m.splitOn "a type pin").length > 1 do
      throw <| IO.userError s!"{path}: another decline: {m}"
  | _ => throw <| IO.userError s!"{path}: Nat.gcd's job does not decline"

#eval natopForeignDeclines "tests/e2e/natop_typepin_foreign.ndjson"

end ConLecheTests.Jobs
