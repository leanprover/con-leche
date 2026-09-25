module

public import ConLeche
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche

public section

/-!
# The recursor check, unit tests

The uniform install's recursor stage (`targetRecCheck`,
`ConLeche/Kernel/Inductives/RecCheck.lean`) through the pure fold step
(`checkDecl` at `pureOps`) on a hand-built block — `U : Type | u : U`
with its recursor — so the pure instantiation is exercised beside the
cached one the e2e corpus runs.
-/

namespace ConLecheTests.RecCheck

open ConLeche

@[expose] def nm (s : String) : Name := .str .anonymous s
@[expose] def nm2 (a b : String) : Name := .str (.str .anonymous a) b
@[expose] def pi (d b : Expr) : Expr := .forallE d b default
@[expose] def lam (d b : Expr) : Expr := .lam d b default
@[expose] def cU : Expr := .const (nm "U") []
@[expose] def cUu : Expr := .const (nm2 "U" "u") []
@[expose] def cRec : Expr := .const (nm2 "U" "rec") [.param (nm "v")]

/-- `U.rec.{v} : (motive : U → Sort v) → motive U.u → (t : U) → motive t` -/
@[expose] def recTy : Expr :=
  pi (pi cU (.sort (.param (nm "v"))))
    (pi (.app (.bvar 0) cUu) (pi cU (.app (.bvar 2) (.bvar 0))))

/-- The block with the rule `U.u ↦ rhs`. -/
@[expose] def block (rhs : Expr) : List ConstantInfo :=
  [.indInfo ⟨nm "U", [], .sort (.succ .zero)⟩ {},
   .ctorInfo ⟨nm2 "U" "u", [], cU⟩ 0 0,
   .recInfo ⟨nm2 "U" "rec", [nm "v"], recTy⟩ 2 2
     [{ ctor := nm2 "U" "u", nfields := 0, ctorParams := 0, fire := .inert, rhs := rhs }]]

/-- The fold step's verdict on the block (`accept`/`reject`/`decline`/`error`). -/
@[expose] def run (rhs : Expr) : String :=
  match checkDecl .verified (pureOps .verified) [] Env.empty (.indDecl (block rhs) 0) with
  | .ok _ => "accept"
  | .error (.invalid _) => "reject"
  | .error (.notImplemented _) => "decline"
  | .error (.internal _) => "error"

-- the generated rule `fun motive h => h`: accepted
#guard run (lam (pi cU (.sort (.param (nm "v")))) (lam (.app (.bvar 0) cUu) (.bvar 0)))
  == "accept"
-- a rule recursing on a CLOSED major (`U.rec motive h U.u`): not a
-- field of the constructor, so not a primitive recursion — REJECTED by
-- the target recursor check
#guard run (lam (pi cU (.sort (.param (nm "v")))) (lam (.app (.bvar 0) cUu)
    (.app (.app (.app cRec (.bvar 1)) (.bvar 0)) cUu)))
  == "reject"

end ConLecheTests.RecCheck
