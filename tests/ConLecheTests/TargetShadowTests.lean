module

public import ConLeche
public import ConLeche.Kernel.Inductives.TargetInstall
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche
meta import ConLeche.Kernel.Inductives.TargetInstall

public section

/-!
# The target shadow, unit tests (lane TSHADOW)

`targetShadow` (`ConLeche/Kernel/Inductives/TargetInstall.lean`) is
GATED out of the install; the e2e corpus measures it through
`--target-shadow` (`tests/target-shadow.sh`), which runs the CACHED
instantiation.  These guards run the PURE one (`ShadowOps.pure`) on a
hand-built block — `U : Type | u : U` with its recursor — so the shared
code is exercised through both.
-/

namespace ConLecheTests.TargetShadow

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

@[expose] def run (rhs : Expr) : Option TargetShadowReport :=
  match targetShadow (ShadowOps.pure .verified) (mkFEnv Env.empty) 0 (block rhs) with
  | .ok r => some r
  | .error _ => none

@[expose] def words (r : Option TargetShadowReport) : Option (List String) :=
  r.map fun r => [r.install.word, r.recCheck.word, r.pos.word]

-- the generated rule `fun motive h => h`: every piece accepts
#guard words (run (lam (pi cU (.sort (.param (nm "v")))) (lam (.app (.bvar 0) cUu) (.bvar 0))))
  == some ["accept", "accept", "accept"]
-- a rule recursing on a CLOSED major (`U.rec motive h U.u`): not a
-- field of the constructor, so not a primitive recursion — REJECTED by
-- the target recursor check
#guard words (run (lam (pi cU (.sort (.param (nm "v")))) (lam (.app (.bvar 0) cUu)
    (.app (.app (.app cRec (.bvar 1)) (.bvar 0)) cUu))))
  == some ["reject", "reject", "accept"]

end ConLecheTests.TargetShadow
