module

public import ConLeche.Cached.ClassC
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche.Cached.ClassC

public section

/-!
# The class checker (CLASSCHECK, experimental route) on small blocks

`checkBlockClass` (`ConLeche/Kernel/Inductives/ClassCheck.lean`) at the
pure operations: an enumeration with official's recursor is accepted,
the same with its rules swapped is rejected (the rules are compared with
the generated ones); level-equivalent class spellings match.  The
full sweeps run through `class-sweep` (`tests/ClassSweep.lean`).
-/

namespace ConLecheTests.ClassCheck

open ConLeche

private def nm (s : String) : Name := .str .anonymous s
private def B : Name := nm "B2"
private def u : Name := nm "u"

/-- `inductive B2 | t | f` with `B2.rec.{u} : {motive : B2 → Sort u} →
motive t → motive f → (x : B2) → motive x` and the rules `rt`, `rf`. -/
private def enumBlock (rt rf : Expr) : List ConstantInfo :=
  let mot : Expr := .forallE (.const B []) (.sort (.param u)) default
  let recTy : Expr :=
    .forallE mot (.forallE (.app (.bvar 0) (.const (B.str "t") []))
      (.forallE (.app (.bvar 1) (.const (B.str "f") []))
        (.forallE (.const B []) (.app (.bvar 3) (.bvar 0)) default) default) default) default
  let rhs (body : Expr) : Expr :=
    .lam mot (.lam (.app (.bvar 0) (.const (B.str "t") []))
      (.lam (.app (.bvar 1) (.const (B.str "f") [])) body default) default) default
  [.indInfo ⟨B, [], .sort (.succ .zero)⟩ {},
   .ctorInfo ⟨B.str "t", [], .const B []⟩ 0 0, .ctorInfo ⟨B.str "f", [], .const B []⟩ 0 0,
   .recInfo ⟨B.str "rec", [u], recTy⟩ 3 3
     [{ ctor := B.str "t", nfields := 0, ctorParams := 0, fire := .inert, rhs := rhs rt },
      { ctor := B.str "f", nfields := 0, ctorParams := 0, fire := .inert, rhs := rhs rf }]]

private def runEnum (rt rf : Expr) : Except CheckError Env :=
  match blockParts? 0 (enumBlock rt rf) with
  | some p => checkBlockClass (pureOps .verified) Env.empty (enumBlock rt rf) p
  | none => .error (.internal "not recognised")

-- official's recursor: accepted
#guard (runEnum (.bvar 1) (.bvar 0)).toBool

-- the rules swapped: a valid term, not the generated rule — rejected
#guard runEnum (.bvar 0) (.bvar 1) matches .error (.invalid _)

-- a class spelled at an equivalent level is the same class
#guard (Expr.const (nm "List") [.max .zero .zero]).eqUpToLevels (.const (nm "List") [.zero])
#guard !(Expr.const (nm "List") [.succ .zero]).eqUpToLevels (.const (nm "List") [.zero])
-- levels compare by their simplified forms (transitive): `max u u` is not
-- simplified to `u`, so it is no spelling of `u` here
#guard !(Expr.const (nm "List") [.max (.param (nm "u")) (.param (nm "u"))]).eqUpToLevels
  (.const (nm "List") [.param (nm "u")])
-- binder data is compared (the reading reads it)
#guard !(Expr.forallE (.sort .zero) (.sort .zero) ⟨.never⟩).eqUpToLevels
  (.forallE (.sort .zero) (.sort .zero) ⟨.ifAllZero []⟩)
#guard (Expr.forallE (.sort (.max .zero .zero)) (.sort .zero) ⟨.never⟩).eqUpToLevels
  (.forallE (.sort .zero) (.sort .zero) ⟨.never⟩)

end ConLecheTests.ClassCheck
