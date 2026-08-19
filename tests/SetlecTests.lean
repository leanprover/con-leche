import Setlec

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace SetlecTests

open Setlec

def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- Axioms are declined (not yet implemented).
#guard (checkDecl Env.empty dummyAxiom).toBool == false

-- The empty list of declarations is accepted.
#guard (checkDecls []).toBool == true

/-! ## Sort-fragment definitions -/

private def mkDef (n : String) (ps : List String) (type value : Expr) : Declaration :=
  .defnDecl { name := .str .anonymous n,
              levelParams := ps.map (.str .anonymous), type := type } value

-- `def basicDef : Type := Prop` (tutorial test 001)
#guard (checkDecls [mkDef "basicDef" [] (.sort (.succ .zero)) (.sort .zero)]).toBool

-- `def bad : Prop := Type` is rejected (type mismatch).
#guard checkDecls [mkDef "bad" [] (.sort .zero) (.sort (.succ .zero))]
  matches .error (.invalid _)

-- Duplicate universe parameters are rejected.
#guard checkDecls [mkDef "dup" ["u", "u"] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- Undeclared universe parameter in the type is rejected.
#guard checkDecls [mkDef "undecl" [] (.sort (.succ (.param (.str .anonymous "u"))))
    (.sort (.param (.str .anonymous "u")))]
  matches .error (.invalid _)

-- Duplicate declarations are rejected.
#guard checkDecls [mkDef "d" [] (.sort (.succ .zero)) (.sort .zero),
                   mkDef "d" [] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- `def levelComp4.{u} : Type 0 := Sort (imax u 0)` (tutorial test 018)
#guard (checkDecls [mkDef "levelComp4" ["u"] (.sort (.succ .zero))
    (.sort (.imax (.param (.str .anonymous "u")) .zero))]).toBool

/-! ## Dependent function types -/

-- `def arrowType : Type := Prop → Prop` (tutorial test 003)
#guard (checkDecls [mkDef "arrowType" [] (.sort (.succ .zero))
  (.forallE (.str .anonymous "a") (.sort .zero) (.sort .zero) .default)]).toBool

-- `def dependentType : Prop := ∀ (p : Prop), p` (tutorial test 004): impredicativity
#guard (checkDecls [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) .default)]).toBool

-- `∀ (p : Prop), p : Type` is rejected (it is a Prop).
#guard checkDecls [mkDef "bad2" [] (.sort (.succ .zero))
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) .default)]
  matches .error (.invalid _)

-- Input expressions containing fvars are rejected.
#guard checkDecls [mkDef "sneaky" [] (.sort (.succ .zero))
    (.fvar 0 (.str .anonymous "x") (.sort (.succ .zero)))]
  matches .error (.invalid _)

/-! ## Theorems -/

private def mkThm (n : String) (type value : Expr) : Declaration :=
  .thmDecl { name := .str .anonymous n, levelParams := [], type := type } value

-- `theorem t : ∀ (p : Prop), p → p`-shaped: a Prop-typed theorem is accepted
-- when its (in-fragment) value matches.
#guard (checkDecls [mkThm "t"
    (.forallE (.str .anonymous "p") (.sort .zero) (.sort .zero) .default)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) .default)])
  matches .error (.invalid _)  -- value `∀ p, p : Prop` vs type `Prop → Prop : Prop`? mismatch

-- A theorem whose type is not a proposition is rejected (tutorial 012).
#guard checkDecls [mkThm "bad3" (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- A theorem stating an accepted Prop with a matching proof-shaped value:
-- `theorem t2 : Prop-valued-forall` where value has exactly that type.
#guard (checkDecls [mkDef "prp" [] (.sort .zero)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) .default),
  mkThm "t2" (.sort .zero) (.const (.str .anonymous "prp") [])]).toBool == false
  -- (const prp : Prop, but Prop ≠ prp's type Prop... value `prp : Prop`; type `Prop`:
  --  `prp : Prop` vs declared `Prop : ?` — declared type must be a Prop; `Prop` is not)

/-! ## Level algebra -/

private def u : Level := .param (.str .anonymous "u")
private def v : Level := .param (.str .anonymous "v")

#guard Level.isEquiv (.max u v) (.max v u) == some true
#guard Level.isEquiv (.max u u) u == some true
#guard Level.isEquiv (.imax u u) u == some true
#guard Level.isEquiv (.imax (.succ .zero) u) (.max (.succ .zero) u) == some false
#guard Level.isEquiv (.imax u .zero) .zero == some true
#guard Level.isEquiv u v == some false
#guard Level.leq .zero u == some true
#guard Level.leq (.succ .zero) u == some false

end SetlecTests
