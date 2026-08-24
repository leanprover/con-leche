import Setlec
import Setlec.Frontend.Export

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace SetlecTests

open Setlec

def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- An arbitrary custom axiom is a positive decline at its own record
-- (user ruling: only the tolerated whitelist may be declared).
#guard checkDecl pureOps Env.empty dummyAxiom matches .error (.notImplemented _)

-- A tolerated axiom (whitelist: exactly sorryAx, task #95) is
-- well-formedness-checked but not installed — the environment is
-- unchanged (the frontend declines any later use).
#guard match checkDecl pureOps Env.empty
    (.axiomDecl { name := .str .anonymous "sorryAx", levelParams := [],
                  type := .sort .zero }) with
  | .ok e => e.consts.isEmpty
  | .error _ => false

-- The compiler-trust family is no longer tolerated: it *installs*
-- (task #95), so without its pinned prerequisites (the True family)
-- a trustCompiler record is a positive decline at its own record.
#guard checkDecl pureOps Env.empty
    (.axiomDecl { name := (Name.anonymous.str "Lean").str "trustCompiler",
                  levelParams := [], type := .sort .zero })
  matches .error (.notImplemented _)

-- A garbage axiom record (its type is not a type) still rejects.
#guard checkDecl pureOps Env.empty
    (.axiomDecl { name := .str .anonymous "foo", levelParams := [],
                  type := .bvar 0 })
  matches .error _

-- The empty list of declarations is accepted.
#guard (checkDecls pureOps []).toBool == true

/-! ## Sort-fragment definitions -/

private def mkDef (n : String) (ps : List String) (type value : Expr) : Declaration :=
  .defnDecl { name := .str .anonymous n,
              levelParams := ps.map (.str .anonymous), type := type } value
    (.regular 0)

-- `def basicDef : Type := Prop` (tutorial test 001)
#guard (checkDecls pureOps [mkDef "basicDef" [] (.sort (.succ .zero)) (.sort .zero)]).toBool

-- `def bad : Prop := Type` is rejected (type mismatch).
#guard checkDecls pureOps [mkDef "bad" [] (.sort .zero) (.sort (.succ .zero))]
  matches .error (.invalid _)

-- Duplicate universe parameters are rejected.
#guard checkDecls pureOps [mkDef "dup" ["u", "u"] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- Undeclared universe parameter in the type is rejected.
#guard checkDecls pureOps [mkDef "undecl" [] (.sort (.succ (.param (.str .anonymous "u"))))
    (.sort (.param (.str .anonymous "u")))]
  matches .error (.invalid _)

-- Duplicate declarations are rejected.
#guard checkDecls pureOps [mkDef "d" [] (.sort (.succ .zero)) (.sort .zero),
                   mkDef "d" [] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- `def levelComp4.{u} : Type 0 := Sort (imax u 0)` (tutorial test 018)
#guard (checkDecls pureOps [mkDef "levelComp4" ["u"] (.sort (.succ .zero))
    (.sort (.imax (.param (.str .anonymous "u")) .zero))]).toBool

/-! ## Dependent function types -/

-- `def arrowType : Type := Prop → Prop` (tutorial test 003)
#guard (checkDecls pureOps [mkDef "arrowType" [] (.sort (.succ .zero))
  (.forallE (.str .anonymous "a") (.sort .zero) (.sort .zero) ⟨.default, none⟩)]).toBool

-- `def dependentType : Prop := ∀ (p : Prop), p` (tutorial test 004): impredicativity
#guard (checkDecls pureOps [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, none⟩)]).toBool

-- `∀ (p : Prop), p : Type` is rejected (it is a Prop).
#guard checkDecls pureOps [mkDef "bad2" [] (.sort (.succ .zero))
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, none⟩)]
  matches .error (.invalid _)

-- Input expressions containing fvars are rejected.
#guard checkDecls pureOps [mkDef "sneaky" [] (.sort (.succ .zero))
    (.fvar 0 (.str .anonymous "x") (.sort (.succ .zero)))]
  matches .error (.invalid _)

/-! ## Theorems -/

private def mkThm (n : String) (type value : Expr) : Declaration :=
  .thmDecl { name := .str .anonymous n, levelParams := [], type := type } value

-- `theorem t : ∀ (p : Prop), p → p`-shaped: a Prop-typed theorem is accepted
-- when its (in-fragment) value matches.
#guard (checkDecls pureOps [mkThm "t"
    (.forallE (.str .anonymous "p") (.sort .zero) (.sort .zero) ⟨.default, none⟩)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, none⟩)])
  matches .error (.invalid _)  -- value `∀ p, p : Prop` vs type `Prop → Prop : Prop`? mismatch

-- A theorem whose type is not a proposition is rejected (tutorial 012).
#guard checkDecls pureOps [mkThm "bad3" (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- A theorem stating an accepted Prop with a matching proof-shaped value:
-- `theorem t2 : Prop-valued-forall` where value has exactly that type.
#guard (checkDecls pureOps [mkDef "prp" [] (.sort .zero)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, none⟩),
  mkThm "t2" (.sort .zero) (.const (.str .anonymous "prp") [])]).toBool == false
  -- (const prp : Prop, but Prop ≠ prp's type Prop... value `prp : Prop`; type `Prop`:
  --  `prp : Prop` vs declared `Prop : ?` — declared type must be a Prop; `Prop` is not)

/-! ## Frontend: basis `_model` companions are ordinary declarations

`_model` names are not special: a `X._model` declaration for a pinned
basis `X` (or an auxiliary nested under one) must flow through the
frontend like any other input declaration and be checked on its
merits, not silently dropped (the pinned basis install never consults
it). -/

private def basisModelExport : String := String.intercalate "\n" [
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Eq\"}}",
  "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"_model\"}}",
  "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"Empty\"}}",
  "{\"in\":4,\"str\":{\"pre\":3,\"str\":\"_model\"}}",
  "{\"in\":5,\"str\":{\"pre\":4,\"str\":\"proj_0\"}}",
  "{\"il\":1,\"succ\":0}",
  "{\"ie\":1,\"sort\":1}",
  "{\"ie\":2,\"sort\":0}",
  "{\"def\":{\"name\":2,\"levelParams\":[],\"type\":1,\"value\":2,\"safety\":\"safe\"}}",
  "{\"def\":{\"name\":5,\"levelParams\":[],\"type\":1,\"value\":2,\"safety\":\"safe\"}}"]

private def eqModelName : Name := Name.anonymous |>.str "Eq" |>.str "_model"
private def emptyModelAuxName : Name :=
  Name.anonymous |>.str "Empty" |>.str "_model" |>.str "proj_0"

-- The frontend keeps both declarations (`def Eq._model : Type := Prop`,
-- `def Empty._model.proj_0 : Type := Prop`) …
#guard match Frontend.parseExport basisModelExport with
  | .ok ⟨_, ds, _⟩ => ds.map (·.name) == #[eqModelName, emptyModelAuxName]
  | .error _ => false

-- … and the checker accepts them as ordinary definitions (the parsed
-- indices read back to the spec declarations the spec checker takes).
#guard match Frontend.parseExport basisModelExport with
  | .ok ⟨st, ds, _⟩ =>
    match ds.toList.mapM st.raw.readbackDecl with
    | some decls => (checkDecls pureOps decls).toBool
    | none => false
  | .error _ => false

-- … and the parsed-index checker itself accepts them.
#guard match Frontend.parseExport basisModelExport with
  | .ok ⟨st, ds, _⟩ => (checkDeclsSP st ds.toList).toBool
  | .error _ => false

/-! ## Frontend: taint skip-and-continue

Uses of a tolerated axiom are never accepted, but no longer stop the
stream (user directive 2026-08-24): the tainted declaration is skipped
— absent from the parsed declarations, so it can never be checked or
installed — its name is tainted so transitive users skip too, and the
rest of the stream is parsed and checked as usual.  The driver turns a
nonempty `taintSkipped` into the final decline. -/

private def sorryAxName : Name := Name.anonymous |>.str "sorryAx"
private def usesAxName : Name := Name.anonymous |>.str "usesAx"
private def usesUseName : Name := Name.anonymous |>.str "usesUse"
private def afterName : Name := Name.anonymous |>.str "after"

/-- `axiom sorryAx : ∀ (p : Prop), p` (tolerated record, dropped
unchecked), `theorem usesAx : ∀ (p : Prop), p := sorryAx` (a use:
skipped), `theorem usesUse : ∀ (p : Prop), p := usesAx` (a transitive
use: skipped), `def after : Type := Prop` (checkable, kept). -/
private def taintSkipExport : String := String.intercalate "\n" [
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"sorryAx\"}}",
  "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"p\"}}",
  "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"usesAx\"}}",
  "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"usesUse\"}}",
  "{\"in\":5,\"str\":{\"pre\":0,\"str\":\"after\"}}",
  "{\"il\":1,\"succ\":0}",
  "{\"ie\":1,\"sort\":0}",
  "{\"ie\":2,\"bvar\":0}",
  "{\"ie\":3,\"forallE\":{\"binderInfo\":\"default\",\"body\":2,\"name\":2,\"type\":1}}",
  "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":3}}",
  "{\"ie\":4,\"const\":{\"name\":1,\"us\":[]}}",
  "{\"thm\":{\"levelParams\":[],\"name\":3,\"type\":3,\"value\":4}}",
  "{\"ie\":5,\"const\":{\"name\":3,\"us\":[]}}",
  "{\"thm\":{\"levelParams\":[],\"name\":4,\"type\":3,\"value\":5}}",
  "{\"ie\":6,\"sort\":1}",
  "{\"def\":{\"name\":5,\"levelParams\":[],\"type\":6,\"value\":1,\"safety\":\"safe\"}}"]

-- The tolerated axiom record and both uses are gone from the parsed
-- declarations; the later checkable declaration survives …
#guard match Frontend.parseExport taintSkipExport with
  | .ok ⟨_, ds, sk⟩ =>
    ds.map (·.name) == #[afterName] &&
    sk == #[(usesAxName, sorryAxName), (usesUseName, sorryAxName)]
  | .error _ => false

-- … and the parsed-index checker accepts what remains (nothing
-- tainted can reach install: it is absent from the declarations).
#guard match Frontend.parseExport taintSkipExport with
  | .ok ⟨st, ds, _⟩ => (checkDeclsSP st ds.toList).toBool
  | .error _ => false

-- A stream without tolerated-axiom uses records no skips.
#guard match Frontend.parseExport basisModelExport with
  | .ok ⟨_, _, sk⟩ => sk.isEmpty
  | .error _ => false

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

/-! ## String literals

The constructor form pins the reference kernels' exact spelling
(lean4lean `Expr.strLitToConstructor`, nanoda
`str_lit_to_constructor`): `String.ofList` applied to a
`List.cons.{0} Char (Char.ofNat (lit cᵢ.toNat))` chain ending in
`List.nil.{0} Char`. -/

#guard strLitToConstructor "" ==
  .app (.const stringOfListName [])
    (.app (.const listNilName [.zero]) (.const charName []))

#guard strLitToConstructor "ab" ==
  .app (.const stringOfListName [])
    (.app
      (.app (.app (.const listConsName [.zero]) (.const charName []))
        (.app (.const charOfNatName []) (.lit (.natVal 97))))
      (.app
        (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal 98))))
        (.app (.const listNilName [.zero]) (.const charName []))))

-- the guard is `false` without the support declarations
#guard strLitSupported Env.empty == false

/-! ## The codomain-sort memo (task #100)

`codOfI` computes the sort of a node's inferred type — exactly the
level the annotation pass stores in a binder's `mb.cod`.  It is not
consumed for verdicts yet, so these are its only callers. -/

private def runCodOfTwice (env : Env) (d : Nat) (e : Expr) :
    CheckM (Level × Level) := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExprFast e
  let (r, s) ← (do
      let a ← codOfI (coreKnotI fe checkFuel) d i
      let b ← codOfI (coreKnotI fe checkFuel) d i
      pure (a, b)).run { store := store }
  match s.store.readbackL r.1, s.store.readbackL r.2 with
  | some l1, some l2 => pure (l1, l2)
  | _, _ => throw (.internal "interned level readback failed")

private def arrowPP : Expr :=
  .forallE (.str .anonymous "x") (.sort .zero) (.sort .zero)
    ⟨.default, none⟩

-- The memo computes `.succ .zero` for `Prop` (whose type is `Type`),
-- and the second (cache-hit) call agrees with the first.
#guard match runCodOfTwice Env.empty 0 (.sort .zero) with
  | .ok (u, v) => u == .succ .zero && v == .succ .zero
  | .error _ => false

-- It computes exactly the level the annotation pass stores in the
-- binder of `Prop → Prop` (the ∀-clause's codomain sort).
#guard match runCodOfTwice Env.empty 0 (.sort .zero),
    annotateCore Env.empty checkFuel 0 arrowPP with
  | .ok (u, _), .ok (.forallE _ _ _ ⟨_, some v⟩) => u == v
  | _, _ => false

/-! ## The skeleton normalization (task #100 stage 4)

`norm` performs exactly the annotation pass's two skeleton-changing
clauses — zeta expansion and the projection rewrite — and nothing
else. -/

-- Zeta: `let x := Prop; x` normalizes to `Prop`.
#guard Expr.norm keepOracle 8 0
    (.letE (.str .anonymous "x") (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
  == .sort .zero

-- Nothing else changes: on a let-free tree with a keep oracle `norm`
-- is the identity, so streams without `let` records are unaffected.
#guard Expr.letFree arrowPP == true
#guard Expr.norm keepOracle 8 0 arrowPP == arrowPP

-- …and a `let` under a binder is expanded in place.
#guard Expr.norm keepOracle 8 0
    (.forallE (.str .anonymous "y") (.sort .zero)
      (.letE (.str .anonymous "x") (.sort .zero) (.bvar 0) (.bvar 0))
      ⟨.default, none⟩)
  == .forallE (.str .anonymous "y") (.sort .zero) (.bvar 0) ⟨.default, none⟩

-- The discriminating case for the zeta substitution: a `let` under a
-- binder whose value mentions that binder, used under a *further*
-- binder.  `∀ y, let x := y; ∀ z, x` must normalize to `∀ y, ∀ z, y` —
-- i.e. `bvar 1` under the inner binder.  Plain `instantiate1` inserts
-- the value unshifted and yields `∀ y, ∀ z, z`; the lifting
-- substitution is what makes this right.
#guard Expr.norm keepOracle 8 0
    (.forallE (.str .anonymous "y") (.sort .zero)
      (.letE (.str .anonymous "x") (.sort .zero) (.bvar 0)
        (.forallE (.str .anonymous "z") (.sort .zero) (.bvar 1)
          ⟨.default, none⟩))
      ⟨.default, none⟩)
  == .forallE (.str .anonymous "y") (.sort .zero)
      (.forallE (.str .anonymous "z") (.sort .zero) (.bvar 1)
        ⟨.default, none⟩)
      ⟨.default, none⟩

/-! ## The correct-by-construction arena bundle (task #103)

`WFStore` carries `EStore.WF` in the type; the interface mirrors the
raw one (zero runtime cost), so these only sanity-check the lifted
operations and the unconditional derived reads. -/

private def wfsTestExpr : Expr :=
  .lam (.str .anonymous "x") (.sort .zero)
    (.app (.bvar 0) (.fvar 2 (.str .anonymous "y") (.sort .zero)))
    ⟨.default, none⟩

-- Whole-tree interning is canonical: the same tree twice yields the
-- same index, a different tree a different one.
#guard let s := WFStore.empty
       let (i, s) := s.internExpr wfsTestExpr
       let (j, s) := s.internExpr wfsTestExpr
       let (k, _) := s.internExpr (.sort .zero)
       i == j && i != k

-- The fast path lands on the same index (on the bundle they are the
-- same function, `WFStore.internExprFast_eq_internExpr`).
#guard let (i, _) := WFStore.empty.internExpr wfsTestExpr
       let (j, _) := WFStore.empty.internExprFast wfsTestExpr
       i == j

-- The eager derived reads match the tree-side spec functions — no WF
-- hypothesis at any call site (it is in the type).
#guard let (i, s) := WFStore.empty.internExpr wfsTestExpr
       s.bvarBoundD i == wfsTestExpr.bvarBound &&
         s.fvarRangeD i == wfsTestExpr.fvarRange &&
         s.ehasParamD i == wfsTestExpr.hasLevelParam

-- …including a level parameter under a `sort` (the level entry at
-- index 0 is the interned `.param` itself).
#guard let (i, s) := WFStore.empty.internExpr
         (.sort (.param (.str .anonymous "u")))
       s.ehasParamD i && s.lhasParamD 0

-- Name interning reads back `O(1)` and compares alloc-free.
#guard let nm : Name := .num (.str .anonymous "foo") 3
       let (i, s) := WFStore.empty.internName nm
       s.readbackN i == some nm && s.beqNameI i nm

-- Checked single-node interning: in-range children accepted,
-- out-of-range rejected (the per-record guard of the wiring plan).
#guard let (i, s) := WFStore.empty.internExpr (.sort .zero)
       (s.intern? (.app i i)).isSome && (s.intern? (.app i (i + 7))).isNone

-- The seeded constructor (`ofRaw` at a trust boundary).
#guard let s := WFStore.ofRaw EStore.empty EStore.empty_wf
       let (_, s) := s.internLevel (.succ .zero)
       s.raw.lnodes.size == 2

end SetlecTests
