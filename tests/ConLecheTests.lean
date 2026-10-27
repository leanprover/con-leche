module

public import ConLeche
public import ConLeche.Frontend.ExportC
public import ConLeche.Model.StreamConsts
import ConLecheTests.PreludeTests
import ConLecheTests.ScanTests
import ConLecheTests.Axioms
import ConLecheTests.FileTests
import ConLecheTests.NestedTests
import ConLecheTests.RecCheckTests
import ConLecheTests.AccessTests
import ConLecheTests.LfpTypes
import ConLecheTests.CondCompare
import ConLecheTests.LetDenotes
import ConLecheTests.StreamTests
import ConLecheTests.RoundsTests
import ConLecheTests.DisplayTests
import ConLecheTests.OleanTests
/- The suite's `#guard`s are EVALUATED, so every constant they name must be
reachable from meta code too; a module needed at both levels is imported
twice (`public import` for the `example`s' statements, `meta import` for
the evaluation). -/
meta import ConLeche
meta import ConLeche.Frontend.ExportC
meta import ConLeche.Cached.Installed
meta import ConLeche.Model.StreamConsts

public section

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace ConLecheTests

open ConLeche

/-! ## Config audit (task #147/#148, vacuity protection)

The mode-relevant compiled constants the verification batteries state
their theorems at.  A theorem stated "at the default configuration"
is silently vacuous if a flag it assumes is compiled the other way;
these guards pin the actual values.  One `#guard` per pinned value,
each naming the theorem family that depends on it. -/

-- `CheckMode` has two command-line values (and their two eager towers,
-- task #353), and `.verified` -- the verified graded lane,
-- `--verified` -- is the first constructor, so it is both the
-- `Inhabited` default and `Main.lean`'s `Args.mode`.
#guard (default : CheckMode) == .verified

-- The verified mode's extra checks (the λ-codomain sort, the η and
-- λ/λ body-type comparisons): ON in the verified lane — the bridges
-- read them off the inversions' `mode.verifiedChecks = true → …`
-- conjuncts, so compiling this `false` at a verified mode would make
-- those conjuncts vacuous — and OFF at `.trusted`, which is the
-- trusted lane (the reference kernel runs none of them).
#guard CheckMode.verifiedChecks .verified == true
#guard CheckMode.verifiedChecks .trusted == false

-- The eager towers (task #353, official's `m_eager_reduce`): each runs
-- its base mode's checks, with the eager flag set; only `.verified`
-- itself is the model tier's mode.
#guard CheckMode.verifiedChecks .verifiedEager == true
#guard CheckMode.verifiedChecks .trustedEager == false
#guard CheckMode.toEager .verified == .verifiedEager
#guard CheckMode.toEager .trusted == .trustedEager
#guard (CheckMode.toEager .verified).eager && !CheckMode.eager .verified
#guard CheckMode.isVerified .verified && !CheckMode.isVerified .verifiedEager

def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- An arbitrary custom axiom is a positive decline at its own record
-- (user ruling: only the tolerated whitelist may be declared).
#guard checkDecl .verified (pureOps .verified) natOpPinSets Env.empty dummyAxiom matches .error (.notImplemented _)

-- A tolerated axiom (whitelist: exactly sorryAx, task #95) is
-- well-formedness-checked but not installed — the environment is
-- unchanged (the frontend declines any later use).
#guard match checkDecl .verified (pureOps .verified) natOpPinSets Env.empty
    (.axiomDecl { name := .str .anonymous "sorryAx", levelParams := [],
                  type := .sort .zero }) with
  | .ok e => e.consts.isEmpty
  | .error _ => false

-- The compiler-trust family is not tolerated: it *installs*
-- (task #95), so without its pinned prerequisites (the True family)
-- a trustCompiler record is a positive decline at its own record.
#guard checkDecl .verified (pureOps .verified) natOpPinSets Env.empty
    (.axiomDecl { name := (Name.anonymous.str "Lean").str "trustCompiler",
                  levelParams := [], type := .sort .zero })
  matches .error (.notImplemented _)

-- A garbage axiom record (its type is not a type) still rejects.
#guard checkDecl .verified (pureOps .verified) natOpPinSets Env.empty
    (.axiomDecl { name := .str .anonymous "foo", levelParams := [],
                  type := .bvar 0 })
  matches .error _

-- The empty list of declarations is accepted.
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets []).toBool == true

/-! ## Sort-fragment definitions -/

private def mkDef (n : String) (ps : List String) (type value : Expr) : Declaration :=
  .defnDecl { name := .str .anonymous n,
              levelParams := ps.map (.str .anonymous), type := type } value
    (.regular 0)

-- `def basicDef : Type := Prop` (tutorial test 001)
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "basicDef" [] (.sort (.succ .zero)) (.sort .zero)]).toBool

-- `def bad : Prop := Type` is rejected (type mismatch).
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "bad" [] (.sort .zero) (.sort (.succ .zero))]
  matches .error (.invalid _)

-- Duplicate universe parameters are rejected.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "dup" ["u", "u"] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- Undeclared universe parameter in the type is rejected.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "undecl" [] (.sort (.succ (.param (.str .anonymous "u"))))
    (.sort (.param (.str .anonymous "u")))]
  matches .error (.invalid _)

-- Duplicate declarations are rejected.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "d" [] (.sort (.succ .zero)) (.sort .zero),
                   mkDef "d" [] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- `def levelComp4.{u} : Type 0 := Sort (imax u 0)` (tutorial test 018)
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "levelComp4" ["u"] (.sort (.succ .zero))
    (.sort (.imax (.param (.str .anonymous "u")) .zero))]).toBool

/-! ## Dependent function types -/

-- `def arrowType : Type := Prop → Prop` (tutorial test 003)
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "arrowType" [] (.sort (.succ .zero))
  (.forallE (.sort .zero) (.sort .zero))]).toBool

-- `def dependentType : Prop := ∀ (p : Prop), p` (tutorial test 004):
-- impredicativity, in both modes.
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.sort .zero) (.bvar 0))]).toBool
#guard (checkDeclsPure .trusted (pureOps .trusted) natOpPinSets [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.sort .zero) (.bvar 0))]).toBool

-- `∀ (p : Prop), p : Type` is rejected (it is a Prop).
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "bad2" [] (.sort (.succ .zero))
    (.forallE (.sort .zero) (.bvar 0))]
  matches .error (.invalid _)

-- Input expressions containing fvars are rejected.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "sneaky" [] (.sort (.succ .zero))
    (.fvar 0 (.sort (.succ .zero)))]
  matches .error (.invalid _)

/-! ## Theorems -/

private def mkThm (n : String) (type value : Expr) : Declaration :=
  .thmDecl { name := .str .anonymous n, levelParams := [], type := type } value

-- `theorem t : ∀ (p : Prop), p → p`-shaped: a Prop-typed theorem is accepted
-- when its (in-fragment) value matches.
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkThm "t"
    (.forallE (.sort .zero) (.sort .zero))
    (.forallE (.sort .zero) (.bvar 0))])
  matches .error (.invalid _)  -- value `∀ p, p : Prop` vs type `Prop → Prop : Prop`? mismatch

-- A theorem whose type is not a proposition is rejected (tutorial 012).
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkThm "bad3" (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- A theorem stating an accepted Prop with a matching proof-shaped value:
-- `theorem t2 : Prop-valued-forall` where value has exactly that type.
#guard (checkDeclsPure .verified (pureOps .verified) natOpPinSets [mkDef "prp" [] (.sort .zero)
    (.forallE (.sort .zero) (.bvar 0)),
  mkThm "t2" (.sort .zero) (.const (.str .anonymous "prp") [])]).toBool == false
  -- (const prp : Prop, but Prop ≠ prp's type Prop... value `prp : Prop`; type `Prop`:
  --  `prp : Prop` vs declared `Prop : ?` — declared type must be a Prop; `Prop` is not)

/-! ## The `PropWhen` datum (`ConLeche/Kernel/PropWhen.lean`) -/

-- The datum is a plain list (duplicates and order kept); the checker
-- reads it only through `isNever` and `isProp`, and `holds` is its
-- meaning.
private def nU : Name := .str .anonymous "u"
private def nV : Name := .str .anonymous "v"
private def nW : Name := .str .anonymous "w"
private def φU : Name → Nat := fun n => if n == nU then 1 else 0
#guard (Level.zeronessOf (.max (.param nW) (.max (.param nU) (.param nW)))).holds φU == false
#guard (Level.zeronessOf (.max (.param nW) (.param nV))).holds φU == true
#guard (Level.zeronessOf (.imax (.param nU) (.succ (.param nV)))).isNever
#guard !(Level.zeronessOf (.max (.param nU) (.param nV))).isNever
#guard (Level.zeronessOf .zero).isProp
#guard !(Level.zeronessOf (.param nU)).isProp
#guard (Level.substPW [nU] [.zero] (Level.zeronessOf (.max (.param nU) .zero))).isProp
#guard (Level.substPW [nU, nV] [.succ .zero, .param nW]
  (PropWhen.ifAllZero [nV, nU])).isNever

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

/-- The declared name of a directly-parsed record (`Declaration` carries no
`name` projection: its constructors differ in arity). -/
private def declCName : ConLeche.Declaration → Name
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ =>
    cv.name
  | .quotDecl _ cv => cv.name
  | .basisDecl _ => .anonymous
  | .indDecl b _ => (b.head?.map (·.name)).getD .anonymous

private def eqModelName : Name := Name.anonymous |>.str "Eq" |>.str "_model"
private def emptyModelAuxName : Name :=
  Name.anonymous |>.str "Empty" |>.str "_model" |>.str "proj_0"

-- The frontend keeps both declarations (`def Eq._model : Type := Prop`,
-- `def Empty._model.proj_0 : Type := Prop`) …
#guard match Frontend.parseExportD basisModelExport with
  | .ok ⟨ds⟩ => ds.map declCName == #[eqModelName, emptyModelAuxName]
  | .error _ => false

-- … and the shipped driver accepts them as ordinary definitions.
#guard match Frontend.parseExportD basisModelExport with
  | .ok ⟨ds⟩ =>
    (ConLeche.Cached.checkDecls .verified natOpPinSets ds).toBool
  | .error _ => false

/-! ## Frontend: `sorryAx` is the fold's

The parser forwards every declaration record, the `sorryAx` axiom
record included (task #292).  The fold checks that record's type,
installs NOTHING for it — there is no set model for it — and DECLINES
at the first record that uses the name. -/

private def usesAxName : Name := Name.anonymous |>.str "usesAx"
private def usesUseName : Name := Name.anonymous |>.str "usesUse"
private def afterName : Name := Name.anonymous |>.str "after"

/-- `axiom sorryAx : ∀ (p : Prop), p` (tolerated record: checked,
installs nothing), `theorem usesAx : ∀ (p : Prop), p := sorryAx` (a
use: declines), `theorem usesUse : ∀ (p : Prop), p := usesAx` (a
transitive use), `def after : Type := Prop`. -/
private def sorryAxExport : String := String.intercalate "\n" [
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

-- EVERY record reaches the fold — the axiom's, both uses', and
-- the independent definition's.
#guard match Frontend.parseExportD sorryAxExport with
  | .ok r =>
    r.decls.map declCName == #[sorryAxName, usesAxName, usesUseName, afterName]
  | .error _ => false

-- The fold DECLINES, at the use: the axiom record installs nothing, so
-- `usesAx`'s value mentions a constant no environment holds, and the
-- name it mentions is `sorryAx`.
#guard match Frontend.parseExportD sorryAxExport with
  | .ok r =>
    match ConLeche.Cached.checkDecls .verified natOpPinSets r.decls with
    | .error (.notImplemented _, _) => true
    | _ => false
  | .error _ => false

-- The axiom record ALONE is accepted (it installs nothing): the
-- prefix up to the first use folds clean.
#guard match Frontend.parseExportD sorryAxExport with
  | .ok r =>
    (ConLeche.Cached.checkDecls .verified natOpPinSets (r.decls.take 1)).toBool
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

/-! ## Uniform β

The subject is `(fun x : Prop => x) Prop`: the argument's type is
`Type`, not `Prop`.  β carries no certificate (task #342), so the
redex reduces in both modes; the ill-typed argument is the business of
inference, not of reduction. -/

private def betaRedex : Expr :=
  .app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)

#guard (whnfCore .verified Env.empty 100 0 betaRedex).toOption
  == some (.sort .zero)
#guard (whnfCore .trusted Env.empty 100 0 betaRedex).toOption
  == some (.sort .zero)

/-! ## The io grade is official's `infer_only` (`ConLeche/Kernel/CoreIO.lean`)

The subject applies a ∀-typed head to `.bvar 0`, whose inference
THROWS (out of fragment) — so any lane that checks the argument fails,
and the io grade, which does not (task #342), computes the type. -/

private def ioRedex : Expr :=
  .app (.fvar 0 (.forallE (.sort .zero) (.sort .zero))) (.bvar 0)

-- (a) The io grade skips the argument, in both modes.
#guard (inferTypeCoreIO .verified Env.empty 6 1 ioRedex).toOption
  == some (.sort .zero)
#guard (inferTypeCoreIO .trusted Env.empty 6 1 ioRedex).toOption
  == some (.sort .zero)

-- (b) The full grade checks it.
#guard (inferTypeCore .verified Env.empty 6 1 ioRedex).toOption
  == none

/-! ## Zero-motive recursors

The recursor stage GENERATES the family and compares the stream's
recursors with it, so a recursor record without the generated motive is
rejected — official's verdict ("invalid recursor").  The witness is
`inductive ZT : Prop | c` closed by `ZT.rec : (t : ZT) → ZT` with the
rule `ZT.rec ZT.c ↦ ZT.c` — an EMPTY rule prefix, no motive.  From a
stream the frontend already refuses such a record ("declares 0 motives",
e2e `corner_rec_empty_prefix`), so these drive the kernel directly. -/

private def zNm (s : String) : Name := .str .anonymous s

private def zRule (c : Name) (rhs : Expr) : RecRule :=
  { ctor := c, nfields := 0, ctorParams := 0, fire := .plain, rhs := rhs }

/-- `inductive T : Prop | c` with the zero-motive `T.rec : (t : T) → T`
and the given rule right-hand side. -/
private def zBlock (T : Name) (rhs : Expr) : List ConstantInfo :=
  [.indInfo ⟨T, [], .sort .zero⟩ {},
    .ctorInfo ⟨T.str "c", [], .const T []⟩ 0 0,
    .recInfo ⟨T.str "rec", [], .forallE (.const T []) (.const T [])⟩ 0 0
      [zRule (T.str "c") rhs]]

/-- The kernel's recursor stage (`checkBlockRec`, the generated stage) on
a one-member block, after the pass over the formers, the constructors
and the classes: the number of recursors it stores. -/
private def zRecK (block : List ConstantInfo) : Except CheckError Nat := do
  let some p₀ := blockParts? 0 block | throw (.internal "blockParts?")
  let q ← checkBlockPass (pureOps .verified) Env.empty p₀ false
  let env₂ := consBlockCtors q.p.nP q.ctorsAs q.env₁
  let out ← checkBlockRec (pureOps .verified) env₂ q.p false q.params q.tbl.toList q.rd q.cls
    block q.cvTas
  pure out.length

-- The stage REJECTS the zero-motive recursor, whatever its rule.
#guard zRecK (zBlock (zNm "ZT") (.const ((zNm "ZT").str "c") [])) matches .error (.invalid _)
#guard zRecK (zBlock (zNm "ZT") (.const (zNm "ZT") [])) matches .error (.invalid _)

-- And so does the whole fold.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets
    [.indDecl (zBlock (zNm "ZT") (.const ((zNm "ZT").str "c") [])) 0]
  matches .error (.invalid _)

/-- The MUTUAL twin: `ZA ZB : Prop`, one constructor each, each with a
zero-motive recursor. -/
private def zMutual (rA rB : Expr) : Declaration :=
  let A := zNm "ZA"; let B := zNm "ZB"
  .indDecl [.indInfo ⟨A, [], .sort .zero⟩ {}, .indInfo ⟨B, [], .sort .zero⟩ {},
    .ctorInfo ⟨A.str "c", [], .const A []⟩ 0 0, .ctorInfo ⟨B.str "c", [], .const B []⟩ 0 0,
    .recInfo ⟨A.str "rec", [], .forallE (.const A []) (.const A [])⟩ 0 0
      [zRule (A.str "c") rA],
    .recInfo ⟨B.str "rec", [], .forallE (.const B []) (.const B [])⟩ 0 0
      [zRule (B.str "c") rB]] 0

-- Rejected at two members too, with the right rules …
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets
    [zMutual (.const ((zNm "ZA").str "c") []) (.const ((zNm "ZB").str "c") [])]
  matches .error (.invalid _)

-- … and with a wrong one.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets
    [zMutual (.const ((zNm "ZA").str "c") []) (.const (zNm "ZB") [])]
  matches .error (.invalid _)

/-! ## The decline message names the tactic behind a native axiom (task #360)

`Lean.Meta.nativeEqTrue` names its axiom
`<declaration>._native.<tactic>.ax_<i>_<j>`. -/

private def nativeAx (decl tac ax : String) : Name :=
  ((Name.anonymous.str decl).str "_native" |>.str tac).str ax

#guard nativeAxiomTactic? (nativeAx "nd" "native_decide" "ax_1_1") == some "native_decide"
#guard nativeAxiomTactic? (nativeAx "dn" "decide" "ax_1_1") == some "decide +native"
#guard nativeAxiomTactic? (nativeAx "bv" "bv_decide" "ax_1_5") == some "bv_decide"
#guard nativeAxiomTactic? (Name.anonymous.str "customAx") == none
#guard nativeAxiomTactic? (nativeAx "nd" "native_decide" "decl_1") == none

-- The installer declines such an axiom with that message.
#guard checkDeclsPure .verified (pureOps .verified) natOpPinSets
    [.axiomDecl
      { name := nativeAx "nd" "native_decide" "ax_1_1", levelParams := [], type := .sort .zero }]
  matches .error (.notImplemented "non-standard axiom (nd._native.native_decide.ax_1_1), apparently added by the `native_decide` tactic; con-leche does not support such axioms at the moment")


end ConLecheTests
