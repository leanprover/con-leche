module

public import ConLeche
public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Frontend.ExportC
import ConLecheTests.PreludeTests
import ConLecheTests.ScanTests
import ConLecheTests.Axioms
/- The suite's `#guard`s are EVALUATED, so every constant they name must be
reachable from meta code too; a module needed at both levels is imported
twice (`public import` for the `example`s' statements, `meta import` for
the evaluation). -/
meta import ConLeche
meta import ConLeche.Kernel.Inductives.NestedInstall
meta import ConLeche.Frontend.ExportC
meta import ConLeche.Cached.Installed

public section

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace ConLecheTests

open ConLeche


/-! ## The copies' order (task #279 K.6)

`nestedTopoOrder` computes the copies' reference relation (DESIGN
§M.22's `CopyRef`, as a `Bool`) and emits a topological order, declining
a cyclic block.  No STREAM can reach the decline — a cyclic pair needs
an ill-kinded container (`J (α : Type → Type) (β : Type) | mk : α β →
J α β` together with `Foo (γ δ : Type) | mk : J δ δ → Foo γ δ`, whose
second declaration Lean rejects with an application type mismatch,
measured at v4.33.0), and an ill-kinded container never enters the
environment, so `containerInfo?` never recovers it.  These guards
therefore exercise the walk directly, on a hand-built two-copy state:
one real member at index 0, the copies at 1 and 2, each in its own mint
group, with pins that are not subterms of each other. -/

private def k6C0 : Name := .str .anonymous "C0"
private def k6C1 : Name := .str .anonymous "C1"

private def k6Copy (nm : Name) (ctorTy : Expr) : AuxType :=
  { name := nm, type := .sort .zero, ctors := [(Name.str nm "mk", ctorTy, 0)] }

/-- Two copies, at indices 1 and 2, groups `(0,1)` and `(1,1)`, pins
`P0` and `P1` (neither a subterm of the other). -/
private def k6State (c0 c1 : Expr) : ElimState :=
  { types := [{ name := Name.str .anonymous "R", type := .sort .zero, ctors := [] },
              k6Copy k6C0 c0, k6Copy k6C1 c1],
    pins := [{ aux := k6C0, container := Name.str .anonymous "A",
               pin := .const (Name.str .anonymous "P0") [], grpBase := 0, grpSize := 1 },
             { aux := k6C1, container := Name.str .anonymous "B",
               pin := .const (Name.str .anonymous "P1") [], grpBase := 1, grpSize := 1 }],
    nextIdx := 3 }

/-- The cyclic state: each copy's constructor mentions the other. -/
private def k6Cyc : ElimState := k6State (.const k6C1 []) (.const k6C0 [])
/-- The chain: copy 0 refers to copy 1, copy 1 to nothing. -/
private def k6Chain : ElimState := k6State (.const k6C1 []) (.sort .zero)

/- The reference relation holds both ways on the cyclic state. -/
#guard copyRefB (ElimState.grp k6Cyc) 1 k6Cyc 0 1
#guard copyRefB (ElimState.grp k6Cyc) 1 k6Cyc 1 0

/- A copy does not refer to itself: its own mint group is excluded. -/
#guard !copyRefB (ElimState.grp k6Cyc) 1 k6Cyc 0 0

/- **The cycle is DECLINED**, naming the two copies' pin indices. -/
#guard
  match nestedTopoOrder (ElimState.grp k6Cyc) 1 k6Cyc with
  | .error (0, 1) => true
  | _ => false

/- **A chain is ORDERED**, the referee first. -/
#guard
  match nestedTopoOrder (ElimState.grp k6Chain) 1 k6Chain with
  | .ok [1, 0] => true
  | _ => false

/- The emitted order passes the four `TopoOrder` conjuncts
(`nestedTopoOrder` checks them before returning). -/
#guard topoOrderOk (copyRefsOf (ElimState.grp k6Chain) 1 k6Chain k6Chain.pins.length)
  k6Chain.pins.length [1, 0]

/- `subB` decides the walk's subterm relation. -/
#guard Expr.subB (.const k6C0 []) (.app (.const k6C1 []) (.const k6C0 []))
#guard !Expr.subB (.const k6C0 []) (.const k6C1 [])

/-! ## The container walk's overshoot, and the cross-check that sees it
(task #279 K.20, docket D1)

`containerMembersGo` takes the maximal prefix of binders after the
parameters whose domain has the MOTIVE shape.  With at least one minor
premise it stops correctly — a minor's result is headed by a BOUND
variable, not a sort.  At a group with NO constructors the next binders
are the recursor's INDEX binders, and an index whose domain is itself
motive-shaped (`∀ (t : C p⃗), Sort _` with `C` a stored inductive at the
block's parameter spine) is taken for a second member: the OVERSHOOT the
model lane found (DESIGN §M.15).  No stream witness was found — the
obvious candidate is accepted by official AND by this route — so the
walk is exercised directly, on a hand-built recursor body.

The closure is K.15 (2)'s `containerGroupOk`, which asks every member of
a recovered group to recover THE SAME group: the guards below show the
two readings disagreeing exactly at the overshoot. -/

private def d1I : Name := .str .anonymous "D1I"
private def d1C : Name := .str .anonymous "D1C"
/-- `(α : Sort 0) → Sort 0`, the former of a zero-constructor block with
one parameter. -/
private def d1Ty : Expr := .forallE (.sort .zero) (.sort .zero) ⟨.never⟩
private def d1Env : Env :=
  ⟨[.indInfo ⟨d1C, [], d1Ty⟩ {}, .indInfo ⟨d1I, [], d1Ty⟩ {}]⟩
/-- `∀ (t : C #pIdx), Sort 0` — a motive-shaped domain at the block's
one parameter. -/
private def d1Motive (C : Name) (pIdx : Nat) : Expr :=
  .forallE (.app (.const C []) (.bvar pIdx)) (.sort .zero) ⟨.never⟩
/-- `I.rec`'s body after `stripPis 1`: the real motive, then an INDEX
binder whose domain is motive-shaped at the other zero-constructor
block. -/
private def d1RecBody : Expr :=
  .forallE (d1Motive d1I 0) (.forallE (d1Motive d1C 1) (.sort .zero) ⟨.never⟩) ⟨.never⟩
/-- `C.rec`'s body: its own motive and nothing else. -/
private def d1RecBodyC : Expr :=
  .forallE (d1Motive d1C 0) (.sort .zero) ⟨.never⟩

/- **THE OVERSHOOT**: the walk off `I.rec` reads a second member. -/
#guard containerMembersGo d1Env 1 8 0 d1RecBody == [d1I, d1C]

/- The walk off `C.rec` reads its own group alone — so the two readings
DISAGREE, which is what `containerGroupOk` (K.15 (2)) compares. -/
#guard containerMembersGo d1Env 1 8 0 d1RecBodyC == [d1C]
#guard containerMembersGo d1Env 1 8 0 d1RecBody != containerMembersGo d1Env 1 8 0 d1RecBodyC

/- With a MINOR premise in front the walk stops at the real member: a
minor's result is an application headed by a bound variable. -/
#guard containerMembersGo d1Env 1 8 0
    (.forallE (d1Motive d1I 0) (.forallE (.app (.bvar 0) (.bvar 1)) (.sort .zero) ⟨.never⟩)
      ⟨.never⟩)
  == [d1I]

/-! ## Config audit (task #147/#148, vacuity protection)

The mode-relevant compiled constants the verification batteries state
their theorems at.  A theorem stated "at the default configuration"
is silently vacuous if a flag it assumes is compiled the other way;
these guards pin the actual values.  One `#guard` per pinned value,
each naming the theorem family that depends on it. -/

-- `CheckMode` has TWO values since the SetR removal (2026-09-05), and
-- `.verified` -- the verified graded lane, `--verified` -- is the
-- first constructor, so it is both the `Inhabited` default and
-- `Main.lean`'s `Args.mode`.  Those agreed by accident before and
-- agree by construction now.  (The constructors were `.setModel` /
-- `.noModel` until the mode rename of 2026-09-06.)
--
-- The β-certificate gate is ON at it and only at it: the two accessors
-- `betaGate` and `verifiedChecks` now separate the same two modes,
-- which is what "two cores" means at the mode level.
#guard (default : CheckMode) == .verified
#guard CheckMode.betaGate .verified == true
#guard CheckMode.betaGate .trusted == false

-- The seven-check gate is OFF at every mode since task #148 T7b: the
-- declarative lane that turned it on (and its `.ttModel` value) was
-- deleted with the mode.  The gated call sites are kept, statically
-- unreachable; these guards are what would notice a mode being added
-- back without the lane that justifies it.
#guard CheckMode.ttChecks .verified == false
#guard CheckMode.ttChecks .trusted == false

-- The λ-codomain-sort gate (task #152, `inferBody`'s `.lam` clause):
-- ON in the verified lane — the set lane's annotation pass reads the
-- fact off `inferTypeCore_lam_inv`'s `mode.verifiedChecks = true → …`
-- conjunct, so compiling this `false` at a verified mode would make
-- that conjunct vacuous — and OFF at `.trusted`, which is the
-- trusted lane (the reference kernel's `infer_lambda` does not
-- sort-check the body's type).
#guard CheckMode.verifiedChecks .verified == true
#guard CheckMode.verifiedChecks .trusted == false

-- The direct simple-structure master switch ships OFF since task #148
-- T0b (it shipped ON from #119/#120 until 2026-08-27).  BOTH verified
-- lanes assumed the switched-off configuration; the set lane's
-- relation family covers no direct-install rule, so a set-lane theorem
-- stated at the default mode would be
-- VACUOUS-BY-FALSE-HYPOTHESIS (risk R4) if this were compiled `true`.
-- Flipping it back is therefore a verification-scope change, not a
-- configuration tweak — this guard makes the flip fail `lake test`.
def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- An arbitrary custom axiom is a positive decline at its own record
-- (user ruling: only the tolerated whitelist may be declared).
#guard checkDecl .verified (pureOps .verified) Env.empty dummyAxiom matches .error (.notImplemented _)

-- A tolerated axiom (whitelist: exactly sorryAx, task #95) is
-- well-formedness-checked but not installed — the environment is
-- unchanged (the frontend declines any later use).
#guard match checkDecl .verified (pureOps .verified) Env.empty
    (.axiomDecl { name := .str .anonymous "sorryAx", levelParams := [],
                  type := .sort .zero }) with
  | .ok e => e.consts.isEmpty
  | .error _ => false

-- The compiler-trust family is no longer tolerated: it *installs*
-- (task #95), so without its pinned prerequisites (the True family)
-- a trustCompiler record is a positive decline at its own record.
#guard checkDecl .verified (pureOps .verified) Env.empty
    (.axiomDecl { name := (Name.anonymous.str "Lean").str "trustCompiler",
                  levelParams := [], type := .sort .zero })
  matches .error (.notImplemented _)

-- A garbage axiom record (its type is not a type) still rejects.
#guard checkDecl .verified (pureOps .verified) Env.empty
    (.axiomDecl { name := .str .anonymous "foo", levelParams := [],
                  type := .bvar 0 })
  matches .error _

-- The empty list of declarations is accepted.
#guard (checkDeclsPure .verified (pureOps .verified) []).toBool == true

/-! ## Sort-fragment definitions -/

private def mkDef (n : String) (ps : List String) (type value : Expr) : Declaration :=
  .defnDecl { name := .str .anonymous n,
              levelParams := ps.map (.str .anonymous), type := type } value
    (.regular 0)

-- `def basicDef : Type := Prop` (tutorial test 001)
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "basicDef" [] (.sort (.succ .zero)) (.sort .zero)]).toBool

-- `def bad : Prop := Type` is rejected (type mismatch).
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "bad" [] (.sort .zero) (.sort (.succ .zero))]
  matches .error (.invalid _)

-- Duplicate universe parameters are rejected.
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "dup" ["u", "u"] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- Undeclared universe parameter in the type is rejected.
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "undecl" [] (.sort (.succ (.param (.str .anonymous "u"))))
    (.sort (.param (.str .anonymous "u")))]
  matches .error (.invalid _)

-- Duplicate declarations are rejected.
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "d" [] (.sort (.succ .zero)) (.sort .zero),
                   mkDef "d" [] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- `def levelComp4.{u} : Type 0 := Sort (imax u 0)` (tutorial test 018)
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "levelComp4" ["u"] (.sort (.succ .zero))
    (.sort (.imax (.param (.str .anonymous "u")) .zero))]).toBool

/-! ## Dependent function types -/

-- `def arrowType : Type := Prop → Prop` (tutorial test 003)
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "arrowType" [] (.sort (.succ .zero))
  (.forallE (.sort .zero) (.sort .zero) ⟨.never⟩)]).toBool

-- `def dependentType : Prop := ∀ (p : Prop), p` (tutorial test 004):
-- impredicativity.  The binder carries the task-#161 sort annotation
-- `.ifAllZero []` ("the codomain is always a proposition"): the
-- verified mode validates annotations and declines a `.never` on a
-- Prop-codomain binder.
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.sort .zero) (.bvar 0) ⟨.ifAllZero []⟩)]).toBool

-- … and the same declaration with the unannotated (`.never`) binder is
-- **accepted** since task #161 P5: `.never` is the parser's placeholder
-- for an absent `"pw"` field, so the annotate pass recomputes it (here
-- to `.ifAllZero []`) and the front door then validates its own write.
-- Before the pass this was a positive decline at `(forall-cod)`.  The
-- design records the consequence deliberately: an explicit
-- `"pw": "never"` is indistinguishable from an absent field and is
-- silently corrected rather than falsified, so the falsifiable claims
-- are exactly the `ifAllZero` ones (see the `bad*` guards below).
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.sort .zero) (.bvar 0) ⟨.never⟩)]).toBool
#guard (checkDeclsPure .trusted (pureOps .trusted) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.sort .zero) (.bvar 0) ⟨.never⟩)]).toBool

-- `∀ (p : Prop), p : Type` is rejected (it is a Prop).
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "bad2" [] (.sort (.succ .zero))
    (.forallE (.sort .zero) (.bvar 0) ⟨.ifAllZero []⟩)]
  matches .error (.invalid _)

-- Input expressions containing fvars are rejected.
#guard checkDeclsPure .verified (pureOps .verified) [mkDef "sneaky" [] (.sort (.succ .zero))
    (.fvar 0 (.sort (.succ .zero)))]
  matches .error (.invalid _)

/-! ## Theorems -/

private def mkThm (n : String) (type value : Expr) : Declaration :=
  .thmDecl { name := .str .anonymous n, levelParams := [], type := type } value

-- `theorem t : ∀ (p : Prop), p → p`-shaped: a Prop-typed theorem is accepted
-- when its (in-fragment) value matches.
#guard (checkDeclsPure .verified (pureOps .verified) [mkThm "t"
    (.forallE (.sort .zero) (.sort .zero) ⟨.never⟩)
    (.forallE (.sort .zero) (.bvar 0) ⟨.never⟩)])
  matches .error (.invalid _)  -- value `∀ p, p : Prop` vs type `Prop → Prop : Prop`? mismatch

-- A theorem whose type is not a proposition is rejected (tutorial 012).
#guard checkDeclsPure .verified (pureOps .verified) [mkThm "bad3" (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- A theorem stating an accepted Prop with a matching proof-shaped value:
-- `theorem t2 : Prop-valued-forall` where value has exactly that type.
#guard (checkDeclsPure .verified (pureOps .verified) [mkDef "prp" [] (.sort .zero)
    (.forallE (.sort .zero) (.bvar 0) ⟨.ifAllZero []⟩),
  mkThm "t2" (.sort .zero) (.const (.str .anonymous "prp") [])]).toBool == false
  -- (const prp : Prop, but Prop ≠ prp's type Prop... value `prp : Prop`; type `Prop`:
  --  `prp : Prop` vs declared `Prop : ?` — declared type must be a Prop; `Prop` is not)

/-! ## Sort-annotation validation: the defensive defeq/eta sites (task #161)

The three front-door sites — (forall-cod), (lam-cod-leaf),
(lam-cod-chain) — are exercised end-to-end by tests/annot/*.ndjson.
The three *defensive* sites — (defeq-forall), (defeq-lam), (eta) —
cannot be reached through the spec knot by any input: every path to
them first infers both compared expressions (`proofIrrel` runs before
the structural arms and before eta), and the front door validates
every binder an infer walks, so by comparison time both annotations
are valid for the same (level-equivalent) codomain sort and `equiv`
(complete) accepts.  That redundancy is by design — the checks are
placed last so they fire only on an otherwise-successful comparison —
so they are unit-tested here against a stub `CoreFns` whose `infer`
does not walk (standing in for the hostile hypothetical the P3/P4
proof rules out). -/

private def stubFns : CoreFns CheckM where
  whnfCore _ e := pure e
  whnf _ e := pure e
  infer _ _ := pure (.sort (.succ .zero))
  defeq _ a b := pure (a == b)
  annotate _ e := pure e
  inferIO _ _ := pure (.sort (.succ .zero))

private def pwForall (pw : PropWhen) : Expr :=
  .forallE (.sort .zero) (.sort .zero) ⟨pw⟩

private def pwLam (pw : PropWhen) : Expr :=
  .lam (.sort .zero) (.sort .zero) ⟨pw⟩

-- (defeq-forall): inequivalent binder annotations on otherwise defeq
-- ∀s are a positive decline at the verified mode …
#guard defeqStep .verified stubFns Env.empty 0 (fun _ a b => pure (a == b)) true
    (pwForall (.ifAllZero [])) (pwForall .never)
  matches .error (.notImplemented _)
-- … and no check at the unverified (trusted) lane.
#guard defeqStep .trusted stubFns Env.empty 0 (fun _ a b => pure (a == b)) true
    (pwForall (.ifAllZero [])) (pwForall .never)
  matches .ok true
-- Equivalent-but-unequal annotations pass: `equiv` is semantic
-- containment, not list equality.
#guard defeqStep .verified stubFns Env.empty 0 (fun _ a b => pure (a == b)) true
    (pwForall (.ifAllZero [.str .anonymous "u", .str .anonymous "u"]))
    (pwForall (.ifAllZero [.str .anonymous "u"]))
  matches .ok true

-- (pw-canonical, task #194): the datum is canonical by construction —
-- equal parameter SETS are equal VALUES, so `==`, `DecidableEq` and
-- `Hashable` decide zero-ness agreement; order and duplicates vanish at
-- the smart constructor; `inter` is commutative and idempotent as an
-- equality; instantiating at the declaration's own parameters is the
-- identity (the law amendment 2 had lost).
private def nU : Name := .str .anonymous "u"
private def nV : Name := .str .anonymous "v"
private def nW : Name := .str .anonymous "w"
#guard PropWhen.ifAllZero [nU, nV] == PropWhen.ifAllZero [nV, nU]
#guard PropWhen.ifAllZero [nU, nU] == PropWhen.ifAllZero [nU]
#guard PropWhen.ifAllZero [nW, nU, nV, nU, nW] == PropWhen.ifAllZero [nU, nV, nW]
#guard PropWhen.ifAllZero [nU, nV] != PropWhen.ifAllZero [nU]
#guard hash (PropWhen.ifAllZero [nV, nU]) == hash (PropWhen.ifAllZero [nU, nV, nU])
#guard (PropWhen.ifAllZero [nW, nV, nU, nV]).toList == [nU, nV, nW]
#guard PropWhen.ifAllZero [nU, nV] != PropWhen.never
#guard (PropWhen.ifAllZero [nU, nV]).inter (PropWhen.ifAllZero [nW])
  == (PropWhen.ifAllZero [nW]).inter (PropWhen.ifAllZero [nV, nU])
#guard (PropWhen.ifAllZero [nU]).inter (PropWhen.ifAllZero [nU]) == PropWhen.ifAllZero [nU]
#guard (PropWhen.ifAllZero [nU]).inter (PropWhen.ifAllZero [nV]) == PropWhen.ifAllZero [nV, nU]
#guard Level.substPW [nU, nV] [.param nU, .param nV] (PropWhen.ifAllZero [nV, nU])
  == PropWhen.ifAllZero [nU, nV]
#guard Level.zeronessOf (.max (.param nW) (.max (.param nU) (.param nW)))
  == PropWhen.ifAllZero [nU, nW]

-- (defeq-lam): the λ congruence arm, same discipline.
#guard defeqStep .verified stubFns Env.empty 0 (fun _ a b => pure (a == b)) true
    (pwLam (.ifAllZero [])) (pwLam .never)
  matches .error (.notImplemented _)
#guard defeqStep .trusted stubFns Env.empty 0 (fun _ a b => pure (a == b)) true
    (pwLam (.ifAllZero [])) (pwLam .never)
  matches .ok true

-- (eta): η-certifying `fun p => f p` against a stuck `f` whose stored
-- ∀-type carries an inequivalent annotation.  The real knot suffices
-- here: `etaCert` infers `f` (an fvar: the stored type is returned,
-- not walked), so the mismatched ∀ meta reaches the comparison.
private def etaStuckTy (pw : PropWhen) : Expr := pwForall pw
private def etaStuckF (pw : PropWhen) : Expr :=
  .fvar 0 (etaStuckTy pw)

#guard etaCert .verified (pureFns .verified Env.empty 100) Env.empty 1
    (.sort .zero)
    (.app (etaStuckF (.ifAllZero [])) (.bvar 0)) ⟨.never⟩
    (etaStuckF (.ifAllZero []))
  matches .error (.notImplemented _)
#guard etaCert .trusted (pureFns .trusted Env.empty 100) Env.empty 1
    (.sort .zero)
    (.app (etaStuckF (.ifAllZero [])) (.bvar 0)) ⟨.never⟩
    (etaStuckF (.ifAllZero []))
  matches .ok true

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

/-- The declared name of a directly-parsed record (`DeclC` carries no
`name` projection: its constructors differ in arity). -/
private def declCName : ConLeche.Cached.DeclC → Name
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ =>
    cv.name
  | .basisDecl _ => .anonymous
  | .indDecl b _ => (b.head?.map (·.name)).getD .anonymous

private def eqModelName : Name := Name.anonymous |>.str "Eq" |>.str "_model"
private def emptyModelAuxName : Name :=
  Name.anonymous |>.str "Empty" |>.str "_model" |>.str "proj_0"

-- The frontend keeps both declarations (`def Eq._model : Type := Prop`,
-- `def Empty._model.proj_0 : Type := Prop`) …
#guard match Frontend.parseExportD basisModelExport with
  | .ok ⟨ds, _, _, _, _, _, _, _, _, _, _⟩ => ds.map declCName == #[eqModelName, emptyModelAuxName]
  | .error _ => false

-- … and the shipped driver accepts them as ordinary definitions.
#guard match Frontend.parseExportD basisModelExport with
  | .ok ⟨ds, _, _, _, _, _, _, _, _, _, _⟩ =>
    (ConLeche.Cached.checkDecls .verified ds.toList).toBool
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
#guard match Frontend.parseExportD taintSkipExport with
  | .ok ⟨ds, sk, _, _, _, _, _, _, _, _, _⟩ =>
    ds.map declCName == #[afterName] &&
    sk == #[(usesAxName, sorryAxName), (usesUseName, sorryAxName)]
  | .error _ => false

-- … and the shipped driver accepts what remains (nothing tainted can
-- reach install: it is absent from the declarations).
#guard match Frontend.parseExportD taintSkipExport with
  | .ok ⟨ds, _, _, _, _, _, _, _, _, _, _⟩ =>
    (ConLeche.Cached.checkDecls .verified ds.toList).toBool
  | .error _ => false

-- A stream without tolerated-axiom uses records no skips.
#guard match Frontend.parseExportD basisModelExport with
  | .ok ⟨_, sk, _, _, _, _, _, _, _, _, _⟩ => sk.isEmpty
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

/-! ## The β-certificate gate (task #161 S9, `ConLeche/Kernel/CoreGated.lean`)

The gated knot is only worth its duplication if the gate is (a) LIVE —
it reduces a redex the ungated `whnfCore` leaves stuck — and (b)
MODE-GATED, per law 1 clause (i): at `--trusted` the annotation is not
validated, so the datum must mean nothing there.  Both are pinned
here, in the vacuity-protection discipline of the config audit above.

The subject is `(fun x : Prop => x) Prop`: the argument's type is
`Type`, not `Prop`, so the per-redex certificate FAILS and the ungated
reduction is stuck at the redex.  Only the binder's `pw` datum and the
mode distinguish the outcomes. -/

private def gateNever : BinderMeta := ⟨.never⟩
private def gateMaybe : BinderMeta := ⟨.ifAllZero []⟩

private def gateRedex (mb : BinderMeta) : Expr :=
  .app (.lam (.sort .zero) (.bvar 0) mb)
    (.sort .zero)

private def gateStuck (mb : BinderMeta) : Expr := gateRedex mb

-- The UNGATED-KNOT guards retired 2026-09-05: they read
--     whnfCore .verified … == some (gateStuck …)      at BOTH data
-- and pinned that the ungated knot runs the per-redex certificate
-- unconditionally (the task-#100 de-gating).  `.verified` was the R
-- mode then; the R core and its mode value are deleted, so the guards
-- pinned a mode that no longer exists.  What survives of the property
-- is (c) below, at `--trusted` — the only ungated mode left.

-- (a) THE GATE IS LIVE: at a validated `.never` binder the gated knot
-- skips the certificate and reduces.  If this guard ever reads
-- `some (gateStuck …)` the duplicated knot has become a no-op.
#guard (whnfCoreGated .verified Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (.sort .zero)

-- (b) THE GATE IS DATUM-EXACT: at a possibly-zero datum the
-- certificate runs unconditionally — the establishment/consumption
-- asymmetry fence.
#guard (whnfCoreGated .verified Env.empty 100 0 (gateRedex gateMaybe)).toOption
  == some (gateStuck gateMaybe)

-- (c) THE GATE IS MODE-GATED (law 1 (i)): at `--trusted` the
-- annotation is not validated, so the gated knot is the ungated one —
-- and, since the R core's retirement, this is also the tree's only
-- witness that the UNGATED knot runs the certificate unconditionally
-- (the task-#100 de-gating), at both data.
#guard (whnfCoreGated .trusted Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (gateStuck gateNever)
#guard (whnfCoreGated .trusted Env.empty 100 0 (gateRedex gateMaybe)).toOption
  == some (gateStuck gateMaybe)
#guard (whnfCore .trusted Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (gateStuck gateNever)
#guard CheckMode.verifiedChecks .trusted == false

/-! ## The io gate (the io-license batch, `ConLeche/Kernel/CoreIO.lean`)

The take-the-waiver probe for the io app clause's statement, at the
kernel level: the gated arm of `inferTypeCoreIO_app_inv`'s disjunction
must be REACHABLE (else the clause's gated branch is a vacuous theorem
wearing a disjunction), and it must be exactly scoped — datum-exact,
and (since the licence ruling of 2026-09-06) datum-**only**: the io
skip is a LICENCE, not certification-only work, so it fires on the
binder's `pw` alone, in both modes.  That is the one point where this
battery stopped mirroring the β gate's above, which still reads
`mode.betaGate` in the mode-parametric spec.

The subject applies a ∀-typed head to `.bvar 0`, whose inference
THROWS (out of fragment) — so any lane that runs the argument
certificate fails, and only a *fired* licence succeeds.  Only the ∀'s
`pw` datum distinguishes the outcomes. -/

private def ioPiTy (mb : BinderMeta) : Expr :=
  .forallE (.sort .zero) (.sort .zero) mb

private def ioRedex (mb : BinderMeta) : Expr :=
  .app (.fvar 0 (ioPiTy mb)) (.bvar 0)

-- (a) THE io GATE IS LIVE: at a `.never` binder the io lane skips the
-- argument certificate and computes the type.
#guard (inferTypeCoreIO .verified Env.empty 6 1 (ioRedex gateNever)).toOption
  == some (.sort .zero)

-- (b) THE io GATE IS DATUM-EXACT: at a possibly-zero datum the
-- certificate runs unconditionally (the squash fence,
-- `io_membership_fails_at_squash`).
#guard (inferTypeCoreIO .verified Env.empty 6 1 (ioRedex gateMaybe)).toOption
  == none

-- (c) THE io LICENCE IS NOT MODE-GATED (the ruling of 2026-09-06,
-- superseding the "mode-gated, law 1 (i)" guard that stood here): the
-- trusted mode omits the *validation* of the datum, never the licence
-- that reads it — so at `--trusted` the licence fires exactly as at
-- `--verified`, and it is still DATUM-exact there.
#guard (inferTypeCoreIO .trusted Env.empty 6 1 (ioRedex gateNever)).toOption
  == some (.sort .zero)
#guard (inferTypeCoreIO .trusted Env.empty 6 1 (ioRedex gateMaybe)).toOption
  == none

-- (d) THE FULL LANE IS STRICTER AT BOTH DATA: the io grade narrows
-- exactly one check, so the gated arm is not absorbed by the kept one.
#guard (inferTypeCore .verified Env.empty 6 1 (ioRedex gateNever)).toOption
  == none

/-! ## `whnf` is the identity on an inductive-headed application (task #279 K.22)

`whnf_indApp_eq` (`ConLeche/Verify/InferLemmas.lean`) proves that a
stored inductive type FORMER is whnf-stuck at any spine: no arm of
`whnfCore` applies, the literal acceleration declines and there is no
value to unfold.  These guards run the real reduction on a hand-built
environment holding one such former and read the subject back
unchanged, in both modes.

The negative control puts a stored DEFINITION at the head of the same
spine, where the delta step DOES fire — so the positive guards are not
measuring an environment in which `whnf` happens to be the identity on
everything. -/

private def k22I : Name := .str .anonymous "K22I"
private def k22D : Name := .str .anonymous "K22D"

private def k22Env : Env :=
  ⟨[.indInfo ⟨k22I, [], .sort (.succ .zero)⟩ {},
    .defnInfo ⟨k22D, [], .sort (.succ .zero)⟩ (.const k22I []) (.regular 1)]⟩

private def k22Spine (hd : Name) : Expr :=
  Expr.mkAppN (.const hd []) [.sort .zero, .sort (.succ .zero)]

#guard (whnf .verified k22Env 100 0 (k22Spine k22I)).toOption == some (k22Spine k22I)
#guard (whnf .trusted k22Env 100 0 (k22Spine k22I)).toOption == some (k22Spine k22I)

-- NEGATIVE CONTROL: the definition-headed spine reduces (to the
-- former-headed one, which is then stuck).
#guard (whnf .verified k22Env 100 0 (k22Spine k22D)).toOption == some (k22Spine k22I)

end ConLecheTests
