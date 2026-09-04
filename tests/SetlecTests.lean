import Setlec
import Setlec.Frontend.Export
import SetlecTests.ZeroSetTests

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace SetlecTests

open Setlec

/-! ## Config audit (task #147/#148, vacuity protection)

The mode-relevant compiled constants the verification batteries state
their theorems at.  A theorem stated "at the default configuration"
is silently vacuous if a flag it assumes is compiled the other way;
these guards pin the actual values.  One `#guard` per pinned value,
each naming the theorem family that depends on it. -/

-- The default mode is `--set-model`: `CheckMode`'s `Inhabited` default
-- (which Main's `Args.mode := .setModel` and the driver dispatch pin
-- operationally — tests/arena.sh's mode_case exercises the flag).  The
-- set-lane consistency theorems (`checkDeclsSP_sound` /
-- `no_proof_of_Empty*` families) are consumed at this mode by the
-- #148 bridge.
#guard (default : CheckMode) == .setModel

-- The seven-check gate is OFF at every mode since task #148 T7b: the
-- declarative lane that turned it on (and its `.ttModel` value) was
-- deleted with the mode.  The gated call sites are kept, statically
-- unreachable; these guards are what would notice a mode being added
-- back without the lane that justifies it.
#guard CheckMode.ttChecks .setModel == false
#guard CheckMode.ttChecks .noModel == false

-- The λ-codomain-sort gate (task #152, `inferBody`'s `.lam` clause):
-- ON in the verified lane — the set lane's annotation pass reads the
-- fact off `inferTypeCore_lam_inv`'s `mode.verified = true → …`
-- conjunct, so compiling this `false` at `.setModel` would make that
-- conjunct vacuous — and OFF at `.noModel`, which is the
-- official-parity lane (the reference kernel's `infer_lambda` does not
-- sort-check the body's type).
#guard CheckMode.verified .setModel == true
#guard CheckMode.verified .noModel == false

-- The direct simple-structure master switch ships OFF since task #148
-- T0b (it shipped ON from #119/#120 until 2026-08-27).  BOTH verified
-- lanes assumed the switched-off configuration; the set lane's
-- relation family covers no direct-install rule, so a set-lane theorem
-- stated at the default mode would be
-- VACUOUS-BY-FALSE-HYPOTHESIS (risk R4) if this were compiled `true`.
-- Flipping it back is therefore a verification-scope change, not a
-- configuration tweak — this guard makes the flip fail `lake test`.
#guard directStructsEnabled == false

def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- An arbitrary custom axiom is a positive decline at its own record
-- (user ruling: only the tolerated whitelist may be declared).
#guard checkDecl .setModel (pureOps .setModel) Env.empty dummyAxiom matches .error (.notImplemented _)

-- A tolerated axiom (whitelist: exactly sorryAx, task #95) is
-- well-formedness-checked but not installed — the environment is
-- unchanged (the frontend declines any later use).
#guard match checkDecl .setModel (pureOps .setModel) Env.empty
    (.axiomDecl { name := .str .anonymous "sorryAx", levelParams := [],
                  type := .sort .zero }) with
  | .ok e => e.consts.isEmpty
  | .error _ => false

-- The compiler-trust family is no longer tolerated: it *installs*
-- (task #95), so without its pinned prerequisites (the True family)
-- a trustCompiler record is a positive decline at its own record.
#guard checkDecl .setModel (pureOps .setModel) Env.empty
    (.axiomDecl { name := (Name.anonymous.str "Lean").str "trustCompiler",
                  levelParams := [], type := .sort .zero })
  matches .error (.notImplemented _)

-- A garbage axiom record (its type is not a type) still rejects.
#guard checkDecl .setModel (pureOps .setModel) Env.empty
    (.axiomDecl { name := .str .anonymous "foo", levelParams := [],
                  type := .bvar 0 })
  matches .error _

-- The empty list of declarations is accepted.
#guard (checkDecls .setModel (pureOps .setModel) []).toBool == true

/-! ## Sort-fragment definitions -/

private def mkDef (n : String) (ps : List String) (type value : Expr) : Declaration :=
  .defnDecl { name := .str .anonymous n,
              levelParams := ps.map (.str .anonymous), type := type } value
    (.regular 0)

-- `def basicDef : Type := Prop` (tutorial test 001)
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "basicDef" [] (.sort (.succ .zero)) (.sort .zero)]).toBool

-- `def bad : Prop := Type` is rejected (type mismatch).
#guard checkDecls .setModel (pureOps .setModel) [mkDef "bad" [] (.sort .zero) (.sort (.succ .zero))]
  matches .error (.invalid _)

-- Duplicate universe parameters are rejected.
#guard checkDecls .setModel (pureOps .setModel) [mkDef "dup" ["u", "u"] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- Undeclared universe parameter in the type is rejected.
#guard checkDecls .setModel (pureOps .setModel) [mkDef "undecl" [] (.sort (.succ (.param (.str .anonymous "u"))))
    (.sort (.param (.str .anonymous "u")))]
  matches .error (.invalid _)

-- Duplicate declarations are rejected.
#guard checkDecls .setModel (pureOps .setModel) [mkDef "d" [] (.sort (.succ .zero)) (.sort .zero),
                   mkDef "d" [] (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- `def levelComp4.{u} : Type 0 := Sort (imax u 0)` (tutorial test 018)
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "levelComp4" ["u"] (.sort (.succ .zero))
    (.sort (.imax (.param (.str .anonymous "u")) .zero))]).toBool

/-! ## Dependent function types -/

-- `def arrowType : Type := Prop → Prop` (tutorial test 003)
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "arrowType" [] (.sort (.succ .zero))
  (.forallE (.str .anonymous "a") (.sort .zero) (.sort .zero) ⟨.default, .never⟩)]).toBool

-- `def dependentType : Prop := ∀ (p : Prop), p` (tutorial test 004):
-- impredicativity.  The binder carries the task-#161 sort annotation
-- `.ifAllZero []` ("the codomain is always a proposition"): the
-- verified mode validates annotations and declines a `.never` on a
-- Prop-codomain binder.
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .ifAllZero []⟩)]).toBool

-- … and the same declaration with the unannotated (`.never`) binder is
-- **accepted** since task #161 P5: `.never` is the parser's placeholder
-- for an absent `"pw"` field, so the annotate pass recomputes it (here
-- to `.ifAllZero []`) and the front door then validates its own write.
-- Before the pass this was a positive decline at `(forall-cod)`.  The
-- design records the consequence deliberately: an explicit
-- `"pw": "never"` is indistinguishable from an absent field and is
-- silently corrected rather than falsified, so the falsifiable claims
-- are exactly the `ifAllZero` ones (see the `bad*` guards below).
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .never⟩)]).toBool
#guard (checkDecls .noModel (pureOps .noModel) [mkDef "dependentType" [] (.sort .zero)
  (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .never⟩)]).toBool

-- `∀ (p : Prop), p : Type` is rejected (it is a Prop).
#guard checkDecls .setModel (pureOps .setModel) [mkDef "bad2" [] (.sort (.succ .zero))
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .ifAllZero []⟩)]
  matches .error (.invalid _)

-- Input expressions containing fvars are rejected.
#guard checkDecls .setModel (pureOps .setModel) [mkDef "sneaky" [] (.sort (.succ .zero))
    (.fvar 0 (.str .anonymous "x") (.sort (.succ .zero)))]
  matches .error (.invalid _)

/-! ## Theorems -/

private def mkThm (n : String) (type value : Expr) : Declaration :=
  .thmDecl { name := .str .anonymous n, levelParams := [], type := type } value

-- `theorem t : ∀ (p : Prop), p → p`-shaped: a Prop-typed theorem is accepted
-- when its (in-fragment) value matches.
#guard (checkDecls .setModel (pureOps .setModel) [mkThm "t"
    (.forallE (.str .anonymous "p") (.sort .zero) (.sort .zero) ⟨.default, .never⟩)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .never⟩)])
  matches .error (.invalid _)  -- value `∀ p, p : Prop` vs type `Prop → Prop : Prop`? mismatch

-- A theorem whose type is not a proposition is rejected (tutorial 012).
#guard checkDecls .setModel (pureOps .setModel) [mkThm "bad3" (.sort (.succ .zero)) (.sort .zero)]
  matches .error (.invalid _)

-- A theorem stating an accepted Prop with a matching proof-shaped value:
-- `theorem t2 : Prop-valued-forall` where value has exactly that type.
#guard (checkDecls .setModel (pureOps .setModel) [mkDef "prp" [] (.sort .zero)
    (.forallE (.str .anonymous "p") (.sort .zero) (.bvar 0) ⟨.default, .ifAllZero []⟩),
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

private def pwForall (pw : PropWhen) : Expr :=
  .forallE (.str .anonymous "p") (.sort .zero) (.sort .zero) ⟨.default, pw⟩

private def pwLam (pw : PropWhen) : Expr :=
  .lam (.str .anonymous "p") (.sort .zero) (.sort .zero) ⟨.default, pw⟩

-- (defeq-forall): inequivalent binder annotations on otherwise defeq
-- ∀s are a positive decline at the verified mode …
#guard defeqStep .setModel stubFns Env.empty 0 (fun a b => pure (a == b))
    (pwForall (.ifAllZero [])) (pwForall .never)
  matches .error (.notImplemented _)
-- … and no check at the unverified lane (official parity).
#guard defeqStep .noModel stubFns Env.empty 0 (fun a b => pure (a == b))
    (pwForall (.ifAllZero [])) (pwForall .never)
  matches .ok true
-- Equivalent-but-unequal annotations pass: `equiv` is semantic
-- containment, not list equality.
#guard defeqStep .setModel stubFns Env.empty 0 (fun a b => pure (a == b))
    (pwForall (.ifAllZero [.str .anonymous "u", .str .anonymous "u"]))
    (pwForall (.ifAllZero [.str .anonymous "u"]))
  matches .ok true

-- (defeq-lam): the λ congruence arm, same discipline.
#guard defeqStep .setModel stubFns Env.empty 0 (fun a b => pure (a == b))
    (pwLam (.ifAllZero [])) (pwLam .never)
  matches .error (.notImplemented _)
#guard defeqStep .noModel stubFns Env.empty 0 (fun a b => pure (a == b))
    (pwLam (.ifAllZero [])) (pwLam .never)
  matches .ok true

-- (eta): η-certifying `fun p => f p` against a stuck `f` whose stored
-- ∀-type carries an inequivalent annotation.  The real knot suffices
-- here: `etaCert` infers `f` (an fvar: the stored type is returned,
-- not walked), so the mismatched ∀ meta reaches the comparison.
private def etaStuckTy (pw : PropWhen) : Expr := pwForall pw
private def etaStuckF (pw : PropWhen) : Expr :=
  .fvar 0 (.str .anonymous "f") (etaStuckTy pw)

#guard etaCert .setModel (pureFns .setModel Env.empty 100) Env.empty 1
    (.str .anonymous "p") (.sort .zero)
    (.app (etaStuckF (.ifAllZero [])) (.bvar 0)) ⟨.default, .never⟩
    (etaStuckF (.ifAllZero []))
  matches .error (.notImplemented _)
#guard etaCert .noModel (pureFns .noModel Env.empty 100) Env.empty 1
    (.str .anonymous "p") (.sort .zero)
    (.app (etaStuckF (.ifAllZero [])) (.bvar 0)) ⟨.default, .never⟩
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
    | some decls => (checkDecls .setModel (pureOps .setModel) decls).toBool
    | none => false
  | .error _ => false

-- … and the parsed-index checker itself accepts them.
#guard match Frontend.parseExport basisModelExport with
  | .ok ⟨st, ds, _⟩ => (checkDeclsSP .setModel st ds.toList).toBool
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
  | .ok ⟨st, ds, _⟩ => (checkDeclsSP .setModel st ds.toList).toBool
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

/-! ## The correct-by-construction arena bundle (task #103)

`WFStore` carries `EStore.WF` in the type; the interface mirrors the
raw one (zero runtime cost), so these only sanity-check the lifted
operations and the unconditional derived reads. -/

private def wfsTestExpr : Expr :=
  .lam (.str .anonymous "x") (.sort .zero)
    (.app (.bvar 0) (.fvar 2 (.str .anonymous "y") (.sort .zero)))
    ⟨.default, .never⟩

-- Whole-tree interning is canonical: the same tree twice yields the
-- same index, a different tree a different one.
#guard let s := WFStore.empty
       let (i, s) := s.internExpr wfsTestExpr
       let (j, s) := s.internExpr wfsTestExpr
       let (k, _) := s.internExpr (.sort .zero)
       i == j && i != k

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

/-! ## Two-tier arena internals (task #64)

Structure-level tests of `enableTierTwo` / tier-dispatched `intern` /
`truncateTierTwo`: fresh flag-on interns go to tier two at tagged
indices, the frozen tier-one cons-table still canonicalizes, and
truncation drops tier two wholesale while every tier-one observation
is untouched.  Low-bit encoding (task #64): a node at position `p` of
tier `t` has public index `2 * p + t`. -/

private def tier0 : EStore := (EStore.empty.intern (.lit (.natVal 1))).2

-- Flag-off stores are pre-tier: flag off, tier two empty.
#guard !tier0.tierTwo && tier0.tnodes.size == 0 && tier0.nodes.size == 1

private def tierE : EStore := tier0.enableTierTwo

-- Enabling sets only the flag.
#guard tierE.tierTwo && tierE.nodes == tier0.nodes
  && tierE.tnodes.size == 0

private def tierI : EIdx × EStore := tierE.intern (.lit (.natVal 2))
private def tierE2 : EStore := tierI.2

-- A fresh flag-on intern lands in tier two at the first odd index;
-- tier one is frozen.
#guard tierI.1 == 1 && tierE2.tnodes.size == 1
  && tierE2.nodes.size == 1

-- `getNode` dispatches tier-blind on the low bit: even reads tier
-- one, odd reads tier two.
#guard tierE2.getNode 0 == some (.lit (.natVal 1))
  && tierE2.getNode 1 == some (.lit (.natVal 2))

-- Flag-on interning of tier-one content hits the frozen tier-one
-- cons-table (canonical index, no duplicate in tier two)…
#guard (tierE2.intern (.lit (.natVal 1))).1 == 0
  && (tierE2.intern (.lit (.natVal 1))).2.tnodes.size == 1

-- …and re-interning tier-two content hits the tier-two cons-table.
#guard (tierE2.intern (.lit (.natVal 2))).1 == 1

-- The derived reads dispatch: a tier-two `.bvar` node's eager bound
-- (second tier-two node, encoded index `2 * 1 + 1 = 3`).
#guard ((tierE2.intern (.bvar 3)).2.bvarBoundD 3) == 4

private def tierT : EStore := tierE2.truncateTierTwo

-- Truncation drops tier two wholesale and clears the flag…
#guard !tierT.tierTwo && tierT.tnodes.size == 0
  && tierT.tcons.size == 0 && tierT.tbvarBs.size == 0

-- …and is the identity on tier-one observations: node reads, cons
-- hits, derived reads, readback.
#guard tierT.nodes == tier0.nodes
  && tierT.getNode 0 == some (.lit (.natVal 1))
  && (tierT.intern (.lit (.natVal 1))).1 == 0
  && tierT.bvarBoundD 0 == tier0.bvarBoundD 0
  && tierT.readbackI 0 == tier0.readbackI 0

-- After truncation the store is flag-off again: fresh interns append
-- tier one (second tier-one position, encoded index `2`).
#guard (tierT.intern (.lit (.natVal 5))).1 == 2

-- The bundles: enable moves `WFStore` into `TWFStore` (the two-tier
-- invariant), tier-blind interning stays inside it, truncation
-- returns to `WFStore` — with the proofs carried by the types.
#guard let b := (WFStore.empty.internExpr (.lit (.natVal 7))).2
       let t2 := b.enableTierTwo
       let (i, t2) := t2.intern (.lit (.natVal 8))
         (by simp [ENode.children]) (by simp [ENode.levels])
         (by simp [ENode.names])
       let b' := t2.truncateTierTwo
       i == 1 && b'.raw.nodes == b.raw.nodes
         && b'.raw.tnodes.size == 0
         && b'.raw.denote 0 == b.raw.denote 0

/-! ## The β-certificate gate (task #161 S9, `Setlec/Kernel/CoreP.lean`)

The gated knot is only worth its duplication if the gate is (a) LIVE —
it reduces a redex the ungated `whnfCore` leaves stuck — and (b)
MODE-GATED, per law 1 clause (i): at `--no-model` the annotation is not
validated, so the datum must mean nothing there.  Both are pinned
here, in the vacuity-protection discipline of the config audit above.

The subject is `(fun x : Prop => x) Prop`: the argument's type is
`Type`, not `Prop`, so the per-redex certificate FAILS and the ungated
reduction is stuck at the redex.  Only the binder's `pw` datum
distinguishes the two knots. -/

private def gateNever : BinderMeta := ⟨.default, .never⟩
private def gateMaybe : BinderMeta := ⟨.default, .ifAllZero []⟩

private def gateRedex (mb : BinderMeta) : Expr :=
  .app (.lam (.str .anonymous "x") (.sort .zero) (.bvar 0) mb)
    (.sort .zero)

private def gateStuck (mb : BinderMeta) : Expr := gateRedex mb

-- The ungated knot is stuck at BOTH data: the certificate is
-- unconditional there (the task-#100 de-gating, untouched).
#guard (whnfCore .setModel Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (gateStuck gateNever)
#guard (whnfCore .setModel Env.empty 100 0 (gateRedex gateMaybe)).toOption
  == some (gateStuck gateMaybe)

-- (a) THE GATE IS LIVE: at a validated `.never` binder the gated knot
-- skips the certificate and reduces.  If this guard ever reads
-- `some (gateStuck …)` the duplicated knot has become a no-op.
#guard (whnfCoreP .setModel Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (.sort .zero)

-- (b) THE GATE IS DATUM-EXACT: at a possibly-zero datum the
-- certificate runs unconditionally — the establishment/consumption
-- asymmetry fence.
#guard (whnfCoreP .setModel Env.empty 100 0 (gateRedex gateMaybe)).toOption
  == some (gateStuck gateMaybe)

-- (c) THE GATE IS MODE-GATED (law 1 (i)): at `--no-model` the
-- annotation is not validated, so the gated knot is the ungated one.
#guard (whnfCoreP .noModel Env.empty 100 0 (gateRedex gateNever)).toOption
  == some (gateStuck gateNever)
#guard CheckMode.verified .noModel == false

/-! ## The io gate (the io-license batch, `Setlec/Kernel/CoreIO.lean`)

The take-the-waiver probe for the io app clause's statement, at the
kernel level: the gated arm of `inferTypeCoreIO_app_inv`'s disjunction
must be REACHABLE (else the clause's gated branch is a vacuous theorem
wearing a disjunction), and it must be exactly scoped — datum-exact
and mode-gated, the same three-point battery as the β gate above.

The subject applies a ∀-typed head to `.bvar 0`, whose inference
THROWS (out of fragment) — so any lane that runs the argument
certificate fails, and only a *fired* gate succeeds.  Only the ∀'s
`pw` datum and the mode distinguish the outcomes. -/

private def ioPiTy (mb : BinderMeta) : Expr :=
  .forallE (.str .anonymous "x") (.sort .zero) (.sort .zero) mb

private def ioRedex (mb : BinderMeta) : Expr :=
  .app (.fvar 0 (.str .anonymous "f") (ioPiTy mb)) (.bvar 0)

-- (a) THE io GATE IS LIVE: at a `.never` binder the io lane skips the
-- argument certificate and computes the type.
#guard (inferTypeCoreIO .setModel Env.empty 6 1 (ioRedex gateNever)).toOption
  == some (.sort .zero)

-- (b) THE io GATE IS DATUM-EXACT: at a possibly-zero datum the
-- certificate runs unconditionally (the squash fence,
-- `io_membership_fails_at_squash`).
#guard (inferTypeCoreIO .setModel Env.empty 6 1 (ioRedex gateMaybe)).toOption
  == none

-- (c) THE io GATE IS MODE-GATED (law 1 (i)): at `--no-model` the
-- annotation is not validated, so the certificate runs even at
-- `.never`.
#guard (inferTypeCoreIO .noModel Env.empty 6 1 (ioRedex gateNever)).toOption
  == none

-- (d) THE FULL LANE IS STRICTER AT BOTH DATA: the io grade narrows
-- exactly one check, so the gated arm is not absorbed by the kept one.
#guard (inferTypeCore .setModel Env.empty 6 1 (ioRedex gateNever)).toOption
  == none

end SetlecTests
