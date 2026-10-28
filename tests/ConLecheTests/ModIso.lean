module

public import ConLeche.MainTheorem
public import ConLeche.Verify.Modular.IsoRun
meta import ConLeche.Cached.ModIso

public section

/-!
# The isolated check and the store's views (task #373)

A modular run checks every module either at its view of one store
(`--modular`) or in an environment of its own built from its imports'
units (`--modular=isolated`).  The theorems that make the two one
check are pinned here at Lean's three axioms, and the isolated mode's
capstone is assembled: an isolated accept gives every module of the
isolated development a model (`modular_model_exists` at
`Mod.isoDevOf`, its hypothesis `Mod.IsoRunOk.localOk`).  A few
`#guard`s evaluate the context construction on a toy store.
-/

namespace ConLecheTests.ModIso

open ConLeche ConLeche.Cached ConLeche.Cached.Mod

/-! ## The equivalence, at the three axioms -/

/--
info: 'ConLeche.Cached.Mod.checkAtView_isolated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkAtView_isolated

/--
info: 'ConLeche.Cached.Mod.RunOk.isoRunOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.isoRunOk

/--
info: 'ConLeche.Cached.Mod.IsoRunOk.runOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsoRunOk.runOk

/--
info: 'ConLeche.Cached.Mod.IsoRunOk.localOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsoRunOk.localOk

/-! ## The isolated mode's capstone -/

universe w

/-- **An isolated accept has a model**: one assignment of sets to the
qualified names, every proof the point, under which every module's own
environment — its constants over the context built from its imports'
units — has a model. -/
example (V : Type w) [SetTheory V] {S : Store} {M : Array ModData}
    (h : IsoRunOk .verified S M) (i : Nat) :
    ∃ G : Modular.Key → (LevelParam → Nat) → V,
      (∀ n lps T φ, G (.proof n lps T) φ = SetTheory.pt) ∧
      ∀ j ≤ i, ∃ m : Model V (isoDevOf S M j).own,
        ∀ n, ((isoDevOf S M j).own.find? n).isSome = true → m.cval n = G ((isoDevOf S M j).res n) :=
  modular_model_exists V natOpPinSets (isoDevOf S M) i fun j _ => h.localOk j

/-- **So has a store accept, in the isolated development**: a store run
is an isolated run (`RunOk.isoRunOk`). -/
example (V : Type w) [SetTheory V] {S : Store} {M : Array ModData}
    (h : RunOk .verified S M) (hI : IdxOk S) (i : Nat) :
    ∀ j ≤ i, ∀ c ∈ (isoDevOf S M j).own.consts, c.toConstantVal.type = .const falseName [] → False :=
  modular_no_False V natOpPinSets (isoDevOf S M) i fun j _ => h.localOk_iso hI j

/-! ## The context on a toy store -/

/-- A name. -/
def nm (s : String) : Name := Name.anonymous |>.str s

/-- A definition `s : Prop := Prop` (the content does not matter). -/
def defn (s : String) : ConstantInfo :=
  .defnInfo ⟨nm s, [], .sort .zero⟩ (.sort .zero) .opaque

/-- Module 0: `a` and `b`; `b`'s value needs module 1 at its private
level. -/
def slot0 : ModSlot :=
  { exp := { at1 := #[some (defn "a"), some (defn "b")], stored := #[true, true],
             tbls := #[none, none], g1 := #[#[], #[]], v1 := #[#[], #[(1, 2)]],
             prf := #[false, false] }
    prv := { priv := #[defn "a", defn "b"], tbls := #[none, none] } }

/-- Module 1: another `a`, and `c`, exported absent. -/
def slot1 : ModSlot :=
  { exp := { at1 := #[some (defn "a"), none], stored := #[true, false], tbls := #[none, none],
             g1 := #[#[], #[]], v1 := #[#[], #[]], prf := #[false, false] }
    prv := { priv := #[defn "a", defn "c"], tbls := #[none, none] } }

def slots : Nat → ModSlot
  | 0 => slot0
  | 1 => slot1
  | _ => {}

-- Both at the exported level: `b` is the assumption of its statement
-- (its value gate is closed), `c` is absent, `a` once.
#guard (isoCtx slots (ByteArray.mk #[1, 1, 0])).find? (nm "b") =
  some (.axiomInfo ⟨nm "b", [], .sort .zero⟩)
#guard (isoCtx slots (ByteArray.mk #[1, 1, 0])).find? (nm "c") = none
#guard ((isoCtx slots (ByteArray.mk #[1, 1, 0])).consts.map (·.name)).length = 2
-- Module 1 privately: `b` is presented as stored, `c` is there.
#guard (isoCtx slots (ByteArray.mk #[1, 2, 0])).find? (nm "b") = some (defn "b")
#guard (isoCtx slots (ByteArray.mk #[1, 2, 0])).find? (nm "c") = some (defn "c")
-- A module not loaded presents nothing (and is not read).
#guard (isoCtx slots (ByteArray.mk #[0, 1, 0])).find? (nm "b") = none
#guard ((isoCtx slots (ByteArray.mk #[0, 0, 0])).consts).isEmpty

end ConLecheTests.ModIso
