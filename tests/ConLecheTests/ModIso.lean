module

public import ConLeche.MainTheorem
public import ConLeche.Verify.Modular.Isolated
meta import ConLeche.Cached.ModIso

public section

/-!
# The isolated check and the store's views (task #373)

A modular run checks every module either at its view of one store
(`--modular`) or in an environment of its own built from the units it
reads (`--modular=isolated`).  The theorems that make the two one check
— a store run is an isolated run of its units (`RunOk.isoRunOk`), an
isolated run a store run at the store of its units (`IsoRunOk.storeOk`)
— are pinned here at Lean's three axioms, and the isolated mode's
capstone is assembled: an isolated accept gives every module of the
development it stands for a model (`modular_model_exists` at
`Mod.isoRunDev`, its hypothesis `Mod.IsoRunOk.localOk`).  A few
`#guard`s evaluate the context construction, its lookup and its
duplicates' check on a toy set of units.
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
info: 'ConLeche.Cached.Mod.RunOk.isoStoreOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.isoStoreOk

/--
info: 'ConLeche.Cached.Mod.IsoStoreOk.runOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsoStoreOk.runOk

/--
info: 'ConLeche.Cached.Mod.IsoRunOk.storeOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsoRunOk.storeOk

/--
info: 'ConLeche.Cached.Mod.IsoRunOk.localOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsoRunOk.localOk

/--
info: 'ConLeche.Cached.Mod.RunOk.isoRunOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RunOk.isoRunOk

/-! ## The isolated mode's capstone -/

universe w

/-- **An isolated accept has a model**: one assignment of sets to the
qualified names, every proof the point, under which every module's own
environment — its constants over the context built from the units it
reads — has a model. -/
example (V : Type w) [SetTheory V] {slots : Array (Thunk ModSlot)} {M : Array ModData}
    (h : IsoRunOk .verified slots M) (i : Nat) :
    ∃ G : Modular.Key → (LevelParam → Nat) → V,
      (∀ n lps T φ, G (.proof n lps T) φ = SetTheory.pt) ∧
      ∀ j ≤ i, ∃ m : Model V (isoRunDev slots M j).own,
        ∀ n, ((isoRunDev slots M j).own.find? n).isSome = true →
          m.cval n = G ((isoRunDev slots M j).res n) :=
  modular_model_exists V natOpPinSets (isoRunDev slots M) i fun j _ => h.localOk j

/-- **So has a store accept, as an isolated run of its units**
(`RunOk.isoRunOk`). -/
example (V : Type w) [SetTheory V] {S : Store} {M : Array ModData}
    (h : RunOk .verified S M) (i : Nat) :
    ∀ j ≤ i, ∀ c ∈ (isoRunDev S.slots (ownData M) j).own.consts,
      c.toConstantVal.type = .const falseName [] → False :=
  modular_no_False V natOpPinSets (isoRunDev S.slots (ownData M)) i fun j _ => h.isoRunOk.localOk j

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

-- The one pass computes the context's lookup (module, position, constant)…
#guard (isoBuild slots (ByteArray.mk #[1, 1, 0])).look (nm "a") = some (0, 0, defn "a")
#guard (isoBuild slots (ByteArray.mk #[0, 1, 0])).look (nm "a") = some (1, 0, defn "a")
#guard (isoBuild slots (ByteArray.mk #[1, 2, 0])).look (nm "c") = some (1, 1, defn "c")
-- …and the duplicates: both modules store an ordinary `a`, which meet when
-- both are loaded (two qualified names), and not when only one is.
#guard (isoBuild slots (ByteArray.mk #[1, 1, 0])).dropped = [(1, 0, nm "a")]
#guard !((isoBuild slots (ByteArray.mk #[1, 1, 0])).keysOk slots)
#guard (isoBuild slots (ByteArray.mk #[0, 1, 0])).keysOk slots
-- A module loaded at the exported level is read without its private record.
#guard (mask slots (ByteArray.mk #[1, 2, 0]) 0).prv.priv.isEmpty
#guard (mask slots (ByteArray.mk #[1, 2, 0]) 1).prv.priv.size = 2
#guard (mask slots (ByteArray.mk #[0, 2, 0]) 0) == {}

end ConLecheTests.ModIso
