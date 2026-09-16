module

public import ConLeche.Model.Inductives.BlockRecKit
public import ConLeche.SetTheory.Derive.LfpCompose
public section

/-!
# The nested block's recursor candidate over `k + nPins` classes (task #315, M7 — lane L-D)

`BlockRecCand.lean`'s twin for a block WITH pins: the recursion
classes are the `k` members followed by the `nPins` pins (a target in
`members ++ pins`, `BlockModel.tgts`), the union is over the members'
carriers AND the pins' carriers at the least tuple (`famAt` at `L`,
DESIGN §U.1 (b): "the pins' recursors are the union's pin
components"), and the recursor is the class recursor `unionRecC`
(`SetModel/UnionRec.lean`) — a pin's class is not a component of the
tuple lfp, so its accessibility is the PINS' own induction
(`PinRecLaws.ind`), the block-model form of `NestedTreeList.lean`'s
`treeAccL_of_param`.

**The extended block model.**  `IsBlockModel` says nothing about a
pin's CONSTRUCTORS (its carrier is the abstract `pinCar`, tied down by
`pinMem`/`pinMono`/`pinLeaf` — §U.13 (b) left the pin's fibre to its
consumer, M7): what the kit needs of pin `q` is `PinCtors` — the
container's constructors AT THE PIN (the copies, restored: `List.cons`
at `Tree` has fields `Tree p⃗` targeting member `0` and `List (Tree p⃗)`
targeting pin `0`), with their field domains at the block's parameter
frame, recursive flags, targets in `members ++ pins`, telescopes,
index expressions, result readings and injection — and `PinRecLaws`,
the semantic laws over them: the targets are classes, the pin's
carrier at every tuple `X` of the space decomposes by the pin's
constructors with the recursive fields read at `famAt X` (`fibre`),
the injections are the point at `Prop` and injective within the pin
(`mkZero`/`mkInj`), the pins' index telescopes are graded at the pins'
frames (`idxOk`), and **the pins' carriers at `X` are the LEAST
families closed under the pins' constructors** (`ind`: the induction
principle with the pins read at the SEPARATED pins — the block-model
form of `lfpTuple_induction` at the pins' section).  At the composed
model `BlockModel.ofNested` every law is the sealed operator's at the
copies' positions (`tupleLfpΦ_fibre` at `k + nPins`, the pins' section
`pinsCar` = an `lfpTuple`); the discharge is the stage's (DESIGN
§U.25).

**The class readers** (`_T` suffix): a class `c < k + nPins` reads the
member's data at `c < k` and pin `c - k`'s otherwise — index count,
index set (`idxT`: the member's `idx`, the pin's `pinIdx`), tuple
(`tupT` at the class's sort `uT`), constructors, fields, flags,
targets, telescopes, index expressions, result readings, injection;
the minors are in AUXILIARY order (the members' constructors first,
then pin `0`'s, pin `1`'s, …: `minorIdxT`, `nCtorsT` — official's
`restoreNested` keeps the auxiliary block's minor order, §U.12).  A
recursive slot is read over an EXTENDED tuple `Y : Nat → V` of `k +
nPins` families (`slotAtT`, `ChainFitT`); the block model's `famAt ψ
ρp X` is the extended tuple at `X`.

**The kit**: `PredRelT`/`kitPredT` (predecessors tagged by their
target CLASS), `kitBT` (the class's motive at its index spine),
`kitIhsT`/`kitStAtT`/`kitStT` (the step: decode by the class's
injection, the minor at `minorIdxT`), `blockRecAtT` (= `unionRecC` at
the extended classes at the carrier), `blockLeafVT` (the frame
`(p⃗, M⃗, m⃗, ı⃗_c, t)` of the RESTORED recursor type: `k + nPins`
motives, `nCtorsT` minors), `blockCandT`.

PROVED here: `kitPredT_from_mem` (a member-class element built at `X`
has its predecessors in the extended union at `X` — the block model's
`fibre` with pin targets allowed), `kitPredT_from_pin` (a pin-class
element at `X`, by `PinRecLaws.fibre`), **`nestedAcc_all`** (every
element of the extended union at the carrier is accessible along
`kitPredT`: the members by `lfpTuple_induction`, the pins by
`PinRecLaws.ind` at the separated tuple and at the carrier), the class
kit `nestedKitC` and its two laws `blockRecAtT_mem_B`/`blockRecAtT_eq`
under the bound's and the step's obligations, and the bound's
obligation `kitBT_mem` at a semantic motive typing.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The pins' constructors at the pin -/

/-- **A pin's constructors at the pin** (see the module docstring):
the container's constructors instantiated at the pin's components —
per constructor its field domains at the block's parameter frame
(depth `nP`; a recursive entry is its target's family applied), its
recursive flags, its fields' targets in `members ++ pins`, its
reflexive telescopes and index expressions, its result's index
readings — and the pin's injection (the container's, abstract). -/
structure PinCtors (V : Type w) where
  /-- the container's constructors, with their field counts -/
  ctors : List (ConstantVal × Nat)
  /-- per constructor: the field domains at the block's parameter frame -/
  Fss : (Name → Nat) → List (List AnnotTerm)
  /-- per constructor: the recursive flags -/
  rss : List (List Bool)
  /-- per constructor and field: the target class -/
  tgts : Nat → Nat → Nat
  /-- per constructor: the reflexive fields' telescopes -/
  tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))
  /-- per constructor: the recursive fields' index expressions -/
  Eiss : (Name → Nat) → List (List (List AnnotTerm))
  /-- per constructor: the result's index readings -/
  Ess : (Name → Nat) → List (List AnnotTerm)
  /-- the injection at a field spine -/
  inj : (Name → Nat) → Nat → List V → V

noncomputable instance : Inhabited (PinCtors V) :=
  ⟨⟨[], fun _ => [], [], fun _ _ => 0, fun _ => [], fun _ => [], fun _ => [], fun _ _ _ => pt⟩⟩

namespace BlockModel

variable (d : BlockModel V) (pc : Nat → PinCtors V)

/-! ### The class readers -/

/-- The number of classes. -/
@[expose] def kT : Nat := d.k + d.nPins

/-- A class's index count. -/
@[expose] def nIdxT (c : Nat) : Nat := if c < d.k then d.nIdxAt c else (d.pinAt (c - d.k)).nIdx

/-- A class's index telescope (the member's at the parameter frame;
the pin's container's, at the pin's frame). -/
@[expose] def IdsT (c : Nat) (ψ : Name → Nat) : List AnnotTerm :=
  if c < d.k then d.IdsM c ψ else (d.pinAt (c - d.k)).Ids ψ

/-- A class's frame at the parameter frame: the parameters for a
member, the pin's frame for a pin. -/
@[expose] noncomputable def frameT (c : Nat) (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  if c < d.k then ρp else d.pinFrame (c - d.k) ψ ρp

/-- **A class's index-tuple set**: the member's `idx`, the pin's `pinIdx`. -/
@[expose] noncomputable def idxT (ψ : Name → Nat) (ρp : Nat → V) (c : Nat) : V :=
  if c < d.k then d.idx ψ ρp c else d.pinIdx (c - d.k) ψ ρp

/-- A class's index spine as its tuple (at the class's sort `uT`). -/
@[expose] noncomputable def tupT (ψ : Name → Nat) (c : Nat) (is : List V) : V := tupW (d.uT c ψ) is

/-- A class's constructors. -/
@[expose] def ctorsT (c : Nat) : List (ConstantVal × Nat) :=
  if c < d.k then d.ctorsM c else (pc (c - d.k)).ctors

/-- A class's field domains, per constructor. -/
@[expose] def FssT (ψ : Name → Nat) (c : Nat) : List (List AnnotTerm) :=
  if c < d.k then d.Fss c ψ else (pc (c - d.k)).Fss ψ

/-- A class's recursive flags, per constructor. -/
@[expose] def rssT (c : Nat) : List (List Bool) := if c < d.k then d.rss c else (pc (c - d.k)).rss

/-- A class's targets, per constructor and field. -/
@[expose] def tgtsT (c : Nat) : Nat → Nat → Nat := if c < d.k then d.tgts c else (pc (c - d.k)).tgts

/-- A class's reflexive telescopes, per constructor. -/
@[expose] def tlssT (ψ : Name → Nat) (c : Nat) : List (List (List (Nat × Nat × AnnotTerm))) :=
  if c < d.k then d.tlss c ψ else (pc (c - d.k)).tlss ψ

/-- A class's recursive fields' index expressions, per constructor. -/
@[expose] def EissT (ψ : Name → Nat) (c : Nat) : List (List (List AnnotTerm)) :=
  if c < d.k then d.Eiss c ψ else (pc (c - d.k)).Eiss ψ

/-- A class's results' index readings, per constructor. -/
@[expose] def EssT (ψ : Name → Nat) (c : Nat) : List (List AnnotTerm) :=
  if c < d.k then d.Ess c ψ else (pc (c - d.k)).Ess ψ

/-- A class's injection. -/
@[expose] def injT (ψ : Name → Nat) (c : Nat) : Nat → List V → V :=
  if c < d.k then d.inj ψ c else (pc (c - d.k)).inj ψ

/-- The minors' count: every class's constructors. -/
@[expose] def nCtorsT : Nat := ((List.range d.kT).map fun c => (d.ctorsT pc c).length).sum

/-- The minor index of class `c`'s constructor `j` (auxiliary order:
the members' constructors, then the pins' in pin order). -/
@[expose] def minorIdxT (c j : Nat) : Nat :=
  ((List.range c).map fun t => (d.ctorsT pc t).length).sum + j

/-- Field `i'`'s telescope at a class. -/
@[expose] def teleAtT (ψ : Name → Nat) (c j i' : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((d.tlssT pc ψ c).getD j []).getD i' []

/-- Field `i'`'s index expressions at a class. -/
@[expose] def eisAtT (ψ : Name → Nat) (c j i' : Nat) : List AnnotTerm :=
  ((d.EissT pc ψ c).getD j []).getD i' []

/-- **A recursive slot over an EXTENDED tuple** `Y` of `k + nPins`
families: field `i` of class `c`'s constructor `j` reads its target
class's family `Y (tgtsT c j i)` at the tuple of its index expressions
under its telescope. -/
@[expose] noncomputable def slotAtT (ψ : Name → Nat) (Y : Nat → V) (c j i : Nat) (ρ : Nat → V) : V :=
  slotSet (d.w ψ) (d.uT (d.tgtsT pc c j i) ψ) ρ (d.teleAtT pc ψ c j i) (d.eisAtT pc ψ c j i)
    (Y (d.tgtsT pc c j i))

/-- **A field spine fits class `c`'s constructor `j` at the extended
tuple `Y` and index tuple `t`** (`ChainFit`'s twin over the classes). -/
@[expose] def ChainFitT (ψ : Name → Nat) (ρp : Nat → V) (Y : Nat → V) (t : V) (c j : Nat)
    (fs : List V) : Prop :=
  FitsFrom ((d.rssT pc c).getD j []) (d.slotAtT pc ψ Y c j) 0 ρp ((d.FssT pc ψ c).getD j []) fs ∧
  ∀ l, l < (d.IdsT c ψ).length →
    interp V (consList fs ρp) (((d.EssT pc ψ c).getD j []).getD l default) = projS l t

/-- **The separated pins**: pin `q`'s carrier at `X` cut down to a
property (the pins' `sepTuple`). -/
@[expose] noncomputable def sepPins (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V)
    (P : Nat → V → V → Prop) (q : Nat) : V :=
  graph (fun t => sep (app (d.pinCar ψ ρp X q) t) (P q t)) (d.pinIdx q ψ ρp)

/-! ### The class readers at a member -/

section Members

variable {d pc} {c : Nat} (hc : c < d.k)
include hc

omit [SetTheory V] in
theorem nIdxT_of_mem : d.nIdxT c = d.nIdxAt c := by simp only [nIdxT, if_pos hc]
omit [SetTheory V] in
theorem IdsT_of_mem (ψ : Name → Nat) : d.IdsT c ψ = d.IdsM c ψ := by simp only [IdsT, if_pos hc]
theorem frameT_of_mem (ψ : Name → Nat) (ρp : Nat → V) : d.frameT c ψ ρp = ρp := by
  simp only [frameT, if_pos hc]
theorem idxT_of_mem (ψ : Name → Nat) (ρp : Nat → V) : d.idxT ψ ρp c = d.idx ψ ρp c := by
  simp only [idxT, if_pos hc]
omit [SetTheory V] in
theorem uT_of_mem (ψ : Name → Nat) : d.uT c ψ = d.uM c ψ := by simp only [uT, if_pos hc]
theorem tupT_of_mem (ψ : Name → Nat) (is : List V) : d.tupT ψ c is = d.tup ψ c is := by
  simp only [tupT, tup, uT, if_pos hc]
omit [SetTheory V] in
theorem ctorsT_of_mem : d.ctorsT pc c = d.ctorsM c := by simp only [ctorsT, if_pos hc]
omit [SetTheory V] in
theorem FssT_of_mem (ψ : Name → Nat) : d.FssT pc ψ c = d.Fss c ψ := by simp only [FssT, if_pos hc]
omit [SetTheory V] in
theorem rssT_of_mem : d.rssT pc c = d.rss c := by simp only [rssT, if_pos hc]
omit [SetTheory V] in
theorem tgtsT_of_mem : d.tgtsT pc c = d.tgts c := by simp only [tgtsT, if_pos hc]
omit [SetTheory V] in
theorem tlssT_of_mem (ψ : Name → Nat) : d.tlssT pc ψ c = d.tlss c ψ := by
  simp only [tlssT, if_pos hc]
omit [SetTheory V] in
theorem EissT_of_mem (ψ : Name → Nat) : d.EissT pc ψ c = d.Eiss c ψ := by
  simp only [EissT, if_pos hc]
omit [SetTheory V] in
theorem EssT_of_mem (ψ : Name → Nat) : d.EssT pc ψ c = d.Ess c ψ := by simp only [EssT, if_pos hc]
omit [SetTheory V] in
theorem injT_of_mem (ψ : Name → Nat) : d.injT pc ψ c = d.inj ψ c := by simp only [injT, if_pos hc]
omit [SetTheory V] in
theorem teleAtT_of_mem (ψ : Name → Nat) (j i' : Nat) : d.teleAtT pc ψ c j i' = d.teleAt ψ c j i' := by
  simp only [teleAtT, teleAt, tlssT, if_pos hc]
omit [SetTheory V] in
theorem eisAtT_of_mem (ψ : Name → Nat) (j i' : Nat) : d.eisAtT pc ψ c j i' = d.eisAt ψ c j i' := by
  simp only [eisAtT, eisAt, EissT, if_pos hc]

/-- A member's slot over the extended tuple at `X` is its slot at `X`,
at a frame whose parameter part is `ρp` (the pin's carrier is taken at
the slot's frame below the fields). -/
theorem slotAtT_of_mem (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (j i : Nat) {fs' : List V}
    (hlen : fs'.length = i) :
    d.slotAtT pc ψ (d.famAt ψ ρp X) c j i (consList fs' ρp) = d.slotAt ψ X c j i (consList fs' ρp) := by
  have hρ : (fun n => consList fs' ρp (n + i)) = ρp :=
    funext fun n => by rw [← hlen]; exact consList_apply_add fs' ρp n
  simp only [slotAtT, slotAt, teleAtT, eisAtT, tlssT, EissT, tgtsT, if_pos hc, hρ]

end Members

/-! ### The class readers at a pin -/

section Pins

variable {d pc} {c : Nat} (hc : ¬ c < d.k)
include hc

omit [SetTheory V] in
theorem nIdxT_of_pin : d.nIdxT c = (d.pinAt (c - d.k)).nIdx := by simp only [nIdxT, if_neg hc]
omit [SetTheory V] in
theorem IdsT_of_pin (ψ : Name → Nat) : d.IdsT c ψ = (d.pinAt (c - d.k)).Ids ψ := by
  simp only [IdsT, if_neg hc]
theorem frameT_of_pin (ψ : Name → Nat) (ρp : Nat → V) : d.frameT c ψ ρp = d.pinFrame (c - d.k) ψ ρp := by
  simp only [frameT, if_neg hc]
theorem idxT_of_pin (ψ : Name → Nat) (ρp : Nat → V) : d.idxT ψ ρp c = d.pinIdx (c - d.k) ψ ρp := by
  simp only [idxT, if_neg hc]
omit [SetTheory V] in
theorem uT_of_pin (ψ : Name → Nat) : d.uT c ψ = (d.pinAt (c - d.k)).u ψ := by
  simp only [uT, if_neg hc]
omit [SetTheory V] in
theorem ctorsT_of_pin : d.ctorsT pc c = (pc (c - d.k)).ctors := by simp only [ctorsT, if_neg hc]
omit [SetTheory V] in
theorem FssT_of_pin (ψ : Name → Nat) : d.FssT pc ψ c = (pc (c - d.k)).Fss ψ := by
  simp only [FssT, if_neg hc]
omit [SetTheory V] in
theorem rssT_of_pin : d.rssT pc c = (pc (c - d.k)).rss := by simp only [rssT, if_neg hc]
omit [SetTheory V] in
theorem tgtsT_of_pin : d.tgtsT pc c = (pc (c - d.k)).tgts := by simp only [tgtsT, if_neg hc]
omit [SetTheory V] in
theorem tlssT_of_pin (ψ : Name → Nat) : d.tlssT pc ψ c = (pc (c - d.k)).tlss ψ := by
  simp only [tlssT, if_neg hc]
omit [SetTheory V] in
theorem EissT_of_pin (ψ : Name → Nat) : d.EissT pc ψ c = (pc (c - d.k)).Eiss ψ := by
  simp only [EissT, if_neg hc]
omit [SetTheory V] in
theorem EssT_of_pin (ψ : Name → Nat) : d.EssT pc ψ c = (pc (c - d.k)).Ess ψ := by
  simp only [EssT, if_neg hc]
omit [SetTheory V] in
theorem injT_of_pin (ψ : Name → Nat) : d.injT pc ψ c = (pc (c - d.k)).inj ψ := by
  simp only [injT, if_neg hc]

end Pins

omit [SetTheory V] in
/-- The extended tuple at `X`, at a class: the member's component or
the pin's carrier. -/
theorem famAt_of_mem {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {c : Nat} (hc : c < d.k) :
    d.famAt ψ ρp X c = X c := by simp only [famAt, if_pos hc]

omit [SetTheory V] in
theorem famAt_of_pin {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {c : Nat} (hc : ¬ c < d.k) :
    d.famAt ψ ρp X c = d.pinCar ψ ρp X (c - d.k) := by simp only [famAt, if_neg hc]

/-! ### The kit -/

/-- **The predecessor relation over the classes**: `tagged c i (injT c
j f⃗)` has, per recursive field `i'` of constructor `j` and per spine
`b⃗` fitting the field's telescope, the predecessor at the TARGET
CLASS (a member or a pin), at the tuple of the field's index
expressions, with value the field applied to the spine. -/
@[expose] def PredRelT (ψ : Name → Nat) (ρp : Nat → V) (u v : V) : Prop :=
  ∃ (c : Nat) (i : V) (j : Nat) (fs : List V) (i' : Nat) (bs : List V),
    c < d.kT ∧ j < (d.ctorsT pc c).length ∧ fs.length = ((d.FssT pc ψ c).getD j []).length ∧
    u = tagged c i (d.injT pc ψ c j fs) ∧
    i' ∈ recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length ∧
    SpineFit (consList (fs.take i') ρp) ((d.teleAtT pc ψ c j i').map (·.2.2)) bs ∧
    v = tagged (d.tgtsT pc c j i')
      (d.tupT ψ (d.tgtsT pc c j i')
        ((d.eisAtT pc ψ c j i').map (interp V (consList bs (consList (fs.take i') ρp)))))
      (bs.foldl SetTheory.app (fs.getD i' pt))

/-- **The extended union at the carrier**: the members' carriers and
the pins' carriers at the least tuple. -/
@[expose] noncomputable def unionT (ψ : Name → Nat) (ρp : Nat → V) : V :=
  unionSet d.kT (d.idxT ψ ρp)
    (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))

/-- **The predecessor map over the classes**: the relation, separated
off the extended union. -/
@[expose] noncomputable def kitPredT (ψ : Name → Nat) (ρp : Nat → V) (u : V) : V :=
  relPred (d.unionT ψ ρp) (d.PredRelT pc ψ ρp) u

/-- **The bound**: at `tagged c i x`, class `c`'s motive at the index
spine of `i` and at `x`. -/
@[expose] noncomputable def kitBT (ψ : Name → Nat) (Ms : Nat → V) (u : V) : V :=
  SetTheory.app
    ((isOfW (d.uT (natIdx (sfst u)) ψ) (d.nIdxT (natIdx (sfst u))) (sfst (ssnd u))).foldl
      SetTheory.app (Ms (natIdx (sfst u))))
    (ssnd (ssnd u))

/-- **The inductive hypotheses** of class `c`'s constructor `j` at the
field spine `f⃗`, from a choice `g` of the predecessors' values. -/
@[expose] noncomputable def kitIhsT (ψ : Name → Nat) (ρp : Nat → V) (ℓ c j : Nat) (fs : List V) (g : V) :
    List V :=
  (recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length).map fun i' =>
    lamTower ℓ (consList (fs.take i') ρp) (d.teleAtT pc ψ c j i') fun σ' =>
      SetTheory.app g
        (tagged (d.tgtsT pc c j i')
          (d.tupT ψ (d.tgtsT pc c j i') ((d.eisAtT pc ψ c j i').map (interp V σ')))
          ((ConLeche.Semantics.frameIdx (d.teleAtT pc ψ c j i').length σ').foldl SetTheory.app
            (fs.getD i' pt)))

/-- The value's constructor and fields at a class, when it has them. -/
@[expose] def DecodesT (ψ : Name → Nat) (c : Nat) (x : V) : Prop :=
  ∃ (j : Nat) (fs : List V), j < (d.ctorsT pc c).length ∧
    fs.length = ((d.FssT pc ψ c).getD j []).length ∧ x = d.injT pc ψ c j fs

open Classical in
/-- **The step at a class and a value**: with `x = injT c j f⃗`, minor
`minorIdxT c j` at the fields and the inductive hypotheses; junk
elsewhere. -/
@[expose] noncomputable def kitStAtT (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (ms : Nat → V) (c : Nat)
    (x g : V) : V :=
  if h : d.DecodesT pc ψ c x then
    (Classical.choose (Classical.choose_spec h) ++
      d.kitIhsT pc ψ ρp ℓ c (Classical.choose h) (Classical.choose (Classical.choose_spec h)) g).foldl
      SetTheory.app (ms (d.minorIdxT pc c (Classical.choose h)))
  else empty

/-- **The step**: at `tagged c i x`, the step at class `c` and value
`x`. -/
@[expose] noncomputable def kitStT (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (ms : Nat → V) (u g : V) : V :=
  d.kitStAtT pc ψ ρp ℓ ms (natIdx (sfst u)) (ssnd (ssnd u)) g

/-- **The nested block's recursor at the frame's data**: the class
recursor over the extended union at the kit's predecessor map, bound
and step, at class `c`, index tuple `i`, value `x`. -/
@[expose] noncomputable def blockRecAtT (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (Ms ms : Nat → V)
    (c : Nat) (i x : V) : V :=
  unionRecC ℓ d.kT (d.idxT ψ ρp) (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
    (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms) (d.kitStT pc ψ ρp ℓ ms) c i x

/-- **Class `c`'s value at a leaf frame of its restored recursor type**
`(p⃗, M⃗, m⃗, ı⃗_c, t)` — `k + nPins` motives, `nCtorsT` minors, the
class's index count — read by position as `blockLeafV` does. -/
@[expose] noncomputable def blockLeafVT (ψ : Name → Nat) (ℓ c : Nat) (σ : Nat → V) : V :=
  d.blockRecAtT pc ψ (shiftE (1 + d.nIdxT c + d.nCtorsT pc + d.kT) 0 σ) ℓ
    (fun c' => if c' < d.kT then σ (1 + d.nIdxT c + d.nCtorsT pc + (d.kT - 1 - c')) else pt)
    (fun J => if J < d.nCtorsT pc then σ (1 + d.nIdxT c + d.nCtorsT pc - 1 - J) else pt)
    c (d.tupT ψ c (ConLeche.Semantics.frameIdx (d.nIdxT c) (shiftE 1 0 σ))) (σ 0)

/-- **The candidate recursor of class `c`**: the λ-tower over its
restored recursor type's binder data whose leaf is the class recursor
at the frame. -/
@[expose] noncomputable def blockCandT (ψ : Name → Nat) (ℓ : Nat) (rds : List (Nat × Nat × AnnotTerm))
    (c : Nat) (ρ : Nat → V) : V :=
  lamTower ℓ ρ rds (d.blockLeafVT pc ψ ℓ c)

/-- The predecessor map stays inside the extended union. -/
theorem kitPredT_sub (ψ : Name → Nat) (ρp : Nat → V) :
    ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitPredT pc ψ ρp u ⊆ˢ d.unionT ψ ρp :=
  fun _ _ => relPred_subset _ _ _

/-- The separated pins lie below the pins' carriers at `X`. -/
theorem sepPins_le {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} (P : Nat → V → V → Prop)
    {q : Nat} (t : V) : app (d.sepPins ψ ρp X P q) t ⊆ˢ app (d.pinCar ψ ρp X q) t := by
  intro y hy
  by_cases ht : t ∈ˢ d.pinIdx q ψ ρp
  · unfold BlockModel.sepPins at hy
    rw [app_graph ht] at hy
    exact (mem_sep.mp hy).1
  · exfalso
    unfold BlockModel.sepPins at hy
    rw [app_graph_of_not_mem ht] at hy
    exact not_mem_empty y hy

end BlockModel

/-! ## The pins' recursion laws -/

/-- **The laws the recursor kit needs of the pins** (see the module
docstring): the targets are classes, the pins' index telescopes are
graded at the pins' frames, the pin's carrier at every tuple of the
space decomposes by the pin's constructors at the extended tuple
(`fibre`), the injections are the point at `Prop` and injective within
the pin (`mkZero`/`mkInj`), and the pins' carriers at a tuple are the
least families closed under the pins' constructors (`ind`). -/
structure PinRecLaws {env : Env} (m : EnvModel V env) (d : BlockModel V) (pc : Nat → PinCtors V) :
    Prop where
  /-- every field's target is a class -/
  tgtsLt : ∀ (ψ : Name → Nat) (q j i : Nat), q < d.nPins → j < (pc q).ctors.length →
    i < (((pc q).Fss ψ).getD j []).length → (pc q).tgts j i < d.k + d.nPins
  /-- the pins' index telescopes are graded at the pins' frames -/
  idxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ q, q < d.nPins → IdxOk ((d.pinAt q).u ψ) (d.pinFrame q ψ ρp) ((d.pinAt q).Ids ψ)
  /-- **the pin's fibre**: the pin's carrier at `X` decomposes by the
  pin's constructors, the recursive fields read at the extended tuple -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ q, q < d.nPins →
    ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ x,
      x ∈ˢ app (d.pinCar ψ ρp X q) t ↔
        ∃ j fs, j < (pc q).ctors.length ∧ d.ChainFitT pc ψ ρp (d.famAt ψ ρp X) t (d.k + q) j fs ∧
          x = (pc q).inj ψ j fs
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, d.w ψ = 0 → ∀ q j fs, (pc q).inj ψ j fs = pt
  /-- at a `Type`-valued block a pin's injections are injective -/
  mkInj : ∀ ψ : Name → Nat, d.w ψ ≠ 0 → ∀ q, q < d.nPins → ∀ j fs j' fs',
    j < (pc q).ctors.length → j' < (pc q).ctors.length →
    fs.length = (((pc q).Fss ψ).getD j []).length → fs'.length = (((pc q).Fss ψ).getD j' []).length →
    (pc q).inj ψ j fs = (pc q).inj ψ j' fs' → j = j' ∧ fs = fs'
  /-- **the pins' induction**: a property closed under the pins'
  constructors — the members read at `X`, the pins at the SEPARATED
  pins — holds on the pins' carriers at `X` -/
  ind : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ P : Nat → V → V → Prop,
    (∀ q, q < d.nPins → ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ j fs, j < (pc q).ctors.length →
      d.ChainFitT pc ψ ρp (segJoin d.k d.nPins (d.famAt ψ ρp X) (d.sepPins ψ ρp X P)) t (d.k + q) j fs →
      P q t ((pc q).inj ψ j fs)) →
    ∀ q, q < d.nPins → ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ x, x ∈ˢ app (d.pinCar ψ ρp X q) t → P q t x

/-! ## Kit -/

/-- A fit reads its slots at the frames it visits only. -/
theorem FitsFrom.congr_slot {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length →
        slot (i + l) (consList (as.take l) ρ) = slot' (i + l) (consList (as.take l) ρ)) →
      (FitsFrom rs slot i ρ Fs as ↔ FitsFrom rs slot' i ρ Fs as)
  | _, _, [], [], _ => Iff.rfl
  | _, _, [], _ :: _, _ => Iff.rfl
  | _, _, _ :: _, [], _ => Iff.rfl
  | i, ρ, F :: Fs, a :: as, hsl => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs as) ↔
      (a ∈ˢ (if rs.getD i false then slot' i ρ else interp V ρ F) ∧
        FitsFrom rs slot' (i + 1) (cons a ρ) Fs as)
    have h0 := hsl 0 (Nat.succ_pos _)
    simp only [List.take_zero, consList_nil, Nat.add_zero] at h0
    rw [h0]
    refine and_congr Iff.rfl (FitsFrom.congr_slot fun l hl => ?_)
    have := hsl (l + 1) (by simpa using hl)
    rw [show i + (l + 1) = i + 1 + l from by omega] at this
    simpa [List.take_succ_cons, consList_cons] using this

/-- A fit is monotone in the slots at its recursive positions. -/
theorem FitsFrom.mono {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → rs.getD (i + l) false = true → ∀ ρ', slot (i + l) ρ' ⊆ˢ slot' (i + l) ρ') →
      FitsFrom rs slot i ρ Fs as → FitsFrom rs slot' i ρ Fs as
  | _, _, [], [], _, hf => hf
  | _, _, [], _ :: _, _, hf => hf.elim
  | _, _, _ :: _, [], _, hf => hf.elim
  | i, ρ, F :: Fs, a :: as, h, hf => by
    obtain ⟨h1, h2⟩ := hf
    refine ⟨?_, FitsFrom.mono (fun l hl hr ρ' => ?_) h2⟩
    · by_cases hr : rs.getD i false = true
      · rw [if_pos hr] at h1 ⊢
        have := h 0 (Nat.succ_pos _) (by rw [Nat.add_zero]; exact hr) ρ
        rw [Nat.add_zero] at this
        exact this a h1
      · rw [if_neg hr] at h1 ⊢; exact h1
    · have := h (l + 1) (by simpa using hl)
        (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr) ρ'
      rw [show i + (l + 1) = i + 1 + l from by omega] at this
      exact this

/-- A slot over an extended tuple is monotone in the tuple's
component at the target. -/
theorem BlockModel.slotAtT_mono (d : BlockModel V) (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {Y Y' : Nat → V} {c j i : Nat} {ρ : Nat → V}
    (h : ∀ t, app (Y (d.tgtsT pc c j i)) t ⊆ˢ app (Y' (d.tgtsT pc c j i)) t) :
    d.slotAtT pc ψ Y c j i ρ ⊆ˢ d.slotAtT pc ψ Y' c j i ρ := by
  unfold BlockModel.slotAtT slotSet
  refine piTele_mono fun bs _ => ?_
  exact h _

/-- A fit at the extended tuple is monotone in the components at the
classes (the recursive fields' targets are classes). -/
theorem BlockModel.ChainFitT_mono (d : BlockModel V) (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {Y Y' : Nat → V} (h : ∀ c', c' < d.kT → ∀ t, app (Y c') t ⊆ˢ app (Y' c') t)
    {t : V} {c j : Nat}
    (htgt : ∀ i, i < ((d.FssT pc ψ c).getD j []).length → ((d.rssT pc c).getD j []).getD i false = true →
      d.tgtsT pc c j i < d.kT)
    {fs : List V} (hf : d.ChainFitT pc ψ ρp Y t c j fs) : d.ChainFitT pc ψ ρp Y' t c j fs :=
  ⟨hf.1.mono (fun l hl hr _ => by
      rw [Nat.zero_add] at hr ⊢
      exact d.slotAtT_mono pc (h _ (htgt l hl hr))), hf.2⟩

/-- A member's fit at `X` is a fit over the extended tuple at `X`. -/
theorem BlockModel.chainFitT_of_chainFit (d : BlockModel V) (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {X : Nat → V} {t : V} {c j : Nat} (hc : c < d.k) {fs : List V}
    (hf : d.ChainFit ψ ρp X t c j fs) : d.ChainFitT pc ψ ρp (d.famAt ψ ρp X) t c j fs := by
  obtain ⟨hfit, hidx⟩ := hf
  refine ⟨?_, ?_⟩
  · rw [BlockModel.rssT_of_mem hc, BlockModel.FssT_of_mem hc]
    refine (FitsFrom.congr_slot (Fs := (d.Fss c ψ).getD j []) (fun l hl => ?_)).mpr hfit
    rw [Nat.zero_add]
    exact BlockModel.slotAtT_of_mem hc ψ ρp X j l
      (by rw [List.length_take, hfit.length_eq]; exact Nat.min_eq_left (Nat.le_of_lt hl))
  · rw [BlockModel.IdsT_of_mem hc, BlockModel.EssT_of_mem hc]
    exact hidx

namespace IsBlockModel

variable {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

/-- The extended tuple at a tuple of the space is a family at every
class's index set. -/
theorem famAt_mem {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X) {c : Nat} (hc : c < d.kT) :
    d.famAt ψ ρp X c ∈ˢ famSpace (d.w ψ) (d.idxT ψ ρp c) := by
  by_cases hck : c < d.k
  · rw [d.famAt_of_mem hck, d.idxT_of_mem hck]; exact hX c hck
  · rw [d.famAt_of_pin hck, d.idxT_of_pin hck]
    exact h.pinMem ψ ρp hρp X hX (c - d.k) (by unfold BlockModel.kT at hc; omega)

/-- **A member's predecessors come from the extended tuple**: at any
tuple `X` of the space, a value of `Φ X c` at an index tuple has every
`kitPredT` predecessor in the union of the extended tuple at `X` — the
block model's `fibre` read at the recursive positions, a pin target's
value in the pin's carrier at `X`. -/
theorem kitPredT_from_mem (pc : Nat → PinCtors V) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X) {c : Nat} (hc : c < d.k) {i : V}
    (hi : i ∈ˢ d.idx ψ ρp c) {x : V} (hx : x ∈ˢ app (d.Φ ψ ρp X c) i) :
    d.kitPredT pc ψ ρp (tagged c i x) ⊆ˢ unionSet d.kT (d.idxT ψ ρp) (d.famAt ψ ρp X) := by
  intro v hv
  obtain ⟨-, c', i', j, fs, i'', bs, -, hj, hlen, heq, hi'', hbs, rfl⟩ := mem_relPred.mp hv
  obtain ⟨rfl, rfl, hxe⟩ := tagged_inj heq
  rw [BlockModel.ctorsT_of_mem hc] at hj
  rw [BlockModel.FssT_of_mem hc] at hlen hi''
  rw [BlockModel.rssT_of_mem hc] at hi''
  rw [BlockModel.injT_of_mem hc] at hxe
  rw [BlockModel.teleAtT_of_mem hc] at hbs
  rw [BlockModel.tgtsT_of_mem hc, BlockModel.eisAtT_of_mem hc]
  obtain ⟨j₂, fs₂, hj₂, hfit, hx₂⟩ := (h.fibre ψ ρp hρp X hX c hc i hi x).mp hx
  have hlen₂ : fs₂.length = ((d.Fss c ψ).getD j₂ []).length := hfit.1.length_eq
  obtain ⟨rfl, rfl⟩ := h.mkInj ψ hw c hc j fs j₂ fs₂ hj hj₂ hlen hlen₂ (hxe.symm.trans hx₂)
  obtain ⟨hi''F, hrec⟩ := mem_recIdx.mp hi''
  have hmem := hfit.1.rec_mem i'' hi''F (by rw [Nat.zero_add]; exact hrec)
  rw [Nat.zero_add] at hmem
  have hlenT : (fs.take i'').length = i'' := by
    rw [List.length_take, hlen]; exact Nat.min_eq_left (Nat.le_of_lt hi''F)
  have hρ : (fun n => consList (fs.take i'') ρp (n + i'')) = ρp := funext fun n => by
    have := consList_apply_add (fs.take i'') ρp n
    rwa [hlenT] at this
  unfold BlockModel.slotAt at hmem
  rw [hρ] at hmem
  have hi''K : i'' < (d.ksF c j).length := by
    rw [BlockModel.rss, rssOfK_getD hj] at hrec
    exact rsOf_getD_true_lt hrec
  have htgt : d.tgts c j i'' < d.kT := h.tgtsLt c j i'' hc hj hi''K
  have hXt := h.famAt_mem hρp hX htgt
  have hXu : ∀ t, app (d.famAt ψ ρp X (d.tgts c j i'')) t ∈ˢ (univ (d.w ψ) : V) :=
    fun t => app_famSpace_mem_univ hXt t
  unfold BlockModel.teleAt at hbs
  have hval := slotSet_fold_mem hXu hmem hbs
  exact tagged_mem_unionSet htgt (mem_idx_of_app_famSpace hXt hval) hval

/-- **A pin's predecessors come from the extended tuple**: at any tuple
`X` of the space, a value of the pin's carrier at `X` has every
predecessor in the union of the extended tuple at `X` — the pin's
`fibre`. -/
theorem kitPredT_from_pin {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat}
    {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X) {q : Nat} (hq : q < d.nPins) {t : V}
    (ht : t ∈ˢ d.pinIdx q ψ ρp) {x : V} (hx : x ∈ˢ app (d.pinCar ψ ρp X q) t) :
    d.kitPredT pc ψ ρp (tagged (d.k + q) t x) ⊆ˢ unionSet d.kT (d.idxT ψ ρp) (d.famAt ψ ρp X) := by
  intro v hv
  obtain ⟨-, c', i', j, fs, i'', bs, -, hj, hlen, heq, hi'', hbs, rfl⟩ := mem_relPred.mp hv
  obtain ⟨rfl, rfl, hxe⟩ := tagged_inj heq
  have hnk : ¬ d.k + q < d.k := by omega
  have hq' : d.k + q - d.k = q := Nat.add_sub_cancel_left _ _
  rw [BlockModel.ctorsT_of_pin hnk, hq'] at hj
  rw [BlockModel.FssT_of_pin hnk, hq'] at hlen hi''
  rw [BlockModel.rssT_of_pin hnk, hq'] at hi''
  rw [BlockModel.injT_of_pin hnk, hq'] at hxe
  obtain ⟨j₂, fs₂, hj₂, hfit, hx₂⟩ := (hp.fibre ψ ρp hρp X hX q hq t ht x).mp hx
  have hlen₂ : fs₂.length = (((pc q).Fss ψ).getD j₂ []).length := by
    have := hfit.1.length_eq
    rwa [BlockModel.FssT_of_pin hnk, hq'] at this
  obtain ⟨rfl, rfl⟩ := hp.mkInj ψ hw q hq j fs j₂ fs₂ hj hj₂ hlen hlen₂ (hxe.symm.trans hx₂)
  obtain ⟨hi''F, hrec⟩ := mem_recIdx.mp hi''
  have hfit1 := hfit.1
  rw [BlockModel.rssT_of_pin hnk, BlockModel.FssT_of_pin hnk, hq'] at hfit1
  have hmem := hfit1.rec_mem i'' hi''F (by rw [Nat.zero_add]; exact hrec)
  rw [Nat.zero_add] at hmem
  have htgt : d.tgtsT pc (d.k + q) j i'' < d.kT := by
    rw [BlockModel.tgtsT_of_pin hnk, hq']
    exact hp.tgtsLt ψ q j i'' hq hj hi''F
  have hXt := h.famAt_mem hρp hX htgt
  have hXu : ∀ t, app (d.famAt ψ ρp X (d.tgtsT pc (d.k + q) j i'')) t ∈ˢ (univ (d.w ψ) : V) :=
    fun t => app_famSpace_mem_univ hXt t
  unfold BlockModel.slotAtT at hmem
  have hval := slotSet_fold_mem hXu hmem hbs
  exact tagged_mem_unionSet htgt (mem_idx_of_app_famSpace hXt hval) hval

/-! ## Accessibility over the extended union -/

/-- The separated pins are families over the pins' index sets. -/
theorem sepPins_mem_famSpace {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    {X : Nat → V} (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X) (P : Nat → V → V → Prop) {q : Nat}
    (hq : q < d.nPins) :
    d.sepPins ψ ρp X P q ∈ˢ famSpace (d.w ψ) (d.pinIdx q ψ ρp) :=
  graph_mem_famSpace fun _ ht => univ_sep_mem (famSpace_app (h.pinMem ψ ρp hρp X hX q hq) ht)

/-- **The pins' classes are accessible at a tuple whose members are**:
at `X` below the carrier with every member value accessible, every
value of a pin's carrier at `X` is accessible — the pins' induction
(`PinRecLaws.ind`), each step's predecessors being member values at
`X` or separated (accessible) pin values. -/
theorem pinsAcc_of {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X)
    (hXL : TupleLe d.k (d.idx ψ ρp) X (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
    (hmem : ∀ c, c < d.k → ∀ i, i ∈ˢ d.idx ψ ρp c → ∀ x, x ∈ˢ app (X c) i →
      ∃ y, y ∈ˢ app (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) (tagged c i x)) :
    ∀ q, q < d.nPins → ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ x, x ∈ˢ app (d.pinCar ψ ρp X q) t →
      ∃ y, y ∈ˢ app (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True))
        (tagged (d.k + q) t x) := by
  have hLmem := lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
  obtain ⟨P, hP⟩ : ∃ P : Nat → V → V → Prop, P = fun q t x => ∃ y, y ∈ˢ app
      (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) (tagged (d.k + q) t x) :=
    ⟨_, rfl⟩
  have hind := hp.ind ψ ρp hρp X hX P
  rw [hP] at hind
  refine hind ?_
  rw [← hP]
  intro q hq t ht j fs hj hfit
  have hnk : ¬ d.k + q < d.k := by omega
  have hq' : d.k + q - d.k = q := Nat.add_sub_cancel_left _ _
  -- the extended tuple the step reads: members at `X`, pins separated
  obtain ⟨Y, hY⟩ : ∃ Y, Y = segJoin d.k d.nPins (d.famAt ψ ρp X) (d.sepPins ψ ρp X P) := ⟨_, rfl⟩
  rw [← hY] at hfit
  have hYfam : ∀ c', c' < d.kT → Y c' ∈ˢ famSpace (d.w ψ) (d.idxT ψ ρp c') := by
    intro c' hc'
    by_cases hck : c' < d.k
    · have : Y c' = X c' := by
        rw [hY, segJoin_lt _ _ hck, d.famAt_of_mem hck]
      rw [this, d.idxT_of_mem hck]; exact hX c' hck
    · have hc'' : c' - d.k < d.nPins := by unfold BlockModel.kT at hc'; omega
      have : Y c' = d.sepPins ψ ρp X P (c' - d.k) := by
        rw [hY]
        show (if d.k ≤ c' ∧ c' < d.k + d.nPins then _ else _) = _
        rw [if_pos ⟨Nat.le_of_not_lt hck, by unfold BlockModel.kT at hc'; exact hc'⟩]
      rw [this, d.idxT_of_pin hck]
      exact h.sepPins_mem_famSpace hρp hX P hc''
  -- the extended tuple lies below the extended tuple at the carrier
  have hYle : ∀ c', c' < d.kT → ∀ t, app (Y c') t ⊆ˢ
      app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c') t := by
    intro c' hc' t' y hy
    by_cases ht' : t' ∈ˢ d.idxT ψ ρp c'
    · by_cases hck : c' < d.k
      · rw [hY, segJoin_lt _ _ hck, d.famAt_of_mem hck] at hy
        rw [d.famAt_of_mem hck]
        rw [d.idxT_of_mem hck] at ht'
        exact hXL c' hck t' ht' y hy
      · have hc'' : c' - d.k < d.nPins := by unfold BlockModel.kT at hc'; omega
        have : Y c' = d.sepPins ψ ρp X P (c' - d.k) := by
          rw [hY]
          show (if d.k ≤ c' ∧ c' < d.k + d.nPins then _ else _) = _
          rw [if_pos ⟨Nat.le_of_not_lt hck, by unfold BlockModel.kT at hc'; exact hc'⟩]
        rw [this] at hy
        rw [d.famAt_of_pin hck]
        rw [d.idxT_of_pin hck] at ht'
        exact h.pinMono ψ ρp hρp X _ hX hLmem hXL _ hc'' t' ht' y (d.sepPins_le P t' y hy)
    · exfalso
      rw [app_famSpace_of_not_mem (hYfam c' hc') ht'] at hy
      exact not_mem_empty y hy
  have htgts : ∀ i, i < ((d.FssT pc ψ (d.k + q)).getD j []).length →
      ((d.rssT pc (d.k + q)).getD j []).getD i false = true → d.tgtsT pc (d.k + q) j i < d.kT := by
    intro i hi _
    rw [BlockModel.FssT_of_pin hnk, hq'] at hi
    rw [BlockModel.tgtsT_of_pin hnk, hq']
    exact hp.tgtsLt ψ q j i hq hj hi
  -- the element is in the pin's carrier at the carrier
  have hfitL := d.ChainFitT_mono pc hYle htgts hfit
  have hxL : (pc q).inj ψ j fs ∈ˢ app (d.pinCar ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) q) t :=
    (hp.fibre ψ ρp hρp _ hLmem q hq t ht _).mpr ⟨j, fs, hj, hfitL, rfl⟩
  have hu : tagged (d.k + q) t ((pc q).inj ψ j fs) ∈ˢ d.unionT ψ ρp := by
    refine tagged_mem_unionSet (by unfold BlockModel.kT; omega) ?_ ?_
    · rw [d.idxT_of_pin hnk, hq']; exact ht
    · rw [d.famAt_of_pin hnk, hq']; exact hxL
  rw [hP]
  refine ⟨pt, accFam_intro (d.kitPredT_sub pc ψ ρp) hu trivial fun v hv => ?_⟩
  -- a predecessor: a recursive field's value, at a member of `X` or a separated pin
  obtain ⟨-, c', i', j', fs', i'', bs, -, hj', hlen', heq, hi'', hbs, rfl⟩ := mem_relPred.mp hv
  obtain ⟨rfl, rfl, hxe⟩ := tagged_inj heq
  rw [BlockModel.ctorsT_of_pin hnk, hq'] at hj'
  rw [BlockModel.FssT_of_pin hnk, hq'] at hlen' hi''
  rw [BlockModel.rssT_of_pin hnk, hq'] at hi''
  rw [BlockModel.injT_of_pin hnk, hq'] at hxe
  have hlen : fs.length = (((pc q).Fss ψ).getD j []).length := by
    have := hfit.1.length_eq
    rwa [BlockModel.FssT_of_pin hnk, hq'] at this
  obtain ⟨rfl, rfl⟩ := hp.mkInj ψ hw q hq j' fs' j fs hj' hj hlen' hlen hxe.symm
  obtain ⟨hi''F, hrec⟩ := mem_recIdx.mp hi''
  have hfit1 := hfit.1
  rw [BlockModel.rssT_of_pin hnk, BlockModel.FssT_of_pin hnk, hq'] at hfit1
  have hmem' := hfit1.rec_mem i'' hi''F (by rw [Nat.zero_add]; exact hrec)
  rw [Nat.zero_add] at hmem'
  have htgt : d.tgtsT pc (d.k + q) j' i'' < d.kT := by
    rw [BlockModel.tgtsT_of_pin hnk, hq']
    exact hp.tgtsLt ψ q j' i'' hq hj' hi''F
  have hYt := hYfam _ htgt
  have hYu : ∀ t, app (Y (d.tgtsT pc (d.k + q) j' i'')) t ∈ˢ (univ (d.w ψ) : V) :=
    fun t => app_famSpace_mem_univ hYt t
  unfold BlockModel.slotAtT at hmem'
  have hval := slotSet_fold_mem hYu hmem' hbs
  have htup := mem_idx_of_app_famSpace hYt hval
  by_cases hck : d.tgtsT pc (d.k + q) j' i'' < d.k
  · rw [hY, segJoin_lt _ _ hck, d.famAt_of_mem hck] at hval
    rw [d.idxT_of_mem hck] at htup
    exact hmem _ hck _ htup _ hval
  · have hc'' : d.tgtsT pc (d.k + q) j' i'' - d.k < d.nPins := by unfold BlockModel.kT at htgt; omega
    have hYc : Y (d.tgtsT pc (d.k + q) j' i'') = d.sepPins ψ ρp X P (d.tgtsT pc (d.k + q) j' i'' - d.k) := by
      rw [hY]
      show (if d.k ≤ _ ∧ _ < d.k + d.nPins then _ else _) = _
      rw [if_pos ⟨Nat.le_of_not_lt hck, by unfold BlockModel.kT at htgt; exact htgt⟩]
    rw [hYc] at hval
    rw [d.idxT_of_pin hck] at htup
    unfold BlockModel.sepPins at hval
    rw [app_graph htup] at hval
    have := (mem_sep.mp hval).2
    rw [hP] at this
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt hck)] at this

/-- **The members' classes are accessible** at the carrier: the
simultaneous induction on the block's tuple, the predecessors at the
separated tuple being separated member values or values of the pins'
carriers at the separated tuple (`pinsAcc_of`). -/
theorem memAcc_all {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) :
    ∀ c, c < d.k → ∀ i, i ∈ˢ d.idx ψ ρp c →
      ∀ x, x ∈ˢ app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) c) i →
      ∃ y, y ∈ˢ app (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) (tagged c i x) := by
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ ρp hρp
  have hLmem := lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
  refine lfpTuple_induction hcl hmono (fun c i x => ∃ y, y ∈ˢ app
    (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) (tagged c i x)) ?_
  intro c hc i hi x hx
  obtain ⟨P, hP⟩ : ∃ P : Nat → V → V → Prop, P = fun c i x => ∃ y, y ∈ˢ app
      (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) (tagged c i x) := ⟨_, rfl⟩
  rw [← hP] at hx
  have hSmem := sepTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) P
  have hSle := sepTuple_le (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) P
  -- the element is in the carrier
  have hxL : x ∈ˢ app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) c) i :=
    lfpTuple_closed hcl hmono c hc i hi x (hmono _ _ hSmem hLmem hSle c hc i hi x hx)
  have hck : c < d.kT := by unfold BlockModel.kT; omega
  have hu : tagged c i x ∈ˢ d.unionT ψ ρp := by
    refine tagged_mem_unionSet hck ?_ ?_
    · rw [d.idxT_of_mem hc]; exact hi
    · rw [d.famAt_of_mem hc]; exact hxL
  -- the separated members are accessible
  have hmemS : ∀ c', c' < d.k → ∀ i', i' ∈ˢ d.idx ψ ρp c' → ∀ x',
      x' ∈ˢ app (sepTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) P c') i' →
      ∃ y, y ∈ˢ app (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True))
        (tagged c' i' x') := by
    intro c' _ i' hi' x' hx'
    unfold sepTuple at hx'
    rw [app_graph hi'] at hx'
    have := (mem_sep.mp hx').2
    rw [hP] at this
    exact this
  refine ⟨pt, accFam_intro (d.kitPredT_sub pc ψ ρp) hu trivial fun v hv => ?_⟩
  have hvS := h.kitPredT_from_mem pc hρp hw hSmem hc hi hx v hv
  obtain ⟨c', hc', i', hi', x', hx', rfl⟩ := mem_unionSet.mp hvS
  by_cases hck' : c' < d.k
  · rw [d.famAt_of_mem hck'] at hx'
    rw [d.idxT_of_mem hck'] at hi'
    exact hmemS c' hck' i' hi' x' hx'
  · rw [d.famAt_of_pin hck'] at hx'
    rw [d.idxT_of_pin hck'] at hi'
    have hc'' : c' - d.k < d.nPins := by unfold BlockModel.kT at hc'; omega
    have := h.pinsAcc_of hp hρp hw hSmem hSle hmemS (c' - d.k) hc'' i' hi' x' hx'
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt hck')] at this

/-- **Every element of the extended union at the carrier is
accessible** along the classes' predecessor map: the members by the
tuple induction, the pins by the pins' induction at the carrier. -/
theorem nestedAcc_all {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) :
    ∀ u, u ∈ˢ d.unionT ψ ρp →
      ∃ y, y ∈ˢ app (accFam (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (fun _ => True)) u := by
  have hLmem := lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
  refine unionAcc_of_classAcc fun c hc i hi x hx => ?_
  by_cases hck : c < d.k
  · rw [d.famAt_of_mem hck] at hx
    rw [d.idxT_of_mem hck] at hi
    exact h.memAcc_all hp hρp hw c hck i hi x hx
  · rw [d.famAt_of_pin hck] at hx
    rw [d.idxT_of_pin hck] at hi
    have hc'' : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
    have := h.pinsAcc_of hp hρp hw hLmem (TupleLe.refl _ _ _) (h.memAcc_all hp hρp hw) (c - d.k) hc''
      i hi x hx
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt hck)] at this

/-! ## The class kit at the block model -/

/-- **The nested block's recursion kit**, from the bound's and the
step's obligations: the predecessor map, bound and step of
`NestedRecCand`, with the union's accessibility `nestedAcc_all`. -/
noncomputable def nestedKitC {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat}
    {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {ℓ : Nat} {Ms ms : Nat → V}
    (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ d.unionT ψ ρp → ∀ g,
      g ∈ˢ piSet (d.kitPredT pc ψ ρp u) (fun j => app
        (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms) (d.kitStT pc ψ ρp ℓ ms)) j) →
      d.kitStT pc ψ ρp ℓ ms u g ∈ˢ d.kitBT ψ Ms u) :
    UnionRecKitC ℓ d.kT (d.idxT ψ ρp) (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) :=
  ⟨d.kitPredT pc ψ ρp, d.kitBT ψ Ms, d.kitStT pc ψ ρp ℓ ms, d.kitPredT_sub pc ψ ρp,
    h.nestedAcc_all hp hρp hw, hB, hst⟩

/-- **The candidate's leaf is typed** (`w ≠ 0`): the nested block's
recursor at the frame's motives and minors lies in the bound, at
every class. -/
theorem blockRecAtT_mem_B {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat}
    {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {ℓ : Nat} {Ms ms : Nat → V}
    (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ d.unionT ψ ρp → ∀ g,
      g ∈ˢ piSet (d.kitPredT pc ψ ρp u) (fun j => app
        (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms) (d.kitStT pc ψ ρp ℓ ms)) j) →
      d.kitStT pc ψ ρp ℓ ms u g ∈ˢ d.kitBT ψ Ms u)
    {c : Nat} (hc : c < d.kT) {i x : V} (hi : i ∈ˢ d.idxT ψ ρp c)
    (hx : x ∈ˢ app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) i) :
    d.blockRecAtT pc ψ ρp ℓ Ms ms c i x ∈ˢ d.kitBT ψ Ms (tagged c i x) :=
  (h.nestedKitC hp hρp hw hB hst).rec_mem_B hc hi hx

/-- **The candidate's recursion equation** (`w ≠ 0`): the nested
block's recursor at a value is the step at the graph over its
predecessors — every member's AND every pin's ι rule at once. -/
theorem blockRecAtT_eq {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat}
    {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {ℓ : Nat} {Ms ms : Nat → V}
    (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ d.unionT ψ ρp → ∀ g,
      g ∈ˢ piSet (d.kitPredT pc ψ ρp u) (fun j => app
        (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms) (d.kitStT pc ψ ρp ℓ ms)) j) →
      d.kitStT pc ψ ρp ℓ ms u g ∈ˢ d.kitBT ψ Ms u)
    {c : Nat} (hc : c < d.kT) {i x : V} (hi : i ∈ˢ d.idxT ψ ρp c)
    (hx : x ∈ˢ app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) i) :
    d.blockRecAtT pc ψ ρp ℓ Ms ms c i x
      = d.kitStT pc ψ ρp ℓ ms (tagged c i x)
          (graph (fun v => recSel (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms)
            (d.kitStT pc ψ ρp ℓ ms)) v) (d.kitPredT pc ψ ρp (tagged c i x))) :=
  (h.nestedKitC hp hρp hw hB hst).rec_eq hc hi hx

end IsBlockModel

/-! ## The bound's obligation -/

theorem BlockModel.kitBT_tagged (d : BlockModel V) (ψ : Name → Nat) (Ms : Nat → V) (c : Nat)
    (i x : V) :
    d.kitBT ψ Ms (tagged c i x)
      = app ((isOfW (d.uT c ψ) (d.nIdxT c) i).foldl app (Ms c)) x := by
  unfold BlockModel.kitBT tagged
  rw [sfst_kpair, ssnd_kpair, natIdx_vnat, sfst_kpair, ssnd_kpair]

/-- A pin's index telescope has the container's index count. -/
theorem IsBlockModel.pinIds_length {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) {q : Nat} (hq : q < d.nPins) (ψ : Name → Nat) :
    ((d.pinAt q).Ids ψ).length = (d.pinAt q).nIdx := by
  unfold PinSyn.Ids
  rw [List.length_map, List.length_drop, (h.pinShape q hq ψ).2.2]
  omega

/-- **The bound's obligation over the classes**: at every element of
the extended union the bound is in `univ ℓ` — every class's motive,
at a fitting index spine of the class's telescope at its frame and a
value of the class's carrier there, a set at the level (the frame's
motives typed at their readings, read SEMANTICALLY; the readings'
form is the stage's). -/
theorem IsBlockModel.kitBT_mem {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat}
    {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) {ℓ : Nat} {Ms : Nat → V}
    (hMs : ∀ c, c < d.kT → ∀ is, SpineFit (d.frameT c ψ ρp) (d.IdsT c ψ) is → ∀ x,
      x ∈ˢ app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) (d.tupT ψ c is) →
      app (is.foldl app (Ms c)) x ∈ˢ (univ ℓ : V)) :
    ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  rw [BlockModel.kitBT_tagged]
  by_cases hck : c < d.k
  · obtain ⟨cvT', cvR', mI', rP', rules', h'⟩ := hreps c hck
    rw [d.idxT_of_mem hck] at hi
    have hi' : i ∈ˢ idxSet (d.uM c ψ) ρp (d.IdsM c ψ) := hi
    obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim hi'
    rw [BlockModel.uT_of_mem hck, BlockModel.nIdxT_of_mem hck, ← h'.IdsM_length ψ,
      isOfW_tupW (h'.idxOk ψ ρp hρp c hck) hsp]
    refine hMs c hc is ?_ x ?_
    · rw [BlockModel.frameT_of_mem hck, BlockModel.IdsT_of_mem hck]
      exact hsp
    · rw [BlockModel.tupT, BlockModel.uT_of_mem hck]
      exact hx
  · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
    rw [d.idxT_of_pin hck] at hi
    have hi' : i ∈ˢ idxSet ((d.pinAt (c - d.k)).u ψ) (d.pinFrame (c - d.k) ψ ρp)
        ((d.pinAt (c - d.k)).Ids ψ) := hi
    obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim hi'
    rw [BlockModel.uT_of_pin hck, BlockModel.nIdxT_of_pin hck, ← h.pinIds_length hq ψ,
      isOfW_tupW (hp.idxOk ψ ρp hρp _ hq) hsp]
    refine hMs c hc is ?_ x ?_
    · rw [BlockModel.frameT_of_pin hck, BlockModel.IdsT_of_pin hck]
      exact hsp
    · rw [BlockModel.tupT, BlockModel.uT_of_pin hck]
      exact hx

/-! ## The step's obligation -/

/-- The step at a decodable value: the minor of SOME decode at its
fields and the inductive hypotheses (unique at `w ≠ 0`). -/
theorem BlockModel.kitStT_tagged (d : BlockModel V) (pc : Nat → PinCtors V) (ψ : Name → Nat)
    (ρp : Nat → V) (ℓ : Nat) (ms : Nat → V) {c : Nat} {i x : V} (g : V) (hdec : d.DecodesT pc ψ c x) :
    ∃ (j' : Nat) (fs' : List V), j' < (d.ctorsT pc c).length ∧
      fs'.length = ((d.FssT pc ψ c).getD j' []).length ∧ x = d.injT pc ψ c j' fs' ∧
      d.kitStT pc ψ ρp ℓ ms (tagged c i x) g
        = (fs' ++ d.kitIhsT pc ψ ρp ℓ c j' fs' g).foldl app (ms (d.minorIdxT pc c j')) := by
  unfold BlockModel.kitStT
  rw [natIdx_sfst_tagged, ssnd_ssnd_tagged]
  unfold BlockModel.kitStAtT
  rw [dif_pos hdec]
  have hspec := Classical.choose_spec (Classical.choose_spec hdec)
  exact ⟨_, _, hspec.1, hspec.2.1, hspec.2.2, rfl⟩

/-- **The graph's values are bounded** over the extended union, from
the bound's obligation alone. -/
theorem BlockModel.graphT_mem_B (d : BlockModel V) (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {ℓ : Nat} {Ms ms : Nat → V}
    (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V)) {u v : V}
    (hu : u ∈ˢ d.unionT ψ ρp)
    (hv : v ∈ˢ app (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms)
      (d.kitStT pc ψ ρp ℓ ms)) u) : v ∈ˢ d.kitBT ψ Ms u := by
  rw [app_recGraph_eq hB (d.kitPredT_sub pc ψ ρp) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

namespace IsBlockModel

variable {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

/-- A recursive field's target is a class, at every class. -/
theorem tgtsT_lt {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) (ψ : Name → Nat) {c : Nat}
    (hc : c < d.kT) {j : Nat} (hj : j < (d.ctorsT pc c).length) {i : Nat}
    (hi : i < ((d.FssT pc ψ c).getD j []).length) (hr : ((d.rssT pc c).getD j []).getD i false = true) :
    d.tgtsT pc c j i < d.kT := by
  by_cases hck : c < d.k
  · rw [BlockModel.ctorsT_of_mem hck] at hj
    rw [BlockModel.rssT_of_mem hck, BlockModel.rss, rssOfK_getD hj] at hr
    rw [BlockModel.tgtsT_of_mem hck]
    exact h.tgtsLt c j i hck hj (rsOf_getD_true_lt hr)
  · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
    rw [BlockModel.ctorsT_of_pin hck] at hj
    rw [BlockModel.FssT_of_pin hck] at hi
    rw [BlockModel.tgtsT_of_pin hck]
    exact hp.tgtsLt ψ _ j i hq hj hi

/-- **A predecessor is in the predecessor map**: at a spine fitting a
class's constructor at the extended tuple at the carrier, a recursive
field's value along a fitting telescope spine, tagged at its target
class and its index tuple, is a predecessor of the tagged injection. -/
theorem kitPredT_mem {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {c : Nat} (hc : c < d.kT) {j : Nat}
    (hj : j < (d.ctorsT pc c).length) {fs : List V}
    (hfit : FitsFrom ((d.rssT pc c).getD j [])
      (d.slotAtT pc ψ (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) c j) 0 ρp
      ((d.FssT pc ψ c).getD j []) fs)
    {i' : Nat} (hi' : i' ∈ recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length)
    {bs : List V} (hbs : SpineFit (consList (fs.take i') ρp) ((d.teleAtT pc ψ c j i').map (·.2.2)) bs)
    (i₀ : V) :
    tagged (d.tgtsT pc c j i')
        (d.tupT ψ (d.tgtsT pc c j i')
          ((d.eisAtT pc ψ c j i').map (interp V (consList bs (consList (fs.take i') ρp)))))
        (bs.foldl app (fs.getD i' pt))
      ∈ˢ d.kitPredT pc ψ ρp (tagged c i₀ (d.injT pc ψ c j fs)) := by
  obtain ⟨hi'F, hrec⟩ := mem_recIdx.mp hi'
  have hmem := hfit.rec_mem i' hi'F (by rw [Nat.zero_add]; exact hrec)
  rw [Nat.zero_add] at hmem
  have htgt := h.tgtsT_lt hp ψ hc hj hi'F hrec
  have hXt := h.famAt_mem hρp (lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) htgt
  have hXu : ∀ t, app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) (d.tgtsT pc c j i')) t
      ∈ˢ (univ (d.w ψ) : V) := fun t => app_famSpace_mem_univ hXt t
  unfold BlockModel.slotAtT at hmem
  have hval := slotSet_fold_mem hXu hmem hbs
  refine mem_relPred.mpr ⟨tagged_mem_unionSet htgt (mem_idx_of_app_famSpace hXt hval) hval, ?_⟩
  exact ⟨c, i₀, j, fs, i', bs, hc, hj, hfit.length_eq, rfl, hi', hbs, rfl⟩

/-- **The inductive hypothesis' value lies in its domain**: the
λ-tower over the field's telescope of the graph's value at the
recursive call is in the nested product of the target class's motive
at the call's index tuple and the field applied — the graph's values
are bounded by the motives (`graphT_mem_B`). -/
theorem kitIhsT_mem {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {ℓ : Nat} {Ms ms : Nat → V}
    (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V)) {c : Nat} (hc : c < d.kT)
    {j : Nat} (hj : j < (d.ctorsT pc c).length) {fs : List V}
    (hfit : FitsFrom ((d.rssT pc c).getD j [])
      (d.slotAtT pc ψ (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) c j) 0 ρp
      ((d.FssT pc ψ c).getD j []) fs)
    {i' : Nat} (hi' : i' ∈ recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length)
    {i₀ g : V}
    (hg : g ∈ˢ piSet (d.kitPredT pc ψ ρp (tagged c i₀ (d.injT pc ψ c j fs))) fun v =>
      app (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms) (d.kitStT pc ψ ρp ℓ ms)) v) :
    lamTower ℓ (consList (fs.take i') ρp) (d.teleAtT pc ψ c j i') (fun σ' =>
        app g
          (tagged (d.tgtsT pc c j i')
            (d.tupT ψ (d.tgtsT pc c j i') ((d.eisAtT pc ψ c j i').map (interp V σ')))
            ((ConLeche.Semantics.frameIdx (d.teleAtT pc ψ c j i').length σ').foldl app
              (fs.getD i' pt))))
      ∈ˢ piTele ℓ (teleOfFields (consList (fs.take i') ρp) ((d.teleAtT pc ψ c j i').map (·.2.2)))
          (fun bs => app
            ((isOfW (d.uT (d.tgtsT pc c j i') ψ) (d.nIdxT (d.tgtsT pc c j i'))
              (d.tupT ψ (d.tgtsT pc c j i')
                ((d.eisAtT pc ψ c j i').map (interp V (consList bs (consList (fs.take i') ρp)))))).foldl
              app (Ms (d.tgtsT pc c j i')))
            (bs.foldl app (fs.getD i' pt))) [] := by
  refine lamTower_mem_piTele fun bs hbs => ?_
  rw [List.nil_append]
  have hlenbs : bs.length = (d.teleAtT pc ψ c j i').length := by
    rw [hbs.length_eq, List.length_map]
  rw [← hlenbs, frameIdx_consList']
  have hv := h.kitPredT_mem hp hρp hc hj hfit hi' hbs i₀
  have hvU := relPred_subset _ _ _ _ hv
  have hgv := app_mem_of_mem_piSet hg hv
  have hBv := d.graphT_mem_B pc hB hvU hgv
  rw [BlockModel.kitBT_tagged] at hBv
  exact hBv

/-- **The step's obligation over the classes** at a `Type`-valued
block: at every element of the extended union and every choice of the
predecessors' values in the graph's fibres, the step lands in the
bound — the value decomposes (a member's by the fixed-point equation
and `fibre`, a pin's by `PinRecLaws.fibre`), the decode is the
decomposition (`mkInj`), and the minor at the fields and the inductive
hypotheses lands in the motive at the index tuple and the injection
(`hms`: the frame's minors typed, read SEMANTICALLY at the classes'
tuples; the readings' form — a pin's minor names the container's
constructor at the pin's components — is the stage's). -/
theorem kitStT_mem (hreps : IsBlockModels m d) {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {ℓ : Nat}
    {Ms ms : Nat → V} (hB : ∀ u, u ∈ˢ d.unionT ψ ρp → d.kitBT ψ Ms u ∈ˢ (univ ℓ : V))
    (hms : ∀ c, c < d.kT → ∀ j, j < (d.ctorsT pc c).length → ∀ t, t ∈ˢ d.idxT ψ ρp c → ∀ fs,
      d.ChainFitT pc ψ ρp (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) t c j fs →
      ∀ vs : List V,
      vs.length = (recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length).length →
      (∀ l, l < vs.length →
        vs.getD l pt ∈ˢ piTele ℓ
          (teleOfFields
            (consList (fs.take ((recIdx ((d.rssT pc c).getD j [])
              ((d.FssT pc ψ c).getD j []).length).getD l 0)) ρp)
            ((d.teleAtT pc ψ c j ((recIdx ((d.rssT pc c).getD j [])
              ((d.FssT pc ψ c).getD j []).length).getD l 0)).map (·.2.2)))
          (fun bs =>
            let i' := (recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length).getD l 0
            app
              ((isOfW (d.uT (d.tgtsT pc c j i') ψ) (d.nIdxT (d.tgtsT pc c j i'))
                (d.tupT ψ (d.tgtsT pc c j i')
                  ((d.eisAtT pc ψ c j i').map (interp V (consList bs (consList (fs.take i') ρp)))))).foldl
                app (Ms (d.tgtsT pc c j i')))
              (bs.foldl app (fs.getD i' pt))) []) →
      (fs ++ vs).foldl app (ms (d.minorIdxT pc c j))
        ∈ˢ app ((isOfW (d.uT c ψ) (d.nIdxT c) t).foldl app (Ms c)) (d.injT pc ψ c j fs)) :
    ∀ u, u ∈ˢ d.unionT ψ ρp → ∀ g,
      g ∈ˢ piSet (d.kitPredT pc ψ ρp u) (fun v =>
        app (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms)
          (d.kitStT pc ψ ρp ℓ ms)) v) →
      d.kitStT pc ψ ρp ℓ ms u g ∈ˢ d.kitBT ψ Ms u := by
  intro u hu g hg
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  -- the value decomposes at its class
  have hdecomp : ∃ j fs, j < (d.ctorsT pc c).length ∧
      d.ChainFitT pc ψ ρp (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) i c j fs ∧
      x = d.injT pc ψ c j fs := by
    by_cases hck : c < d.k
    · obtain ⟨cvT', cvR', mI', rP', rules', h'⟩ := hreps c hck
      rw [d.famAt_of_mem hck] at hx
      rw [d.idxT_of_mem hck] at hi
      rw [← h'.carrier_app_eq hρp hck hi] at hx
      obtain ⟨j, fs, hj, hcf, rfl⟩ :=
        (h'.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) c hck i hi x).mp hx
      refine ⟨j, fs, ?_, d.chainFitT_of_chainFit pc hck hcf, ?_⟩
      · rw [BlockModel.ctorsT_of_mem hck]; exact hj
      · rw [BlockModel.injT_of_mem hck]
    · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
      rw [d.famAt_of_pin hck] at hx
      rw [d.idxT_of_pin hck] at hi
      obtain ⟨j, fs, hj, hcf, rfl⟩ :=
        (hp.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) _ hq i hi x).mp hx
      rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hck)] at hcf
      refine ⟨j, fs, ?_, hcf, ?_⟩
      · rw [BlockModel.ctorsT_of_pin hck]; exact hj
      · rw [BlockModel.injT_of_pin hck]
  obtain ⟨j, fs, hj, hfit, rfl⟩ := hdecomp
  have hlenfs : fs.length = ((d.FssT pc ψ c).getD j []).length := hfit.1.length_eq
  have hdec : d.DecodesT pc ψ c (d.injT pc ψ c j fs) := ⟨j, fs, hj, hlenfs, rfl⟩
  obtain ⟨j', fs', hj', hlen', hx', heq⟩ := d.kitStT_tagged pc ψ ρp ℓ ms g hdec
  rw [heq]
  -- the decode is the decomposition
  have hjfs : j = j' ∧ fs = fs' := by
    by_cases hck : c < d.k
    · rw [BlockModel.injT_of_mem hck] at hx'
      rw [BlockModel.ctorsT_of_mem hck] at hj hj'
      rw [BlockModel.FssT_of_mem hck] at hlenfs hlen'
      exact h.mkInj ψ hw c hck j fs j' fs' hj hj' hlenfs hlen' hx'
    · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
      rw [BlockModel.injT_of_pin hck] at hx'
      rw [BlockModel.ctorsT_of_pin hck] at hj hj'
      rw [BlockModel.FssT_of_pin hck] at hlenfs hlen'
      exact hp.mkInj ψ hw _ hq j fs j' fs' hj hj' hlenfs hlen' hx'
  obtain ⟨rfl, rfl⟩ := hjfs
  rw [BlockModel.kitBT_tagged]
  refine hms c hc j hj i hi fs hfit _ ?_ ?_
  · unfold BlockModel.kitIhsT
    rw [List.length_map]
  · intro l hl
    unfold BlockModel.kitIhsT at hl ⊢
    rw [List.length_map] at hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
      Option.getD_some]
    have hgetD : (recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length).getD l 0
        = (recIdx ((d.rssT pc c).getD j []) ((d.FssT pc ψ c).getD j []).length)[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    rw [hgetD]
    exact h.kitIhsT_mem hp hρp hB hc hj hfit.1 (List.getElem_mem hl) hg

end IsBlockModel

end ConLeche.Model
