module

public import ConLeche.Semantics.Inductives.DeclNested
public import ConLeche.Model.Inductives.NestedFit
public section

/-!
# The nested route's premise, the model with its blocks, and the run's record (task #315, M6 s3 / M7)

The definitions `declNested_of`'s two named facts are stated over,
split out of `DeclNestedCore.lean` for two reasons: the tail grew to
the CONCRETE block model (task #315 M7-2, DESIGN §U.29), so the
consumer must import `NestedCore.lean` and name `nestedBlockModel` —
everything `NestedCore.lean` needs of the consumer's file lives here;
and the CROSSING kit (`ContainerCross.lean` — a container's block model
across an environment extension, task #315 M7-3) sits between the
premise and its consumer:

* `ContainerModeled` / `EnvBlockModels` / `PinsModeled` — a stored
  container's block model in the container's own terms, at every
  stored container, and read at the elimination's pins; with it the
  container's pins' LAWS and SHAPES (`BlockAt`: `PinRecLaws` — the
  pins' carriers are the least families closed under the pins'
  constructors — and `PinShapes`, the pins' `CopyCtorShape` against
  their containers) at ONE global assignment of block models to
  container groups (`EnvBlocksOf`; `blockOf` is its witness), task
  #315 L-E, DESIGN §U.36;
* `EnvModelB` — the P-tier environment invariant WITH its blocks
  (task #315 M7-3, DESIGN §U.31): `EnvModelM` and, on top, that field;
* `NestedBlockModelOf` — the record of the nested run's own block
  model.

The tag shape is what the pin identification (`pinLeaf`) needs — a
copy's constructors are the container's, instantiated at the pin, at
the SAME member-local positions (DESIGN §U.15 (a)).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin ContainerInfo IndCaps fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The premise: the containers' block models -/

/-- **A container's block model, in the container's own terms** (task
#315 M6 s9, DESIGN §U.21 (a) — the strengthening §U.19 (e) asked for):
the block model `d` of the group `containerInfo?` reads for a stored
inductive has ONE member per `ci.members` entry, IN ORDER, named as
the entry names it, with that entry's constructor count, the group's
parameter count, and `IsBlockModel` at every member at the entry's own
constant; the members and constructors typed, the injections the
tagged towers at the member-local positions, and every member's
parameter telescope the first member's AS A FRAME (official's
cross-member check, `MutualFormersFacts.frame`).  Every clause is true
of every block model this checker builds (`mutualBlockModelOf_ofMutual`:
`memberNames`/`ctors`; `MutualFormersFacts.frame`; the native `k = 1`
instance trivially) and none follows from the abstract clauses (the
recursor's motive ORDER is not one).  The shape of the `EnvModelM`
field to come (M7), which makes it by construction. -/
structure ContainerModeled {env : Env} (m : EnvModel V env) (ci : ContainerInfo)
    (d : BlockModel V) : Prop where
  /-- one member per `all`-group entry -/
  k : d.k = ci.members.length
  /-- the member names are exactly the members (task #315 L-E, at lane
  L-B's request: `memberName` reads `getD … .anonymous`, so a target
  past the list's end would read as `.anonymous` and `ordFree` could
  not be consumed) -/
  namesLen : d.memberNames.length = d.k
  /-- the group's parameter count -/
  nP : d.nP = ci.nP
  /-- the block at every member -/
  reps : IsBlockModels m d
  /-- the members, constructors and pins typed -/
  typed : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ ∧ PinsTyped m d ψ
  /-- the injections are the tagged towers at the member-local
  positions, **at a container with parameters** (task #315 M7-4,
  DESIGN §U.45): the clause is FALSE at the pinned `Nat` (whose carrier
  `ω` holds `natzero = ∅`) and at the pinned `PUnit` (whose carrier
  `{pt}` holds the proof point), and `0 < d.nP` is its own scope — the
  only consumer is a pin's container (`NestedPinGroupSyn.inj`), and
  `nestedOccOk` mints a pin only where a member is mentioned among
  `args.take ci.nP`, which is empty at `ci.nP = 0`. -/
  inj : 0 < d.nP → ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
    d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt]))
  /-- member `i` is the `i`-th entry: its name, its CONSTRUCTORS BY
  NAME AND IN ORDER (task #315 L-B: the copies' identities read the
  entry's constructor records positionally — `IsBlockModel.rules` ties
  the block model's constructors to a recursor's rule list, but no
  clause ties THAT list to the environment's, so the count alone is
  not enough), and `IsBlockModel` at the entry's own constant -/
  member : ∀ (i : Nat) (M : ContainerMember), ci.members[i]? = some M →
    d.memberName i = M.name ∧ (d.ctorsM i).map (·.1.name) = M.ctors.map (·.name) ∧
    ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel m M.name ⟨M.name, M.lps, M.type⟩ cvR mI rP rules d i
  /-- every member's parameter telescope is the first member's, as a frame -/
  frame : ∀ i, i < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM i ψ).take d.nP).map (·.2.2)).reverse ρ
  /-- **an ORDINARY field mentions no member** (task #315 L-B, DESIGN
  §U.30): `mutualCtorKinds` calls a field ordinary exactly when it
  mentions none of the block's members, but `BlockOpened.ord` records
  only `constsResolve env₀` and `env₀` is unconstrained, so the
  abstract clauses do not carry it.  The copies' identities need it to
  know that the elimination left a container-ordinary field alone
  (`replaceAllNested_of_no_mention`). -/
  ordFree : ∀ (i j l : Nat) (x : Expr), i < d.k → j < (d.ctorsM i).length →
    (d.xFvsF i j)[l]? = some x → (d.ksF i j).getD l .ordinary = .ordinary →
    ConLeche.mentionsMember d.memberNames x.fvarTypeD = false
  /-- **a PIN'S COMPONENTS mention a member** (task #315 L-B's request,
  DESIGN §U.62 (e), §U.64): `ordFree`'s twin — the other half of
  `mutualCtorKinds`' `iff`.  The classification calls a field nested at
  `q` exactly when its spine's head is `(pinAt q).J` and one of the
  first `(pinAt q).nPJ` arguments mentions a member of the block's own
  group; `BlockOpened.nestF` records the head, the argument count and
  `constsResolve env₀` for the arguments PAST `nPJ`, and says nothing
  about the parameter part, so the copies' `pinF` arm cannot see the
  mention it needs.

  Spelled on the PIN'S OWN COMPONENTS (`DsE`, DESIGN §U.67 (b) B1) and
  not on the field's opened domain: at the nested block's own read-back
  the two are the same list — the restored domain is the pin re-opened
  at the parameter openers — but only the components' form has a
  source, the kernel's K.44 `nestedPinMentionOk`; the opened-domain
  spelling dies at the `NestedCtorsStaged` boundary, where
  `BlockOpened.nestF` is all that survives.  A stored container's block
  model carries `DsE` as a `PinSyn` field, so the consumer loses
  nothing.

  Stated with `q < d.nPins`, which the consumer has for free
  (`IsBlockModels.tgt_pin_lt` at the field) and which lets a pins-free
  block discharge the clause in the `pinNP`/`pinψ` idiom. -/
  nestMention : ∀ q, q < d.nPins →
    ∃ e ∈ (d.pinAt q).DsE.take (d.pinAt q).nPJ,
      ConLeche.mentionsMember d.memberNames e = true
  /-- **a pin's container is not a member** of the block: the opened
  form of a nested field (`BlockOpened.nestF`) is shape-compatible with
  a member occurrence at the parameters, which the copies' kind reading
  must exclude. -/
  pinsNotMembers : ∀ q, q < d.nPins → (d.pinAt q).J ∉ d.memberNames
  /-- **a pin's parameter count is the one `containerInfo?` reads**, at
  the block's own pre-block environment (`d.env₀`, where
  `BlockOpened.nestF` resolves the pin's index arguments):
  `replaceAllNested_occurrence` splits a container application at
  exactly that count. -/
  pinNP : ∀ q, q < d.nPins → ∃ ci' : ContainerInfo,
    ConLeche.containerInfo? d.env₀ (d.pinAt q).J = some ci' ∧ (d.pinAt q).nPJ = ci'.nP
  /-- **a pin's level assignment is the substitution of its level
  arguments for its container's level parameters** (task #315 L-E,
  DESIGN §U.39): the syntactic form every pin this checker records has
  (`pinOf`, `NestedPinGroupSyn.rep`), which the entry theorem's step
  (iii) needs of a STORED container's pins — two level assignments
  giving one READING of the container need not give one reading of its
  constructors, so the correspondence of pins is carried on the level
  ARGUMENTS (`PinCorr`) and reaches the assignments through this
  clause. -/
  pinψ : ∀ q, q < d.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
    env.find? (d.pinAt q).J = some (.indInfo cvT caps) →
    (d.pinAt q).lvls.length = cvT.levelParams.length ∧
    ∀ ψ : Name → Nat, (d.pinAt q).ψJ ψ = Level.substFn ψ cvT.levelParams (d.pinAt q).lvls

/-- **A stored container's PIN data are a congruence in the level
assignment** (task #315 L-E, DESIGN §U.72 (e) — REQUESTED of M7-3 as a
`ContainerModeled` clause, and carried as a premise until it lands):
two assignments agreeing on the group's own constant's level parameters
give ONE index universe, ONE component list and ONE index telescope at
every pin of the block.

`IsBlockModel.uParams` and `FormerData.params` are the same fact at the
MEMBERS; nothing in the tier says it at the pins, and the PIN class of
the container instance transfer needs it twice — at `copyTransfer_via`'s
`huT` (the two copies' targets' index universes, `copyTarget_u`, when
the target is one of the container's OWN pins) and at the `pinF` arm of
the WALK (the two sides' `PinCorr` are at the same own pin, so
`ClassPin`'s `frame` and `idx` come down to that pin's `Ds`/`Ids` at the
two assignments).

Four parts, and the WALK at a PIN class spends each exactly once
(DESIGN §U.74): the pins' level ARGUMENTS scoped in the group's own
level parameters (`ClassPin`'s `psi`, through `Level.substFn_ext` —
this is also `targetPin_corr`'s `hpd`), the pins' COMPONENTS bounded at
the container's parameters (`frame`, through `interp_congr_below`: the
two sides read one component at two frames that agree only below
`d.nP`), and the `u`/`Ds`/`Ids` congruences (`frame` and `idx`).

It is true of every pin this checker records — a pin's level arguments
and components are read off the block's own opened constructor, so they
mention only the block's level parameters and its parameter context —
and vacuous at a pins-free container. -/
@[expose] def ContainerPinParams (cvI : ConstantVal) (d : BlockModel V) : Prop :=
  ∀ q, q < d.nPins →
    (∀ v ∈ (d.pinAt q).lvls, v.allParamsDefined cvI.levelParams = true) ∧
    (∀ (ψ : Name → Nat) (e : AnnotTerm), e ∈ (d.pinAt q).Ds ψ →
      ConLeche.Term.Term.bvarsBelow d.nP e.erase) ∧
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ pp ∈ cvI.levelParams, ψ₁ pp = ψ₂ pp) →
      (d.pinAt q).u ψ₁ = (d.pinAt q).u ψ₂ ∧
      (d.pinAt q).Ds ψ₁ = (d.pinAt q).Ds ψ₂ ∧
      (d.pinAt q).Ids ψ₁ = (d.pinAt q).Ids ψ₂

omit [SetTheory V] in
/-- At a pins-free container the clause is vacuous. -/
theorem ContainerPinParams.of_noPins {cvI : ConstantVal} {d : BlockModel V} (hnp : d.pins = []) :
    ContainerPinParams (V := V) cvI d := by
  intro q hq
  simp only [BlockModel.nPins, hnp, List.length_nil] at hq
  exact absurd hq (Nat.not_lt_zero _)

/-- **A member's index telescope is bounded at the parameters** — the
MEMBER twin of `pinIds_below` (task #315 L-E, DESIGN §U.73). -/
theorem memberIds_below {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    (hreps : IsBlockModels m dJ) {i : Nat} (hi : i < dJ.k) (ψ : Name → Nat) :
    FieldsBelow dJ.nP (dJ.IdsM i ψ) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  refine DomsBelow.fields ?_
  have := DomsBelow.drop dJ.nP (hI.former.below ψ)
  simpa using this

/-! ## The correspondence a container instance is compared along -/

/-- A class's LEVEL ASSIGNMENT: the block's own at a member, the pin's
at a pin (`BlockModel.frameT`'s twin — task #315 L-E, DESIGN §U.57). -/
@[expose] def BlockModel.psiT (d : BlockModel V) (ψ : Name → Nat) (c : Nat) : Name → Nat :=
  if c < d.k then ψ else (d.pinAt (c - d.k)).ψJ ψ

/-- A class's CONTAINER's name: the member's own at a member (its group
is the block's), the pin's container at a pin. -/
@[expose] def BlockModel.nameT (d : BlockModel V) (c : Nat) : Name :=
  if c < d.k then d.memberName c else (d.pinAt (c - d.k)).J

omit [SetTheory V] in
theorem BlockModel.psiT_of_mem (d : BlockModel V) (ψ : Name → Nat) {c : Nat} (hc : c < d.k) :
    d.psiT ψ c = ψ := by simp only [psiT, if_pos hc]

omit [SetTheory V] in
theorem BlockModel.psiT_of_pin (d : BlockModel V) (ψ : Name → Nat) {c : Nat} (hc : ¬ c < d.k) :
    d.psiT ψ c = (d.pinAt (c - d.k)).ψJ ψ := by simp only [psiT, if_neg hc]

omit [SetTheory V] in
theorem BlockModel.nameT_of_mem (d : BlockModel V) {c : Nat} (hc : c < d.k) :
    d.nameT c = d.memberName c := by simp only [nameT, if_pos hc]

omit [SetTheory V] in
theorem BlockModel.nameT_of_pin (d : BlockModel V) {c : Nat} (hc : ¬ c < d.k) :
    d.nameT c = (d.pinAt (c - d.k)).J := by simp only [nameT, if_neg hc]

/-- **The ROOT's class `c` and the block's pin `q` are ONE family**
(task #315 L-E, DESIGN §U.57): the relation the container instance
transfer runs along, and `relMeet`'s `R`.

A container instance is compared with the block's pins through ONE
container — its ROOT (DESIGN §U.55 (c)) — whose classes are its members
and its OWN pins (`BlockModel.kT`); `dR`, `ψR`, `ρR` are the root's
model, level assignment and parameter frame, `D`, `ψ`, `ρp` the block's.
The clauses are exactly what the transfer consumes at the pair: ONE
container (`name` — which `targetPin_corr` supplies at a rewritten
field and the group views at a member), ONE level assignment on that
container's own level parameters (`psi` — `ContainerModeled.pinψ` and
`Level.substFn_map_subst`), ONE frame on its parameters (`frame` —
`PinCorr`'s components at their values, `interp_instAll`), and ONE
index set (`idx`), which is what makes the two families comparable
fibre by fibre.

It is a RELATION and not a map, in both directions: two of the root's
pins may instantiate to one block pin (`K (J α)`, `K (J β)` at
`Ds = [P4, P4]`), and two block pins may read alike; `relMeet` and
`lfpTuple_le_of_rel` absorb both. -/
structure ClassPin (env : Env) (D dR : BlockModel V) (ψ ψR : Name → Nat) (ρp ρR : Nat → V)
    (c q : Nat) : Prop where
  /-- `c` is one of the root's classes -/
  cLt : c < dR.kT
  /-- `q` is one of the block's pins -/
  qLt : q < D.nPins
  /-- ONE container -/
  name : dR.nameT c = (D.pinAt q).J
  /-- ONE level assignment, at that container's own level parameters -/
  psi : ∀ (cvT : ConstantVal) (caps : IndCaps),
    env.find? (D.pinAt q).J = some (.indInfo cvT caps) →
    ∀ p ∈ cvT.levelParams, dR.psiT ψR c p = (D.pinAt q).ψJ ψ p
  /-- ONE frame, at that container's parameters -/
  frame : ∀ v, v < (D.pinAt q).nPJ → dR.frameT c ψR ρR v = D.pinFrame q ψ ρp v
  /-- ONE index set: the fibres are compared at the same tuples -/
  idx : dR.idxT ψR ρR c = D.pinIdx q ψ ρp

/-- **`ClassPin`, at the covering's ROOT GROUP** (task #315 L-E,
DESIGN §U.71): the relation the container instance transfer actually
runs along — `ClassPin` plus the record of WHERE a MEMBER class comes
from, namely the root group itself, class `c` at pin `r + c`.

The conjunct costs the covering nothing (`classPin_of_rootMember` is
stated at exactly that pair, and `classPin_of_pinCorr` produces a PIN
class, where it is vacuous) and it is what aligns the two sides at a
member class: the block's group of `r + c` is the ROOT group, whose
block model IS `dR`.  Without it the alignment would need
`containerInfo?` to agree ACROSS the members of a group, which is not
an environment fact — it holds only under the run's own
`nestedContainersOk` (K.14) or a just-installed block's read-back
(K.34), neither of which the abstract transfer has. -/
@[expose] def ClassPinAt (env : Env) (D dR : BlockModel V) (ψ ψR : Name → Nat)
    (ρp ρR : Nat → V) (r c q : Nat) : Prop :=
  ClassPin env D dR ψ ψR ρp ρR c q ∧ (c < dR.k → q = r + c)

/-- **A container instance is covered by its ROOT's classes** (task
#315 L-E, DESIGN §U.58): every pin of the instance — K.37's
`nestedPinInstOf` reads the partition — is `ClassPin`-related to a
class of the root's container.  The root is a mint GROUP, not a pin:
K.40's measurement over 152 container instances found the group the
unit (152/152 with one entry group per instance; 151/152 with a single
pin, `nested_p05`'s `P5Ev`/`P5Od` being a mutual group of size two
minted together, with one parent and two parent-minimal pins), and the
entry condition is that the group's parent lies OUTSIDE the instance,
not that it is absent.

This is the ONE thing the container instance transfer cannot derive
from the models (DESIGN §U.55 (c)): the root container's own
declaration minted the instance's other containers as ITS pins, which
is a fact about that elimination.  K.40's mint parent carries it; the
covering is the parent chain. -/
@[expose] def InstanceCovered (env : Env) (D dR : BlockModel V) (ψ ψR : Name → Nat)
    (ρp ρR : Nat → V) (inst : Nat → Nat) (r : Nat) : Prop :=
  ∀ q, q < D.nPins → inst q = inst r → ∃ c, ClassPinAt env D dR ψ ψR ρp ρR r c q

/-! ## The pins' laws and shapes of a stored block -/

instance : Nonempty (BlockModel V) :=
  ⟨{ nP := 0, k := 0, resSort := .zero, isProp := false, large := false, env₀ := ⟨[]⟩
     memberNames := [], nIdxs := [], ppsM := fun _ _ => [], uM := fun _ _ => 0
     ctorsM := fun _ => [], idxF := fun _ _ => [], dsF := fun _ _ _ => [], esF := fun _ _ _ => []
     srcsF := fun _ _ => [], ksF := fun _ _ => [], tgts := fun _ _ _ => 0, fvsPF := fun _ _ => []
     xFvsF := fun _ _ => [], xrestF := fun _ _ => .sort .zero, eissF := fun _ _ _ => []
     tssF := fun _ _ _ => [], pins := [], Φ := fun _ _ _ _ => pt, pinCar := fun _ _ _ _ => pt
     inj := fun _ _ _ _ => pt }⟩

/-- **A stored block's targets, viewed** (task #315 L-E): the block
model's members and pins at the class readers (`uT`/`IdsT`,
`NestedRecCand.lean`), its pins' components, and the stored readings at
the carrier `acval`. -/
@[expose] def BlockModel.targetView (d : BlockModel V) (acval : Name → (Name → Nat) → AnnotTerm)
    (ψ : Name → Nat) : TargetView V where
  k := d.k
  n := d.nPins
  w := d.w ψ
  u := fun t => d.uT t ψ
  Ids := fun t => d.IdsT t ψ
  Ds := fun t => (d.pinAt (t - d.k)).Ds ψ
  DsE := fun t => (d.pinAt (t - d.k)).DsE
  EA := targetRead acval d.memberNames d.pins d.nP d.k ψ
  J := fun t => if t < d.k then d.memberName t else (d.pinAt (t - d.k)).J
  lvls := fun t => if t < d.k then [] else (d.pinAt (t - d.k)).lvls

/-- **A pin group of a stored block, viewed** (task #315 L-E; the
run's `NestedPinGroupSyn` made abstract): the pins `[q₀, q₀ + kJ)` of
`d` are the members of one container block model `dJ` in order — named
as its members, sharing their level assignment and components, with
the container's arities at each member, the container's sort the
block's at the group's level assignment, and the components fitting
the container's parameters at every parameter frame of the block. -/
structure PinGroupView (d dJ : BlockModel V) (q₀ kJ : Nat) : Prop where
  seg : q₀ + kJ ≤ d.nPins
  kpos : 0 < kJ
  kEq : dJ.k = kJ
  name : ∀ i, i < kJ → (d.pinAt (q₀ + i)).J = dJ.memberName i
  same : ∀ i, i < kJ → ∀ ψ : Name → Nat,
    (d.pinAt (q₀ + i)).ψJ ψ = (d.pinAt q₀).ψJ ψ ∧ (d.pinAt (q₀ + i)).Ds ψ = (d.pinAt q₀).Ds ψ
  /-- the group's pins share their components' EXPRESSIONS (task #315
  L-E, DESIGN §U.51: the container instance transfer reads a target's
  head off a component, and the group's shape is stated at the base
  pin's) -/
  sameDsE : ∀ i, i < kJ → (d.pinAt (q₀ + i)).DsE = (d.pinAt q₀).DsE
  lvls : ∀ i, i < kJ → (d.pinAt (q₀ + i)).lvls = (d.pinAt q₀).lvls
  pinU : ∀ i, i < kJ → ∀ ψ : Name → Nat, (d.pinAt (q₀ + i)).u ψ = dJ.uM i ((d.pinAt q₀).ψJ ψ)
  pinNP : ∀ i, i < kJ → (d.pinAt (q₀ + i)).nPJ = dJ.nP
  pinNIdx : ∀ i, i < kJ → (d.pinAt (q₀ + i)).nIdx = dJ.nIdxAt i
  pinPps : ∀ i, i < kJ → (d.pinAt (q₀ + i)).pps = dJ.ppsM i
  pinDsLen : ∀ ψ : Name → Nat, ((d.pinAt q₀).Ds ψ).length = dJ.nP
  w : ∀ ψ : Name → Nat, dJ.w ((d.pinAt q₀).ψJ ψ) = d.w ψ
  DsFit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V), SpineFit ρ (d.params ψ) as →
    SpineFit (consList as ρ) (dJ.params ((d.pinAt q₀).ψJ ψ))
      (((d.pinAt q₀).Ds ψ).map (interp V (consList as ρ)))

/-- **A pin group's index set IS its container's** (task #315 L-E,
DESIGN §U.71): at a group `[q₀, q₀ + kK)` of `d` with container `dJ`,
pin `q₀ + i`'s index-tuple set is `dJ`'s member `i`'s at the pin's
frame — the sort by `pinU`, the telescope by `pinPps`/`pinNP`, the
frame by `same`.  What turns a `ClassPin`'s index clause into the
block's own `idx` at the pin's class, on either side of the pair. -/
theorem BlockModel.pinIdx_of_view {d dJ : BlockModel V} {q₀ kK : Nat}
    (S : PinGroupView d dJ q₀ kK) (ψ : Name → Nat) (ρ : Nat → V) {i : Nat} (hi : i < kK) :
    d.pinIdx (q₀ + i) ψ ρ = dJ.idx ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ ρ) i := by
  have hfr : d.pinFrame (q₀ + i) ψ ρ = d.pinFrame q₀ ψ ρ := by
    unfold BlockModel.pinFrame; rw [(S.same i hi ψ).2]
  have hIds : (d.pinAt (q₀ + i)).Ids ψ = dJ.IdsM i ((d.pinAt q₀).ψJ ψ) := by
    unfold PinSyn.Ids
    rw [S.pinPps i hi, S.pinNP i hi, (S.same i hi ψ).1]
    rfl
  unfold BlockModel.pinIdx BlockModel.idx
  rw [hfr, hIds, S.pinU i hi ψ]

/-- **A pin's index telescope is bounded at its components** (task #315
L-E, DESIGN §U.72): the pin's container member's telescope over the
container's parameters (`pinPps`/`pinNP`, `FormerData.below`,
`DomsBelow.drop`/`.fields`) — `classPin_of_pinCorr`'s `hIdsBelow` at
the root's own pin. -/
theorem pinIds_below {env : Env} {m : EnvModel V env} {d dJ : BlockModel V} {q₀ kK : Nat}
    (S : PinGroupView d dJ q₀ kK) (hreps : IsBlockModels m dJ) {i : Nat} (hi : i < kK)
    (ψ : Name → Nat) (ρ : Nat → V) :
    FieldsBelow (((d.pinAt (q₀ + i)).Ds ψ).map (interp V ρ)).length
      ((d.pinAt (q₀ + i)).Ids ψ) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i (S.kEq ▸ hi)
  have hlen : (((d.pinAt (q₀ + i)).Ds ψ).map (interp V ρ)).length = dJ.nP := by
    rw [List.length_map, (S.same i hi ψ).2, S.pinDsLen ψ]
  have hIds : (d.pinAt (q₀ + i)).Ids ψ
      = ((dJ.ppsM i ((d.pinAt (q₀ + i)).ψJ ψ)).drop dJ.nP).map (·.2.2) := by
    unfold PinSyn.Ids
    rw [S.pinPps i hi, S.pinNP i hi]
  rw [hlen, hIds]
  refine DomsBelow.fields ?_
  have := DomsBelow.drop dJ.nP (hI.former.below ((d.pinAt (q₀ + i)).ψJ ψ))
  simpa using this

/-- **A pin group's own members are their own partners** (task #315
L-E, DESIGN §U.65 — `InstanceCovered`'s first case, §U.55 (b)'s Base):
at the ROOT group `[r, r + kR)` of a container instance, read at the
root pin's level assignment and frame, the container's MEMBER class `i`
and the block's pin `r + i` are `ClassPin`-related, and every clause is
a field of the group's view: the container by `name`, the level
assignment and the components by `same`, and the index set by `pinU`
with the pin's index telescope being its container member's
(`pinPps`/`pinNP`).

**No record is needed for this case** — it is the covering's base, and
K.41's pairing is for the instance's OTHER groups. -/
theorem classPin_of_rootMember {env : Env} {D dR : BlockModel V} {r kR : Nat}
    (S : PinGroupView D dR r kR) {ψ : Name → Nat} {ρp : Nat → V} {i : Nat} (hi : i < kR) :
    ClassPin env D dR ψ ((D.pinAt r).ψJ ψ) ρp (D.pinFrame r ψ ρp) i (r + i) where
  cLt := by
    show i < dR.k + dR.nPins
    rw [S.kEq]
    omega
  qLt := by have := S.seg; omega
  name := by
    rw [dR.nameT_of_mem (by rw [S.kEq]; exact hi)]
    exact (S.name i hi).symm
  psi := by
    intro cvT caps _ q _
    rw [dR.psiT_of_mem ((D.pinAt r).ψJ ψ) (show i < dR.k by rw [S.kEq]; exact hi),
      (S.same i hi ψ).1]
  frame := by
    intro v _
    show (if i < dR.k then D.pinFrame r ψ ρp else _) v = _
    rw [if_pos (by rw [S.kEq]; exact hi)]
    unfold BlockModel.pinFrame
    rw [(S.same i hi ψ).2]
  idx := by
    show (if i < dR.k then dR.idx ((D.pinAt r).ψJ ψ) (D.pinFrame r ψ ρp) i else _) = _
    rw [if_pos (by rw [S.kEq]; exact hi)]
    show idxSet (dR.uM i ((D.pinAt r).ψJ ψ)) (D.pinFrame r ψ ρp)
        (dR.IdsM i ((D.pinAt r).ψJ ψ))
      = idxSet ((D.pinAt (r + i)).u ψ) (D.pinFrame (r + i) ψ ρp) ((D.pinAt (r + i)).Ids ψ)
    have hIds : (D.pinAt (r + i)).Ids ψ = dR.IdsM i ((D.pinAt (r + i)).ψJ ψ) := by
      unfold PinSyn.Ids
      rw [S.pinPps i hi, S.pinNP i hi]
      rfl
    have hfr : D.pinFrame (r + i) ψ ρp = D.pinFrame r ψ ρp := by
      unfold BlockModel.pinFrame
      rw [(S.same i hi ψ).2]
    rw [hIds, hfr, (S.same i hi ψ).1, S.pinU i hi ψ]

/-- **The pins' shapes of a stored block** against a global assignment
`B` of block models to container groups (task #315 L-E, DESIGN §U.36):
every pin `q` of `d` sits in a group `(q₀, kJ)` whose container is
`B ci` at the group `containerInfo?` reads for the pin's container, and
pin `q`'s constructors (`pc q`, the copies restored — `PinCtors`) have
`CopyCtorShape` against that container at the group's level assignment
and components, at every parameter frame.  The assignment is ONE
function for the whole environment so that the shape a container's own
pins carry and the shape the block being installed proves speak of the
SAME model of the pins' container — what the global entry theorem
composes (`nestedPinLeaf_all`).

The COUNT conjunct (task #315 L-E, DESIGN §U.73 (d), the maintainer's
ruling): a pin's constructors are as many as its container member's.
`ChainFitT` at a pin class reads `(pc q).ctors` (`ctorsT_of_pin`), so
the container instance transfer's `j` ranges over that list, while the
shape below is supplied only for `j < ((B ci).ctorsM i').length`;
`PinCtors` is a bare record and `PinRecLaws` quantifies `j` over the
former everywhere, so without this nothing forbids a pin carrying
constructors its container does not have, and the transfer would have
no shape at them.

**Its three producer classes**, so that nobody rediscovers them: the
five PINNED BASIS blocks, where it is vacuous (`d.pins = []`, so `q`
does not exist); the NESTED route, where it is
`NestedPinGroupSyn.ctorCount` composed with `nestedPc`'s own count; and
M7-3's NATIVE and MUTUAL sites, whose blocks are pins-free for the same
reason as the basis (`ContainerCross.lean`'s pins-free construction).
The transports (`PinShapes.crossEnv`, `PinShapes.congrB`) carry it
unchanged. -/
@[expose] def PinShapes {env : Env} (m : EnvModel V env) (B : ContainerInfo → BlockModel V)
    (d : BlockModel V) (pc : Nat → PinCtors V) : Prop :=
  ∀ q, q < d.nPins → ∃ (q₀ kJ i : Nat) (ci : ContainerInfo), q = q₀ + i ∧ i < kJ ∧
    ConLeche.containerInfo? env (d.pinAt q).J = some ci ∧
    PinGroupView d (B ci) q₀ kJ ∧
    (∀ i', i' < kJ → (pc (q₀ + i')).ctors.length = ((B ci).ctorsM i').length) ∧
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ i' j, i' < kJ → j < ((B ci).ctorsM i').length →
      ∀ (cvT : ConstantVal) (caps : IndCaps),
        env.find? (d.pinAt (q₀ + i')).J = some (.indInfo cvT caps) →
      CopyCtorShape (d.targetView m.acval ψ) m.acval (B ci) ((d.pinAt q₀).ψJ ψ) ((d.pinAt q₀).Ds ψ)
        cvT.levelParams (d.pinAt q₀).lvls (fun l => (pc (q₀ + i')).tgts j l)
        (((pc (q₀ + i')).tlss ψ).getD j [])
        (((pc (q₀ + i')).Eiss ψ).getD j []) ρp i' j (d.k + q₀) kJ
        (((pc (q₀ + i')).Fss ψ).getD j []) ((pc (q₀ + i')).rss.getD j [])
        (((pc (q₀ + i')).Ess ψ).getD j [])

/-- **A container group's obligation at the assignment `B`** (task #315
L-E, DESIGN §U.36 — the `pins` clause the maintainer's plan asked of
`ContainerModeled`, stated beside it because it names the OTHER
containers' models through `B`): the group's block model `B ci` in the
container's own terms, and its pins' constructors with the recursor
kit's laws — the pins' carriers at any member tuple are the LEAST
families closed under them (`PinRecLaws.ind`, the leastness the `Prop`
countermodel of DESIGN §U.36 violates) — and their shapes against `B`. -/
@[expose] def BlockAt {env : Env} (m : EnvModel V env) (B : ContainerInfo → BlockModel V)
    (ci : ContainerInfo) : Prop :=
  ContainerModeled m ci (B ci) ∧
  ∃ pc : Nat → PinCtors V, PinRecLaws m (B ci) pc ∧ PinShapes m B (B ci) pc

/-- **Every stored container carries its block's model at the
assignment `B`**: at every group `containerInfo?` reads, `BlockAt`. -/
@[expose] def EnvBlocksOf {env : Env} (m : EnvModel V env) (B : ContainerInfo → BlockModel V) :
    Prop :=
  ∀ (J : Name) (ci : ContainerInfo), ConLeche.containerInfo? env J = some ci → BlockAt m B ci

/-- **Every stored container carries its block's model** at the model
`m`, in the container's own terms (`ContainerModeled` at the group
`containerInfo?` reads), with its pins' laws and shapes — for ONE
assignment of block models to container groups.  The `EnvModelB`
field (DESIGN §U.13 (f) 1, §U.31). -/
@[expose] def EnvBlockModels {env : Env} (m : EnvModel V env) : Prop :=
  ∃ B : ContainerInfo → BlockModel V, EnvBlocksOf m B

/-- **The block model of a container group** — THE assignment the
field witnesses, chosen once for the whole environment, so that every
pin of a mint group reads the SAME block model and a container's own
pins' shapes speak of the models the block being installed reads. -/
noncomputable def blockOf {env : Env} (m : EnvModel V env) (ci : ContainerInfo) : BlockModel V :=
  Classical.epsilon (EnvBlocksOf m) ci

/-- **The pins' containers carry their blocks' models** — `EnvBlockModels`
read at the elimination's pins (`ElimState.pins`) at the chosen
assignment: the premise the pin groups' assembly consumes (DESIGN
§U.21). -/
@[expose] def PinsModeled {env : Env} (m : EnvModel V env) (pins : List NestedPin) : Prop :=
  ∀ q ∈ pins, ∀ ci : ContainerInfo, ConLeche.containerInfo? env q.container = some ci →
    BlockAt m (blockOf m) ci

/-- A container the elimination read is a stored inductive. -/
theorem containerInfo?_found {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) :
    ∃ (cv : ConstantVal) (caps : IndCaps), env.find? I = some (.indInfo cv caps) := by
  unfold ConLeche.containerInfo? at h
  by_cases hq : (I == ConLeche.quotName) = true
  · rw [if_pos hq] at h; exact nomatch h
  · rw [if_neg hq] at h
    cases hf : env.find? I with
    | none => rw [hf] at h; exact nomatch h
    | some ci' =>
      rw [hf] at h
      cases ci' with
      | indInfo cv caps => exact ⟨cv, caps, rfl⟩
      | _ => simp [bind, Option.bind] at h

/-- The chosen assignment carries every stored container's block. -/
theorem blockOf_of_env {env : Env} {m : EnvModel V env} (hm : EnvBlockModels m) :
    EnvBlocksOf m (blockOf m) :=
  Classical.epsilon_spec hm

/-- The chosen block model of a group is a `ContainerModeled` one. -/
theorem blockOf_spec {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    (h : BlockAt m (blockOf m) ci) : ContainerModeled m ci (blockOf m ci) :=
  h.1

/-- **The pins are modelled at an environment whose stored inductives
are** (`EnvBlockModels` read at the pins' containers). -/
theorem pinsModeled_of_env {env : Env} {m : EnvModel V env} (hm : EnvBlockModels m)
    {pins : List NestedPin} (_hok : ConLeche.nestedContainersOk env pins = true) :
    PinsModeled m pins :=
  fun q _ ci hci => blockOf_of_env hm q.container ci hci

/-- **The shapes read the assignment at the pins' containers only**. -/
theorem PinShapes.congrB {env : Env} {m : EnvModel V env} {B B' : ContainerInfo → BlockModel V}
    {d : BlockModel V} {pc : Nat → PinCtors V}
    (hBB : ∀ q, q < d.nPins → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env (d.pinAt q).J = some ci → B' ci = B ci)
    (h : PinShapes m B d pc) : PinShapes m B' d pc := by
  intro q hq
  obtain ⟨q₀, kJ, i, ci, hqe, hi, hci, hgv, hsh⟩ := h q hq
  rw [← hBB q hq ci hci] at hgv hsh
  exact ⟨q₀, kJ, i, ci, hqe, hi, hci, hgv, hsh⟩

/-- **The leastness law is not vacuous** (the check DESIGN §U.36 records
against the `Prop` countermodel of the maintainer's plan, `PLAN` §5): at
a tuple `X` at which NO spine fits any of pin `q`'s constructors, the
pin's carrier at `X` is EMPTY — `PinRecLaws.ind` at the property
`False`.  A model whose `pinCar` is constant (its carrier value at every
tuple, the "weird" `EnvModel` that satisfies every clause of
`IsBlockModel`/`ContainerModeled`) violates it at the bottom tuple of a
container whose pin's constructors all take a member field. -/
theorem PinRecLaws.pinCar_empty_of_noFit {env : Env} {m : EnvModel V env} {d : BlockModel V}
    {pc : Nat → PinCtors V} (h : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X) {q : Nat} (hq : q < d.nPins)
    (hnofit : ∀ Y : Nat → V, (∀ mm, mm < d.k → Y mm = X mm) →
      ∀ (t : V) (j : Nat) (fs : List V), j < (pc q).ctors.length →
        ¬ d.ChainFitT pc ψ ρp Y t (d.k + q) j fs) :
    ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ x, ¬ x ∈ˢ SetTheory.app (d.pinCar ψ ρp X q) t := by
  intro t ht x hx
  refine h.ind ψ ρp hρp X hX (fun q' _ _ => q' ≠ q) (fun q' _ t' _ j fs hj hfit hqq => ?_)
    q hq t ht x hx rfl
  subst hqq
  refine hnofit _ (fun mm hmm => ?_) t' j fs hj hfit
  rw [segJoin_lt _ _ hmm, d.famAt_of_mem hmm]

/-- `PinRecLaws` reads no model: it crosses any change of model. -/
theorem PinRecLaws.cross {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V} {pc : Nat → PinCtors V} (h : PinRecLaws m₁ d pc) : PinRecLaws m₂ d pc :=
  ⟨h.tgtsLt, h.idxOk, h.fibre, h.mkZero, h.mkInj, h.injW, h.ind⟩

/-! ## The model with its blocks -/

/-- **The P-tier environment invariant WITH ITS BLOCKS** (task #315
M7-3, DESIGN §U.31): `EnvModelM` and, on top, every stored container's
block model (`EnvBlockModels` at the carrier) — the field that replaces
the premise `EnvBlockModels` of the nested consumer.  A structure
CARRYING `EnvModelM` rather than a field of it because `ContainerModeled`
is stated at the block-model tier (`IsBlockModel`, the stage kits'
readings), which sits ABOVE `EnvModelM` in the import order: the
field's type cannot be named there.  Every stage of the fold lifts to
it (`Model/Inductives/EnvModelBStages.lean`); the fold flips to carrying
it with the nested route (M8). -/
structure EnvModelB (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env)
    extends EnvModelM V μ env where
  /-- every stored container carries its block's model -/
  blocks : EnvBlockModels base2

/-! ## The block model of a nested run -/

/-- **The block model is the run's block**: its arities, names and
constructors are the recogniser's and the restore's, its pins the
elimination's (the container, its level arguments and its components
at the block's parameter openers).  The consumer (M7) reads the block
model CONCRETELY (`NestedCoreOut`, `DeclNestedCore.lean`); this record
is what the abstract clauses of the assembly consume. -/
structure NestedBlockModelOf (env : Env) (p : NestedParts) (st : ElimState)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (d : BlockModel V) : Prop where
  k : d.k = p.k
  nP : d.nP = p.nP
  env₀ : d.env₀ = env
  memberNames : d.memberNames = p.memberNames
  large : d.large = p.large
  nPins : d.nPins = st.pins.length
  /-- pin `q` is the elimination's `q`-th pin: the container, the
  level arguments and the components at the block's parameter openers -/
  pin : ∀ q pin, st.pins[q]? = some pin →
    (d.pinAt q).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container (d.pinAt q).lvls) (d.pinAt q).DsE
  /-- a member's constructors are its restored ones -/
  ctors : ∀ t, t < p.k → d.ctorsM t = (ctorsR.getD t []).map fun c => (c.1, c.2.2)

end ConLeche.Model
