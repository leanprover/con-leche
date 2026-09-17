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
container (`name` — which `targetHead_corr` supplies at a rewritten
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
  lvls := fun t => (d.pinAt (t - d.k)).lvls

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
composes (`nestedPinLeaf_all`). -/
@[expose] def PinShapes {env : Env} (m : EnvModel V env) (B : ContainerInfo → BlockModel V)
    (d : BlockModel V) (pc : Nat → PinCtors V) : Prop :=
  ∀ q, q < d.nPins → ∃ (q₀ kJ i : Nat) (ci : ContainerInfo), q = q₀ + i ∧ i < kJ ∧
    ConLeche.containerInfo? env (d.pinAt q).J = some ci ∧
    PinGroupView d (B ci) q₀ kJ ∧
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ i' j, i' < kJ → j < ((B ci).ctorsM i').length →
      ∀ (cvT : ConstantVal) (caps : IndCaps),
        env.find? (d.pinAt (q₀ + i')).J = some (.indInfo cvT caps) →
      CopyCtorShape (d.targetView m.acval ψ) m.acval (B ci) ((d.pinAt q₀).ψJ ψ) ((d.pinAt q₀).Ds ψ)
        (d.pinAt q₀).DsE cvT.levelParams (d.pinAt q₀).lvls (fun l => (pc (q₀ + i')).tgts j l)
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
