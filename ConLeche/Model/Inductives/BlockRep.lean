module

public import ConLeche.Model.Inductives.FixStageRec
public section

/-!
# `BlockData` and `BlockModelAt` — THE datum of an inductive block (task #315, M3)

Every stored inductive type is a MEMBER of a block, and the block is
represented as the simultaneous least pre-fixed point of ONE operator
on a TUPLE of families (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`), one COMPONENT per member,
each over the member's own plain index-tuple set.  No member tag
enters an index, no constructor position is flattened across members,
no copy of anything is minted: a single family is the block with
`k = 1` (`lfpTuple_one`).

**The data** (`BlockData`) is the fixpoint route's spelling of a
block, keyed by component and by the component's OWN constructor
position: per component its telescope reading, index-tuple sort and
constructors, per constructor the readings of its stored type
(`BlockCtorDataI`'s data: `dsF`, `esF`, `ksF`, `eissF`, `tssF`) and,
per field, the COMPONENT it targets (`tgts`); the tuple operator `Φ`
and the component-local constructor injections `inj` — both abstract,
so a pinned block whose elements are not tagged towers is represented
on the nose.

**The width.**  A block has `k` MEMBERS (the declared families) and
`nInst` INSTANCE components (the copies a nested block's container
contributes, DESIGN-theory §2.2); the operator's width is
`N = k + nInst`.  Deliverable 1 installs no nested block, so every
instance is built at `nInst = 0` — but the width is a field, and every
clause but `leaf` quantifies over ALL `N` components, so adding
instances later changes no statement.  `leaf` is at members only: only
a member has a stored former whose leaf the environment model reads.

**The clause** (`BlockModelAt`), for the block whose members are
`names`:

* at every parameter frame each component's index telescope is graded
  (`idxOk`) and `Φ` is a monotone, space-preserving tuple functor with
  a closed tuple (`functor` — its third conjunct is (W) at tuples,
  `SetModel/TupleContainer.lean`), whose component `c`'s fibre at
  `(X, t)` consists exactly of the injections `inj c j fs` of the
  spines fitting component `c`'s constructor `j` at `(X, t)`
  (`fibre`), a recursive field read at the component of the member it
  targets (`ChainFit`, stated SEMANTICALLY: an entry is a set, the
  slot the target's family at the tuple of the index expressions under
  the field's telescope — `slotSet`);
* **the leaf**: a member's former at fitting parameters and its own
  indices is the fibre of the least pre-fixed TUPLE's component at the
  index tuple (`leaf`);
* **the constructors**: component `c`'s constructor `j` at fitting
  parameters and fields is `inj c j fs` (`ctor`, at EVERY component —
  F0's finding: official emits a recursor per instance, so an
  instance's ι rule cannot be stated without its constructors'
  injections); the injections are the point at a `Prop`-valued block
  (`mkZero`) and injective WITHIN a component at a `Type`-valued one
  (`mkInj` — cross-component disjointness is never needed: the
  recursor's union tags the components).

`fibre` and `functor` quantify over ALL tuples of the tuple space and
ALL parameter frames in the `Sat` domain, never over the carrier:
that is falsifier F0's finding (formation `inj … ∈ univ w` is
derivable from `functor`'s `MapsTuple` and `fibre` only at that
strength).

Task #315's `IsBlockModel` is this clause plus the per-constant facts
of a STORED member (its type's strip, the recursor's arithmetic and
rules).  Those are not clauses here: they are inputs to establishing
the representation, not part of it — `BlockCtorFacts` bundles the
constructor half.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The block's data -/

/-- **The representation data of a block** (see the module
docstring). -/
structure BlockData (V : Type w) where
  /-- the parameter count (shared by the components) -/
  nP : Nat
  /-- the number of MEMBERS (the declared families) -/
  k : Nat
  /-- the number of INSTANCE components (`0` before nested blocks) -/
  nInst : Nat
  /-- the result sort (every member's stored type ends in it) -/
  resSort : Level
  /-- `resSort` is provably zero -/
  isProp : Bool
  /-- the eliminator is large -/
  large : Bool
  /-- the members' names, by position -/
  memberNames : List Name
  /-- per member: its index count -/
  nIdxs : List Nat
  /-- per component: its parameter-and-index telescope reading -/
  ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per component: its index-tuple sort -/
  uM : Nat → (Name → Nat) → Nat
  /-- per component: its constructors, in order, with their field counts -/
  ctorsM : Nat → List (ConstantVal × Nat)
  /-- per component and constructor: the residual's index arguments -/
  idxF : Nat → Nat → List Expr
  /-- per component and constructor: the type reading's binder data -/
  dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per component and constructor: the result's index readings -/
  esF : Nat → Nat → (Name → Nat) → List AnnotTerm
  /-- per component and constructor: the field sources -/
  srcsF : Nat → Nat → List (Option Nat)
  /-- per component and constructor: the opened parameter variables -/
  fvsPF : Nat → Nat → List Expr
  /-- per component and constructor: the opened field variables -/
  xFvsF : Nat → Nat → List Expr
  /-- per component and constructor: the opened residual -/
  xrestF : Nat → Nat → Expr
  /-- per component and constructor: the fields WITH HOLES (lane HOLE2) —
  the walked term's reading, members abstracted to the holes
  (`BlockAbsRead`) -/
  absFF : Nat → Nat → (Name → Nat) → List AnnotTerm
  /-- **the tuple operator**, at a level assignment and a parameter
  frame: a meta-level function on tuples of families, component `c` a
  set-level family over component `c`'s index-tuple set -/
  Φ : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- **the constructor injections**: component `c`'s constructor `j`
  (component-local) at a field spine -/
  inj : (Name → Nat) → Nat → Nat → List V → V

namespace BlockData

variable (d : BlockData V)

/-- The operator's WIDTH: members plus instance components. -/
@[expose] def N : Nat := d.k + d.nInst

/-- The result sort's value. -/
@[expose] def w (ψ : Name → Nat) : Nat := d.resSort.eval ψ

/-- Member `mm`'s name. -/
@[expose] def memberName (mm : Nat) : Name := d.memberNames.getD mm .anonymous

/-- Member `mm`'s index count. -/
@[expose] def nIdxAt (mm : Nat) : Nat := d.nIdxs.getD mm 0

/-- The parameter telescope (the block's, read off component `0`: the
components share their parameters). -/
@[expose] def params (ψ : Name → Nat) : List AnnotTerm := ((d.ppsM 0 ψ).take d.nP).map (·.2.2)

/-- Component `c`'s own index telescope, at the parameter frame. -/
@[expose] def IdsM (c : Nat) (ψ : Name → Nat) : List AnnotTerm :=
  ((d.ppsM c ψ).drop d.nP).map (·.2.2)

/-- Component `c`'s constructor data list (the fixpoint kit's, its
field-kind slots empty: the block's datum classifies no field). -/
@[expose] def cds (c : Nat) (ψ : Name → Nat) : List CtorDatumR :=
  fixCtorDataList (d.dsF c) (d.esF c) (fun _ => []) (fun _ _ => []) (fun _ _ => []) ψ
    (d.ctorsM c) 0

/-- Component `c`'s field domains, per constructor (the real readings:
a recursive entry is its TARGET's former applied). -/
@[expose] def Fss (c : Nat) (ψ : Name → Nat) : List (List AnnotTerm) := fssOfR d.nP (d.cds c ψ)

/-- Component `c`'s results' index readings, per constructor. -/
@[expose] def Ess (c : Nat) (ψ : Name → Nat) : List (List AnnotTerm) := essOfR (d.cds c ψ)

/-- **The tuple of index-tuple sets** at a parameter frame: component
`c`'s is the tower set over its own index telescope. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun c => idxSet (d.uM c ψ) ρp (d.IdsM c ψ)

/-- Component `c`'s index spine as its index tuple. -/
@[expose] noncomputable def tup (ψ : Name → Nat) (c : Nat) (is : List V) : V :=
  tupW (d.uM c ψ) is

end BlockData

namespace BlockData

variable (d : BlockData V)

/-- **A field spine fits component `c`'s constructor `j` as STORED** at
the parameter frame `ρp` and the index tuple `t`: its field readings
at `ρp`, and the constructor's result index readings at it are the
components of `t` — the fit a rule's certificates read. -/
@[expose] def StoredFit (ψ : Name → Nat) (ρp : Nat → V) (t : V) (c j : Nat) (fs : List V) :
    Prop :=
  j < (d.ctorsM c).length ∧ SpineFit ρp ((d.Fss c ψ).getD j []) fs ∧
  ∀ l, l < (d.IdsM c ψ).length →
    interp V (consList fs ρp) (((d.Ess c ψ).getD j []).getD l default) = projS l t

end BlockData

/-! ## The constructors' reading facts -/

/-- **The per-constructor facts of a block component's constructor**:
the constructor is stored with the block's level parameters and its
type reads as the block data says. -/
@[expose] def BlockCtorFacts {env : Env} (m : EnvModel V env) (d : BlockData V) (lps : List Name)
    (c j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧
  cA.1.levelParams = lps ∧
  BlockCtorDataI m (d.memberName c) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp d.large
    (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.fvsPF c j) (d.xFvsF c j) (d.xrestF c j)

/-- **A block component's constructor's READING facts** —
`BlockCtorFacts` without the storage: what the constructor's stored type
reads as at the model, whether or not the constructor is stored yet (the
formers' stage reads the constructors before they are consed). -/
@[expose] def BlockCtorRead {env : Env} (m : EnvModel V env) (d : BlockData V) (lps : List Name)
    (c j : Nat) (cA : ConstantVal × Nat) : Prop :=
  BlockCtorDataI m (d.memberName c) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp d.large
    (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.fvsPF c j) (d.xFvsF c j) (d.xrestF c j)

/-! ## The constructors' fields WITH HOLES (lane HOLE2)

Charter item 2: a constructor's fields are read with HOLES at the
block's members — the member-abstracted constructor type, instantiated
at the parameters, then one variable per member (member `m` at
`nP + m`), then the earlier fields (the layout `nestPos` walks,
`Kernel/Inductives/Positivity.lean`).  The datum carries them as a
primary field (`absFF`): the walked term's reading, chosen once
(`BlockAbsRead`, `Model/Inductives/BlockAbsRead.lean`).  No field is
classified: every fact about their shape is the stored field shape
facts' (`StoredFieldShapes`). -/

namespace BlockData

variable (d : BlockData V)

/-- Component `c`'s constructor `j`'s fields with holes (the datum's
own, `absFF`). -/
@[expose] def absF (ψ : Name → Nat) (c j : Nat) : List AnnotTerm := d.absFF c j ψ

/-- Component `c`'s constructor `j`'s result index readings, below the
holes and the fields. -/
@[expose] def absE (ψ : Name → Nat) (c j : Nat) : List AnnotTerm :=
  ((d.Ess c ψ).getD j []).map (·.liftN d.k ((d.Fss c ψ).getD j []).length)

end BlockData

/-! ## The block's LFP CLAUSE (lane ENVLFP)

The part of the representation the environment invariant records
(`Model/Annot/BlockLfp.lean`): the datum is `d`'s own fields — the
operator IS `d.Φ` — with the constructors' fields read with holes
(lane HOLE2).  The clause is produced in `BlockLfpHoles.lean`. -/

/-- **A block's lfp datum**: its fields are `d`'s. -/
@[expose] def BlockData.toLfp (d : BlockData V) : LfpDatum V where
  names := d.memberNames
  k := d.k
  N := d.N
  w := d.w
  params := d.params
  pars := fun m ψ => ((d.ppsM m ψ).take d.nP).map (·.2.2)
  ids := fun c ψ => d.IdsM c ψ
  u := fun c ψ => d.uM c ψ
  Φ := d.Φ
  inj := d.inj
  nctors := fun c => (d.ctorsM c).length
  ctorName := fun c j => ((d.ctorsM c).getD j default).1.name
  fields := d.absF
  resIdx := d.absE

/-! ## The clause -/

/-- **The representation of the block whose members are `names`** at
the block data `d` (see the module docstring). -/
structure BlockModelAt (m : EnvModel V env) (names : List Name) (d : BlockData V) : Prop where
  /-- the data's members are the block's -/
  names : d.memberNames = names
  /-- at every parameter frame every component's index telescope is graded -/
  idxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ)
  /-- **`Φ` is a monotone tuple functor** on the tuple space over the
  components' index-tuple sets, mapping it into itself, with a closed
  tuple ((W) at tuples) -/
  functor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    MapsTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    ∃ L, IsClosedTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) L
  /-- **the container functor**: component `c`'s fibre at `(X, t)` is
  the set of injections of the spines fitting one of component `c`'s
  constructors' fields WITH HOLES at the hole frame of `X` (charter
  item 2) -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
    ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
      x ∈ˢ app (d.Φ ψ ρp X c) t ↔ ∃ j fs, d.toLfp.HFits ψ ρp X t c j fs ∧ x = d.inj ψ c j fs
  /-- **the hole fit grows with the tuple** (positivity's, at the fit) -/
  fitsMono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X Y, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) Y →
    TupleLe d.N (d.idx ψ ρp) X Y → ∀ c, c < d.N → ∀ (t : V) (j : Nat) (fs : List V),
      d.toLfp.HFits ψ ρp X t c j fs → d.toLfp.HFits ψ ρp Y t c j fs
  /-- **the leaf**: a MEMBER's former at fitting parameters and its own
  indices is the least pre-fixed TUPLE's component at the index tuple -/
  leaf : ∀ mm, mm < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) (d.IdsM mm ψ) is →
    (as ++ is).foldl app (interp V ρ (m.acval (d.memberName mm) ψ))
      = app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ)) mm)
          (d.tup ψ mm is)
  /-- **the constructors**: component `c`'s constructor `j` at fitting
  parameters and fields is its injection -/
  ctor : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V),
      SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) ((d.Fss c ψ).getD j []) fs →
      (as ++ fs).foldl app (interp V ρ (m.acval cA.1.name ψ)) = d.inj ψ c j fs
  /-- **the constructors' RESULT index fit**: at a fitting parameter
  frame, a field spine fitting the constructor's own field domains
  carries the constructor's result index readings into the COMPONENT's
  own index telescope.  This is a consequence of the constructor's
  TYPING — its type ends in `T p⃗ e⃗`, inferred at the opened
  telescope, so the arguments `e⃗` were certified against the
  member's index binders — and it is `idxFit` at the RESULT rather
  than at a recursive field; both are `BlockModelAt.leaf`'s second
  hypothesis, at the two positions a fibre reads. -/
  resIdxFit : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
    ∀ fs : List V, SpineFit ρp ((d.Fss c ψ).getD j []) fs →
    SpineFit ρp (d.IdsM c ψ) (((d.Ess c ψ).getD j []).map (interp V (consList fs ρp)))
  /-- **the carrier's fit is the STORED fit**: at the least tuple, a
  spine hole-fits a constructor exactly when it fits the constructor's
  stored field readings and its result index readings are the index
  tuple's components (the override law: a field with holes read where
  every hole holds its member's carrier is the stored field) -/
  carrier : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ c, c < d.N → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ (j : Nat) (fs : List V),
      d.toLfp.HFits ψ ρp (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) t c j fs ↔
        d.StoredFit ψ ρp t c j fs
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, d.w ψ = 0 → ∀ c j fs, d.inj ψ c j fs = pt
  /-- at a `Type`-valued block a component's injections are injective
  across its constructors and spines of the constructors' lengths -/
  mkInj : ∀ ψ : Name → Nat, d.w ψ ≠ 0 → ∀ c, c < d.N → ∀ j fs j' fs',
    j < (d.ctorsM c).length → j' < (d.ctorsM c).length →
    fs.length = ((d.Fss c ψ).getD j []).length → fs'.length = ((d.Fss c ψ).getD j' []).length →
    d.inj ψ c j fs = d.inj ψ c j' fs' → j = j' ∧ fs = fs'

/-! ## Derived laws -/

/-- A fitting parameter spine satisfies the parameter telescope. -/
theorem BlockData.satOfSpine (d : BlockData V) {ψ : Name → Nat} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (d.params ψ) as) : Sat V (d.params ψ).reverse (consList as ρ) := by
  have := ConLeche.Model.sat_of_spineFit (Sat_nil V ρ) hsp
  simpa using this

end ConLeche.Model
