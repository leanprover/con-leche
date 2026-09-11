module

public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Semantics.Tower.FixFamI
public section

/-!
# The representation clause of the environment invariant (task #280)

Every stored inductive type **has a representation as the least fixed
point of a container functor spelled from its stored constructor
types** — the one fact the environment invariant (`EnvModelM`,
`ConLeche/Model/Annot/EnvModelM.lean`) records about an inductive
beyond the typing of its constants.  Nothing is stored at run time;
the clause lives in the proof tier only, and the nested route
(task #279) reads a container's representation here when a later
block nests through it.

**The datum** (`IndRepData`) is the fixpoint route's own spelling of a
block (`ConLeche/Semantics/Tower/FixLeafI.lean`): the parameter and
index telescope `pps`, the index-tuple sort `u`, and per constructor
the readings of its stored type — the field data `dsF`, the result's
index readings `esF`, the field kinds `ksF` with the recursive
fields' index expressions `eissF` and reflexive telescopes `tssF`
(`FixCtorDataI`) — from which the X-chains `chainsXI` of the family
functor are spelled.  The functor itself is a set `Φ` and the
constructor injections a family `inj`; both are abstract so that a
pinned block whose elements are not tagged towers (`Nat` as ω, whose
successor is the von Neumann one) is represented on the nose, not up
to an isomorphism.

**The clause** (`IndRep`), for a stored inductive `T` with its
recursor `T.rec`:

* the stored types read as the spelling says (`former`, `ctors`), and
  the recursor's rules list the constructors in order (`rules`,
  `mI`, `rP`);
* at every parameter frame the X-chains are graded (`chains`) and
  `Φ` is a monotone functor on families over the index-tuple set with
  a closed member (`functor`) whose fibre at `(X, t)` consists
  exactly of the injections `inj j fs` of the field spines fitting
  constructor `j`'s X-chain at `(X, t)` (`fibre`) — the container
  functor, with the injections injective (`mkInj`);
* **the leaf**: the type former applied to fitting parameters and
  indices is the fibre of the least fixed point of `Φ` at the index
  tuple (`leaf`) — form (L)/(M0) of the nested design;
* **the constructors**: constructor `j` applied to fitting
  parameters and fields is `inj j fs` (`ctor`) — the fixed point's own
  injection, so that a later identification of a copy with the
  container needs no transport.

`IndReps` is the clause over the whole store, keyed on the pair
(`T` stored as `indInfo`, `T.rec` stored as `recInfo`): a block's
representation is claimed once its recursor is stored, which is the
last constant of every inductive install.  `Quot` is stored as an
inductive record for the checker's uniformity but has no `Quot.rec`,
so nothing is claimed of it — as official's `Quot` is not an
inductive type (`quotInfo`), `is_nested_inductive_app` never fires on
it, and no block nests through it.

**Transitional exemption.**  A block installed by the modeled route
(`Kernel/Inductives/Modeled.lean`: today's mutual and nested blocks)
has no representation here; what the route establishes is that the
block's leaves are its stored `_model`'s (`ModeledLeaf`), and the
clause is the disjunction.  The right disjunct is deleted with the
route (tasks #278, #279).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The representation datum of a block** (see the module
docstring): the fixpoint route's spelling of the block, the semantic
functor `Φ` (per level assignment and parameter frame) and the
constructor injections `inj` (per level assignment and constructor
position). -/
structure IndRepData (V : Type w) where
  /-- the parameter count -/
  nP : Nat
  /-- the index count -/
  nIdx : Nat
  /-- the result sort (the stored type's) -/
  resSort : Level
  /-- `resSort` is provably zero -/
  isProp : Bool
  /-- the eliminator is large -/
  large : Bool
  /-- the pre-block environment (a ghost witness: the ordinary field
  domains resolve in it, so they mention neither the former nor a
  constructor) -/
  env₀ : Env
  /-- the constructors, in order, with their field counts -/
  ctorsA : List (ConstantVal × Nat)
  /-- per constructor: the residual's index arguments -/
  idxF : Nat → List Expr
  /-- per constructor: the type reading's binder data -/
  dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per constructor: the result's index readings -/
  esF : Nat → (Name → Nat) → List AnnotTerm
  /-- per constructor: the field sources -/
  srcsF : Nat → List (Option Nat)
  /-- per constructor: the field kinds -/
  ksF : Nat → List RecFieldKind
  /-- per constructor: the opened parameter variables -/
  fvsPF : Nat → List Expr
  /-- per constructor: the opened field variables -/
  xFvsF : Nat → List Expr
  /-- per constructor: the opened residual -/
  xrestF : Nat → Expr
  /-- per constructor: the recursive fields' index expressions -/
  eissF : Nat → (Name → Nat) → List (List AnnotTerm)
  /-- per constructor: the reflexive fields' telescopes -/
  tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))
  /-- the former's parameter-and-index telescope reading -/
  pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- the index-tuple sort -/
  u : (Name → Nat) → Nat
  /-- the family functor, at a level assignment and a parameter frame -/
  Φ : (Name → Nat) → (Nat → V) → V
  /-- the constructor injections: constructor `j` at a field spine -/
  inj : (Name → Nat) → Nat → List V → V

namespace IndRepData

variable (d : IndRepData V)

/-- The result sort's value. -/
@[expose] def w (ψ : Name → Nat) : Nat := d.resSort.eval ψ

/-- The parameter telescope. -/
@[expose] def params (ψ : Name → Nat) : List AnnotTerm := ((d.pps ψ).take d.nP).map (·.2.2)

/-- The index telescope, at the parameter frame. -/
@[expose] def Ids (ψ : Name → Nat) : List AnnotTerm := ((d.pps ψ).drop d.nP).map (·.2.2)

/-- The constructor data list. -/
@[expose] def cds (ψ : Name → Nat) : List CtorDatumR :=
  fixCtorDataList d.dsF d.esF d.ksF d.eissF d.tssF ψ d.ctorsA 0

/-- The recursive flags. -/
@[expose] def rss : List (List Bool) := rssOfK d.ksF d.ctorsA.length

/-- The reflexive telescopes. -/
@[expose] def tlss (ψ : Name → Nat) : List (List (List (Nat × Nat × AnnotTerm))) := tlssOfR (d.cds ψ)

/-- The recursive fields' index expressions. -/
@[expose] def Eiss (ψ : Name → Nat) : List (List (List AnnotTerm)) := eissOfR (d.cds ψ)

/-- The field domains (the real readings: a recursive entry is the
former's leaf applied, which the X-chain ignores in favour of the
slot). -/
@[expose] def Fss (ψ : Name → Nat) : List (List AnnotTerm) := fssOfR d.nP (d.cds ψ)

/-- The results' index readings. -/
@[expose] def Ess (ψ : Name → Nat) : List (List AnnotTerm) := essOfR (d.cds ψ)

/-- The index-tuple set at a parameter frame. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : V := idxSet (d.u ψ) ρp (d.Ids ψ)

/-- **A field spine fits constructor `j` at the functor frame `(ρp, X, t)`**:
it has the constructor's field count, it fits the X-chain (an ordinary
field's domain, a recursive field's slot `X ⟨e⃗⟩` under its telescope),
and the constructor's index expressions at it are the components of
the tuple `t` — exactly the elimination shape of the fixpoint route's
fibre (`fixStepI_elim`). -/
@[expose] def ChainFit (ψ : Name → Nat) (ρp : Nat → V) (X t : V) (j : Nat) (fs : List V) : Prop :=
  fs.length = ((d.Fss ψ).getD j []).length ∧
  SpineFit (cons t (cons X ρp))
    (chainXIGo (d.u ψ) (d.Ids ψ) (d.rss.getD j []) ((d.tlss ψ).getD j []) ((d.Eiss ψ).getD j [])
      ((d.Fss ψ).getD j []) 0) fs ∧
  EqAll (consList fs (cons t (cons X ρp)))
    (eqsXI (d.Ids ψ).length ((d.Fss ψ).getD j []).length ((d.Ess ψ).getD j []))

end IndRepData

/-- **The representation of a stored inductive `T`** with recursor
`T.rec = .recInfo cvR mI rP rules`, at the datum `d` (see the module
docstring). -/
structure IndRep (m : EnvModel V env) (T : Name) (cvT cvR : ConstantVal) (mI rP : Nat)
    (rules : List RecRule) (d : IndRepData V) : Prop where
  /-- the stored type is the telescope over the parameters and indices
  ending in the result sort -/
  strip : ∃ bs, cvT.type.stripPis (d.nP + d.nIdx) = some (bs, .sort d.resSort)
  /-- the `Prop` bit is the result sort's -/
  isProp : d.isProp = (Level.isEquiv d.resSort .zero == some true)
  /-- the recursor's major position: one motive, one minor per
  constructor, the indices -/
  mI : mI = d.nP + 1 + d.ctorsA.length + d.nIdx
  /-- the recursor's rule prefix -/
  rP : rP = d.nP + 1 + d.ctorsA.length
  /-- the recursor's rules are the constructors, in order -/
  rules : rules.map (·.ctor) = d.ctorsA.map (·.1.name)
  /-- the former's type reads as the telescope -/
  former : FormerData m cvT (d.nP + d.nIdx) d.resSort d.pps
  /-- every constructor is stored and its type reads as the datum says
  (`FixCtorDataI`: the field kinds, the recursive slots, the index
  readings) -/
  ctors : ∀ j cA, d.ctorsA[j]? = some cA →
    FixCtorFactsAt m d.env₀ T cvT.levelParams d.nP d.nIdx d.resSort d.isProp d.large d.idxF d.dsF
      d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF d.tssF j cA
  /-- the residuals' index arguments resolve -/
  idxRes : ∀ j cA, d.ctorsA[j]? = some cA → ∀ e ∈ d.idxF j, e.constsResolve env = true
  /-- the index-tuple sort reads only the block's level parameters -/
  uParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvT.levelParams, ψ₁ q = ψ₂ q) → d.u ψ₁ = d.u ψ₂
  /-- a constructor's parameter telescope is the former's, as a frame -/
  paramsIff : ∀ j cA, d.ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.dsF j ψ).take d.nP).map (·.2.2)).reverse ρ
  /-- at every parameter frame the X-chains are graded -/
  chains : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    XChainsOk (d.u ψ) (d.w ψ) ρp (d.Ids ψ) d.rss (d.tlss ψ) (d.Eiss ψ) (d.Fss ψ) (d.Ess ψ)
  /-- `Φ` is a monotone functor on the family space over the index-tuple
  set, mapping it into itself, with a closed member -/
  functor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    d.Φ ψ ρp ∈ˢ lfpFamFunSpace V (d.u ψ) (d.w ψ) (d.idx ψ ρp) ∧
    MonoFam (d.w ψ) (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    MapsFam (d.w ψ) (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    ∃ L, IsClosedFam (d.w ψ) (d.idx ψ ρp) (d.Φ ψ ρp) L
  /-- **the container functor**: the fibre of `Φ X` at a tuple `t` is
  the set of injections of the field spines fitting some constructor
  at `(X, t)` -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, X ∈ˢ famSpace (d.w ψ) (d.idx ψ ρp) → ∀ t, t ∈ˢ d.idx ψ ρp → ∀ x,
      x ∈ˢ app (app (d.Φ ψ ρp) X) t ↔
        ∃ j fs, j < d.ctorsA.length ∧ d.ChainFit ψ ρp X t j fs ∧ x = d.inj ψ j fs
  /-- **the leaf**: the former at fitting parameters and indices is the
  least fixed point's fibre at the index tuple -/
  leaf : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) (d.Ids ψ) is →
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      = app (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) (tupW (d.u ψ) is)
  /-- **the constructors**: constructor `j` at fitting parameters and
  fields is its injection -/
  ctor : ∀ j cA, d.ctorsA[j]? = some cA →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V),
      SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) ((d.Fss ψ).getD j []) fs →
      (as ++ fs).foldl app (interp V ρ (m.acval cA.1.name ψ)) = d.inj ψ j fs
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, d.w ψ = 0 → ∀ j fs, d.inj ψ j fs = pt
  /-- at a `Type`-valued block the injections are injective across
  constructors and spines of the constructors' lengths -/
  mkInj : ∀ ψ : Name → Nat, d.w ψ ≠ 0 → ∀ j fs j' fs',
    j < d.ctorsA.length → j' < d.ctorsA.length →
    fs.length = ((d.Fss ψ).getD j []).length → fs'.length = ((d.Fss ψ).getD j' []).length →
    d.inj ψ j fs = d.inj ψ j' fs' → j = j' ∧ fs = fs'

/-- **A modeled block's leaf is its stored model's** — what the
modeled route establishes (`BlockAcvalInstalled`); the transitional
exemption of `IndReps`, deleted with the route. -/
@[expose] def ModeledLeaf (m : EnvModel V env) (T : Name) : Prop :=
  (env.find? (T.str "_model")).isSome = true ∧
  ∀ ψ : Name → Nat, m.acval (T.str "_model") ψ = m.acval T ψ

/-- **The representation clause**: every stored inductive whose recursor
is stored has a representation, or is a modeled block. -/
@[expose] def IndReps (m : EnvModel V env) : Prop :=
  ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps) (cvR : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? T = some (.indInfo cvT caps) →
    env.find? (T.str "rec") = some (.recInfo cvR mI rP rules) →
    (∃ d : IndRepData V, IndRep m T cvT cvR mI rP rules d) ∨ ModeledLeaf m T

end ConLeche.Model
