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

**The clause** (`IndRep`), for a stored inductive `T` — the member
`mm` of its block — with its recursor `T.rec`:

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

**The member view** (task #278 M2.6).  A block has `k` members
(`nIdxs`, `memberNames`, the per-constructor member table `mems` and
the per-field target table `tgts`), and the clause is stated for ONE
of them: the stored recursor's arithmetic is `mI = nP + k + n +
nIdx_mm` over the whole block's `n` constructors, its rules are member
`mm`'s own (`memberCtors`), its former's telescope is member `mm`'s
(`ppsM mm`), and its leaf sends member `mm`'s own index spine to the
CONTAINER's index tuple (`tup`, over the container's index telescope
`IdsC`).  A single family is the instance `k = 1`, `mm = 0`, every
`mems`/`tgts` entry `0`, `tup = tupW u`, `IdsC` the former's own
index telescope — which is what the fixpoint route
(`Model/Inductives/FixRep.lean`) and the pinned blocks supply.

`IndReps` is the clause over the whole store, keyed on the stored
RECURSOR `T.rec` (which then names its stored former `T`): a block's
representation is claimed once its recursor is stored, which is the
last constant of every inductive install.  `Quot` is stored as an
inductive record for the checker's uniformity but has no `Quot.rec`,
so nothing is claimed of it — as official's `Quot` is not an
inductive type (`quotInfo`), `is_nested_inductive_app` never fires on
it, and no block nests through it.

**Transitional exemption.**  A block installed by the modeled route
(`Kernel/Inductives/Modeled.lean`: today's mutual and nested blocks)
has no representation here; what the route establishes is that every
member's leaf — the recursor's in particular — is its stored
`_model`'s (`ModeledLeaf`), and the clause is the disjunction.  The
right disjunct is deleted with the route (tasks #278, #279); until
then no consumer may extract `IndRep` for an arbitrary block.
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
  /-- per constructor: the result's index readings AT THE CONTAINER (the
  stored type's `esF` at a single family; at a mutual block the tagged
  singleton `[⟨inj m ⟨e⃗⟩⟩]` over the tag telescope, task #278) -/
  essC : Nat → (Name → Nat) → List AnnotTerm
  /-- per constructor: the recursive fields' index expressions AT THE
  CONTAINER (`eissF` at a single family; the tagged singletons at a
  mutual block) -/
  eissC : Nat → (Name → Nat) → List (List AnnotTerm)
  /-- the number of members of the block (`1` at a single family) -/
  k : Nat
  /-- per member: its index count (`nIdx` is the CONTAINER's) -/
  nIdxs : List Nat
  /-- the members' names, by member position -/
  memberNames : List Name
  /-- per constructor: the member it belongs to -/
  mems : Nat → Nat
  /-- per constructor and field: the member the field targets -/
  tgts : Nat → Nat → Nat
  /-- per member: its parameter-and-index telescope reading -/
  ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per member: its binders' universe levels (`FormerData.lvls`) -/
  lvlsM : Nat → (Name → Nat) → List Nat
  /-- the CONTAINER's index telescope (at a single family the former's
  own; at a mutual block the block-position tag's) -/
  IdsC : (Name → Nat) → List AnnotTerm
  /-- the index-tuple sort -/
  u : (Name → Nat) → Nat
  /-- member `m`'s index spine as a tuple of the CONTAINER's index set
  (at a single family `tupW u is`) -/
  tup : (Name → Nat) → Nat → List V → V
  /-- the family functor, at a level assignment and a parameter frame -/
  Φ : (Name → Nat) → (Nat → V) → V
  /-- the constructor injections: constructor `j` at a field spine -/
  inj : (Name → Nat) → Nat → List V → V

namespace IndRepData

variable (d : IndRepData V)

/-- The result sort's value. -/
@[expose] def w (ψ : Name → Nat) : Nat := d.resSort.eval ψ

/-- Member `mm`'s name. -/
@[expose] def memberName (mm : Nat) : Name := d.memberNames.getD mm .anonymous

/-- Member `mm`'s index count. -/
@[expose] def nIdxAt (mm : Nat) : Nat := d.nIdxs.getD mm 0

/-- The parameter telescope (the block's, read off member `0`: the
members share their parameters). -/
@[expose] def params (ψ : Name → Nat) : List AnnotTerm := ((d.ppsM 0 ψ).take d.nP).map (·.2.2)

/-- Member `mm`'s own index telescope, at the parameter frame. -/
@[expose] def IdsM (mm : Nat) (ψ : Name → Nat) : List AnnotTerm :=
  ((d.ppsM mm ψ).drop d.nP).map (·.2.2)

/-- Member `mm`'s own constructors, in the block's order and paired
with nothing: the constructors `J` with `mems J = mm`. -/
@[expose] def memberCtors (mm : Nat) : List (ConstantVal × Nat) :=
  (d.ctorsA.zipIdx.filter fun x => d.mems x.2 == mm).map (·.1)

/-- The constructor data list at the CONTAINER's index readings (the
chains, `IndRep.chains`/`fibre`). -/
@[expose] def cdsC (ψ : Name → Nat) : List CtorDatumR :=
  fixCtorDataList d.dsF d.essC d.ksF d.eissC d.tssF ψ d.ctorsA 0

/-- The recursive flags. -/
@[expose] def rss : List (List Bool) := rssOfK d.ksF d.ctorsA.length

/-- The reflexive telescopes. -/
@[expose] def tlss (ψ : Name → Nat) : List (List (List (Nat × Nat × AnnotTerm))) := tlssOfR (d.cdsC ψ)

/-- The recursive fields' index expressions. -/
@[expose] def Eiss (ψ : Name → Nat) : List (List (List AnnotTerm)) := eissOfR (d.cdsC ψ)

/-- The field domains (the real readings: a recursive entry is the
former's leaf applied, which the X-chain ignores in favour of the
slot). -/
@[expose] def Fss (ψ : Name → Nat) : List (List AnnotTerm) := fssOfR d.nP (d.cdsC ψ)

/-- The results' index readings. -/
@[expose] def Ess (ψ : Name → Nat) : List (List AnnotTerm) := essOfR (d.cdsC ψ)

/-- The index-tuple set at a parameter frame. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : V := idxSet (d.u ψ) ρp (d.IdsC ψ)

/-- **A field spine fits constructor `j` at the functor frame `(ρp, X, t)`**:
it has the constructor's field count, it fits the X-chain (an ordinary
field's domain, a recursive field's slot `X ⟨e⃗⟩` under its telescope),
and the constructor's index expressions at it are the components of
the tuple `t` — exactly the elimination shape of the fixpoint route's
fibre (`fixStepI_elim`). -/
@[expose] def ChainFit (ψ : Name → Nat) (ρp : Nat → V) (X t : V) (j : Nat) (fs : List V) : Prop :=
  fs.length = ((d.Fss ψ).getD j []).length ∧
  SpineFit (cons t (cons X ρp))
    (chainXIGo (d.u ψ) (d.IdsC ψ) (d.rss.getD j []) ((d.tlss ψ).getD j []) ((d.Eiss ψ).getD j [])
      ((d.Fss ψ).getD j []) 0) fs ∧
  EqAll (consList fs (cons t (cons X ρp)))
    (eqsXI (d.IdsC ψ).length ((d.Fss ψ).getD j []).length ((d.Ess ψ).getD j []))

end IndRepData

omit [SetTheory V] in
/-- At a single-family block (every constructor at the same member)
the member's constructors are all of them. -/
theorem IndRepData.memberCtors_of_all {d : IndRepData V} {mm : Nat} (h : ∀ j, d.mems j = mm) :
    d.memberCtors mm = d.ctorsA := by
  unfold IndRepData.memberCtors
  rw [List.filter_eq_self.mpr (fun x _ => by rw [h]; exact beq_self_eq_true mm)]
  exact List.zipIdx_map_fst 0 d.ctorsA

/-- **The chains' grading** at a parameter frame: the index telescope
graded, the X-chains graded at every family and tuple, the recursive
slots fitting there — `XChainsOk` without its closure witness (the
closed member of the representing functor is `IndRep.functor`'s). -/
structure ChainsOk (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Fss Ess : List (List AnnotTerm)) : Prop where
  hI : IdxOk u ρp Ids
  hok : FixChainsOkI u w ρp Ids Ids.length rss tlss Eiss Fss Ess
  hfit : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
    ∀ j, j < Fss.length →
      SlotsFitX u w ρp Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) X t 0 [] (Fss.getD j [])

theorem xChainsOk_toChainsOk {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) : ChainsOk u w ρp Ids rss tlss Eiss Fss Ess :=
  ⟨h.hI, h.hok, h.hfit⟩

/-- **The representation of a stored inductive `T`**, the member `mm`
of its block, with recursor `T.rec = .recInfo cvR mI rP rules`, at the
datum `d` (see the module docstring).  A single-family block is the
instance `k = 1`, `mm = 0`. -/
structure IndRep (m : EnvModel V env) (T : Name) (cvT cvR : ConstantVal) (mI rP : Nat)
    (rules : List RecRule) (d : IndRepData V) (mm : Nat) : Prop where
  /-- `T` is member `mm` of the block -/
  member : d.memberName mm = T
  /-- the stored type is the telescope over the parameters and the
  member's own indices, ending in the result sort -/
  strip : ∃ bs, cvT.type.stripPis (d.nP + d.nIdxAt mm) = some (bs, .sort d.resSort)
  /-- the `Prop` bit is the result sort's -/
  isProp : d.isProp = (Level.isEquiv d.resSort .zero == some true)
  /-- the recursor's major position: one motive per member, one minor
  per constructor OF THE BLOCK, the member's own indices -/
  mI : mI = d.nP + d.k + d.ctorsA.length + d.nIdxAt mm
  /-- the recursor's rule prefix -/
  rP : rP = d.nP + d.k + d.ctorsA.length
  /-- the recursor's rules, when it carries any, are the MEMBER's
  constructors in order (a rule-less entry — a mutual block's recursor
  PROVISIONED before its rules are checked, task #278 — claims the
  representation with this clause vacuous) -/
  rules : rules ≠ [] → rules.map (·.ctor) = (d.memberCtors mm).map (·.1.name)
  /-- the former's type reads as the member's telescope -/
  former : FormerData m cvT (d.nP + d.nIdxAt mm) d.resSort (d.ppsM mm) (d.lvlsM mm)
  /-- every constructor OF THE BLOCK is stored and its type reads as
  the datum says (`FixCtorDataI` at the constructor's own member, with
  the per-field target member: the field kinds, the recursive slots,
  the index readings) -/
  ctors : ∀ j cA, d.ctorsA[j]? = some cA →
    FixCtorFactsAt m d.env₀ (d.memberName (d.mems j)) cvT.levelParams d.nP (d.nIdxAt (d.mems j))
      d.resSort d.isProp d.large d.idxF d.dsF
      d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF d.tssF j cA
      (fun i => d.memberName (d.tgts j i)) (fun i => d.nIdxAt (d.tgts j i))
  /-- every constructor's own member and every field's target member
  is a stored inductive — what licenses the constructors' readings to
  cross a fresh cons (`IndRep.cross`); at a single family both are the
  block's own former -/
  memsFound : ∀ j, j < d.ctorsA.length →
    (∃ (cv : ConstantVal) (caps : IndCaps),
      env.find? (d.memberName (d.mems j)) = some (.indInfo cv caps)) ∧
    ∀ i, ∃ (cv : ConstantVal) (caps : IndCaps),
      env.find? (d.memberName (d.tgts j i)) = some (.indInfo cv caps)
  /-- the residuals' index arguments resolve -/
  idxRes : ∀ j cA, d.ctorsA[j]? = some cA → ∀ e ∈ d.idxF j, e.constsResolve env = true
  /-- the index-tuple sort reads only the block's level parameters -/
  uParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvT.levelParams, ψ₁ q = ψ₂ q) → d.u ψ₁ = d.u ψ₂
  /-- a constructor's parameter telescope is the former's, as a frame -/
  paramsIff : ∀ j cA, d.ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.dsF j ψ).take d.nP).map (·.2.2)).reverse ρ
  /-- at every parameter frame the X-chains are graded -/
  chains : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ChainsOk (d.u ψ) (d.w ψ) ρp (d.IdsC ψ) d.rss (d.tlss ψ) (d.Eiss ψ) (d.Fss ψ) (d.Ess ψ)
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
  /-- **the leaf**: the member's former at fitting parameters and its
  OWN indices is the least fixed point's fibre at the container's index
  tuple of that spine (`tup`) -/
  leaf : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) (d.IdsM mm ψ) is →
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      = app (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) (d.tup ψ mm is)
  /-- the member's own index spine, as the container's index tuple,
  lands in the container's index set -/
  tupMem : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ is, SpineFit ρp (d.IdsM mm ψ) is → d.tup ψ mm is ∈ˢ d.idx ψ ρp
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

/-- **A modeled constant's leaf is its stored model's** — what the
modeled route establishes for every block member
(`BlockAcvalInstalled`, `BlockInstalledTT`); the transitional exemption
of `IndReps`, keyed on the block's RECURSOR (the constant the clause is
keyed on, whatever block it came with), deleted with the route. -/
@[expose] def ModeledLeaf (m : EnvModel V env) (T : Name) : Prop :=
  (env.find? (T.str "_model")).isSome = true ∧
  ∀ ψ : Name → Nat, m.acval (T.str "_model") ψ = m.acval T ψ

/-- **The representation clause**: every stored recursor `T.rec` is the
recursor of a stored inductive `T` that has a representation — or is a
modeled block's.  Keyed on the RECURSOR, the last constant of every
inductive install, so that a fresh type former owes nothing and a
fresh recursor claims its block. -/
@[expose] def IndReps (m : EnvModel V env) : Prop :=
  ∀ (n : Name) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env.find? n = some (.recInfo cvR mI rP rules) →
    ∀ T : Name, n = T.str "rec" →
    (∃ (cvT : ConstantVal) (caps : IndCaps) (d : IndRepData V) (mm : Nat),
      env.find? T = some (.indInfo cvT caps) ∧ IndRep m T cvT cvR mI rP rules d mm) ∨
    -- TRANSITIONAL: the right disjunct is the modeled route's fact and is
    -- deleted with that route (tasks #278 mutual, #279 nested); until it
    -- is gone no consumer may extract `IndRep` for an arbitrary block
    ModeledLeaf m n

/-- **The head's obligation for the clause** at a fresh cons: a fresh
recursor `T.rec` claims its block's representation, or is modeled;
every other head owes nothing (`IndRepsHead.ofNtc`). -/
@[expose] def IndRepsHead (env : Env) (c₀ : ConstantInfo)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩) : Prop :=
  ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
    ∀ T : Name, cvR.name = T.str "rec" →
    (∃ (cvT : ConstantVal) (caps : IndCaps) (d : IndRepData V) (mm : Nat),
      Env.find? ⟨c₀ :: env.consts⟩ T = some (.indInfo cvT caps) ∧
      IndRep m₂ T cvT cvR mI rP rules d mm) ∨
    ModeledLeaf m₂ cvR.name

/-- A head that is no recursor owes nothing. -/
theorem IndRepsHead.ofNtc {c₀ : ConstantInfo} (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) :
    IndRepsHead env c₀ m₂ :=
  fun cv mI rP rules h => absurd h (hnotrec cv mI rP rules)

end ConLeche.Model
