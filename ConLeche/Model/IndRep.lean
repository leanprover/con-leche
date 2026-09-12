module

public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.RecSpell
public import ConLeche.Semantics.Tower.FixFamI
import ConLeche.Kernel.Inductives.StructParts
public import ConLeche.Kernel.Inductives.NestedParts
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

**The recursor's shape** (task #279 M-A′).  The only spellable handle a
later block has on a stored container's elements is the container's
RECURSOR (values are `AnnotTerm` leaves; the datum's `Φ`/`inj` are
abstract sets), so the clause also records, at a block with
parameters, that the stored recursor's type reads to the generated
`k`-motive tower (`recRead`) and that EVERY member's recursor, once the
block's recursors are stored, is stored and reads as the datum says of
it — its type as the tower at that member, its rules as the member's
constructors with their generated cores (`rulesRead`, `RecReadAt`; the
nested route's fold from a container's recursor needs the whole family
read off one datum) — all over the datum's constructor
data, in the RECURSOR's view of the block: the real members followed
by the block's own COPY members (a nested block's copies of containers
at pins, `kReal ≤ t < k`), every member's family spelled at its pins
(`pinsAV`; a real member's are the parameter variables), the copies'
constructors after the real ones (`ctorsC`), and the field kinds with
their targets among all members (`ksR`, `tgtsR`, `eissR`, `tssR`).  The
FAMILY view below — the chains, the functor, the fibre, the leaf, the
constructors — is over the real members and their constructors alone;
at a block without copies the two views coincide and every field is
its default.

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
  /-- the elimination level parameter's name (`.anonymous` at a small
  eliminator) -/
  elim : Name
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
  /-- the number of REAL members (stored formers): members `≥ kReal`
  are copies (task #279) -/
  kReal : Nat := k
  /-- the copies' constructors, in the recursor's minor order after
  the real ones: name, level parameters, the container constructor's
  type INSTANTIATED at the pins under the block's parameter binders,
  and the field count -/
  ctorsC : List (ConstantVal × Nat) := []
  /-- per member: its pins' readings at the parameter frame (a real
  member's: the parameter variables) -/
  pinsAV : Nat → (Name → Nat) → List AnnotTerm := fun _ _ => paramBvarsAt nP nP
  /-- per member: its container's parameter count (a real member's:
  the block's) -/
  nPM : Nat → Nat := fun _ => nP
  /-- per member: its recursor's name (`T_t.rec`; a copy's is
  `T₁.rec_k`) -/
  recNames : Nat → Name := fun t => (memberNames.getD t .anonymous).str "rec"
  /-- per constructor (real and copy): the field kinds in the RECURSOR's
  view — a field into a copy is recursive or reflexive there -/
  ksR : Nat → List RecFieldKind := ksF
  /-- per constructor and field: the target member in the recursor's
  view -/
  tgtsR : Nat → Nat → Nat := tgts
  /-- per constructor: the recursive fields' index readings in the
  recursor's view -/
  eissR : Nat → (Name → Nat) → List (List AnnotTerm) := eissF
  /-- per constructor: the reflexive fields' telescopes in the
  recursor's view -/
  tssR : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := tssF

namespace IndRepData

variable (d : IndRepData V)

/-- The result sort's value. -/
@[expose] def w (ψ : Name → Nat) : Nat := d.resSort.eval ψ

/-- The elimination level. -/
@[expose] def elimL : Level := ConLeche.structElimLevel d.elim d.large

/-- The elimination level's bit. -/
@[expose] def bb (ψ : Name → Nat) : Nat := pwBit ψ (Level.zeronessOf d.elimL)

/-- All constructors of the recursor's block: the real ones, then the
copies'. -/
@[expose] def ctorsAll : List (ConstantVal × Nat) := d.ctorsA ++ d.ctorsC

/-- The number of constructors of the recursor's block. -/
@[expose] def nAll : Nat := d.ctorsA.length + d.ctorsC.length

/-- The members' leaves at a model, by member position. -/
@[expose] def Ls (m : EnvModel V env) (ψ : Name → Nat) : List AnnotTerm :=
  (List.range d.k).map fun t => m.acval (d.memberNames.getD t .anonymous) ψ

/-- The members' index binder data. -/
@[expose] def ipss (ψ : Name → Nat) : List (List (Nat × Nat × AnnotTerm)) :=
  (List.range d.k).map fun t => (d.ppsM t ψ).drop d.nP

/-- The constructor data in the recursor's view (all constructors, the
recursor's kinds and index readings). -/
@[expose] def cdsR (ψ : Name → Nat) : List CtorDatumR :=
  fixCtorDataList d.dsF d.esF d.ksR d.eissR d.tssR ψ d.ctorsAll 0

/-- The members' pins at an assignment. -/
@[expose] def pinsOf (ψ : Name → Nat) : Nat → List AnnotTerm := fun t => d.pinsAV t ψ

/-- **Member `mm`'s recursor type's binder data**: the `k`-motive tower
at the members' pins (`recDataAVP`). -/
@[expose] def recDataAV (m : EnvModel V env) (ψ : Name → Nat) (mm : Nat) :
    List (Nat × Nat × AnnotTerm) :=
  recDataAVP m ψ (d.Ls m ψ) (d.pinsOf ψ) d.nP d.nIdxs d.elimL ((d.ppsM 0 ψ).take d.nP) (d.ipss ψ)
    (d.cdsR ψ) d.mems d.tgtsR mm

/-- **Constructor `j`'s rule, as its recursor reads it**: the λ-tower
over the rule's binder data with the `k`-motive core, the inductive
hypotheses firing the target members' recursor leaves. -/
@[expose] def ruleAV (m : EnvModel V env) (ψ : Name → Nat) (j nF : Nat) : AnnotTerm :=
  mkLamsAV (ruleDataAVP m ψ (d.Ls m ψ) (d.pinsOf ψ) d.nP d.nIdxs d.elimL ((d.ppsM 0 ψ).take d.nP)
      (d.ipss ψ) (d.cdsR ψ) d.mems d.tgtsR (d.dsF j ψ))
    (mutualRuleCoreAV (d.bb ψ) (fun t => m.acval (d.recNames t) ψ) (d.tgtsR j) d.nP d.k d.nAll nF j
      (ConLeche.recIdxOf (d.ksR j)) (d.tssR j ψ) (d.eissR j ψ))

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

/-- Member `mm`'s constructors among ALL of the recursor's block (the
real ones and the copies'), in the recursor's minor order (task #279
M-B′): the constructors `J` of `ctorsAll` with `mems J = mm`. -/
@[expose] def memberCtorsAll (mm : Nat) : List (ConstantVal × Nat) :=
  (d.ctorsAll.zipIdx.filter fun x => d.mems x.2 == mm).map (·.1)

/-- The recursors' level parameters over the block's `lps`: the
elimination level first when the eliminator is large
(`MutualParts.rlps`, `nativeRecLpsOk`). -/
@[expose] def rlps (lps : List Name) : List Name := if d.large then d.elim :: lps else lps

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

/-- The recursor tower's spelling depends on the model only through the
members' and the constructors' leaves. -/
theorem recDataAV_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {mm : Nat}
    (hL : ∀ t, t < d.k → m₁.acval (d.memberName t) ψ = m₂.acval (d.memberName t) ψ)
    (hC : ∀ cd ∈ d.cdsR ψ, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    d.recDataAV m₁ ψ mm = d.recDataAV m₂ ψ mm := by
  have hLs : d.Ls m₁ ψ = d.Ls m₂ ψ := by
    unfold IndRepData.Ls
    exact List.map_congr_left fun t ht => hL t (List.mem_range.mp ht)
  unfold IndRepData.recDataAV
  rw [hLs, recDataAVP_congr hC]

/-- A rule's spelling depends on the model only through the members',
the constructors' and the recursors' leaves. -/
theorem ruleAV_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {j nF : Nat}
    (hL : ∀ t, t < d.k → m₁.acval (d.memberName t) ψ = m₂.acval (d.memberName t) ψ)
    (hC : ∀ cd ∈ d.cdsR ψ, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ)
    (hR : ∀ t, t < d.k → m₁.acval (d.recNames t) ψ = m₂.acval (d.recNames t) ψ)
    (htgt : ∀ i, d.tgtsR j i < d.k) :
    d.ruleAV m₁ ψ j nF = d.ruleAV m₂ ψ j nF := by
  have hLs : d.Ls m₁ ψ = d.Ls m₂ ψ := by
    unfold IndRepData.Ls
    exact List.map_congr_left fun t ht => hL t (List.mem_range.mp ht)
  unfold IndRepData.ruleAV
  rw [hLs, ruleDataAVP_congr hC,
    mutualRuleCoreAV_congr_Rof (Rof' := fun t => m₂.acval (d.recNames t) ψ)
      (fun i _ => hR _ (htgt i))]

end IndRepData

omit [SetTheory V] in
/-- At a single-family block (every constructor at the same member)
the member's constructors are all of them. -/
theorem IndRepData.memberCtors_of_all {d : IndRepData V} {mm : Nat} (h : ∀ j, d.mems j = mm) :
    d.memberCtors mm = d.ctorsA := by
  unfold IndRepData.memberCtors
  rw [List.filter_eq_self.mpr (fun x _ => by rw [h]; exact beq_self_eq_true mm)]
  exact List.zipIdx_map_fst 0 d.ctorsA

omit [SetTheory V] in
/-- At a single-family block without copies, the member's constructors
among all of the recursor's block are all of them. -/
theorem IndRepData.memberCtorsAll_of_all {d : IndRepData V} {mm : Nat} (h : ∀ j, d.mems j = mm)
    (hC : d.ctorsC = []) : d.memberCtorsAll mm = d.ctorsA := by
  unfold IndRepData.memberCtorsAll IndRepData.ctorsAll
  rw [hC, List.append_nil, List.filter_eq_self.mpr (fun x _ => by rw [h]; exact beq_self_eq_true mm)]
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

/-- **Member `t`'s recursor, read** (task #279 M-B′): the recursor
`recNames t` is stored with the block's level parameters and
arithmetic, its type reads as the `k`-motive tower at member `t`, its
rules list member `t`'s constructors of the recursor's block in order,
and each such constructor's rule reads as the generated core (the
inductive hypotheses firing the target members' recursor leaves); and
**the motive walk** (task #279 M-B′ step 3a): the recursor type's
body below the parameters, walked by the kernel's `containerMembersGo`
in ANY environment storing the real members, yields the real members'
names in order — the syntactic fact `containerInfo?` reads a
container's group off, stated over every environment because the
walk stops at the first minor premise for a reason that does not
depend on the environment (`Verify/Inductives/ContainerWalk.lean`). -/
@[expose] def RecReadAt (m : EnvModel V env) (d : IndRepData V) (lps : List Name) (t : Nat) :
    Prop :=
  ∃ (cvR' : ConstantVal) (mI' rP' : Nat) (rules' : List RecRule),
    env.find? (d.recNames t) = some (.recInfo cvR' mI' rP' rules') ∧
    cvR'.levelParams = d.rlps lps ∧
    mI' = d.nP + d.k + d.nAll + d.nIdxAt t ∧ rP' = d.nP + d.k + d.nAll ∧
    (∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvR'.type
      = some (mkPisAV (d.recDataAV m ψ t) (mutualConcAV d.k d.nAll (d.nIdxAt t) t))) ∧
    rules'.map (·.ctor) = (d.memberCtorsAll t).map (·.1.name) ∧
    (∀ j cA, d.ctorsAll[j]? = some cA → d.mems j = t →
      ∃ rl : RecRule, rl ∈ rules' ∧ rl.ctor = cA.1.name ∧
        ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 rl.rhs = some (d.ruleAV m ψ j cA.2)) ∧
    ∃ (bs : List (Expr × BinderMeta)) (body : Expr), cvR'.type.stripPis d.nP = some (bs, body) ∧
      ∀ env' : Env,
        (∀ t', t' < d.kReal → ∃ (cv : ConstantVal) (caps : IndCaps),
          env'.find? (d.memberName t') = some (.indInfo cv caps)) →
        containerMembersGo env' d.nP (rP' + 1) 0 body = (List.range d.kReal).map d.memberName

omit [SetTheory V] in
/-- The members' level-parameter clause transports along any
lookup-preserving map (task #279 M-B′ step 3a). -/
theorem membersLps_of_find {env env' : Env} {d : IndRepData V} {cvT : ConstantVal}
    (hF : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci → env'.find? n = some ci)
    (hfound : ∀ t, t < d.k → ∃ (cv : ConstantVal) (caps : IndCaps),
      env.find? (d.memberName t) = some (.indInfo cv caps))
    (hlps : ∀ t, t < d.k → ∀ (cv : ConstantVal) (caps : IndCaps),
      env.find? (d.memberName t) = some (.indInfo cv caps) → cv.levelParams = cvT.levelParams) :
    ∀ t, t < d.k → ∀ (cv : ConstantVal) (caps : IndCaps),
      env'.find? (d.memberName t) = some (.indInfo cv caps) → cv.levelParams = cvT.levelParams := by
  intro t ht cv caps hf
  obtain ⟨cv', caps', hf'⟩ := hfound t ht
  rw [hF _ _ hf'] at hf
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
  exact hlps t ht _ _ hf'

omit [SetTheory V] in
/-- At a one-member block whose stored former is the clause's, the
level-parameter clause is immediate. -/
theorem membersLps_one {env : Env} {d : IndRepData V} {cvT : ConstantVal} (hk : d.k = 1)
    {caps₀ : IndCaps} (hf : env.find? (d.memberName 0) = some (.indInfo cvT caps₀)) :
    ∀ t, t < d.k → ∀ (cv : ConstantVal) (caps : IndCaps),
      env.find? (d.memberName t) = some (.indInfo cv caps) → cv.levelParams = cvT.levelParams := by
  intro t ht cv caps hf'
  rw [hk] at ht
  obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf')
  rfl

omit [SetTheory V] in
/-- A one-member block's real-member names are distinct. -/
theorem memberNodup_one {d : IndRepData V} (hk : d.kReal = 1) :
    ((List.range d.kReal).map d.memberName).Nodup := by
  rw [hk, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
  exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

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
  /-- **every member's recursor reads as the generated tower and cores**
  (task #279 M-A′/M-B′; stated before the `mI`/`rP`/`rules` fields,
  whose names shadow the parameters): once THIS recursor is stored
  with its rules — the block's group store, where every member's
  recursor is stored — each member `t`'s recursor is stored and reads
  as the datum says of it (`RecReadAt`).  A later block nesting through
  a container reads the whole family off ONE datum here: the fold it
  spells from `J.rec` needs the sibling recursors' towers and rules,
  which no other member's clause could be made to agree with. -/
  rulesRead : d.nP ≠ 0 → rules ≠ [] → env.find? cvR.name = some (.recInfo cvR mI rP rules) →
    ∀ t, t < d.k → RecReadAt m d cvT.levelParams t
  /-- the recursor's major position: one motive per member, one minor
  per constructor OF THE BLOCK, the member's own indices -/
  mI : mI = d.nP + d.k + d.nAll + d.nIdxAt mm
  /-- the recursor's rule prefix -/
  rP : rP = d.nP + d.k + d.nAll
  /-- the recursor's rules, when it carries any, are the MEMBER's
  constructors in order (a rule-less entry — a mutual block's recursor
  PROVISIONED before its rules are checked, task #278 — claims the
  representation with this clause vacuous) -/
  rules : rules ≠ [] → rules.map (·.ctor) = (d.memberCtors mm).map (·.1.name)
  /-- the copies come after the real members -/
  kRealLe : d.kReal ≤ d.k
  /-- the represented member is a real one -/
  memReal : mm < d.kReal
  /-- the member's recursor is the stored one -/
  recName : d.recNames mm = cvR.name
  /-- every field's target in the recursor's view is a member -/
  tgtsRLt : ∀ j i, d.tgtsR j i < d.k
  /-- every member of the recursor's block is a stored inductive -/
  membersFound : ∀ t, t < d.k →
    ∃ (cv : ConstantVal) (caps : IndCaps), env.find? (d.memberName t) = some (.indInfo cv caps)
  /-- every stored member carries the block's level parameters (task
  #279 M-B′ step 3a: `containerInfo?` compares them) -/
  membersLps : ∀ t, t < d.k → ∀ (cv : ConstantVal) (caps : IndCaps),
    env.find? (d.memberName t) = some (.indInfo cv caps) → cv.levelParams = cvT.levelParams
  /-- the real members' names are distinct (task #279 M-B′ step 3a:
  `containerInfo?` requires the group `Nodup`) -/
  memberNodup : ((List.range d.kReal).map d.memberName).Nodup
  /-- a constructor of the recursor's block belongs to a real member
  exactly when it is a real one (task #279 M-B′ step 3a: a real
  member's rules are among `ctorsA`) -/
  memsReal : ∀ j, j < d.nAll → (d.mems j < d.kReal ↔ j < d.ctorsA.length)
  /-- the copies' constructors are stored constants -/
  ctorsCFound : ∀ cC ∈ d.ctorsC, (env.find? cC.1.name).isSome = true
  /-- a real member's pins are the parameter variables and its
  container is the block -/
  pinsReal : ∀ t, t < d.kReal →
    (∀ ψ : Name → Nat, d.pinsAV t ψ = paramBvarsAt d.nP d.nP) ∧ d.nPM t = d.nP
  /-- **the recursor's type reads as the generated tower** (task #279
  M-A′): at a block with parameters — the only ones a later block can
  nest through — the stored recursor type reads to the Π-tower over the
  `k`-motive binder data at the members' pins with the core
  `motive_mm ı⃗ t` -/
  recRead : d.nP ≠ 0 → ∀ ψ : Name → Nat,
    denoteMeta m.acval env ψ 0 cvR.type
      = some (mkPisAV (d.recDataAV m ψ mm) (mutualConcAV d.k d.nAll (d.nIdxAt mm) mm))
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
