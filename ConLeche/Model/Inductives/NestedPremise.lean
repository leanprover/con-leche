module

public import ConLeche.Semantics.Inductives.DeclNested
public import ConLeche.Model.Inductives.NestedFit
-- `containerInfo?_inv`, for `ContainerModeled.pinParamsOf`'s re-indexing:
-- proof-only, hence a plain import (task #315 M7-3 session 22).
import ConLeche.Verify.Inductives.NestedGroupInv
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
(DESIGN §U.86): the pins' level ARGUMENTS scoped in the group's own
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

/-- **A PIN, SPELLED AT ANOTHER INSTANTIATION** (task #315 M7-3
session 14, DESIGN §U.73 (a)): the recorded pin `q` — its container
applied to components that stand at the BLOCK's own parameter
openers — written out at the level arguments `lvls` and components
`DsE` a reader was asked for.

The components are CLOSED first (`Expr.abstractRange x 0 nP 0`, which
is the restore table's own closing of a pin, `restoreTbl`), then level
-instantiated, then re-opened at `DsE`; so the whole form is a
FUNCTION of the recorded OPENED components and needs no new `PinSyn`
field.  The level arguments are substituted syntactically, at the
container's own level parameters.

This is the shape `containerOwnPinsAt` produces: it instantiates the
mimic recursor's binders with `Expr.instPis ty (Ds ++ pad)` AFTER
`instantiateLevelParams`, and the restore wrote each mimic recursor's
major premise FROM the recorded pin (`restoreNode`), so the pin comes
back closed, level-instantiated and re-opened exactly here. -/
@[expose] def PinSyn.ownAt (q : PinSyn) (nP : Nat) (lps : List Name) (lvls : List Level)
    (DsE : List Expr) : Expr :=
  Expr.mkAppN (.const q.J (q.lvls.map (Level.subst lps lvls)))
    (q.DsE.map fun x =>
      Expr.instSeq DsE (DsE.length - 1)
        ((Expr.abstractRange x 0 nP 0).instantiateLevelParams lps lvls))

/-- **A BLOCK MODEL'S OWN PINS AS TERMS, AT ITS OWN PARAMETERS** (task
#315 K.68's model side): the list the checker's `nestedPinTermsSelf`
computes, spelled from the block model's own record instead.

A clause stated over this names NO ENVIRONMENT, so it transports in a
word — and it is the same list both sides of K.67/K.68's composition
run their `findIdx?` over, which is why the collapse question never
arises: neither side has to argue that equal terms have equal images,
because both name one index. -/
@[expose] def BlockModel.ownPinTerms (d : BlockModel V) (lps : List Name) : List Expr :=
  (List.range d.nPins).map fun z =>
    (d.pinAt z).ownAt d.nP lps (lps.map Level.param)
      (ConLeche.containerParamOpeners d.nP)

/-- **THE FIELD SHAPE: EVERY OWN PIN THE MIMICS SPELL IS ONE OF THE
BLOCK MODEL'S RECORDED PINS, SPELLED AT THAT INSTANTIATION** (task
#315 M7-3 session 14, DESIGN §U.73 (a)) — the form
`ContainerModeled.ownPins` must take, and the reason is the CROSSING.

`ContainerModeled` is proved where a container is INSTALLED and
consumed where a LATER block is checked, so every clause crosses
`ContainerModeled.crossEnvP`.  The reading form below does NOT cross:
its `DenoteMetaSpine` premise is CONTRAVARIANT (reading monotonicity
runs `env₁ → env₂`, and the clause would have to pull a reading at
`env₂` back to `env₁`).  This one mentions no model at all — only the
environment the table is read at and the block model's own recorded
pins — so it crosses as soon as the TABLE does, which is the one thing
`crossEnvP`'s `hF` does not give (it deliberately does not preserve
`.recInfo`s, and the own-pin table is read off exactly those).  That
residue is the queued kernel record K.43: a per-install Bool pinning
the number of mimics under a container is what makes the table
invariant under a later install.

`ContainerOwnPinsSyn.toReadOf` (`NestedOwnPinsRead.lean`, which is
above this file) is the bridge to the reading form the
consumer (`pinCorr_of_ownPins`) wants.

**THE COMPONENTS MUST BE CLOSED, and the clause is FALSE without it**
(task #315 M7-3 session 18, DESIGN §U.104 (a) — REFUTED on two real
runs, not argued).  `containerOwnPinsAtGo` instantiates the mimic
recursor at `Ds ++ pad`, and `Expr.instPis` peels ONE binder per
argument at cursor 0 — so the PAD substitutions run on the
already-inserted components, at descending cursors, and a component
carrying a LOOSE BOUND VARIABLE is eaten by the pad.  `PinSyn.ownAt`
re-opens the recorded (openers-instantiated, hence pad-processed) pin
at `DsE` afterwards, so the same bvar survives there.  At
`tests/e2e/nested_rec.ndjson`'s `Tree` the reader answers
`[List (Tree Sort)]` where `ownAt` predicts `[List (Tree #0)]`, at
`DsE = [Expr.bvar 0]`; `nested_p30`'s `P30` is the same.  Lane L-B's
`instPis_openers_subst` carries `hDcl : ∀ a ∈ Ds, a.looseBVarsBounded 0`
for exactly this reason — that hypothesis is not a proof artefact, it
is the gap.

The closedness costs no consumer: `toReadOf` already takes it (inside
its `hDsE`), and the seven pins-free sites go through `of_noMimics`,
which only gains an `intro`.

**TWO CLAUSES, AND THE SECOND IS THE POSITION** (task #315, lane
WIDE's (f3) finding).  The first clause is membership-to-existence:
every table entry is SOME recorded pin.  That is all the block-to-
container direction ever needed, and it is what `pinCorr_of_ownPins`
reads.  It does not, however, say WHICH, nor that a recorded pin occurs
in the table at all — so a consumer that needs a *function* from the
container's own pin INDEX to anything (the wide identification's
reindexing `σ` is one: it runs on `[0, d.k + d.nPins)` and reads
`d.pinAt`, `d.pinIdx`, `d.tgts`) gets nothing from it.  The second
clause is that function's domain: the table's entry AT the recorded
pin's own index is that pin, spelled at the instantiation.  It is TRUE
and it needs no new record — the checker certifies the table at the
identity instantiation to be the recorded pin list verbatim, position
by position, and `containerOwnPinsAtGo_subst` moves it to any other
instantiation as a `List.map`, so `nestedOwnPins_of` proves it with the
position it already holds.  At a pins-free block it is vacuous
(`of_noOwn` takes `d.nPins = 0` for it, which every such site has by
`rfl` or by its block record's `pins` clause).  It is guarded by
`DsE.length = d.nP`, and has to be: a reader asked at the WRONG number
of components gets the empty table, which is vacuous for the first
clause and false for this one. -/
@[expose] def ContainerOwnPinsSyn (env : Env) (d : BlockModel V) : Prop :=
  ∀ (i : Nat) (cvC : ConstantVal) (caps : IndCaps) (lvls : List Level) (DsE ps : List Expr),
    i < d.k → env.find? (d.memberName i) = some (.indInfo cvC caps) →
    (∀ a ∈ DsE, a.looseBVarsBounded 0 = true) →
    ConLeche.containerOwnPinsAt env (d.memberName i) lvls DsE = some ps →
    (∀ e ∈ ps, ∃ qK, qK < d.nPins ∧ e = (d.pinAt qK).ownAt d.nP cvC.levelParams lvls DsE) ∧
    (∀ qK, qK < d.nPins → DsE.length = d.nP →
      ps[qK]? = some ((d.pinAt qK).ownAt d.nP cvC.levelParams lvls DsE))

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

  Spelled on the PIN'S OWN COMPONENTS (`DsE`) and not on the field's
  opened domain — the respelling DESIGN records as
  "`ContainerModeled.nestMention` RESPELLED", in the merge record for
  M7-3's retry merge.  (The old citation "§U.67 (b) B1" was rot: §U.67
  is M7-3 session 10, whose (b) has no `nestMention`, no `DsE` and no
  B1/B2 naming.  Cite a DESIGN finding BY TITLE and let the integrator
  number it — the rule the same audit produced.)  The reason: at the
  nested block's own read-back the two are the same list — the restored domain is the pin re-opened
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
  /-- **A NESTED FIELD'S PARAMETER ARGUMENTS MENTION A MEMBER**, on the
  field's OPENED DOMAIN (task #315 PINF, DESIGN "the pin case IS
  dropped").

  `nestMention` spells the same existence on the pin's RECORDED
  components, which is where K.44 (`nestedPinMentionOk`) has it.  A
  consumer working on the copies' `pinF` arm needs it on the FIELD's
  own argument spine instead, and `BlockOpened.nestF` — which records
  the head, the argument count and `constsResolve env₀` for the
  arguments PAST `nPJ` — says nothing about the parameter part, so
  nothing derives one from the other: `BlockCtorData` keeps only
  READINGS there (`nestEntry`), and a reading is not an injection.

  It is a MENTION and not the equality `= DsE.map (instSeq fvsP …)`:
  the restore hands the domain as the pin CLOSED over the parameters
  and REOPENED at the constructor's own openers
  (`ReadCtx.restoredOpened`'s `RestoredField`), and the two opener lists
  are DEFEQ, not equal, so the round trip is not the identity.  A
  mention travels through it all the same
  (`mentionsMember_abstractRange` at K.30's leaves,
  `mentionsMember_instSeq`), and a mention is all the consumer wants.

  Stated at BOTH recursive kinds and with `q < d.nPins`, so a pins-free
  block discharges it in `nestMention`'s own idiom. -/
  nestArgsMention : ∀ (i j l : Nat) (x : Expr) (q : Nat), i < d.k → j < (d.ctorsM i).length →
    (d.xFvsF i j)[l]? = some x → d.nestOf i j l = some q → q < d.nPins →
    (d.ksF i j).getD l .ordinary = .recursive →
    ∃ e ∈ x.fvarTypeD.getAppArgs.take (d.pinAt q).nPJ,
      ConLeche.mentionsMember d.memberNames e = true
  /-- **AND THE SAME ON THE STORED CONSTRUCTOR'S ABSTRACT DOMAIN**
  (task #315 PINF, DESIGN "(ii)'s price MEASURED BEFORE IT WAS BUILT").

  `nestArgsMention` is the OPENED spelling, which is the side
  `BlockOpened` works on.  K.60's Bool
  (`nestedCopyPinFieldsOk`) reads the CLOSED one — it strips the
  container's stored constructor to `nP + nFields` binders and tests
  `jbs[nP + l]`'s own argument spine — and it MUST: the classification
  it concludes about is computed on that same stored type, and a member
  mention that lives only in an opener's ANNOTATION mints no pin, so a
  guard on the opened domain would claim something false.

  The two do not derive from one another.  `Expr.mentionsConst`
  descends into an `.fvar`'s annotation, so an earlier RECURSIVE
  field's opener carries a member mention into the opened spine that
  the abstract one does not have: abstract ⟹ opened
  (`mentionsMember_instSeq`), never back.  So both sides are carried,
  from the restore, where the field's spine is still visibly the pin —
  here LIFTED past the field binders rather than closed and reopened
  (`NestedStageFacts.pinArgsAbs`).

  Recursive only and with `q < d.nPins`, in `nestArgsMention`'s own
  idiom. -/
  nestArgsMentionAbs : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat), i < d.k →
    (d.ctorsM i)[j]? = some cA →
    cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
    d.nestOf i j l = some q → q < d.nPins →
    (d.ksF i j).getD l .ordinary = .recursive →
    ∃ e ∈ dom.1.getAppArgs.take (d.pinAt q).nPJ,
      ConLeche.mentionsMember d.memberNames e = true
  /-- **AND THE SAME AT A REFLEXIVE NESTED FIELD, ONE `Π`-TOWER DOWN**
  (task #315 K.63).

  `nestArgsMentionAbs` is the guard K.60 reads: it dispatches on the
  stored domain's own HEAD, and a reflexive nested field's domain is a
  `Π`, so `getAppFn` is not a `.const` and K.60's walk falls into its
  catch-all and claims nothing there — by construction.  K.63 is the
  twin that asks the same question of the domain's `stripDomPis` BODY,
  and this is the mention its guard needs, spelled where the Bool reads
  it.

  The two are disjoint by construction and neither derives from the
  other: the body's spine is not the domain's, and `getAppArgs` of a
  `Π` is empty.  Reflexive only and with `q < d.nPins`, in
  `nestArgsMentionAbs`' own idiom. -/
  nestArgsMentionAbsRefl : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat), i < d.k →
    (d.ctorsM i)[j]? = some cA →
    cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
    d.nestOf i j l = some q → q < d.nPins →
    (d.ksF i j).getD l .ordinary = .reflexive →
    ∃ e ∈ (ConLeche.stripDomPis dom.1).getAppArgs.take (d.pinAt q).nPJ,
      ConLeche.mentionsMember d.memberNames e = true
  /-- **AND THE SPINE ITSELF, NOT ONLY A MENTION** (task #315 WIDE
  (1′)): a nested finitary field's abstract domain, CUT at the
  container's own parameter count and read in the container's own
  scope, IS the recorded pin spelled at that scope.

  `nestArgsMentionAbs` says only that SOME argument of that cut
  mentions a member.  That is enough to know a pin was minted and not
  enough to know WHICH, and a consumer that needs a FUNCTION from the
  container's own pin classes — the wide identification's reindexing —
  needs which: it reads the cut's position in
  `containerOwnPinsSelf`, whose entry at `q` is exactly this clause's
  right-hand side (`ContainerOwnPinsSyn`'s positional conjunct).

  The two spellings of "the container's own scope" are the two
  substitution idioms this tree uses, and they agree: the kernel's cut
  is `instantiateList … (containerParamOpeners nP).reverse l` — the
  field stands under `l` earlier binders, so the pin's parameter
  variables are `bvar (l + i)` — and `PinSyn.ownAt` closes the recorded
  components and reopens them with `instSeq` at cut `nP - 1`.  The
  level arguments are the identity instantiation, so the clause holds
  at EVERY `lps` and takes it as a parameter rather than reading the
  member's own.

  Recursive only and with `q < d.nPins`, in `nestArgsMentionAbs`' own
  idiom, so the pins-free sites stay vacuous. -/
  nestPinSpineAbs : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat) (lps : List Name), i < d.k →
    (d.ctorsM i)[j]? = some cA →
    cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
    d.nestOf i j l = some q → q < d.nPins →
    (d.ksF i j).getD l .ordinary = .recursive →
    Expr.instantiateList
        (Expr.mkAppN dom.1.getAppFn (dom.1.getAppArgs.take (d.pinAt q).nPJ))
        (ConLeche.containerParamOpeners d.nP).reverse l
      = (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners d.nP)
  /-- **AND THE SPINE AT A REFLEXIVE NESTED FIELD** (task #315 K.65's
  consumer): `nestPinSpineAbs` one `Π`-tower down, carried beside it
  for the reason `nestArgsMentionAbsRefl` is carried beside
  `nestArgsMentionAbs` — a reflexive nested field's stored domain is a
  `Π`, so the finitary clause's `getAppFn` is the `Π` itself and it
  says nothing there.

  The cut moves with the tower.  The spine sits under the field's own
  binders as well as the constructor's, so the parameters it mentions
  are `domPiDepth dom.1` further out and the instantiation follows
  them; `domPiDepth` is `0` and `stripDomPis` the identity on a
  finitary domain, so this clause and the one above ask the same
  question of the same cut wherever both could apply.  **It is stated
  at the kernel's own two functions on purpose**: K.65's arm is
  reached by no accepted stream, so the agreement between the cut the
  checker compares at and the cut the model records cannot be
  certified by a corpus and has to be BY CONSTRUCTION. -/
  nestPinSpineAbsRefl : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat) (lps : List Name), i < d.k →
    (d.ctorsM i)[j]? = some cA →
    cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
    d.nestOf i j l = some q → q < d.nPins →
    (d.ksF i j).getD l .ordinary = .reflexive →
    Expr.instantiateList
        (Expr.mkAppN (ConLeche.stripDomPis dom.1).getAppFn
          ((ConLeche.stripDomPis dom.1).getAppArgs.take (d.pinAt q).nPJ))
        (ConLeche.containerParamOpeners d.nP).reverse (l + ConLeche.domPiDepth dom.1)
      = (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners d.nP)
  /-- **NO `.proj` NODE OF A STORED CONSTRUCTOR TYPE NAMES A MEMBER**
  (task #315 PINF, DESIGN "the `ConstWF` fifth clause does NOT deliver
  the derivation").

  A consumer walking a container's stored constructor type and carrying
  a member MENTION across a substitution loses it at a `.proj` node:
  `Expr.mentionsConst (.proj s _ x)` counts the STRUCTURE NAME `s`,
  while `uniformIndOccsE` (whose node test dispatches on `getAppFn`)
  never looks at it and `instantiate1` does not touch it either.  The
  arm is vacuous in fact, and this clause is where that fact is held.

  **Not derivable at the consumer, and not a kernel Bool.**  Neither
  walk constrains a `.proj` node's structure name — `normPosDomM`
  rejects only a Π whose domain mentions a member, and `uniformOccNode`
  answers `some false` at a `.proj` node and descends into the subject
  alone.  What rejects it is `checkConstantVal`/`checkConstantValPre`'s
  `projTablesOk` at the INSERTION environment, where a member being
  declared is `.indInfo` and has no projection table.  `ConstWF` cannot
  carry that: it is stated at the CURRENT environment and
  `projTablesOk`'s `.proj` node is a `findProj?` `.isSome`, satisfied
  more often in a LARGER environment — so a fifth clause there would be
  satisfied by exactly the node it was meant to exclude.  The fact lives
  where it is true: `FrontDoorFacts.slots`, at the door's own
  environment, which every install route holds
  (`Expr.ProjSlotsOk.noProjAt` against the member's empty slot).

  Spelled on the STORED constructor type and not on the opened field
  domains: that is the form the doors hand, the form `ProjFree`'s kit
  (`BlockRepCross.lean`) descends from, and the form `copyResid`
  delivers to the consumer (`cAJ.1.type = cc.type`). -/
  ctorProjFree : ∀ (i j : Nat) (cA : ConstantVal × Nat), i < d.k →
    (d.ctorsM i)[j]? = some cA →
    ∀ T ∈ d.memberNames, ∀ n : Nat, ConLeche.Expr.NoProjAt T n cA.1.type
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
  /-- **A pin's container reads the SAME group at the model's
  environment as at the block's own** (task #315 M7-3 session 20, lane
  L-B's request): `pinNP` is spelled at `d.env₀`, the block's own
  pre-block environment, because that is where `BlockOpened.nestF`
  resolves a pin's index arguments — and a consumer working at the
  MODEL's environment cannot use it there.  This is the monotonicity
  that carries it across: the container is stored at `d.env₀` and no
  install since has disturbed it.

  Requested in place of an EQUATION `d.env₀ = env`, which is false at
  three of the nine sites (the nested, mutual and native routes all
  build this record at a model of the OUTPUT environment while `env₀`
  is the pre-block one) and unavailable at the four basis sites. -/
  pinConts : ∀ q, q < d.nPins → ∀ ci' : ContainerInfo,
    ConLeche.containerInfo? d.env₀ (d.pinAt q).J = some ci' →
    ConLeche.containerInfo? env (d.pinAt q).J = some ci'
  /-- **EVERY OWN PIN THE BLOCK'S MIMICS SPELL IS ONE OF ITS RECORDED
  PINS, AT THAT INSTANTIATION** (task #315 M7-3, the lane record "the
  field shape: every own pin the mimics spell is one of the block
  model's recorded pins, spelled at that instantiation").

  `containerOwnPinsAt` reads a stored container's own pins off its
  MIMIC recursors and hands back `Expr`s; `classPin_of_pinCorr`, on the
  other side, wants a `PinCorr` at a pin the BLOCK MODEL RECORDS.
  Nothing else in `ContainerModeled`/`BlockAt` relates the two, and this
  clause is what does.

  Carried in the SYNTACTIC form (`ContainerOwnPinsSyn`) and not in the
  reading form (`ContainerOwnPins`) because the record is proved where a
  container is INSTALLED and consumed where a LATER block is checked, so
  every clause has to cross `ContainerModeled.crossEnvP` — and the
  reading form does not: its `DenoteMetaSpine` premise is CONTRAVARIANT
  (reading monotonicity runs `env₁ → env₂`, and the clause would have to
  pull a reading at `env₂` back to `env₁`).  `ContainerOwnPinsSyn.toReadOf`
  (`NestedOwnPinsRead.lean`) is the bridge to the form the consumer
  wants; see `ContainerOwnPinsSyn`'s own docstring for why the
  components must be closed. -/
  ownPins : ContainerOwnPinsSyn (V := V) env d
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
  /-- **A PIN'S DATA DEPEND ON THE ASSIGNMENT ONLY THROUGH THE
  CONTAINER'S OWN LEVEL PARAMETERS** (task #315 lane L-E session 17's
  request, DESIGN §U.69 (e)): two assignments agreeing on the group's
  level parameters give one index universe, one component reading and
  one index telescope at every pin.

  A record and not a derivation, and lane L-E checked before asking:
  `IsBlockModel.uParams` and `FormerData.params` are the MEMBERS'
  congruences; the `u` and `Ids` congruences reduce (through the
  container's own `PinShapes` view, `ContainerModeled.params_congr` and
  `pinψ`) to the FIRST part, which no other record carries; and the
  `Ds` parts do not reduce at all — a `PinSyn`'s components are an
  abstract `(Name → Nat) → List AnnotTerm`, so both their BOUND (the
  walk's `frame` at a pin class reads one component at two frames that
  agree only below `d.nP`) and their congruence have to be recorded.
  Consumers: `huT`'s pin branch inside `copyTransfer_via`, and the
  `pinF` arm of the walk.

  Stated over the GROUP's member record (`ci.members[i]?`), not over an
  `env.find?` as `pinψ` is: `M.lps` IS the `cvI.levelParams` the
  definition asks for, which is what makes the member record the right
  carrier and lets the clause mention no environment at all — hence it
  crosses an extension VERBATIM (`crossEnvP` passes it through
  unchanged).  A consumer holding the stored constant instead re-indexes
  it by `pinParamsOf` below.  Vacuous at a pins-free container, like its
  neighbours. -/
  pinParams : ∀ (i : Nat) (M : ConLeche.ContainerMember), ci.members[i]? = some M →
    ContainerPinParams (V := V) ⟨M.name, M.lps, M.type⟩ d
  /-- **THE CONTAINER'S OWN PINS ARE SPELLED DIFFERENTLY FROM ONE
  ANOTHER** (task #315, lane WIDE's (f3)): two of the container's
  recorded pins with ONE pin term are one pin.

  **Why a container needs a clause for a fact the block being installed
  has for free.**  The elimination dedupes by pin EXPRESSION —
  `replaceIfNested` mints only on a miss — so a run's own pin list is
  `pinsDistinct` (K.31, the left conjunct of `nestedContainersOk`), and
  the run's consumers read it there.  A CONTAINER, however, is consumed
  at a LATER block, where its own run is gone; and the checks a run
  makes about its own elimination are exactly the facts that do not
  travel, because nothing in a stored constant records them.  So a
  consumer that has to IDENTIFY one of a container's own pins — by its
  term, which is the only handle a table read gives — needs the fact
  carried, and this clause carries it, the way `ownPins` carries the
  table itself.

  Stated as an INJECTION rather than as a `Nodup`, because that is the
  consumer's shape: a table lookup answers a POSITION, and what the
  identification needs is that the position is the pin's own.  It
  mentions no environment and no model, so it crosses an extension
  verbatim, and it is vacuous at a pins-free container, like its
  neighbours. -/
  pinsDistinct : ∀ q q', q < d.nPins → q' < d.nPins →
    Expr.mkAppN (.const (d.pinAt q).J (d.pinAt q).lvls) (d.pinAt q).DsE
      = Expr.mkAppN (.const (d.pinAt q').J (d.pinAt q').lvls) (d.pinAt q').DsE → q = q'
  /-- **AND THE SAME AT THE SPELLING THE TABLE USES** (task #315 WIDE
  (2″)): two of the container's recorded pins with one OWN-PIN TABLE
  ENTRY are one pin.

  `pinsDistinct` is about the recorded pin TERM; the consumer looks a
  term up in `containerOwnPinsSelf`, whose entry at `q` is that term
  passed through `PinSyn.ownAt` at the identity level instantiation and
  the SYNTHETIC parameter openers — which is the term with every
  parameter `fvar`'s ANNOTATION replaced by `Expr.sort Level.zero`
  (`abstractRange` drops it, the reopening puts the synthetic one
  back).  **Annotation-erasure is not injective in general**, so
  `pinsDistinct` does not give this: a `findIdx?` over the table may
  answer an EARLIER position than the pin's own unless the entries are
  known distinct, and the whole point of the lookup is that the
  position IS the pin's.

  What makes it true here is K.30 (`pinsScoped`): a recorded pin's
  `fvar` leaves are the FIRST FORMER's openers, so a given index
  carries ONE annotation across all of a block's pins and the erasure
  loses nothing on this set.  That is a fact about the block's own run,
  so — like `pinsDistinct`, `ownPins` and `nestPinSpineAbs` — it has to
  be carried rather than re-derived, and it is discharged at the
  block's own read-back where K.30 is still in hand.

  Stated at every `lps`, as `nestPinSpineAbs` is and for the same
  reason: the level instantiation is the identity.  It mentions no
  environment and no model, so it crosses an extension verbatim, and it
  is vacuous at a pins-free container. -/
  pinsDistinctAt : ∀ q q' (lps : List Name), q < d.nPins → q' < d.nPins →
    (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
        (ConLeche.containerParamOpeners d.nP)
      = (d.pinAt q').ownAt d.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners d.nP) → q = q'
  /-- **THE PINS' COMPONENTS STAND AT THE PARAMETER OPENERS** (task
  #315 WIDE, lane LE): at every own pin, every recorded component has
  no loose bound variable and every free variable it carries —
  annotation included — is one of `d.nP` openers, at that opener's own
  index.  K.30 (`pinsScoped`) at a container, which is where the
  reading of the own-pin TABLE begins: `PinSyn.ownAt` closes a
  component over the parameters and reopens it at the instantiation,
  and `denoteMeta_ownAt_component` reads that round trip only for a
  component the openers scope.

  Stated PER PIN, so a pins-free block discharges it in
  `nestMention`'s idiom; it mentions no environment and no model, so it
  crosses an extension verbatim. -/
  pinDsScoped : ∀ q, q < d.nPins →
    ∃ params : List Expr, params.length = d.nP ∧
      (∀ j, j < d.nP → ∃ ty, params[j]? = some (Expr.fvar j ty)) ∧
      ∀ x ∈ (d.pinAt q).DsE, x.looseBVarsBounded 0 = true ∧
        ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params
  /-- **AND THEIR CONSTANTS RESOLVE** (task #315 K.64's consumer): the
  GUARD the next clause needs to cross a later install.

  `pinDsRead` below is a `denoteMeta` conclusion, so it crosses
  covariantly — but through `crossEnvP`'s `hde`, which is guarded,
  because `hde` is refutable across a projection-table cons
  (`hde_not_of_newTable`).  Every other subject of that crossing takes
  its guard from a front door's resolution
  (`ProjFree.of_constsResolve`); a pin's components have no front
  door, and K.64 (`pinsResolve`) is the record that supplies it.

  Crosses by `crossEnvP`'s `hres`, and vacuous at a pins-free
  block. -/
  pinDsRes : ∀ q, q < d.nPins → ∀ x ∈ (d.pinAt q).DsE,
    x.constsResolve env = true
  /-- **AND THEY READ AS THE RECORDED READINGS** (task #315 WIDE, lane
  LE): at every own pin and every level assignment, the recorded
  components READ, at the container's own parameter depth, as the
  `PinSyn`'s recorded `Ds`.

  `PinSyn.Ds` is an abstract field, so nothing but a clause ties it to
  `DsE`: the run states it of the block it is installing
  (`NestedStageFacts.pinDs`) and no law of `IsBlockModel` or
  `ContainerModeled` recovers it at a STORED container.  It is what
  makes the own-pin table usable semantically —
  `ContainerOwnPinsSyn.toReadOf` turns the syntactic table into the
  reading form with exactly this and `pinDsScoped` — and the wide
  identification needs the reading form at every own pin, including
  the pins a container minted inside its own copies, which no field of
  the container names.

  It is a `denoteMeta` CONCLUSION, so it crosses an install
  covariantly — through the GUARDED `hde`, whose `ProjFree` the two
  clauses above supply: `pinDsRes` at a LATER install (where the newly
  tabled names are fresh) and K.64's table conjunct at the block's
  OWN. -/
  pinDsRead : ∀ q, q < d.nPins → ∀ φ : Name → Nat,
    DenoteMetaSpine m.acval env φ d.nP (d.pinAt q).DsE ((d.pinAt q).Ds φ)

/-- **The block model's member names ARE the container group's**, as
lists (task #315 PINF): `k` and `namesLen` give the length and
`member` the entries.  What a consumer needs to hand a
`mentionsMember` of the model's list to a kernel record spelled on the
group's (`nestedCopyPinFieldsOk`), and back. -/
theorem ContainerModeled.memberNames_eq {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (C : ContainerModeled m ci d) :
    d.memberNames = ci.members.map (·.name) := by
  have hlen : d.memberNames.length = (ci.members.map (·.name)).length := by
    rw [C.namesLen, C.k, List.length_map]
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hik : i < ci.members.length := by rw [List.length_map] at h2; exact h2
  obtain ⟨M, hM⟩ : ∃ M, ci.members[i]? = some M := ⟨_, List.getElem?_eq_getElem hik⟩
  have hname := (C.member i M hM).1
  have hmn : d.memberNames[i] = d.memberName i := by
    show _ = d.memberNames.getD i .anonymous
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hml : (ci.members.map (·.name))[i] = M.name := by
    have h := List.getElem?_map (f := fun M : ConLeche.ContainerMember => M.name)
      (l := ci.members) (i := i)
    rw [hM] at h
    rw [List.getElem?_eq_getElem h2] at h
    exact Option.some.inj h
  rw [hmn, hml, hname]

/-- **THE ENVIRONMENT'S OWN-PIN TABLE IS THE MODEL'S, POSITION BY
POSITION** (task #315 WIDE (3), the correspondence's TABLE
translation): `containerOwnPinsSelf` — the reader K.67's and K.68's
Bools run their `findIdx?` over — hands back exactly `d.ownPinTerms`
at the container's own level parameters.

`ContainerOwnPinsSyn`'s positional clause says this of
`containerOwnPinsAt`, and `containerOwnPinsSelf` IS that reader at the
identity level instantiation and the parameter openers.  What the
proof adds is the group's own bookkeeping: the member index the name
sits at (`memberNames_eq`), the head member's level parameters — the
clause answers at the READ member's and the reader asks at the HEAD
member's, and `containerInfo?_inv` says a group's members share the
first's — and the openers' length.

The level parameters are handed back EXISTENTIALLY: a consumer that
must meet a second reading of the same table (`d.ownPinTerms lps` on
the model side) instantiates that side here rather than naming a
spelling of its own. -/
theorem ContainerModeled.ownPinsSelfAt {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (C : ContainerModeled m ci d) {Cn : Name}
    (hci : ConLeche.containerInfo? env Cn = some ci)
    {ownT : List Expr} (hown : ConLeche.containerOwnPinsSelf env Cn = some ownT) :
    ∃ lps : List Name, ∀ z, z < d.nPins →
      ownT[z]? = some ((d.pinAt z).ownAt d.nP lps (lps.map Level.param)
        (ConLeche.containerParamOpeners d.nP)) := by
  classical
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfI, -, hmemI, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hci
  -- the group is non-empty, and its HEAD member's level parameters are the read one's
  have hmem0 : 0 < ci.members.length := by
    rcases List.mem_iff_getElem.mp hmemI with ⟨y, hy, -⟩
    rw [List.length_map] at hy; omega
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ci.members[0]? = some M₀ :=
    ⟨_, List.getElem?_eq_getElem hmem0⟩
  obtain ⟨cvC₀, -, -, -, -, -, -, hlps₀, -, hlpsT₀, -, -⟩ :=
    hmembers M₀ (List.mem_of_getElem? hM₀)
  have hhead0 : ci.members.head? = some M₀ := by
    rw [List.head?_eq_getElem?]; exact hM₀
  have hlvlsEq : M₀.lps = cvT.levelParams := by rw [hlps₀, hlpsT₀]
  have hAt : ConLeche.containerOwnPinsAt env Cn (cvT.levelParams.map Level.param)
      (ConLeche.containerParamOpeners ci.nP) = some ownT := by
    rw [← hlvlsEq, ← hown]
    simp only [ConLeche.containerOwnPinsSelf, bind, Option.bind, hci, hhead0]
  -- the member index the container's name sits at
  have hCn : Cn ∈ d.memberNames := by rw [C.memberNames_eq]; exact hmemI
  obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hCn
  have hik : i < d.k := by rw [← C.namesLen]; exact hi
  have hname : d.memberName i = Cn := by
    show d.memberNames.getD i .anonymous = Cn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact hiv
  have hclO : ∀ a ∈ ConLeche.containerParamOpeners ci.nP, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
    rfl
  have hlenO : (ConLeche.containerParamOpeners ci.nP).length = d.nP := by
    rw [C.nP]; simp [ConLeche.containerParamOpeners]
  have hopen : ConLeche.containerParamOpeners ci.nP = ConLeche.containerParamOpeners d.nP := by
    rw [C.nP]
  obtain ⟨-, hpos⟩ := C.ownPins i cvT caps (cvT.levelParams.map Level.param)
    (ConLeche.containerParamOpeners ci.nP) ownT hik (by rw [hname]; exact hfI) hclO
    (by rw [hname]; exact hAt)
  refine ⟨cvT.levelParams, fun z hz => ?_⟩
  have h := hpos z hz hlenO
  rwa [hopen] at h

/-- **A member's index telescope is bounded at the parameters** — the
MEMBER twin of `pinIds_below` (task #315 L-E, DESIGN §U.77). -/
theorem memberIds_below {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    (hreps : IsBlockModels m dJ) {i : Nat} (hi : i < dJ.k) (ψ : Name → Nat) :
    FieldsBelow dJ.nP (dJ.IdsM i ψ) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  refine DomsBelow.fields ?_
  have := DomsBelow.drop dJ.nP (hI.former.below ψ)
  simpa using this

/-- **The pins' congruence, re-indexed by the STORED constant** (task
#315 M7-3 session 22, for lane L-E's quantified premise): the clause
`pinParams` is carried at the group's MEMBER record, a consumer that
has looked the container's name up in the environment has its
`ConstantVal` instead, and the two agree because `containerInfo?`
CHECKS every member's level parameters against the queried constant's
(`containerInfo?_inv`: `M.lps = cvC.levelParams` and
`cvC.levelParams = cvT.levelParams`) — the same step
`nestedOwnPins_of` makes for its two walks.

The member is the one NAMED by `J`, which `containerInfo?_inv` puts in
the group (`J ∈ ci.members.map (·.name)`), so no index and no
non-emptiness hypothesis is needed. -/
theorem ContainerModeled.pinParamsOf {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (C : ContainerModeled m ci d) {J : Name} {cv : ConstantVal}
    {caps : IndCaps} (hci : ConLeche.containerInfo? env J = some ci)
    (hf : env.find? J = some (.indInfo cv caps)) :
    ContainerPinParams (V := V) cv d := by
  -- every name is bound: a `-` here would clear a variable the LATER
  -- conjuncts depend on, and rcases then eats them too
  obtain ⟨cvT, _capsT, _cvR, _mI, _rP, _rules, hfT, _hfR, hmemJ, _hnd, hmems⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨M, hM, -⟩ := List.mem_map.mp hmemJ
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
  obtain ⟨cvC, _capsC, _cvRc, _mIc, _rulesC, _hfM, _hfMr, hMlps, _hMty, hlpsEq, _hlen, _hct⟩ :=
    hmems M hM
  have hcvT : cvT = cv :=
    (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hfT.symm.trans hf))).1
  have hlps : M.lps = cv.levelParams := by rw [hMlps, hlpsEq, hcvT]
  intro q hq
  obtain ⟨hlvls, hbelow, hcongr⟩ := C.pinParams i M hi q hq
  refine ⟨fun v hv => by rw [← hlps]; exact hlvls v hv, hbelow, fun ψ₁ ψ₂ hag => ?_⟩
  exact hcongr ψ₁ ψ₂ fun pp hpp => hag pp (hlps ▸ hpp)

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
     Ψaux := fun _ _ _ _ => pt, pinCtors := fun _ => default, inj := fun _ _ _ _ => pt }⟩

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

/-- **THE OWNER'S HALF OF THE TWO COPIES' FIELD-DATA TIE, AS A
PREDICATE** (task #315 WIDE (3), step 1(a)): at a field the container
calls ORDINARY and a later block's copy made recursive, the OWNER's own
recomputation of the field's target — `ordTargetDom`, the stored domain
cut and instantiated at the owner's own pin (K.67's spelling) — READS,
at the block's parameter frame opened to the field's cut, as an
application whose ARGUMENTS after the head container's parameters are
the copy's index expressions.

It is the conclusion of `NestedPinsRun.copyOrdFRightPinOrdTargetReadAt`
and its reflexive twin, with the run's syntactic residual already
discharged: the frame (`ψ`, `ρp`) and a fitting prefix `fs₁` are
INPUTS, exactly as `CopyCtorShape`'s `ordF` conjunct takes them, and
the head `fb` and the head container's parameters `Ps` are existential
— nothing about them is claimed beyond their count, which is what the
consumer splits the spine at.

The cut is the field's own `l` at a finitary field and `l +
domPiDepth …` at a reflexive one, so the two arms are ONE statement:
the recomputation's own tower depth is a function of the arguments the
predicate already takes, and no call site spells it. -/
@[expose] def OrdTargetRead (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (ψ : Name → Nat) (ρp : Nat → V) (nP l : Nat) (Ds Fs Eis : List AnnotTerm)
    (nPK : Nat) (lpsC : List Name) (nPJ q : Nat) (ownSelf : List Expr) (dom : Expr) : Prop :=
  ∀ fs₁ : List V, fs₁.length = l →
    SpineFit (consList (Ds.map (interp V ρp)) ρp) (Fs.take l) fs₁ →
    ∃ (fb : AnnotTerm) (Ps : List AnnotTerm), Ps.length = nPK ∧
      denoteMeta acval env ψ
          (nP + (l + ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC ownSelf q dom)))
          (Expr.instSeq
            (ConLeche.Verify.openFvars nP
              (l + ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC ownSelf q dom)))
            (l + ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC ownSelf q dom) - 1)
            (ConLeche.ordTargetDom lpsC nPJ ownSelf q l dom))
        = some (AnnotTerm.mkAppN fb (Ps ++ Eis))

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

The COUNT conjunct (task #315 L-E, DESIGN §U.77 (d), the maintainer's
ruling): a pin's constructors are as many as its container member's.
`ChainFitT` at a pin class reads `(pc q).ctors` (`ctorsT_of_pin`), so
the container instance transfer's `j` ranges over that list, while the
shape below is supplied only for `j < ((B ci).ctorsM i').length`;
`PinCtors` is a bare record and `PinRecLaws` quantifies `j` over the
former everywhere, so without this nothing forbids a pin carrying
constructors its container does not have, and the transfer would have
no shape at them.

**THE ROW CONJUNCT** (task #315 WIDE, lane `uniform-carry`): K.61's
row at each of the container's own pins, carried onto the container's
model so that a LATER block can read it.  At a field of the pin's
container that is container-recursive into one of THAT container's own
pins, the copy lands on a pin of `d` — which one is not derivable
here, because the expansion's dedup and the instantiation are the
run's and no law of the block model recovers them — and that pin's
container, index universe, index telescope and components are the
container's own pin's at the group's instantiation.

It is `PinGroupInst`'s `hstgt` and `hpinσ` together, in the model's own
spelling (`(pc (q₀ + i')).tgts` rather than the auxiliary block's
target table), and it is what the collapse-aware correspondence — "σ
of the container's pick is the block's pick" — reads on the CONTAINER's
side.  Stated modulo nothing: the two picks are compared at the pin's
DATA and not at its index, because the two sides index different lists
and two own pins that collapse at one instantiation need not collapse
at the other.  `PinCorr`'s `EA` clause is absent for the reason it is
absent from `hpinσ`: `targetRead_of_pin` rebuilds it from the three
that are here, and it is the only one that reads a model.

**THE OWNER'S HALF** (task #315 WIDE (3), step 1(a)): at a field the
pin's container calls ORDINARY and the block's rewrite made recursive,
whose block target is a PIN and not a member, the OWNER's own
recomputation of the field's target — `ordTargetDom`, K.67's spelling —
READS, at the block's parameter frame opened to the field's cut, as an
application whose arguments past the head container's parameters are
the copy's index expressions (`OrdTargetRead`).  The row beside it
relates the two copies' TARGETS; this relates their index
EXPRESSIONS, which is what the wide identification's pin half asks for
where it compares two index spines rather than two class numbers.

It names the TARGET PIN `z` and takes its parameter count from the
block's own record (`(d.pinAt z).nPJ`) rather than from a
`containerInfo?` of the recomputation's head.  That is deliberate: a
clause may only PRODUCE environment facts, and one that produced a
group at an arbitrary NAME would have to be carried across every
install by a frame no crossing site holds.  With the target named, the
only environment the conjunct mentions is the reading's own, and
`PinShapes.crossEnv` discharges it with the guarded `hde` alone.

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
    (∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < ((B ci).ctorsM i').length → ∀ l,
      l < (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j []).length →
      (((B ci).rss i').getD j []).getD l false = true →
      ¬ (B ci).tgts i' j l < (B ci).k →
      ∃ q', q' < d.nPins ∧
        (pc (q₀ + i')).tgts j l = d.k + q' ∧
        (d.pinAt q').J = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).J ∧
        ∀ φ : Name → Nat,
          (d.pinAt q').u φ
              = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).u ((d.pinAt q₀).ψJ φ) ∧
          (d.pinAt q').Ids φ
              = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).Ids ((d.pinAt q₀).ψJ φ) ∧
          (d.pinAt q').Ds φ
              = (((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).Ds ((d.pinAt q₀).ψJ φ)).map
                  (AnnotTerm.instAll ((d.pinAt q₀).Ds φ) 0)) ∧
    (∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < ((B ci).ctorsM i').length → ∀ l,
      l < (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j []).length →
      (((B ci).rss i').getD j []).getD l false = false →
      ((pc (q₀ + i')).rss.getD j []).getD l false = true →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps : List Name),
      ((B ci).ctorsM i')[j]? = some cA →
      cA.1.type.stripPis ((B ci).nP + cA.2) = some (bs, rr) →
      bs[(B ci).nP + l]? = some dom →
      ∀ (lpsC : List Name) (Jm : ContainerMember),
      ci.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (M : Name) (us : List Level),
      (ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps) (q₀ + i') l dom.1).getAppFn
          = .const M us →
      (∀ mm, d.memberNames.findIdx? (· == M) = some mm → (pc (q₀ + i')).tgts j l = mm) ∧
      (d.memberNames.findIdx? (· == M) = none →
        ∃ z : Nat, z < d.nPins ∧
          (d.pinAt z).ownAt d.nP lps (lps.map Level.param)
              (ConLeche.containerParamOpeners d.nP)
            = Expr.mkAppN
                (ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps)
                  (q₀ + i') l dom.1).getAppFn
                ((ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps) (q₀ + i') l
                  dom.1).getAppArgs.take (d.pinAt z).nPJ) ∧
          (pc (q₀ + i')).tgts j l = d.k + z)) ∧
    (∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < ((B ci).ctorsM i').length → ∀ l,
      l < (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j []).length →
      (((B ci).rss i').getD j []).getD l false = false →
      ((pc (q₀ + i')).rss.getD j []).getD l false = true →
      ¬ (pc (q₀ + i')).tgts j l < d.k →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps : List Name),
      ((B ci).ctorsM i')[j]? = some cA →
      cA.1.type.stripPis ((B ci).nP + cA.2) = some (bs, rr) →
      bs[(B ci).nP + l]? = some dom →
      ∀ (lpsC : List Name) (Jm : ContainerMember),
      ci.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (K : Name) (usK : List Level),
      (dom.1.instantiateLevelParams lpsC ((d.pinAt (q₀ + i')).lvls)).getAppFn = .const K usK →
      ∃ z : Nat, z < d.nPins ∧ (pc (q₀ + i')).tgts j l = d.k + z ∧
        OrdTargetRead (V := V) m.acval env ψ ρp d.nP l
          ((d.pinAt q₀).Ds ψ)
          (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j [])
          ((((pc (q₀ + i')).Eiss ψ).getD j []).getD l [])
          ((d.pinAt z).nPJ) lpsC (B ci).nP (q₀ + i') (d.ownPinTerms lps) dom.1) ∧
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

/-- **K.68's ROW, READ AT ONE PIN** (task #315 WIDE (3)): `PinShapes`'
`ordF` clause projected out at a pin, the way `rowTarget` projects the
recursive one.

At a field the pin's container calls ORDINARY and the copy made
recursive, the copy's target is the class the CONTAINER's own
recomputation names — a member of the container by its NAME among
`d.memberNames`, or one of the container's own pins by its TERM in
`d.ownPinTerms`, the container's own spelling of its pin table.  The
block reading this runs the SAME recomputation (K.67's
`ordTargetDom` at `containerOwnPinsSelf`'s entry, which is that same
term by `ContainerOwnPinsSyn`), so the two sides name one class and
nothing has to cross a substitution. -/
theorem PinShapes.rowTargetOrd {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    {d : BlockModel V} {pc : Nat → PinCtors V} (h : PinShapes m B d pc)
    {q : Nat} (hq : q < d.nPins) {ci : ContainerInfo}
    (hci : ConLeche.containerInfo? env (d.pinAt q).J = some ci) :
    ∃ q₀ kJ i, q = q₀ + i ∧ i < kJ ∧ PinGroupView d (B ci) q₀ kJ ∧
      ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < ((B ci).ctorsM i').length → ∀ l,
        l < (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j []).length →
        (((B ci).rss i').getD j []).getD l false = false →
        ((pc (q₀ + i')).rss.getD j []).getD l false = true →
        ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
          (dom : Expr × ConLeche.BinderMeta) (lps : List Name),
        ((B ci).ctorsM i')[j]? = some cA →
        cA.1.type.stripPis ((B ci).nP + cA.2) = some (bs, rr) →
        bs[(B ci).nP + l]? = some dom →
        ∀ (lpsC : List Name) (Jm : ContainerMember),
        ci.members[i']? = some Jm → Jm.lps = lpsC →
        ∀ (M : Name) (us : List Level),
        (ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps) (q₀ + i') l dom.1).getAppFn
            = .const M us →
        (∀ mm, d.memberNames.findIdx? (· == M) = some mm → (pc (q₀ + i')).tgts j l = mm) ∧
        (d.memberNames.findIdx? (· == M) = none →
          ∃ z : Nat, z < d.nPins ∧
            (d.pinAt z).ownAt d.nP lps (lps.map Level.param)
                (ConLeche.containerParamOpeners d.nP)
              = Expr.mkAppN
                  (ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps)
                    (q₀ + i') l dom.1).getAppFn
                  ((ConLeche.ordTargetDom lpsC (B ci).nP (d.ownPinTerms lps) (q₀ + i') l
                    dom.1).getAppArgs.take (d.pinAt z).nPJ) ∧
            (pc (q₀ + i')).tgts j l = d.k + z) := by
  obtain ⟨q₀, kJ, i, ci', hqe, hi, hci', hgv, -, -, hord, -, -⟩ := h q hq
  obtain rfl : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  exact ⟨q₀, kJ, i, hqe, hi, hgv, hord⟩

/-- **THE ROW, READ AS THE TARGET VIEW'S DATA AT THE FIELD** (task
#315 WIDE, lane `uniform-carry`): the shape the collapse-aware
correspondence consumes.

The transfer between two copies of ONE container at two
instantiations (`copyTransfer_via_pin`) reads a field's target only
through the TARGET VIEW — `TV.u (tg l)`, `TV.Ids (tg l)`,
`TV.Ds (tg l)`, `TV.J (tg l)`, which is everything `slotSet` and the
copies' readings take — and never through the target's INDEX.  That is
not a convenience: the two sides index different pin lists, and two of
the container's own pins that collapse at one instantiation need not
collapse at the other, so no equation between the two indices is
available or wanted.  What IS available is that both sides' data are
the SAME container pin's, at their own instantiations, and this
theorem is the row in exactly that form.

Applying it on each side at one field of one container and rewriting
gives the correspondence: the two targets carry one universe, one
index telescope, one container and componentwise-corresponding
components.  The remaining `PinCorr` clauses — the target's reading
`EA` and its level arguments — are NOT here, and the reason is the
crossing: both need the container's stored `levelParams`, hence an
`env.find?` guard, and the row is carried through
`PinShapes.crossEnv` precisely because it names no environment.  A
consumer that needs them takes `ContainerModeled.pinψ` at the two
pins, where that lookup is already in hand. -/
theorem PinShapes.rowTarget {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    {d : BlockModel V} {pc : Nat → PinCtors V} (h : PinShapes m B d pc)
    {q : Nat} (hq : q < d.nPins) {ci : ContainerInfo}
    (hci : ConLeche.containerInfo? env (d.pinAt q).J = some ci) :
    ∃ q₀ kJ i, q = q₀ + i ∧ i < kJ ∧ PinGroupView d (B ci) q₀ kJ ∧
      ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < ((B ci).ctorsM i').length → ∀ l,
        l < (((B ci).Fss i' ((d.pinAt q₀).ψJ ψ)).getD j []).length →
        (((B ci).rss i').getD j []).getD l false = true →
        ¬ (B ci).tgts i' j l < (B ci).k →
        ¬ (pc (q₀ + i')).tgts j l < d.k ∧
        ∀ φ : Name → Nat,
          (d.targetView m.acval φ).J ((pc (q₀ + i')).tgts j l)
              = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).J ∧
          (d.targetView m.acval φ).u ((pc (q₀ + i')).tgts j l)
              = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).u ((d.pinAt q₀).ψJ φ) ∧
          (d.targetView m.acval φ).Ids ((pc (q₀ + i')).tgts j l)
              = ((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).Ids ((d.pinAt q₀).ψJ φ) ∧
          (d.targetView m.acval φ).Ds ((pc (q₀ + i')).tgts j l)
              = (((B ci).pinAt ((B ci).tgts i' j l - (B ci).k)).Ds ((d.pinAt q₀).ψJ φ)).map
                  (AnnotTerm.instAll ((d.pinAt q₀).Ds φ) 0) := by
  obtain ⟨q₀, kJ, i, ci', hqe, hi, hci', hgv, -, hrow, -, -, -⟩ := h q hq
  obtain rfl : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  refine ⟨q₀, kJ, i, hqe, hi, hgv, fun ψ i' hi' j hj l hl hrs hpinT => ?_⟩
  obtain ⟨q', -, htg, hJ, hrest⟩ := hrow ψ i' hi' j hj l hl hrs hpinT
  -- the target is a PIN class, and the view reads the pin there
  have hnt : ¬ (pc (q₀ + i')).tgts j l < d.k := by rw [htg]; omega
  have hsub : (pc (q₀ + i')).tgts j l - d.k = q' := by rw [htg]; omega
  refine ⟨hnt, fun φ => ?_⟩
  obtain ⟨hu, hIds, hDs⟩ := hrest φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (if (pc (q₀ + i')).tgts j l < d.k then _ else _) = _
    rw [if_neg hnt, hsub]; exact hJ
  · show d.uT _ φ = _
    unfold BlockModel.uT
    rw [if_neg hnt, hsub]; exact hu
  · show d.IdsT _ φ = _
    unfold BlockModel.IdsT
    rw [if_neg hnt, hsub]; exact hIds
  · show (d.pinAt _).Ds φ = _
    rw [hsub]; exact hDs

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

/-- **A STORED CONTAINER'S OWN PIN, READ AGAINST ITS PIN'S CONTAINER AT
THE ABSTRACT ASSIGNMENT** (task #315 M7-3): at a pin `q` of the block
model `B ci` of a stored container group, the pin's own container is
some group `ci'`, and the pin's index data — the member NAME, the
parameter count `nPJ`, the parameter-and-index telescope `pps`, and the
index-tuple sort `u` — is `B ci'`'s at one member index `i`, the
member's own, at the PIN's level assignment.

**Why it exists, and why it is not a clause.**  Another lane needed the
container half of a pin's index data at the ABSTRACT assignment `B`
(not at a concrete, already-constructed block model), checked every
record it was holding, and found the view only at concrete models — so
it was about to ask for a new clause on `ContainerModeled`.  It needs
none: `PinShapes`, which `EnvBlocksOf` already carries at every stored
container through `BlockAt`, states exactly this, at the abstract `B`,
and its `PinGroupView` has the four consequences as fields
(`name`, `pinNP`, `pinPps`, `pinU`, with `kEq` for the bound).  A
clause was therefore considered and REJECTED: the fact DERIVES, so no
producer is burdened with it — including producers that do not exist
yet, which is the argument a site-by-site enumeration cannot make.
This is the move L-E's record *the pins' semantic data, exposed per
pin — DERIVED, so no producer owes anything* made for the nested run's
own syntactic record; here it is made for a STORED container's, at the
global assignment L-E's record *the structure change and the global
entry theorem* introduced.

**Two points of care.**  The sort equation is stated at the pin's OWN
level assignment `((B ci).pinAt q).ψJ ψ`, not at its group base's: the
consumer holds the pin, not the base, and `PinGroupView.same` moving
one to the other is the only real step of the proof.  And the member
index is forced by the NAME (`PinGroupView.name`), which is the point
of the lemma — no positional matching is needed, and none appears in
the statement; the container `ci'` comes out of `PinShapes`'
existential and is identified with the caller's by `Option.some.inj`. -/
theorem ownPinView_of_blocks {env : Env} {m : EnvModel V env}
    {B : ContainerInfo → BlockModel V} (hb : EnvBlocksOf m B)
    {J : Name} {ci : ContainerInfo} (hci : ConLeche.containerInfo? env J = some ci)
    {q : Nat} (hq : q < (B ci).nPins)
    {ci' : ContainerInfo}
    (hci' : ConLeche.containerInfo? env ((B ci).pinAt q).J = some ci') :
    ∃ i, i < (B ci').k ∧
      ((B ci).pinAt q).J = (B ci').memberName i ∧
      ((B ci).pinAt q).nPJ = (B ci').nP ∧
      ((B ci).pinAt q).pps = (B ci').ppsM i ∧
      ∀ ψ : Name → Nat, ((B ci).pinAt q).u ψ = (B ci').uM i (((B ci).pinAt q).ψJ ψ) := by
  obtain ⟨-, pc, -, hsh⟩ := hb J ci hci
  obtain ⟨q₀, kJ, i, ciq, hqe, hi, hciq, hgv, -⟩ := hsh q hq
  obtain rfl := Option.some.inj (hciq.symm.trans hci')
  refine ⟨i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgv.kEq]; exact hi
  · rw [hqe]; exact hgv.name i hi
  · rw [hqe]; exact hgv.pinNP i hi
  · rw [hqe]; exact hgv.pinPps i hi
  · intro ψ
    rw [hqe, (hgv.same i hi ψ).1]
    exact hgv.pinU i hi ψ

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

/-! ## The container's own pins, read back (task #315 M7-3 session 13) -/

/-- **Determinism of a read spine**: `denoteMeta` is a function, so one
list of expressions reads as one list of terms.  (The twin at two
carriers and two environments is `DenoteMetaSpine.eq_of_pointwise`,
`NestedRecWalk.lean`, which this file is below.) -/
theorem DenoteMetaSpine.det {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {dp : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval env φ dp as vs → DenoteMetaSpine acval env φ dp as vs' → vs = vs'
  | _, _, _, .nil, h' => by cases h'; rfl
  | _, _, _, .cons ha h, h' => by
    cases h' with
    | cons ha' h'' => rw [Option.some.inj (ha.symm.trans ha'), DenoteMetaSpine.det h h'']

omit [SetTheory V] in
/-- **THE SYNTACTIC CLAUSE AT A PINS-FREE BLOCK, AGAINST K.43's
`_inv`** (task #315 M7-3 session 14): `ContainerOwnPins.of_noOwn`'s
twin at the field's own shape.  The wiring at the native, mutual and
five pinned basis sites is one line each. -/
theorem ContainerOwnPinsSyn.of_noOwn {env : Env} {d : BlockModel V}
    (hnp : d.nPins = 0)
    (hempty : ∀ (i : Nat) (lvls : List Level) (DsE ps : List Expr), i < d.k →
      ConLeche.containerOwnPinsAt env (d.memberName i) lvls DsE = some ps → ps = []) :
    ContainerOwnPinsSyn (V := V) env d := by
  intro i _cvC _caps lvls DsE ps hi _ _ hps
  refine ⟨fun e he => ?_, fun qK hqK _ => absurd hqK (by rw [hnp]; omega)⟩
  rw [hempty i lvls DsE ps hi hps] at he
  exact nomatch he

/-- **K.43's BRIDGE: A BLOCK WITH NO MIMICS HAS AN EMPTY OWN-PIN
TABLE** (task #315 M7-3 session 15, DESIGN §U.74 (b)).

`blockOwnMimicsOk env first 0` says `first.rec_1` is not a stored
recursor, and `containerOwnPinsAtGo`'s very first step looks that name
up and stops; so the reader returns the empty table at EVERY
instantiation.  `first` is the group's own first member, which is where
the walk starts (`containerOwnPinsAt` reads `ci.members.head?`), and
that is why each route certifies the Bool at exactly its block's first
former.

This is the model-side consequence K.43's plan named ("the bridge from
it to `containerOwnPinsAt envOut C lvls Ds = some []` is a VERIFY
lemma"); it is stated here rather than in `Verify/*` because
`ContainerOwnPinsSyn` — its only consumer — is stated here. -/
theorem containerOwnPinsAt_nil {env : Env} {C : Name} {ci : ContainerInfo}
    {M : ConLeche.ContainerMember}
    (hci : ConLeche.containerInfo? env C = some ci) (hM : ci.members.head? = some M)
    (h : ConLeche.blockOwnMimicsOk env M.name 0 = true)
    (lvls : List Level) (Ds : List Expr) :
    ConLeche.containerOwnPinsAt env C lvls Ds = some [] := by
  obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
  show (do
    let c ← env.find? C
    let .indInfo cvT _ := c | none
    let ci' ← ConLeche.containerInfo? env C
    let first ← ci'.members.head?
    pure (ConLeche.containerOwnPinsAtGo env (first.name.str "rec") cvT.levelParams lvls Ds
      ci'.nP 64 0)) = some []
  rw [hf, hci]
  show (do
    let first ← ci.members.head?
    pure (ConLeche.containerOwnPinsAtGo env (first.name.str "rec") cv.levelParams lvls Ds
      ci.nP 64 0)) = some []
  rw [hM]
  show some (ConLeche.containerOwnPinsAtGo env (M.name.str "rec") cv.levelParams lvls Ds
      ci.nP 64 0) = some []
  refine congrArg some ?_
  simp only [ConLeche.blockOwnMimicsOk, List.range_zero, List.all_nil, Bool.true_and,
    Bool.not_eq_true'] at h
  unfold ConLeche.isRecInfoAt at h
  unfold ConLeche.containerOwnPinsAtGo
  split
  · rename_i cvR mI rP rules hfind
    rw [hfind] at h
    exact nomatch h
  · rfl

omit [SetTheory V] in
/-- **THE PINS-FREE ROUTES' CLAUSE, FROM K.43** (task #315 M7-3
session 15): the native route, the mutual route and the five pinned
basis blocks install no mimic recursor and certify it
(`blockOwnMimicsOk … 0`), and their block model's members all read back
the SAME group — whose first member is the name the Bool was certified
at.  `containerOwnPinsAt_nil` then empties the table at every member
and every instantiation, and `of_noOwn` finishes.

One line per site, as DESIGN §U.69 (b) promised. -/
theorem ContainerOwnPinsSyn.of_noMimics {env : Env} {d : BlockModel V} {first : Name}
    (hnp : d.nPins = 0)
    (hmim : ConLeche.blockOwnMimicsOk env first 0 = true)
    (hgrp : ∀ i, i < d.k → ∃ (ci : ContainerInfo) (M : ConLeche.ContainerMember),
      ConLeche.containerInfo? env (d.memberName i) = some ci ∧
      ci.members.head? = some M ∧ M.name = first) :
    ContainerOwnPinsSyn (V := V) env d := by
  refine ContainerOwnPinsSyn.of_noOwn hnp fun i lvls DsE ps hi hps => ?_
  obtain ⟨ci, M, hci, hM, hname⟩ := hgrp i hi
  rw [containerOwnPinsAt_nil hci hM (by rw [hname]; exact hmim) lvls DsE] at hps
  exact (Option.some.inj hps).symm

/-- **EVERY OWN PIN THE MIMICS SPELL IS ONE OF THE BLOCK MODEL'S
RECORDED PINS, AT THAT INSTANTIATION** (task #315, lane L-E's request,
DESIGN §U.65 (d) — the bridge §U.71 (e) withdrew the "not needed"
claim for): `containerOwnPinsAt` reads a stored container's own pins
off its MIMIC RECURSORS, already instantiated at the level arguments
and components of the pin that names the container, and hands back
`Expr`s; K.41's inversion (`nestedPinRootPairOk_inv`) lands a block's
pin TERM in that list.  `classPin_of_pinCorr`, on the other side, wants
a `PinCorr` at `d.pinAt qK` — the block model's RECORDED pin.  Nothing
in `ContainerModeled`/`BlockAt` relates the two; this is what does.

**The shape, against §U.65 (d).**  Two corrections, both forced by the
tree (DESIGN §U.69 (a)):

1. the components are carried at their READINGS, not by an `Expr`
   rewriting law.  §U.65 (d) spelled the instantiated component as
   `Expr.instSeq Ds 0 (Expr.instantiateLevelParams lpsC lvls x)` over
   the recorded `x ∈ (d.pinAt q).DsE`.  That cannot be right as
   stated: a block model's `DsE` is the pin's components AT THE
   BLOCK'S PARAMETER OPENERS (`PinSyn.DsE`, read at depth `nP` —
   `NestedStageFacts.pinDs`), i.e. already opened at the install's
   free variables, while `containerOwnPinsAt` instantiates the mimic
   recursor's BINDERS; and `Expr.instSeq`'s cut DESCENDS
   (`instSeq (a :: as) t e = instSeq as (t - 1) (e.instantiate1 a t)`),
   so `0` is the innermost binder, not the outermost.  What the
   consumer actually needs of the components is their READINGS — the
   `Ds` clause of `PinCorr` — so the clause states exactly that: the
   spelled pin's arguments READ as the container's recorded components
   read at the instantiated level assignment and instantiated at the
   outer components' readings (`AnnotTerm.instAll Ds 0`, `PinCorr`'s
   own form);
2. the level arguments stay syntactic (`Level.subst` at the
   container's own level parameters, which `env.find?` binds): that is
   `PinCorr`'s `lvls` clause on the nose, and the `psi` clause reaches
   the assignments through `ContainerModeled.pinψ` on both sides
   (`Level.substFn_map_subst`).

**This is NOT the field** (task #315 M7-3 session 14, DESIGN §U.73
(a)): `ContainerModeled.ownPins` must be the SYNTACTIC clause
`ContainerOwnPinsSyn` above, because this one cannot cross
`ContainerModeled.crossEnvP` — its `DenoteMetaSpine` premise is
CONTRAVARIANT (reading monotonicity runs `env₁ → env₂`, and the clause
would have to pull a reading at `env₂` back to `env₁`).  This is the
form the CONSUMER wants, and `ContainerOwnPinsSyn.toReadOf` is the
bridge — UNCONDITIONAL since task #315 M7-3 session 16, DESIGN
§U.75 (a). -/
@[expose] def ContainerOwnPins {env : Env} (m : EnvModel V env) (d : BlockModel V) : Prop :=
  ∀ (i : Nat) (cvC : ConstantVal) (caps : IndCaps) (lvls : List Level)
    (DsE ps : List Expr) (Ds : List AnnotTerm) (ψ : Name → Nat) (dp : Nat),
    i < d.k → env.find? (d.memberName i) = some (.indInfo cvC caps) →
    ConLeche.containerOwnPinsAt env (d.memberName i) lvls DsE = some ps →
    DenoteMetaSpine m.acval env ψ dp DsE Ds →
    (∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true) →
    DsE.length = d.nP →
    (∀ e ∈ ps, ∃ (qK : Nat) (es : List Expr), qK < d.nPins ∧
      e = Expr.mkAppN
        (.const (d.pinAt qK).J ((d.pinAt qK).lvls.map (Level.subst cvC.levelParams lvls))) es ∧
      DenoteMetaSpine m.acval env ψ dp es
        (((d.pinAt qK).Ds (Level.substFn ψ cvC.levelParams lvls)).map (AnnotTerm.instAll Ds 0))) ∧
    (∀ qK, qK < d.nPins → ∃ es : List Expr,
      ps[qK]? = some (Expr.mkAppN
        (.const (d.pinAt qK).J ((d.pinAt qK).lvls.map (Level.subst cvC.levelParams lvls))) es) ∧
      DenoteMetaSpine m.acval env ψ dp es
        (((d.pinAt qK).Ds (Level.substFn ψ cvC.levelParams lvls)).map (AnnotTerm.instAll Ds 0)))

/-- **THE CLAUSE AT A PINS-FREE BLOCK, AGAINST K.43's `_inv`** (task
#315 M7-3 session 13, DESIGN §U.69 (b)): a block model with no pins
carries `ContainerOwnPins` as soon as the container's own-pin table is
EMPTY at the environment the record is stated over — which is exactly
what the queued kernel record `blockOwnMimicsOk` (K.43, `n := 0` at the
native and mutual routes) certifies, through the Verify bridge its plan
names ("`containerOwnPinsAt envOut C lvls Ds = some []`").

§U.68 (a) found the emptiness NOT derivable in the model tier:
`containerOwnPinsAtGo` looks up `Name.appendIndexAfter (C.str "rec") 1`
and only a nested block whose FIRST former is `C` can put a `.recInfo`
there, so excluding it is an environment-history invariant no record
carries.  This theorem is the whole model-side consequence, so the
wiring when K.43 lands is one line per route. -/
theorem ContainerOwnPins.of_noOwn {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hnp : d.nPins = 0)
    (hempty : ∀ (i : Nat) (lvls : List Level) (DsE ps : List Expr), i < d.k →
      ConLeche.containerOwnPinsAt env (d.memberName i) lvls DsE = some ps → ps = []) :
    ContainerOwnPins m d := by
  intro i _cvC _caps lvls DsE ps _Ds _ψ _dp hi _ hps _ _ _
  refine ⟨fun e he => ?_, fun qK hqK => absurd hqK (by rw [hnp]; omega)⟩
  rw [hempty i lvls DsE ps hi hps] at he
  exact nomatch he

/-- **THE BRIDGE'S CORE** (task #315 M7-3 session 13, DESIGN §U.69
(c); split out at lane WIDE's (f3)): from an equality of PIN TERMS —
the block's pin `q` spelled as the container's own pin `qK` at the
root pin's level arguments and components — the correspondence
`PinCorr` at the block's target `D.k + q`, which is
`classPin_of_pinCorr`'s input.  Its two callers differ only in where
the equality comes from: `pinCorr_of_ownPins` reads it off the table
by MEMBERSHIP and hands back an existential `qK`, `pinCorr_of_ownPins_at`
reads it off the table at a GIVEN POSITION and keeps it.

The positional clause is guarded by the components' COUNT, and has to
be: `containerOwnPinsAt` does not check it — `ownPinsStep`'s own guard
`Ds.length == nPr` makes every step answer `[]` instead — so at a
reader asked at the wrong number of components the table is EMPTY and
the position says nothing.  `ContainerOwnPinsSyn` carries the same
guard for the same reason.

This is the Expr-to-`AnnotTerm` half lane L-E named: the `J` and
`lvls` clauses come out of the term equality by `mkAppN`'s inversion at
a constant head, and the `Ds` clause by DETERMINISM of the readings —
the block's own components read as `(D.pinAt q).Ds ψ`
(`NestedStageFacts.pinDs` at the run, `ContainerModeled`'s twin at a
stored container) and the spelled ones as the container's instantiated
at the outer components, and they are ONE list of expressions.  `EA` is
then `targetRead` at a pin (the stored container at the pin's level
assignment and components) with the two assignments identified through
the pins' `pinψ` laws (`Level.substFn_map_subst`) and the carrier's own
`acval_params`.

The index universe and index telescope (`u`, `Ids`) are the container's
at both sides and are NOT this bridge's: they are premises, which lane
L-E discharges from the pins' group views (`PinGroupView.pinU`,
`pinPps`/`pinNP`). -/
theorem pinCorr_of_pinEq {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {ψ : Name → Nat} {dp q qK : Nat} {cvC : ConstantVal}
    {lvlsK : List Level} {es : List Expr} {Ds₀ : List AnnotTerm}
    (hqK : qK < dR.nPins)
    (heq : Expr.mkAppN (.const (D.pinAt q).J (D.pinAt q).lvls) (D.pinAt q).DsE
      = Expr.mkAppN
        (.const (dR.pinAt qK).J ((dR.pinAt qK).lvls.map (Level.subst cvC.levelParams lvlsK))) es)
    (hes : DenoteMetaSpine m.acval env ψ dp es
      (((dR.pinAt qK).Ds (Level.substFn ψ cvC.levelParams lvlsK)).map (AnnotTerm.instAll Ds₀ 0)))
    (hDsD : DenoteMetaSpine m.acval env ψ dp (D.pinAt q).DsE ((D.pinAt q).Ds ψ))
    (hψD : ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (D.pinAt q).J = some (.indInfo cv cp) →
      ∀ ψ' : Name → Nat, (D.pinAt q).ψJ ψ' = Level.substFn ψ' cv.levelParams (D.pinAt q).lvls)
    (hψK : ∀ qK, qK < dR.nPins → ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (dR.pinAt qK).J = some (.indInfo cv cp) →
      (dR.pinAt qK).lvls.length = cv.levelParams.length ∧
      ∀ ψ' : Name → Nat, (dR.pinAt qK).ψJ ψ' = Level.substFn ψ' cv.levelParams (dR.pinAt qK).lvls)
    (hfoundK : ∀ qK, qK < dR.nPins →
      ∃ (cv : ConstantVal) (cp : IndCaps), env.find? (dR.pinAt qK).J = some (.indInfo cv cp))
    (huIds : (D.pinAt q).J = (dR.pinAt qK).J →
      (D.pinAt q).u ψ = (dR.pinAt qK).u (Level.substFn ψ cvC.levelParams lvlsK) ∧
      (D.pinAt q).Ids ψ = (dR.pinAt qK).Ids (Level.substFn ψ cvC.levelParams lvlsK)) :
    PinCorr (D.targetView m.acval ψ) m.acval dR (Level.substFn ψ cvC.levelParams lvlsK)
      Ds₀ cvC.levelParams lvlsK (D.k + q) qK := by
  -- the term equality, inverted at the constant head
  have hhead : (Expr.const (D.pinAt q).J (D.pinAt q).lvls)
      = .const (dR.pinAt qK).J ((dR.pinAt qK).lvls.map (Level.subst cvC.levelParams lvlsK)) := by
    have := congrArg Expr.getAppFn heq
    rwa [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at this
  have hargs : (D.pinAt q).DsE = es := by
    have := congrArg Expr.getAppArgs heq
    rwa [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN,
      show (Expr.const (D.pinAt q).J (D.pinAt q).lvls).getAppArgs = [] from rfl,
      show (Expr.const (dR.pinAt qK).J
          ((dR.pinAt qK).lvls.map (Level.subst cvC.levelParams lvlsK))).getAppArgs = [] from rfl,
      List.nil_append, List.nil_append] at this
  obtain ⟨hJ, hlvls⟩ : (D.pinAt q).J = (dR.pinAt qK).J ∧
      (D.pinAt q).lvls = (dR.pinAt qK).lvls.map (Level.subst cvC.levelParams lvlsK) := by
    exact ⟨congrArg (fun e => match e with | .const n _ => n | _ => .anonymous) hhead,
      congrArg (fun e => match e with | .const _ us => us | _ => []) hhead⟩
  -- the components' READINGS are one list
  have hDs : (D.pinAt q).Ds ψ
      = ((dR.pinAt qK).Ds (Level.substFn ψ cvC.levelParams lvlsK)).map
          (AnnotTerm.instAll Ds₀ 0) :=
    DenoteMetaSpine.det hDsD (hargs ▸ hes)
  -- the two level assignments agree on the container's own parameters
  obtain ⟨cv, cp, hfK⟩ := hfoundK qK hqK
  obtain ⟨hvlen, hlawK⟩ := hψK qK hqK cv cp hfK
  have hpsi : ∀ r ∈ cv.levelParams,
      (D.pinAt q).ψJ ψ r
        = (dR.pinAt qK).ψJ (Level.substFn ψ cvC.levelParams lvlsK) r := by
    intro r hr
    rw [hψD cv cp (by rw [hJ]; exact hfK) ψ, hlvls, Level.substFn_map_subst hvlen hr, hlawK]
  have hacval : m.acval (D.pinAt q).J ((D.pinAt q).ψJ ψ)
      = m.acval (dR.pinAt qK).J
          ((dR.pinAt qK).ψJ (Level.substFn ψ cvC.levelParams lvlsK)) := by
    rw [hJ]
    exact m.acval_params _ _ hfK _ _ hpsi
  have hnk : ¬ D.k + q < D.k := by omega
  have hsub : D.k + q - D.k = q := by omega
  obtain ⟨hu, hIds⟩ := huIds hJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the stored reading at the pin
    show targetRead m.acval D.memberNames D.pins D.nP D.k ψ (D.k + q) = _
    rw [targetRead_of_pin hnk, hsub]
    show AnnotTerm.mkAppN (m.acval (D.pinAt q).J ((D.pinAt q).ψJ ψ)) ((D.pinAt q).Ds ψ) = _
    rw [hacval, hDs]
  · show (D.pinAt (D.k + q - D.k)).Ds ψ = _
    rw [hsub, hDs]
  · show D.uT (D.k + q) ψ = _
    rw [BlockModel.uT_of_pin hnk ψ, hsub, hu]
  · show D.IdsT (D.k + q) ψ = _
    rw [BlockModel.IdsT_of_pin hnk ψ, hsub, hIds]
  · show (if D.k + q < D.k then _ else (D.pinAt (D.k + q - D.k)).J) = _
    rw [if_neg hnk, hsub, hJ]
  · show (if D.k + q < D.k then _ else (D.pinAt (D.k + q - D.k)).lvls) = _
    rw [if_neg hnk, hsub, hlvls]

/-- **THE BRIDGE, at SOME own pin** — `pinCorr_of_pinEq` off the
membership clause of `ContainerOwnPins`.  This is the direction K.41
records: the block's pin `q`, whose recorded TERM sits among the root
container's own pins, IS one of the container's recorded pins.  The own
pin it is, is an existential, which is all this direction ever needed. -/
theorem pinCorr_of_ownPins {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {ψ : Name → Nat} {dp i q : Nat} {cvC : ConstantVal} {caps : IndCaps}
    {lvlsK : List Level} {DsE₀ ps : List Expr} {Ds₀ : List AnnotTerm}
    (hown : ContainerOwnPins m dR)
    (hi : i < dR.k) (hfind : env.find? (dR.memberName i) = some (.indInfo cvC caps))
    (hps : ConLeche.containerOwnPinsAt env (dR.memberName i) lvlsK DsE₀ = some ps)
    (h0 : DenoteMetaSpine m.acval env ψ dp DsE₀ Ds₀)
    (hsc : ∀ a ∈ DsE₀, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hDlen : DsE₀.length = dR.nP)
    (hmem : Expr.mkAppN (.const (D.pinAt q).J (D.pinAt q).lvls) (D.pinAt q).DsE ∈ ps)
    (hDsD : DenoteMetaSpine m.acval env ψ dp (D.pinAt q).DsE ((D.pinAt q).Ds ψ))
    (hψD : ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (D.pinAt q).J = some (.indInfo cv cp) →
      ∀ ψ' : Name → Nat, (D.pinAt q).ψJ ψ' = Level.substFn ψ' cv.levelParams (D.pinAt q).lvls)
    (hψK : ∀ qK, qK < dR.nPins → ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (dR.pinAt qK).J = some (.indInfo cv cp) →
      (dR.pinAt qK).lvls.length = cv.levelParams.length ∧
      ∀ ψ' : Name → Nat, (dR.pinAt qK).ψJ ψ' = Level.substFn ψ' cv.levelParams (dR.pinAt qK).lvls)
    (hfoundK : ∀ qK, qK < dR.nPins →
      ∃ (cv : ConstantVal) (cp : IndCaps), env.find? (dR.pinAt qK).J = some (.indInfo cv cp))
    (huIds : ∀ qK, qK < dR.nPins → (D.pinAt q).J = (dR.pinAt qK).J →
      (D.pinAt q).u ψ = (dR.pinAt qK).u (Level.substFn ψ cvC.levelParams lvlsK) ∧
      (D.pinAt q).Ids ψ = (dR.pinAt qK).Ids (Level.substFn ψ cvC.levelParams lvlsK)) :
    ∃ qK, qK < dR.nPins ∧
      PinCorr (D.targetView m.acval ψ) m.acval dR (Level.substFn ψ cvC.levelParams lvlsK)
        Ds₀ cvC.levelParams lvlsK (D.k + q) qK := by
  obtain ⟨qK, es, hqK, heq, hes⟩ :=
    (hown i cvC caps lvlsK DsE₀ ps Ds₀ ψ dp hi hfind hps h0 hsc hDlen).1 _ hmem
  exact ⟨qK, hqK, pinCorr_of_pinEq hqK heq hes hDsD hψD hψK hfoundK (huIds qK hqK)⟩

/-- **THE BRIDGE, at a GIVEN own pin** (task #315, lane WIDE's (f3)):
`pinCorr_of_pinEq` off the POSITIONAL clause of `ContainerOwnPins`.

This is the direction the wide identification's reindexing needs and the
membership form cannot give: the caller names the container's own pin
`qK` and exhibits the block pin whose recorded term sits at THAT
position of the table, and the conclusion is the correspondence at that
very `qK`.  Its caller is the instance map (K.61), whose value is a
table POSITION and whose consumer indexes by the container's block
model — the two indexings this clause ties together. -/
theorem pinCorr_of_ownPins_at {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {ψ : Name → Nat} {dp i q qK : Nat} {cvC : ConstantVal} {caps : IndCaps}
    {lvlsK : List Level} {DsE₀ ps : List Expr} {Ds₀ : List AnnotTerm}
    (hown : ContainerOwnPins m dR)
    (hi : i < dR.k) (hfind : env.find? (dR.memberName i) = some (.indInfo cvC caps))
    (hps : ConLeche.containerOwnPinsAt env (dR.memberName i) lvlsK DsE₀ = some ps)
    (h0 : DenoteMetaSpine m.acval env ψ dp DsE₀ Ds₀)
    (hqK : qK < dR.nPins) (hDlen : DsE₀.length = dR.nP)
    (hsc : ∀ a ∈ DsE₀, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hat : ps[qK]? = some
      (Expr.mkAppN (.const (D.pinAt q).J (D.pinAt q).lvls) (D.pinAt q).DsE))
    (hDsD : DenoteMetaSpine m.acval env ψ dp (D.pinAt q).DsE ((D.pinAt q).Ds ψ))
    (hψD : ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (D.pinAt q).J = some (.indInfo cv cp) →
      ∀ ψ' : Name → Nat, (D.pinAt q).ψJ ψ' = Level.substFn ψ' cv.levelParams (D.pinAt q).lvls)
    (hψK : ∀ qK, qK < dR.nPins → ∀ (cv : ConstantVal) (cp : IndCaps),
      env.find? (dR.pinAt qK).J = some (.indInfo cv cp) →
      (dR.pinAt qK).lvls.length = cv.levelParams.length ∧
      ∀ ψ' : Name → Nat, (dR.pinAt qK).ψJ ψ' = Level.substFn ψ' cv.levelParams (dR.pinAt qK).lvls)
    (hfoundK : ∀ qK, qK < dR.nPins →
      ∃ (cv : ConstantVal) (cp : IndCaps), env.find? (dR.pinAt qK).J = some (.indInfo cv cp))
    (huIds : (D.pinAt q).J = (dR.pinAt qK).J →
      (D.pinAt q).u ψ = (dR.pinAt qK).u (Level.substFn ψ cvC.levelParams lvlsK) ∧
      (D.pinAt q).Ids ψ = (dR.pinAt qK).Ids (Level.substFn ψ cvC.levelParams lvlsK)) :
    PinCorr (D.targetView m.acval ψ) m.acval dR (Level.substFn ψ cvC.levelParams lvlsK)
      Ds₀ cvC.levelParams lvlsK (D.k + q) qK := by
  obtain ⟨es, hes0, hes⟩ :=
    (hown i cvC caps lvlsK DsE₀ ps Ds₀ ψ dp hi hfind hps h0 hsc hDlen).2 qK hqK
  exact pinCorr_of_pinEq hqK (Option.some.inj (hat.symm.trans hes0)) hes hDsD hψD hψK hfoundK huIds

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
