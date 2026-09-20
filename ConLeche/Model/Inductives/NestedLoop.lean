module

public import ConLeche.Model.Inductives.NestedCore
public import ConLeche.Model.Inductives.NestedStageCtor
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedInv
public section

/-!
# The restored constructors' loop, assembled (task #315, M6 s8)

`NestedCtorsStaged` (the restored constructors' LOOP, `NestedCore.lean`)
discharged modulo two named facts (DESIGN §U.20):

* **`NestedPinsStaged`** — the pins' records (`PinSyn`, one per pin of
  the elimination, `pinsLen`/`pinRec`), the components' readings at the
  prefix model (`pinDs`), and the pin GROUPS (`NestedPinGroup`) at the
  prefix model — s9's subject (K.29 + the strengthened
  `EnvBlockModels`);
* **`NestedReadLaw`** — THE RESTORE READING LAW: per restored
  constructor, its data at the restored domains at the prefix model
  (`NestedCtorRead`: the loop's per-constructor input `NestedCtorInput`,
  the block model's `BlockCtorData` through the nested arm, and the
  domain facts) — the syntactic kits' consumer.

From them the loop `stageNestedMembers` conses every restored
constructor with its AUXILIARY leaf, and `nestedCtorsStaged_of`
assembles `NestedLoopFacts`: the pin records, the extension facts
(`find`, `hde`), the members' leaves kept, the agreement off the
restored names, the reading law crossed to the loop's model
(`BlockCtorData.crossEnv`), the domain facts, and the groups crossed
(`NestedPinGroup.crossEnv`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

section Assembly

variable {F : Nat} {g : Bool} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-! ## The pin groups across an extension -/

/-- **A pin group crosses an extension** (`IsBlockModel.crossEnv`'s
hypotheses): the container's block model, its representation at the
group's members and its typing travel; every other field is
model-free. -/
theorem NestedPinGroup.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {q₀ kJ : Nat} {dJ : BlockModel V}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hmem : ∀ t, t < p.k → (env₁.find? ((D).memberName t)).isSome = true)
    (hpin : ∀ q, q < pinsS.length → (env₁.find? ((D).pinAt q).J).isSome = true)
    (G : PG m₁ q₀ kJ dJ) : PG m₂ q₀ kJ dJ :=
  { inst := G.inst
    seg := G.seg
    reps := G.reps.crossEnv hF hres hag hde
    kpos := G.kpos
    kEq := G.kEq
    rep := fun i hi => by
      obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
      exact ⟨cvT, cvR, mI, rP, rules, hI.crossEnv hF hres hag hde⟩
    typed := fun ψ => (G.typed ψ).crossEnv hag G.reps
    pinsTyped := fun ψ => (G.pinsTyped ψ).crossEnv hag G.reps (G.kEq ▸ G.kpos)
    inj := G.inj
    pinU := G.pinU
    pinNP := G.pinNP
    pinNIdx := G.pinNIdx
    pinPps := G.pinPps
    pinDsLen := G.pinDsLen
    w := G.w
    same := G.same
    lvls := G.lvls
    sameE := G.sameE
    stored := fun i hi => by
      obtain ⟨cvT, caps, hf, hψ⟩ := G.stored i hi
      exact ⟨cvT, caps, hF _ _ (fun _ _ _ _ h => nomatch h) hf, hψ⟩
    idx := G.idx
    ctorCount := G.ctorCount
    ctorsOf := G.ctorsOf
    DsFit := G.DsFit
    shape := fun i hi cvT caps hf ψ ρp hρp i' hi' j hj => by
      have hk : (D).k = p.k := rfl
      obtain ⟨cvT₁, caps₁, hf₁, -⟩ := G.stored i hi
      have hf₂ := hF _ (.indInfo cvT₁ caps₁) (fun _ _ _ _ h => nomatch h) hf₁
      have he := ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hf.symm.trans hf₂))
      rw [he.1]
      refine CopyShapeA.of_acval m₁.acval (fun t ht => congrFun (hag _ (hmem t ht)) ψ)
        (fun q hq => congrFun (hag _ (hpin q hq)) _)
        (fun qK hqK => ?_) (G.reps.tgt_pin_lt (G.kEq ▸ hi') (List.getElem?_eq_getElem hj))
        (G.shape i hi cvT₁ caps₁ hf₁ ψ ρp hρp i' hi' j hj)
      obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
      obtain ⟨cv, caps, hf⟩ := hI.pinsFound qK hqK
      exact congrFun (hag _ (by rw [hf]; rfl)) _
    entry := G.entry
    -- the owner-half tie (task #315 WIDE (3), step 1(a)) is a
    -- `denoteMeta` CONCLUSION at the block's own parameter frame, so it
    -- crosses on `hde` alone: every other object it names — the pins'
    -- records, the container's stored constructor, the own-pin table —
    -- is read at the PRE-BLOCK environment, which does not move.
    ordTgt := fun ψ ρp hsat i' hi' j hj l hl hord hrss hpinT cA bs rr dom lps lpsC hjA hstrip
        hdom i₀ hi₀ ciC Jm hciC hJmC hlpsE Kn usK hfin => by
      obtain ⟨z, hz, htg, hEl, hOT⟩ := G.ordTgt ψ ρp hsat i' hi' j hj l hl hord hrss hpinT cA bs rr
        dom lps lpsC hjA hstrip hdom i₀ hi₀ ciC Jm hciC hJmC hlpsE Kn usK hfin
      refine ⟨z, hz, htg, hEl, fun fs₁ hfs hfit => ?_⟩
      obtain ⟨htl, fb, Ps, hlen, hd⟩ := hOT fs₁ hfs hfit
      exact ⟨htl, fb, Ps, hlen, hde _ _ _ hd⟩ }

/-! ## The two named facts' interfaces -/

/-- **The pins' facts at the prefix model** (`NestedPinsStaged`'s
conclusion): one `PinSyn` per pin of the elimination, whose container,
level arguments and components are the pin's (`pinRec`), whose
components read at the block's parameter depth (`pinDs`), and every pin
in a group (`NestedPinGroup`) — the groups stated at every choice of
the restored data `dsR`/`xFvsR`, which they do not mention. -/
structure NestedPinFacts (st : ElimState) (mp₁ : EnvModelM V μ ENV₁) : Prop where
  pinsLen : pinsS.length = st.pins.length
  pinRec : ∀ (q : Nat) (pin : NestedPin), st.pins[q]? = some pin →
    (pinsS.getD q default).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container (pinsS.getD q default).lvls) (pinsS.getD q default).DsE
  pinDs : ∀ q, q < pinsS.length → ∀ ψ : Name → Nat,
    DenoteMetaSpine mp₁.base2.acval ENV₁ ψ b.nP (pinsS.getD q default).DsE
      ((pinsS.getD q default).Ds ψ)
  /-- **the pins' components are GRADED at the block's parameter frame**
  (task #315 M7-2): `nestedPinsOk`'s own `inferType` runs at the
  block's PARAMETER context, which is the guard a grading needs; the
  nested rule's pin conjunct spends the clause at the recursor's
  padded frame -/
  pinWd : ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V ((((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse) ρ →
    ∀ A ∈ (pinsS.getD q default).Ds ψ, WellDenotedV V ρ A
  /-- the container's level assignment at the pin is the pin's level
  arguments substituted for the container's parameters, and the two
  lists have one length (what `denoteMeta_const` reads at the head
  `.const J lvls`; U-19b's reading law consumes it at `nestEntry`) -/
  pinψ : ∀ q, q < pinsS.length → ∀ (cvT : ConstantVal) (caps : IndCaps),
    (ENV₁).find? (pinsS.getD q default).J = some (.indInfo cvT caps) →
    (pinsS.getD q default).lvls.length = cvT.levelParams.length ∧
    ∀ ψ : Name → Nat, (pinsS.getD q default).ψJ ψ
      = Level.substFn ψ cvT.levelParams (pinsS.getD q default).lvls
  /-- **a pin's parameter count is the one `containerInfo?` reads of
  its container** at the PRE-BLOCK environment (task #315 M7-3
  session 11, DESIGN §U.67 (c) 5): the group's own two facts —
  `NestedPinGroupSyn.pinNP` (the pin's count is its container's block
  model's) and `NestedPinGroupSyn.modeled` (that block model
  represents the container's `containerInfo?` group) — which
  `NestedPinGroupSyn.ofParts` drops, so the record carries the
  composite.  `ContainerModeled.pinNP` is its consumer: the nested
  block's own read-back demands it, at `d.env₀ = env`. -/
  pinNP : ∀ q, q < pinsS.length → ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env (pinsS.getD q default).J = some ci →
    (pinsS.getD q default).nPJ = ci.nP
  /-- the copy's index count is the pin's (the auxiliary block's member
  `p.k + q` is the container member instantiated at the pin; U-19b's
  reading law consumes it at `nestEisLen`) -/
  pinNIdx : ∀ q, q < pinsS.length →
    (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx
  groups : ∀ (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR' : Nat → Nat → List Expr) (q : Nat), q < pinsS.length →
    ∃ (q₀ kJ i : Nat) (dJ : BlockModel V), q = q₀ + i ∧ i < kJ ∧
      NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR') (xFvsR := xFvsR') (pinsS := pinsS)
        mp₁.base2 q₀ kJ dJ
  /-- **the groups with their block model NAMED by the environment
  model's own assignment** (task #315 M7-3 session 12): `groups` keyed
  by the reading `containerInfo?` makes of the pin's container at the
  PRE-BLOCK environment, at `blockOf mp.base2` — the form
  `NestedTailOut.groups` used to assume, and the pins' shapes' own
  (`nestedPinShapes_of` at ONE assignment, DESIGN §U.36 (d)).  The
  construction has it: `NestedPinsRun.groupSyn` instantiates the group
  at `blockOf mp.base2 (baseInfo env st q)` and the pin's own reading
  IS its group's base's (`containerInfo?_eq_of_names` at K.14's two
  agreements), so the field costs the core nothing and the existential
  `groups` above is its projection. -/
  groupsAt : ∀ (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR' : Nat → Nat → List Expr) (q : Nat), q < pinsS.length →
    ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env (pinsS.getD q default).J = some ci →
    ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧
      NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR') (xFvsR := xFvsR') (pinsS := pinsS)
        mp₁.base2 q₀ kJ (blockOf mp.base2 ci)

/-- **THE RESTORE READING LAW at one constructor** (`NestedReadLaw`'s
conclusion, per restored constructor `(ctorsR.getD mm [])[j]? = some c`
of member `mm < k`, at the prefix model): the loop's per-constructor
input — the door, the data at the restored domains `dsR mm j`, the
auxiliary constructor's term-level facts at the auxiliary domains
`dsF (b.ownOffset mm + j)`, their agreement at fitting prefixes, the
fold and the chain facts, everything at the block's one sort
`f₀.s` (`MutualFormersFacts.sEq`); the block model's constructor data
through the nested arm (`BlockCtorFacts`'s third conjunct, verbatim);
and the domain facts (`NestedLoopFacts.domFacts` with the binder
bits). -/
structure NestedCtorRead (mp₁ : EnvModelM V μ ENV₁) (mm j : Nat) (c : ConstantVal × Nat × Nat) :
    Prop where
  input : NestedCtorInput mp₁ F (fms.getD mm default).cvTa.name b.lps b.nP c.2.2
    (fms.getD mm default).nIdx j mm f₀.s (Level.isEquiv f₀.s .zero == some true) b.large c.1
    W (fun ψ => f₀.s.eval ψ) (blkIdss b ppsF)
    (fun ψ => (mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm))
    (fun ψ => (blkEss b ctorsA ppsF W esF ψ).drop (b.ownOffset mm)) (ppsF mm)
    (dsF (b.ownOffset mm + j)) (dsR mm j) (esF (b.ownOffset mm + j)) (idxF (b.ownOffset mm + j))
    (srcsF (b.ownOffset mm + j))
  data : BlockCtorData mp₁.base2 (D).env₀ ((D).memberName mm)
    (fun i => (D).memberName ((D).tgts mm j i)) (fun i => (D).nIdxAt ((D).tgts mm j i))
    (fun i => (D).nestOf mm j i) (D).pinAt b.lps c.1 (D).nP c.2.2 ((D).nIdxAt mm) (D).resSort
    (D).isProp (D).large ((D).idxF mm j) ((D).dsF mm j) ((D).esF mm j) ((D).srcsF mm j)
    ((D).ksF mm j) ((D).fvsPF mm j) ((D).xFvsF mm j) ((D).xrestF mm j) ((D).eissF mm j)
    ((D).tssF mm j)
  dom : ∀ ψ : Name → Nat,
    (dsR mm j ψ).length = (dsF (b.ownOffset mm + j) ψ).length ∧
    (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP ∧
    (∀ i, ((D).nestOf mm j i = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) →
      (dsR mm j ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default)
  /-- **A NESTED FINITARY FIELD'S PARAMETER ARGUMENTS ARE THE RESTORED
  PIN'S** (task #315 PINF): `BlockOpened.nestF` keeps the head, the
  argument count and the resolution PAST `nPJ` and drops the parameter
  part, and nothing below recovers it — so the one clause of
  `ContainerModeled` that speaks about it
  (`nestArgsMention`) has to be carried from here, where
  `RestoredField`'s own pin case still has it.

  Carried as the EQUALITY against the restored pin — the pin closed
  over the parameters and reopened at this constructor's openers —
  rather than as the mention the consumer wants, because the mention
  step needs K.30 (`pinsScoped`) and K.44 (`nestedPinMentionOk`),
  neither of which reaches this tier. -/
  pinArgs : ∀ (l : Nat) (x pin : Expr) (q : Nat),
    ((D).xFvsF mm j)[l]? = some x →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    x.fvarTypeD.getAppArgs.take ((D).pinAt q).nPJ
      = (Expr.instSeq ((D).fvsPF mm j) ((D).nP - 1)
          (Expr.abstractRange pin 0 p.nP 0)).getAppArgs
  /-- **AND THE SAME ON THE ABSTRACT DOMAIN** (task #315 PINF): the
  clause above is on the OPENED spine, which is the side the reading
  law works on.  K.60's guard reads the CLOSED one — the container's
  stored constructor STRIPPED — and the transport between the two runs
  only abstract ⟹ opened (an opener's annotation can carry a mention
  the abstract domain does not have), so the pin case is carried on
  BOTH sides from here.

  The lift is the abstract twin of the opened form's reopening: the
  pin lives in the parameter context, so under `l` field binders it
  stands lifted by `l`, and the depth is stated as that DEFINITE `l`:
  the mention the `nestArgsMentionAbs` consumer wants survives any
  lift, but the wide identification's consumer is an EQUATION under
  `instantiateList … l`, which does not.  Carried at the SPINE — the
  whole domain as the lifted pin applied to a remainder, with the
  arity of the pin's own argument list beside it — so that the
  `getAppArgs.take` form is one `List.take_left'` away (task #315 WIDE
  (1′)). -/
  pinArgsAbs : ∀ (l : Nat) (bs : List (Expr × BinderMeta)) (r : Expr)
      (dom : Expr × BinderMeta) (pin : Expr) (q : Nat),
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0).getAppArgs.length
          = ((D).pinAt q).nPJ ∧
      dom.1 = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0) rest
  /-- **AND THE SAME AT A REFLEXIVE NESTED FIELD** (task #315 K.63):
  `pinArgsAbs` one `Π`-tower down.  A reflexive nested field's stored
  domain is a telescope whose BODY carries the pin, which is the shape
  K.63's guard reads (`stripDomPis`), and the two arms are disjoint by
  construction — a `Π`'s `getAppFn` is never a `.const`, so K.60 claims
  nothing here and K.63 claims nothing at a finitary field.

  At `pinArgsAbs`' strength: the SPINE, with the pin lifted past both
  towers — the field binders (`l`) and the domain's own (`dep`) — and
  the pin's argument count beside it. -/
  pinArgsAbsRefl : ∀ (l : Nat) (bs : List (Expr × BinderMeta)) (r : Expr)
      (dom : Expr × BinderMeta) (pin : Expr) (q : Nat),
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .reflexive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
          (l + ConLeche.domPiDepth dom.1) 0).getAppArgs.length = ((D).pinAt q).nPJ ∧
      ConLeche.stripDomPis dom.1
        = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
            (l + ConLeche.domPiDepth dom.1) 0) rest
  /-- **THE RESTORED CONSTRUCTOR'S STORED TYPE HAS ITS `.proj` SLOTS AT
  THE MEMBERS' PREFIX ENVIRONMENT** (task #315 PINF): the front door's
  own `slots`, kept because it is the only place the fact is TRUE.
  `ProjSlotsOk` is not antitone in the environment — its `.proj` node is
  a `findProj?` `.isSome` — so `ConstWF` at a later environment cannot
  supply it, and at ENV₁ the block's members are `.indInfo` with no
  projection table, which is what makes it say
  "no `.proj` node names a member".

  Carried raw rather than as the `NoProjAt` the consumer wants:
  turning the empty slot into a `NoProjAt` needs `ProjOkT` at the
  pre-block environment and the members' freshness, and those meet the
  clause at `nestedContainerModeled`. -/
  ctorSlots : ConLeche.Expr.ProjSlotsOk ENV₁ c.1.type

end Assembly

/-! ## The named facts -/

/-- **The pins' records and groups at the prefix model** (NAMED, DESIGN
§U.20; consumer `nestedCtorsStaged_of`): at the run's conjuncts through
`restoreCtors` and the prefix formers' model, one `PinSyn` per pin with
its container/levels/components the elimination's, the components read
at the block's parameter depth, and every pin in a group
(`NestedPinFacts`).  s9's subject: K.29 (`nestedGroupsOk`) for the
groups' segments and the strengthened `EnvBlockModels` for one
container block model per group. -/
@[expose] def NestedPinsStaged (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀ →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    -- THE PINS' SCOPE (K.30): every pin's free variables are the first
    -- former's openers, annotation included, and no loose bvar
    ConLeche.pinsScoped p.nP st = true →
    -- **THE COPIES' TARGETS** (K.32, task #315 L-E, DESIGN §U.64): a
    -- copy's group-internal recursive field points at the copy of the
    -- container member its own field points at, which the copies'
    -- identities read on the `ordF` arm (lane L-B's `NestedPinsShape`)
    ConLeche.nestedCopyTargetsOk env p b st stored = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    ConLeche.nestedPinRankOk env p b st stored = true →
    -- **THE POSITIVITY NORMALISATION ON THE MINTED COPY** (K.42, task
    -- #315, lane L-B): at every ORDINARY field of every copy's
    -- constructor, the stored domain IS the positivity normalisation of
    -- the MINTED one, which the copies' identities read on the
    -- `ordF`-LEFT arm (lane L-B's `NestedPinsShape`)
    (∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2)) →
    -- **THE SAME WALK AT A PIN TARGET, REWRITTEN** (K.51, task #315,
    -- lane L-B): a copy field whose target is a MIMIC has a stored
    -- domain headed by that mimic, so the normalisation of the MINTED
    -- domain is rewritten before the comparison — which lets the
    -- `ordF`-RIGHT arm read a pin target off the minted domain with no
    -- `pinLeaf` anywhere (lane L-B's `NestedPinsShape`)
    (∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
      (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored
          (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true) →
    -- K.60: a container's nested field lands on a block pin
    ConLeche.nestedCopyPinFieldsOk env p b st stored = true →
    -- K.63: the same, one `Π`-tower down — a container's REFLEXIVE
    -- nested field lands on a block pin, where K.60's guard (a `.const`
    -- head on the stored domain) claims nothing
    ConLeche.nestedCopyReflFieldsOk env p b st stored = true →
    -- K.61: the container instance map — a pin's container's own pins,
    -- instantiated at that pin's levels and components, ARE pins of the
    -- block, and a copy's field sitting at one of those own pins records
    -- the map's value as its target (the wide identification's σ)
    ConLeche.nestedInstMapOk env p b st stored = true →
    -- K.62: a rewritten ORDINARY field's target is OUTSIDE that map's
    -- image (the wide identification's `houtσ`)
    ConLeche.nestedOrdOutsideOk env p b st stored = true →
    -- K.67: and it IS the owning container's own class, imaged — the
    -- positive twin at the same guard, which the wide identification's
    -- PIN half needs where `houtσ` only says the target is outside
    ConLeche.nestedOrdTargetOk env p b st stored = true →
    -- K.68: and it is THIS block's own class, by its own recomputation
    -- — K.67's self-relative twin, which the CONTAINER's side of the
    -- wide correspondence is built from
    ConLeche.nestedOrdSelfTargetOk env p b st stored = true →
    -- K.69: and its DOMAIN is the owner's, one substitution apart,
    -- under the guard that the OWNER's copy fired
    ConLeche.nestedOrdNormOk μ env p b st stored = true →
    -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the prefix
    -- formers' environment
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok () →
    -- **THE PINS' CONSTANTS RESOLVE** (K.64): at that same environment
    -- — the guard a container's pins' components' READINGS need to
    -- cross a later install's projection table
    ConLeche.pinsResolve (ConLeche.consMutualFormers (fms.take p.k) env) st.pins = true →
    -- the auxiliary block's formers' stage, at the scratch run
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
      = .ok (ConLeche.consMutualFormers fms env, fms) →
    MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF →
    b.k = p.k + st.pins.length →
    ConLeche.mutualCtorsGrouped b.ctors = true →
    b.blockNames.Nodup →
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
      = .ok (ctorsA, sortss) →
    -- the prefix formers' model: the members' leaves the auxiliary
    -- block's, agreeing with the pre-block model off the members,
    -- the members stored with their data
    (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t) →
    (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n) →
    (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (ConLeche.consMutualFormers (fms.take p.k) env).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
      FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)) →
    -- the restored constructors, checked at the prefix environment
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ∃ pinsS : List PinSyn,
      NestedPinFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁'

/-- **THE RESTORE READING LAW** (NAMED, DESIGN §U.20; consumer
`nestedCtorsStaged_of`): given the pins' facts at the prefix model,
the restored domains `dsR` and opened field variables `xFvsR` exist
such that every restored constructor's data at the prefix model is
`NestedCtorRead`: the door's `CtorDataI` at the restored domains, the
auxiliary constructor's term-level facts at the auxiliary domains and
their agreement at fitting prefixes (the pin identification
`nestedIdent_of` at the nested entries), and the block model's
`BlockCtorData` through the nested arm.  The syntactic kits'
consumer (`restoreNested_opened`, the `restoreTbl` lookups, the
annotation erasure). -/
@[expose] def NestedReadLaw (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀ →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    -- the auxiliary block's formers' stage, at the scratch run
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
      = .ok (ConLeche.consMutualFormers fms env, fms) →
    MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF →
    b.k = p.k + st.pins.length →
    ConLeche.mutualCtorsGrouped b.ctors = true →
    b.blockNames.Nodup →
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
      = .ok (ctorsA, sortss) →
    -- the prefix formers' model: the members' leaves the auxiliary
    -- block's, agreeing with the pre-block model off the members,
    -- the members stored with their data
    (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t) →
    (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n) →
    (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (ConLeche.consMutualFormers (fms.take p.k) env).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
      FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)) →
    -- the restored constructors, checked at the prefix environment
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ∀ pinsS : List PinSyn,
      NestedPinFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁' →
      ∃ (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
        (xFvsR : Nat → Nat → List Expr),
        ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
          (ctorsR.getD mm [])[j]? = some c →
          NestedCtorRead (V := V) (F := F) (p := p) (b := b) (fms := fms) (f₀ := f₀)
            (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W)
            (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
            (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR)
            (xFvsR := xFvsR) (pinsS := pinsS) mp₁' mm j c


/-! ## The consumer, at the section's data -/

section Consumer

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- **`NestedLoopFacts` from the two named facts**, at the section's data. -/
theorem nestedLoopFacts_of (hpins : NestedPinsStaged V μ F) (hread : NestedReadLaw V μ F)
    (hμ : μ.verifiedChecks = true) (hE : ConLeche.EtaFamiliesClosed env) {st : ElimState}
    {envAux : Env} {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
    (mp₁' : EnvModelM V μ ENV₁)
    (hPM : PinsModeled mp.base2 st.pins)
    (h0 : (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true)
    (h1 : uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true)
    (hfA : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA)
    (hcA : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hcount : st.pins.length = p.numNested)
    (hfresh : ConLeche.copiesFresh env p.k st = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hb : ConLeche.auxBlock p st = some b)
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hclosed : ConLeche.pinsClosed p.nP st.pins = true)
    (hpinsAux : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins
      = .ok ())
    (hcaps : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hsrc : ConLeche.nestedCopySrcOk env p st = true)
    (hgrp : ConLeche.nestedGroupsOk env p st = true)
    (hsc : ConLeche.pinsScoped p.nP st = true)
    (hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true)
    (hkinds : ConLeche.nestedPinKindsOk p b st stored = true)
    (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    (hK42 : ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2))
    (hK51 : ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
      (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored
          (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true)
    (hK60 : ConLeche.nestedCopyPinFieldsOk env p b st stored = true)
    (hK63 : ConLeche.nestedCopyReflFieldsOk env p b st stored = true)
    (hK61 : ConLeche.nestedInstMapOk env p b st stored = true)
    (hK62 : ConLeche.nestedOrdOutsideOk env p b st stored = true)
    (hK67 : ConLeche.nestedOrdTargetOk env p b st stored = true)
    (hK68 : ConLeche.nestedOrdSelfTargetOk env p b st stored = true)
    (hK69 : ConLeche.nestedOrdNormOk μ env p b st stored = true)
    (hpins₁ : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) ENV₁ p.nP st.pins = .ok ())
    (hK64 : ConLeche.pinsResolve (ENV₁) st.pins = true)
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
      = .ok (ConLeche.consMutualFormers fms env, fms))
    (h : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + st.pins.length)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hnd : b.blockNames.Nodup)
    (hctorsA : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
      = .ok (ctorsA, sortss))
    (hleafM' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    (hoff' : ∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n)
    (hfind' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (ENV₁).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
      FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t))
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR) :
    ∃ (mp₂ : EnvModelM V μ ENV₂)
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (xFvsR : Nat → Nat → List Expr) (pinsS : List PinSyn),
      NestedLoopFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) st mp₁' mp₂ := by
  obtain ⟨pinsS, PF⟩ := hpins hμ mp hE p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF
    esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux
    hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hK42 hK51 hK60 hK63 hK61 hK62 hK67 hK68 hK69 hpins₁ hK64 hformers h hbk h3
    hnd
    hctorsA hleafM' hoff' hfind' hctors
  obtain ⟨dsR, xFvsR, hR⟩ := hread hμ mp hE p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF
    esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux
    hstored hclosed hpinsAux hcaps hsrc hgrp hkinds hformers h hbk h3 hnd hctorsA hleafM' hoff' hfind'
    hctors pinsS PF
  -- the restored constructors, positionally
  have hlenS : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  obtain ⟨hlenR, hposR⟩ := ConLeche.mapM_except_inv hctors
  have hlenT : (stored.take p.k).length = p.k := by
    rw [List.length_take, hlenS, hbk]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hmemR : ∀ mm, mm < p.k → ∃ (a : AuxStored) (cs : List (ConstantVal × Nat × Nat)),
      stored[mm]? = some a ∧ ctorsR[mm]? = some cs ∧
      ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps a.ctors
        = .ok cs := by
    intro mm hmm
    obtain ⟨a, cs, ha, hcs, hrun⟩ := hposR mm (by rw [hlenT]; exact hmm)
    rw [List.getElem?_take_of_lt hmm] at ha
    exact ⟨a, cs, ha, hcs, hrun⟩
  have hmmk : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (ctorsR.getD mm [])[j]? = some c →
      mm < p.k := by
    intro mm j c hc
    rcases Nat.lt_or_ge mm p.k with hlt | hge
    · exact hlt
    · have hnone : ctorsR[mm]? = none := List.getElem?_eq_none (by rw [hlenR, hlenT]; exact hge)
      rw [List.getD_eq_getElem?_getD, hnone] at hc
      simp at hc
  -- the auxiliary constructor of a restored one
  have hauxC : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
      (ctorsR.getD mm [])[j]? = some c →
      ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 := by
    intro mm j c hmm hc
    obtain ⟨a, cs, ha, hcs, hrun⟩ := hmemR mm hmm
    rw [List.getD_eq_getElem?_getD, hcs, Option.getD_some] at hc
    have hjl : j < a.ctors.length := by
      rw [← (ConLeche.restoreCtors_id hrun).1]; exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[j]? = some c₀ := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨ty, -, hco⟩ := (ConLeche.restoreCtors_id hrun).2 j c₀ c hc₀ hc
    obtain ⟨cA, hcA', -, -, hnF⟩ :=
      (ConLeche.auxStored_ctor_eq haux hformers hctorsA h3 hstored ha).2 j c₀ hc₀
    exact ⟨cA, hcA', by rw [hco]; exact hnF⟩
  -- the names: distinct, and none found at the prefix environment
  have hndC : (ctorsA.map (·.1.name)) = b.ctors.map (·.cv.name) := h.namesC
  have hndR : (ctorsR.flatten.map (·.1.name)).Nodup :=
    ConLeche.restoredCtors_nodup haux hformers hctorsA h3 hstored hctors hnd hndC
  have hnPR : ∀ c ∈ ctorsR.flatten, c.2.1 = b.nP :=
    ConLeche.restoredCtors_nP haux hformers hctorsA h3 hstored hctors
  have hneR : ∀ n : Name, ((ENV₁).find? n).isSome = true → ∀ c ∈ ctorsR.flatten, n ≠ c.1.name := by
    intro n hn c hc heq
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hcs
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcin
    have hc' : (ctorsR.getD mm [])[j]? = some c := by
      rw [List.getD_eq_getElem?_getD, hmm]; exact hj
    have := (hR mm j c (hmmk mm j c hc') hc').input.door.fresh
    rw [heq, this] at hn
    exact nomatch hn
  have hkle : p.k ≤ fms.length := by rw [h.lenFms, hbk]; exact Nat.le_add_right _ _
  have hE₁ : ConLeche.EtaFamiliesClosed (ENV₁) :=
    ConLeche.Semantics.EtaFamiliesClosed.ofFreshExt hE
      (ConLeche.Semantics.consMutualFormers_freshExt fun f hf => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
        have ht' : t < p.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1
          rw [List.length_take] at this
          omega
        rw [List.getElem?_take_of_lt ht'] at ht
        exact h.fresh t f ht)
  -- the loop
  obtain ⟨mp₂, -, hF₂, hde₂, hag₂, hcons₂⟩ :=
    stageNestedMembers (V := V) (μ := μ) (F := F)
      (Tof := fun mm => (fms.getD mm default).cvTa.name)
      (nIdxOf := fun mm => (fms.getD mm default).nIdx) (resSortOf := fun _ => f₀.s)
      (Idss := blkIdss b ppsF)
      (FssROf := fun mm ψ => (mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm))
      (EssOf := fun mm ψ => (blkEss b ctorsA ppsF W esF ψ).drop (b.ownOffset mm))
      (ppsOf := ppsF) (dsAOf := fun mm j => dsF (b.ownOffset mm + j)) (dsROf := dsR)
      (EsOf := fun mm j => esF (b.ownOffset mm + j)) (idxOf := fun mm j => idxF (b.ownOffset mm + j))
      (srcsOf := fun mm j => srcsF (b.ownOffset mm + j)) (W := W) (w := fun ψ => f₀.s.eval ψ)
      (lps := b.lps) (nP := b.nP) (isProp := (Level.isEquiv f₀.s .zero == some true))
      (large := b.large) mp₁' hndR hnPR (fun mm j c hc => (hR mm j c (hmmk mm j c hc) hc).input) hE₁
  have hagE : ∀ n : Name, ((ENV₁).find? n).isSome = true → mp₂.base2.acval n = mp₁'.base2.acval n :=
    fun n hn => hag₂ n (hneR n hn)
  have hFne : ∀ (n : Name) (ci : ConstantInfo), (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (ENV₁).find? n = some ci → (ENV₂).find? n = some ci := fun _ _ _ hf => hF₂ hf
  have hres : ∀ e : Expr, e.constsResolve (ENV₁) = true → e.constsResolve (ENV₂) = true :=
    constsResolve_of_findPreserved hF₂
  have hName : ∀ (t : Nat), t < p.k → (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).memberName t = (fms.getD t default).cvTa.name := by
    intro t ht
    show ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht,
      fms_get (Nat.lt_of_lt_of_le ht hkle)]
    rfl
  have hfoundM : ∀ t, t < p.k → ((ENV₁).find? ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).memberName t)).isSome = true := by
    intro t ht
    rw [hName t ht, (hfind' t _ ht (fms_get (Nat.lt_of_lt_of_le ht hkle))).1]
    rfl
  have hfoundP : ∀ q, q < pinsS.length → ((ENV₁).find? ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt q).J).isSome = true := by
    intro q' hq'
    obtain ⟨q₀', kJ', i', dJ', hqe', hi', G'⟩ := PF.groups dsR xFvsR q' hq'
    obtain ⟨cv, caps, hf⟩ := G'.found hi'
    rw [hqe', hf]
    rfl
  refine ⟨mp₂, dsR, xFvsR, pinsS,
    { pinsLen := PF.pinsLen, pinRec := PF.pinRec, pinNP := PF.pinNP
      pinDs := fun q hq ψ => DenoteMetaSpine.transfer (fun e _ h => hde₂ ψ b.nP e h) (PF.pinDs q hq ψ)
      pinWd := PF.pinWd
      find := hF₂, pinψ := PF.pinψ, pinNIdx := PF.pinNIdx, hde := hde₂
      leafKeep := ?_, agreeC := hag₂, ctorFacts := ?_, domFacts := ?_, groups := ?_
      groupsAt := ?_
      pinArgs := fun mm j l x pin q hmm hj hx hpinE hn hk => by
        obtain ⟨c, hc⟩ : ∃ c, (ctorsR.getD mm [])[j]? = some c := ⟨_, List.getElem?_eq_getElem hj⟩
        exact (hR mm j c hmm hc).pinArgs l x pin q hx hpinE hn hk
      pinArgsAbs := fun mm j l c bs r dom pin q hmm hc hs hd hpinE hn hk =>
        (hR mm j c hmm hc).pinArgsAbs l bs r dom pin q hs hd hpinE hn hk
      pinArgsAbsRefl := fun mm j l c bs r dom pin q hmm hc hs hd hpinE hn hk =>
        (hR mm j c hmm hc).pinArgsAbsRefl l bs r dom pin q hs hd hpinE hn hk
      ctorSlots := fun mm j c hmm hc => (hR mm j c hmm hc).ctorSlots }⟩
  · -- the members' leaves
    intro t f ht hft
    exact hag₂ f.cvTa.name (hneR _ (by rw [(hfind' t f ht hft).1]; rfl))
  · -- the restored constructors: the reading law crossed
    intro mm j c hmm hc
    have R := hR mm j c hmm hc
    obtain ⟨cA, hcA, hnF⟩ := hauxC mm j c hmm hc
    obtain ⟨hrec, hleaf⟩ := hcons₂ mm j c hc
    refine ⟨cA, hcA, hnF, fun ψ => hleaf ψ, fun e he => hres e (R.input.idxRes e he), hrec,
      R.input.lpsC, ?_⟩
    refine BlockCtorData.crossEnv hagE hde₂ (hfoundM mm hmm) ?_ ?_ R.data
    · -- a member target is stored
      intro i _ hn
      have hlt : (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k := by
        rcases Nat.lt_or_ge ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i) (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k with hlt | hge
        · exact hlt
        · rw [(nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).nestOf_some (Nat.not_lt.mpr hge)] at hn
          exact nomatch hn
      exact hfoundM _ hlt
    · -- a pin's container is stored
      intro i q hi hq
      have hJl : b.ownOffset mm + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
      have hnlt : ¬ (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k := by
        intro hlt
        rw [(nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).nestOf_none hlt] at hq
        exact nomatch hq
      rw [(nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).nestOf_some hnlt] at hq
      obtain rfl := Option.some.inj hq
      have htgt : (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i < p.k + pinsS.length := by
        show tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k + pinsS.length
        rw [PF.pinsLen, ← hbk, ← h.lenFms]
        exact (h.ksJ _ _ hcA).2.2 i
      have hk : (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k = p.k := rfl
      rw [hk] at hnlt
      have hqlt : (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i - p.k < pinsS.length := by omega
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := PF.groups dsR xFvsR _ hqlt
      obtain ⟨cv, caps, hf⟩ := G.found hi'
      show ((ENV₁).find? ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).tgts mm j i - (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k)).J).isSome = true
      rw [hk, hqe, hf]
      rfl
  · -- the domain facts
    intro mm j ψ hmm hj
    obtain ⟨c, hc⟩ : ∃ c, (ctorsR.getD mm [])[j]? = some c := ⟨_, List.getElem?_eq_getElem hj⟩
    exact (hR mm j c hmm hc).dom ψ
  · -- the groups, crossed
    intro q hq
    obtain ⟨q₀, kJ, i, dJ, hqe, hi, G⟩ := PF.groups dsR xFvsR q hq
    exact ⟨q₀, kJ, i, dJ, hqe, hi, G.crossEnv hFne hres hagE hde₂ hfoundM hfoundP⟩
  · -- the groups at the container's reading, crossed the same way
    -- (task #315 M7-3 session 12)
    intro q hq ci hci
    obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := PF.groupsAt dsR xFvsR q hq ci hci
    exact ⟨q₀, kJ, i, hqe, hi, G.crossEnv hFne hres hagE hde₂ hfoundM hfoundP⟩

end Consumer

/-- **The restored constructors' loop, modulo the pins' facts and the
reading law**: the pins' records and groups (`NestedPinsStaged`) and
the per-constructor reading law (`NestedReadLaw`) at the prefix
model; the loop `stageNestedMembers` conses every restored constructor
with its auxiliary leaf; the loop's outputs are `NestedLoopFacts` —
the reading law and the groups crossed to the loop's model. -/
theorem nestedCtorsStaged_of {F : Nat} (hpins : NestedPinsStaged V μ F)
    (hread : NestedReadLaw V μ F) : NestedCtorsStaged V μ F :=
  fun hμ _ mp hE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mp₁' hPM h0 h1 hfA hcA helim
    hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hK42
    hK51 hK60 hK63 hK61 hK62 hK67 hK68 hK69 hpins₁ hformers h hbk h3 hnd hctorsA hleafM' hoff' hfind' hctors =>
  nestedLoopFacts_of hpins hread hμ hE (mp := mp) mp₁' hPM h0 h1 hfA hcA helim hcount hfresh hcont
    hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hK42 hK51 hK60 hK63 hK61 hK62 hK67 hK68 hK69 hpins₁ hformers h
    hbk h3 hnd hctorsA hleafM' hoff' hfind' hctors

end ConLeche.Model
