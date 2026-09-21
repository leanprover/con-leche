module

import ConLeche.Model.Inductives.ContainerCross
import ConLeche.Verify.Inductives.NestedRootLabel
public import ConLeche.Model.Inductives.NestedPinLeafAll
public section

/-!
# Step (4)'s two residues that are NOT ordering facts (task #315 WIDE (f3))

`nestedPinsLe_of_wide`'s per-instance step (`nestedPinWideStep`,
`NestedPinsLeInd.lean`) is an induction over the container INSTANCES,
and the induction's hypothesis reaches the pins of OTHER instances
only.  Two of the identification's inputs LOOK as though they needed
more than that, and this module is where the reading that says they do
not is proved:

* **`hent`** — the copies' entries.  `CopyEntryOut` is asked at every
  copy-recursive field whose target leaves the mint GROUP, and the
  copies of the container's OWN pins leave the group while staying
  inside the INSTANCE.  The wide route spends the entries only through
  `CopyEntryOut.ord`, and `CopyEntryOrd`'s guard is the container's
  ORDINARY fields — so the producer never visits the `pinF` arm and
  never asks `S` at an in-instance target.  `nestedPinsEntryOrd_at`
  below is that producer, `nestedPinsEntry_at`'s ordinary half with
  the rank induction's own scope `S` carried instead of the
  unconditional identity.
* **`hdom₁`'s CONTAINER-RECURSIVE ARM** — `hdom₁rec`, asked at
  `nestedPinPairAt_pinσ`.  At a field the container calls recursive the
  two copies' slots are ONE slot up to the family
  (`CopyCtorShape.slot_container`, `copyTarget_u`,
  `slotSet_congr_below`) and the two families are EQUAL by the class
  equation, so the arm is the OWNER's bound `hdom₂` read on the other
  side.  `copyDomRec_via` below is that reading; the ordering it
  spends is the one `hdom₂`'s own producer (`dom₂_of_run`) already
  spends, namely `hY`/`hYC` at the OWNER, and no `S` and no `TupleLe`
  at the group's own pins.

The entry producer IS consumed: `nestedPinWideStep` no longer takes
`hent` at all, and builds it here from `hIH`/`hPfGroup` and `hout`.
`nestedPinDomRec_of_dom₂` is NOT: `hdom₁rec` is still a named
hypothesis of `nestedPinPairAt_pinσ`, in a file this module does not
own, and the discharge there is the merge session's one `exact`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps ContainerInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The rank induction's instance label and scope -/

/-- **THE INSTANCE LABEL the induction measures**, named once: K.52's
own list, which `nestedPinsLe_of_rank` reads off the run
(`nestedPinInstOf` = the connected-component label of the OWN-reference
edges `nestedPinEdges`, `Kernel/Inductives/NestedInstall.lean`).  The
RANK (`nestedPinRankOf`) is the well-founded measure; the label is what
"the same instance" means in the step's hypothesis. -/
abbrev instLabel (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) (q : Nat) : Nat :=
  (ConLeche.nestedPinInstOf env p b st stored).getD q 0

/-- **THE RANK INDUCTION'S SCOPE AT A PIN `q`** (task #315 WIDE (f5),
lane DOM): the pins `q'` its hypothesis reaches — an edge from a pin of
`q`'s OWN instance, landing in ANOTHER instance.  `nestedPinsLe_of_wide`
hands exactly this as `hIHeq`; naming it lets the step's `hIH` and the
producer of its `hout` speak of one predicate. -/
abbrev NestedOutScope (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) (edges : List (Nat × Nat × Bool)) (n q q' : Nat) : Prop :=
  ∃ q₀', q₀' < n ∧ instLabel env p b st stored q₀' = instLabel env p b st stored q ∧
    (∃ own : Bool, (q₀', q', own) ∈ edges) ∧
    instLabel env p b st stored q' ≠ instLabel env p b st stored q

/-! ## `hdom₁`'s container-recursive arm is the other side's bound -/

/-- **THE CONTAINER-RECURSIVE SLOT BOUND TRAVELS BETWEEN THE TWO
COPIES** (task #315 WIDE (f3), lane DOM): at a field the container `dK`
calls RECURSIVE, side 1's slot is inside `dK`'s real field domain as
soon as side 2's is — no ordering fact of side 1's own is spent.

Three statements do it and all three are `copyTransfer_via_pin`'s own
(`NestedPinLeafAll.lean`, the container-recursive branch of its walk,
read in the other direction):

* `CopyCtorShape.slot_container` rewrites EITHER copy's slot into the
  CONTAINER's `tlss`/`Eiss` at that copy's frame, and `copyTarget_u`
  equates the two copies' target universes — so after the rewrite the
  two slots differ only in the FRAME and in the FAMILY;
* `slotSet_congr_below` moves the container's data between the two
  frames, which agree below the parameter depth (`hρ`);
* `hrel` — the two families at a container-recursive field are EQUAL.
  On the wide route side 2's tuple is side 1's read through the
  instance map (`X₂ = X₁ ∘ σ`), so this is `congrArg X₁` of the class
  equation `recσ_of_run` already produces.

The container's own field domain is ONE set at either frame
(`interp_congr_below` over `IsBlockModel.Fss_below`), which is what
closes the two ends. -/
theorem copyDomRec_via {m : EnvModel V env} {dK : BlockModel V}
    {acval : Name → (Name → Nat) → AnnotTerm}
    {TV₁ TV₂ : TargetView V} {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm}
    {lpsK : List Name} {lvls₁ lvls₂ : List Level}
    {tg₁ tg₂ : Nat → Nat} {tls₁ tls₂ : List (List (Nat × Nat × AnnotTerm))}
    {Eis₁ Eis₂ : List (List AnnotTerm)} {ρ₁ ρ₂ : Nat → V} {base₁ base₂ kK i j : Nat}
    {Fs₁ Fs₂ Es₁ Es₂ : List AnnotTerm} {rs₁ rs₂ : List Bool} {X₁ X₂ : Nat → V}
    (hreps : IsBlockModels m dK) (hi : i < dK.k) (hkK : dK.k = kK)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hρ : ∀ v, v < dK.nP →
      consList (Ds₁.map (interp V ρ₁)) ρ₁ v = consList (Ds₂.map (interp V ρ₂)) ρ₂ v)
    (hwK : dK.w ψ₁ = dK.w ψ₂)
    (huT : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hw₁ : dK.w ψ₁ = TV₁.w) (hw₂ : dK.w ψ₂ = TV₂.w)
    (hu₁ : ∀ i', i' < kK → TV₁.u (base₁ + i') = dK.uM i' ψ₁)
    (hu₂ : ∀ i', i' < kK → TV₂.u (base₂ + i') = dK.uM i' ψ₂)
    (h₁ : CopyCtorShape TV₁ acval dK ψ₁ Ds₁ lpsK lvls₁ tg₁ tls₁ Eis₁ ρ₁ i j base₁ kK Fs₁ rs₁ Es₁)
    (h₂ : CopyCtorShape TV₂ acval dK ψ₂ Ds₂ lpsK lvls₂ tg₂ tls₂ Eis₂ ρ₂ i j base₂ kK Fs₂ rs₂ Es₂)
    (hdom₂ : ∀ l, l < ((dK.Fss i ψ₂).getD j []).length → rs₂.getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂) (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
      slotSet TV₂.w (TV₂.u (tg₂ l)) (consList fs₁ ρ₂) (tls₂.getD l []) (Eis₂.getD l [])
          (X₂ (tg₂ l))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
            (((dK.Fss i ψ₂).getD j []).getD l default))
    (hrel : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true → X₁ (tg₁ l) = X₂ (tg₂ l)) :
    ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₁.map (interp V ρ₁)) ρ₁) (((dK.Fss i ψ₁).getD j []).take l) fs₁ →
      slotSet TV₁.w (TV₁.u (tg₁ l)) (consList fs₁ ρ₁) (tls₁.getD l []) (Eis₁.getD l [])
          (X₁ (tg₁ l))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
            (((dK.Fss i ψ₁).getD j []).getD l default) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨hF, hE, htl, -⟩ := hI.ctor_params hj hψ
  have hcd := hI.ctorData hj
  have hwT : TV₁.w = TV₂.w := by rw [← hw₁, ← hw₂, hwK]
  have hfrm : ∀ (as : List V) v, v < dK.nP + as.length →
      consList as (consList (Ds₁.map (interp V ρ₁)) ρ₁) v
        = consList as (consList (Ds₂.map (interp V ρ₂)) ρ₂) v :=
    fun as v hv => consList_agree_above hρ as v (by omega)
  intro l hl hr fs₁ hl₁ hsp
  subst hl₁
  have hl₂ : fs₁.length < ((dK.Fss i ψ₂).getD j []).length := by rw [← hF]; exact hl
  have hsp₂ : SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂)
      (((dK.Fss i ψ₂).getD j []).take fs₁.length) fs₁ := by
    rw [← hF]
    exact spineFit_congr_fields (fieldsBelow_take _ (hI.Fss_below hj ψ₁)) hρ hsp
  have hcdom : interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
        (((dK.Fss i ψ₁).getD j []).getD fs₁.length default)
      = interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
        (((dK.Fss i ψ₂).getD j []).getD fs₁.length default) := by
    rw [hF]
    exact interp_congr_below V _ (dK.nP + fs₁.length) _ _
      (fieldsBelow_getD _ (hI.Fss_below hj ψ₂) hl₂) (hfrm fs₁)
  have hr₂ : rs₂.getD fs₁.length false = true := by
    by_cases hnt : dK.tgts i j fs₁.length < dK.k
    · exact (h₂.recF _ hl₂ hr hnt).1
    · exact (h₂.pinF _ hl₂ hr hnt).1
  have hcongr : slotSet TV₂.w (TV₂.u (tg₂ fs₁.length))
        (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
        (((dK.tlss i ψ₂).getD j []).getD fs₁.length [])
        (((dK.Eiss i ψ₂).getD j []).getD fs₁.length []) (X₂ (tg₂ fs₁.length))
      = slotSet TV₂.w (TV₂.u (tg₂ fs₁.length))
        (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
        (((dK.tlss i ψ₂).getD j []).getD fs₁.length [])
        (((dK.Eiss i ψ₂).getD j []).getD fs₁.length []) (X₂ (tg₂ fs₁.length)) := by
    refine slotSet_congr_below (k := dK.nP + fs₁.length) ?_ (fun e he => ?_) (hfrm fs₁)
    · rw [IsBlockModel.tlss_getD hj]
      exact hcd.tssBelow ψ₂ fs₁.length
    · have hmem : e ∈ (dK.eissF i j ψ₂).getD fs₁.length [] := by
        rwa [IsBlockModel.Eiss_getD hj] at he
      rw [IsBlockModel.tlss_getD hj]
      exact hcd.eissBelow ψ₂ fs₁.length e hmem
  rw [h₁.slot_container hl hr fs₁ rfl, hwT,
    copyTarget_u h₁ h₂ hkK hu₁ hu₂ hl hl₂ hr (huT fs₁.length), htl, hE,
    hrel _ hl hr, hcdom, hcongr, ← h₂.slot_container hl₂ hr fs₁ rfl]
  exact hdom₂ _ hl₂ hr₂ fs₁ rfl hsp₂

/-! ## The run-level producer: `hdom₁rec` at the assembly's own data -/

section Run

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
  {pinsS : List PinSyn} {env₂ : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "GF" => GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "ΨA" => nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
  (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
  (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
  (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
  (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)

/-- **`hdom₁rec`, PRODUCED** (task #315 WIDE (f3), lane DOM): the
container-RECURSIVE arm of `nestedPinPairAt_pinσ`'s `hdom₁`
(`NestedPinLeafAll.lean:7459`), stated verbatim, from the OWNER's own
bound `hdom₂` and the class equation, and from NOTHING ELSE that the
assembly does not already hold.

Both inputs are `have`s of the assembly at the point the arm is asked:

* `hdom₂` is `dom₂_of_run`'s conclusion at `Y = X₁ ∘ σ` — whose own
  inputs are `hY`/`hYC`, the rank induction's own two AT THE OWNER, and
  the block-model laws `copyEntryAt_pin`/`auxLfp_eq_famAt` of an
  already-installed container;
* `hXrec` is `recσ_of_run`'s class equation at a container-recursive
  field, which the assembly already computes (`hXrecTgt`) and already
  passes to `nestedFitc_pin`.

So the arm spends NO ordering fact inside the instance: no `S` at an
in-instance target, no rank among the mint group's own pins, and no
`TupleLe` for the inner container.  The transport itself is
`copyDomRec_via`; everything here is the assembly's own bookkeeping —
the stored record at the group's member, the level-parameter
agreement, the two target universes and the two index-universe
readings. -/
theorem nestedPinDomRec_of_dom₂ (m : EnvModel V env₂)
    {st : ElimState} (dJf : Nat → BlockModel V)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ iq j : Nat} (G : GF st m q₀ kJ (dJf q₀)) (hiq : iq < kJ)
    (hjl : j < ((dJf q₀).ctorsM iq).length)
    {dR : BlockModel V} {q₀' : Nat} {ψR : Name → Nat} {ρR : Nat → V}
    (S₂ : PinGroupView dR (dJf q₀) q₀' kJ)
    {ciK : ContainerInfo} (CK : ContainerModeled m ciK (dJf q₀))
    {IK : Name} (hciK : ConLeche.containerInfo? env₂ IK = some ciK)
    {cvK : ConstantVal} {capsK : IndCaps} (hfK : env₂.find? IK = some (.indInfo cvK capsK))
    (hpp : ContainerPinParams (V := V) cvK (dJf q₀))
    (hψ : ∀ pp ∈ cvK.levelParams, ((dR.pinAt q₀').ψJ ψR) pp = (((D).pinAt (q₀ + iq)).ψJ ψ) pp)
    (hfr : ∀ v, v < (dJf q₀).nP → dR.pinFrame q₀' ψR ρR v = (D).pinFrame (q₀ + iq) ψ ρp v)
    {lvls₁ : List Level}
    (h₁ : CopyCtorShape (dR.targetView m.acval ψR) m.acval (dJf q₀) ((dR.pinAt q₀').ψJ ψR)
      ((dR.pinAt q₀').Ds ψR) cvK.levelParams lvls₁
      (fun l => (dR.pinCtors (q₀' + iq)).tgts j l) (((dR.pinCtors (q₀' + iq)).tlss ψR).getD j [])
      (((dR.pinCtors (q₀' + iq)).Eiss ψR).getD j []) ρR iq j
      (dR.k + q₀') kJ (((dR.pinCtors (q₀' + iq)).Fss ψR).getD j [])
      ((dR.pinCtors (q₀' + iq)).rss.getD j []) (((dR.pinCtors (q₀' + iq)).Ess ψR).getD j []))
    {σ : Nat → Nat}
    -- **`dom₂_of_run`'s conclusion at `Y = X₁ ∘ σ`**
    (hdom₂ : ∀ l, l < (((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).length →
      ((dR.pinCtors (q₀' + iq)).rss.getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (((dR.pinAt q₀').Ds ψR).map (interp V ρR)) ρR)
        ((((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).take l) fs₁ →
      slotSet (dR.w ψR) (dR.uT ((dR.pinCtors (q₀' + iq)).tgts j l) ψR) (consList fs₁ ρR)
          ((((dR.pinCtors (q₀' + iq)).tlss ψR).getD j []).getD l [])
          ((((dR.pinCtors (q₀' + iq)).Eiss ψR).getD j []).getD l [])
          ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))
            (σ ((dR.pinCtors (q₀' + iq)).tgts j l)))
        ⊆ˢ interp V (consList fs₁ (consList (((dR.pinAt q₀').Ds ψR).map (interp V ρR)) ρR))
            ((((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).getD l default))
    -- **`recσ_of_run`'s class equation at a container-RECURSIVE field**
    (hXrec : ∀ l, l < (((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss iq).getD j []).getD l false = true →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0
        = σ ((dR.pinCtors (q₀' + iq)).tgts j l)) :
    ∀ l, l < (((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss iq).getD j []).getD l false = true →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame (q₀ + iq) ψ ρp)
        ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).take l) fs₁ →
      slotSet (f₀.s.eval ψ)
          (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) (consList fs₁ ρp)
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
          ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))
            (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0))
        ⊆ˢ interp V (consList fs₁ ((D).pinFrame (q₀ + iq) ψ ρp))
            ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).getD l default) := by
  classical
  have hiqK : iq < (dJf q₀).k := S₂.kEq ▸ hiq
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored iq hiq
  have hmemName : (dJf q₀).memberName iq = ((D).pinAt (q₀ + iq)).J := hI.member
  have hlps : cvT.levelParams = cvK.levelParams :=
    CK.memberLpsI hciK hfK hiqK (by rw [hmemName]; exact hfind)
  have hpar := CK.params_congr hciK hfK hψ hiqK
  have hj : ((dJf q₀).ctorsM iq)[j]? = some (((dJf q₀).ctorsM iq).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
  have hsh := G.shape iq hiq cvT caps hfind ψ ρp hρp iq j hiq hjl
  unfold CopyShapeA at hsh
  have hcaLps : ((((dJf q₀).ctorsM iq).getD j default).1).levelParams = cvT.levelParams :=
    (hI.ctors iq j _ hiqK hj).2.1
  have hψcA : ∀ pp ∈ ((((dJf q₀).ctorsM iq).getD j default).1).levelParams,
      ((dR.pinAt q₀').ψJ ψR) pp = (((D).pinAt (q₀ + iq)).ψJ ψ) pp := by
    rw [hcaLps, hlps]; exact hψ
  have hfrR : ∀ v, v < (dJf q₀).nP →
      consList (((dR.pinAt q₀').Ds ψR).map (interp V ρR)) ρR v
        = (D).pinFrame (q₀ + iq) ψ ρp v := fun v hv => hfr v hv
  -- the two copies' target universes are the container's own datum
  have huT : ∀ l, (dJf q₀).uT ((dJf q₀).tgts iq j l) ((dR.pinAt q₀').ψJ ψR)
      = (dJf q₀).uT ((dJf q₀).tgts iq j l) (((D).pinAt (q₀ + iq)).ψJ ψ) := by
    intro l
    by_cases hnt : (dJf q₀).tgts iq j l < (dJf q₀).k
    · rw [BlockModel.uT_of_mem hnt, BlockModel.uT_of_mem hnt]
      exact (CK.params_congr hciK hfK hψ hnt).1
    · rw [BlockModel.uT_of_pin hnt, BlockModel.uT_of_pin hnt]
      by_cases hqq : (dJf q₀).tgts iq j l - (dJf q₀).k < (dJf q₀).nPins
      · exact ((hpp _ hqq).2.2 _ _ hψ).1
      · unfold BlockModel.pinAt
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show (dJf q₀).pins.length ≤ _ from by
            unfold BlockModel.nPins at hqq; omega)]
        rfl
  -- the two index-universe readings at the group's own members
  have hu₁ : ∀ i', i' < kJ →
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS m.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).u (p.k + q₀ + i')
        = (dJf q₀).uM i' (((D).pinAt (q₀ + iq)).ψJ ψ) := by
    intro i' hi'
    show nestedU p.k W pinsS ψ (p.k + q₀ + i') = _
    rw [Nat.add_assoc, nestedU_pin]
    exact G.syn.pinU iq hiq ψ i' (by omega)
  have hu₂ : ∀ i', i' < kJ →
      (dR.targetView m.acval ψR).u (dR.k + q₀' + i')
        = (dJf q₀).uM i' ((dR.pinAt q₀').ψJ ψR) := by
    intro i' hi'
    show dR.uT (dR.k + q₀' + i') ψR = _
    rw [Nat.add_assoc, BlockModel.uT_of_pin (by omega) ψR, Nat.add_sub_cancel_left]
    exact S₂.pinU i' hi' ψR
  intro l hl hrec _ fs₁ hl₁ hsp
  exact copyDomRec_via (tg₂ := fun l' => (dR.pinCtors (q₀' + iq)).tgts j l')
    (X₂ := fun c => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (σ c))
    G.syn.reps hiqK G.syn.kEq hj
    (fun pp hpp' => (hψcA pp hpp').symm) (fun v hv => (hfrR v hv).symm)
    hpar.2.2.symm (fun l' => (huT l').symm)
    (G.syn.w iq hiq ψ) (S₂.w ψR) hu₁ hu₂ hsh (by rw [hlps]; exact h₁) hdom₂
    (fun l' hl' hr' => congrArg _ (hXrec l' hl' hr')) l hl hrec fs₁ hl₁ hsp

/-! ## The Ord-only entry producer -/

/-- **STEP (iv) AT THE `ordF`-RIGHT ARM ALONE** (task #315 WIDE (f3),
lane DOM): `CopyEntryOrd` at one copy's constructor, from the rank
induction's own scope and NOTHING at an in-instance target.

`nestedPinsEntry_at` produces `CopyEntryOut` — the entries at EVERY
copy-recursive field whose target leaves the mint group — and reaches
the copies of the container's OWN pins through `nestedTargetReads_L`'s
`S` at the `pinF` arm.  `S` at an in-instance target is what an
induction over the container INSTANCES may not assume
(`nestedTargetReads_L`'s own docstring), and those copies stay inside
the instance.

`CopyEntryOrd`'s guard is `((dJ.rss i).getD j []).getD l false = false`
— the container calls the field ORDINARY — so the `pinF` arm is not
asked about at all, and the only scope the producer needs is `hout`:
at a field the container calls ordinary and the block's rewrite made
recursive, whose target is a PIN, that pin satisfies `S`.  That is the
same premise `nestedPinEntryOutEq` already takes, and this theorem is
that per-field equality packaged as the residual's `Prop`. -/
theorem nestedPinsEntryOrd_at (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {S : Nat → Prop} {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {j : Nat} (hj : j < ((dJf q₀).ctorsM i).length)
    (hout : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD l false = true →
      (((dJf q₀).rss i).getD j []).getD l false = false →
      ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0) < p.k →
      S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0) - p.k)) :
    CopyEntryOrd (dJf q₀) (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []) ρp i j
      (p.k + q₀) kJ ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) []) (f₀.s.eval ψ)
      (nestedU p.k W pinsS ψ)
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) := by
  have hψeq : ((D).pinAt (q₀ + i)).ψJ ψ = ((D).pinAt q₀).ψJ ψ :=
    (G.syn.ψJEq i 0 hi G.syn.kpos ψ).trans (by rw [Nat.add_zero])
  have hDseq : ((D).pinAt (q₀ + i)).Ds ψ = ((D).pinAt q₀).Ds ψ := G.syn.sameDs i hi ψ
  have hjA : ((dJf q₀).ctorsM i)[j]? = some (((dJf q₀).ctorsM i).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  unfold CopyEntryOrd CopyEntryAt
  rw [hψeq, hDseq]
  intro l hl hord hrs hgout fs₁ hl₁ hsp
  exact nestedPinEntryOutEq hμ h hbk m hleafM dJf hgroups hρp G hIH hPfGroup hi hjA hout
    l hl hrs hord hgout fs₁ hl₁ hsp

/-- **STEP (iv)'s `ordF`-RIGHT ARM IN THE RESIDUAL'S OWN SHAPE**
(task #315 WIDE (f3), lane DOM): `CopyEntryAOrd` exactly as
`nestedPinWideStep`'s `hent` asks for it — at the group's pin `i` for
the level assignment and components and at constructor `(i', j)` —
from `nestedPinsEntryOrd_at` at `i'`, the group's own `ψJEq`/`sameDs`
moving the reading data between its members.

This is `nestedPinsEntry_of`'s twin at the WEAKER residual, and it is
the producer step (4) was waiting for: no `S` at an in-instance target
occurs anywhere in it. -/
theorem nestedPinsEntryOrd_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {S : Nat → Prop} {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    (hout : ∀ i' j, i' < kJ → j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k →
      S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k)) :
    ∀ i', i' < (dJf q₀).k → ∀ j, j < ((dJf q₀).ctorsM i').length →
      CopyEntryAOrd (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        (dJf q₀) (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ) q₀ (dJf q₀).k i' j := by
  have hkE : (dJf q₀).k = kJ := G.syn.kEq
  intro i' hi'K j hj
  have hi' : i' < kJ := hkE ▸ hi'K
  have hψ : ((D).pinAt (q₀ + i)).ψJ ψ = ((D).pinAt (q₀ + i')).ψJ ψ := G.syn.ψJEq i i' hi hi' ψ
  have hDs : ((D).pinAt (q₀ + i)).Ds ψ = ((D).pinAt (q₀ + i')).Ds ψ := by
    rw [G.syn.sameDs i hi ψ, ← G.syn.sameDs i' hi' ψ]
  unfold CopyEntryAOrd
  rw [hψ, hDs, hkE]
  exact nestedPinsEntryOrd_at hμ h hbk m hleafM dJf hgroups hρp hIH hPfGroup G hi' hj
    (hout i' j hi' hj)

/-! ## `hout`'s two halves at a ROOT group -/

/-- **THE STEP'S `hout`, AT A ROOT GROUP** (task #315 WIDE (f5), lane
DOM): at a field the container calls ORDINARY and the block's rewrite
made recursive, whose target is a PIN, that pin is in the rank
induction's scope — PROVIDED the group `q₀` is its instance's ROOT
group (`hrootGrp`).

`hout` was a hypothesis of `nestedPinWideStep` and DESIGN's WIDE (f3)
row showed it FALSE at an arbitrary mint group (`nested_p04`).  Its two
halves are here:

* **the EDGE half** is `hedgeAt`, the K.32-shaped lookup bridge between
  the model's spellings (`blkRss ctorsA kinds`, `mutTgts …`) and
  `nestedPinEdges`' own lookups.  `nestedPinEdges_mem`
  (`Verify/Inductives/NestedInv.lean`) is the theorem it instantiates;
  what stands between them is the lookup matching, which lives in
  `NestedCopyInst.lean` — not this lane's file — and is carried here as
  a named hypothesis with this exact statement;
* **the LABEL half** is `ConLeche.nestedPinOutLabel`
  (`Verify/Inductives/NestedRootLabel.lean`), whose four links are K.66,
  K.75 clause (2), the roots table's constancy on an instance and K.75
  clause (1).  The two K.75 clauses are the named hypotheses `hK75pool`
  and `hK75grp`; their Bools' verbatim text and their measurement (zero
  fires on the shadow suite, `init-full` and Mathlib in both modes) are
  in DESIGN's WIDE (f4) row.

`hrootGrp` is stated at the group's pin `q₀ + i` and moved to the other
members by K.37's clause (4) (a mint group is ONE instance) and
`nestedPinRootGroup_congr`. -/
theorem nestedPinsOut_of_root (m : EnvModel V env₂)
    {st : ElimState} {stored : List AuxStored} {edges : List (Nat × Nat × Bool)}
    (hed : ConLeche.nestedPinEdges env p b st stored = some edges)
    (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    (hK29 : ConLeche.nestedGroupsOk env p st = true)
    (hK62 : ConLeche.nestedOrdOutsideOk env p b st stored = true)
    -- **K.75 clause (1)**: the root group's own-pin POOL, read as the
    -- instance map's INDEX-level image
    (hK75pool : ∀ q, q < st.pins.length → ∀ g,
      (ConLeche.nestedPinRootGroup env p b st stored).getD q none = some g →
      (st.pins.getD q default).grpBase = g ∨
        ∃ i, i < st.pins.length ∧ (st.pins.getD i default).grpBase = g ∧
          ∃ mi, ConLeche.nestedInstMapAt env st i = some mi ∧ mi.contains q = true)
    -- **K.75 clause (2)**: K.62 at the source's whole MINT GROUP
    (hK75grp : ∀ s' t', (s', t', false) ∈ edges →
      ∀ d, d < (st.pins.getD s' default).grpSize →
      ∀ mi, ConLeche.nestedInstMapAt env st ((st.pins.getD s' default).grpBase + d) = some mi →
        mi.contains t' = false)
    (hpinsLen : st.pins.length = pinsS.length)
    (dJf : Nat → BlockModel V) {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    (hrootGrp : (ConLeche.nestedPinRootGroup env p b st stored).getD (q₀ + i) none = some q₀)
    {ψ : Name → Nat}
    (hedgeAt : ∀ i' j, i' < kJ → j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k →
      ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k < pinsS.length ∧
        (q₀ + i', (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k, false) ∈ edges)) :
    ∀ i' j, i' < kJ → j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k →
      NestedOutScope env p b st stored edges pinsS.length (q₀ + i)
        ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k) := by
  obtain ⟨edges', hed', _, _, h4⟩ := ConLeche.nestedPinRankOk_inv hrank
  rw [hed] at hed'
  obtain rfl : edges = edges' := Option.some.inj hed'
  have hseg := G.syn.seg
  have hlt : q₀ + i < st.pins.length := by rw [hpinsLen]; omega
  intro i' j hi' hj l hl hrssB hrssC hge
  obtain ⟨htlt, hedge⟩ := hedgeAt i' j hi' hj l hl hrssB hrssC hge
  have hlt' : q₀ + i' < st.pins.length := by rw [hpinsLen]; omega
  -- a mint group is ONE instance (K.37's clause (4)), so every member
  -- carries the group's label and the group's root
  have hlab : instLabel env p b st stored (q₀ + i')
      = instLabel env p b st stored (q₀ + i) := by
    have e1 := h4 (q₀ + i') hlt'
    have e2 := h4 (q₀ + i) hlt
    rw [(G.syn.grp i' hi').1] at e1
    rw [(G.syn.grp i hi).1] at e2
    exact e1.trans e2.symm
  have hroot' : (ConLeche.nestedPinRootGroup env p b st stored).getD (q₀ + i') none
      = some (st.pins.getD (q₀ + i') default).grpBase := by
    rw [(G.syn.grp i' hi').1, ConLeche.nestedPinRootGroup_congr hlt' hlt hlab]
    exact hrootGrp
  refine ⟨q₀ + i', by omega, hlab, ⟨false, hedge⟩, ?_⟩
  rw [← hlab]
  exact ConLeche.nestedPinOutLabel hK29 hK62 hK75pool
    (fun d hd mi hmi => hK75grp _ _ hedge d hd mi hmi) hed hlt'
    (by rw [hpinsLen]; exact htlt) hedge hroot'

end Run

/-! ## The wide identification at a class that is NOT a member

(task #315 WIDE (f3), lane DOM session 2)

`ofNested_pin_block_of_wide_inst` (`NestedFit.lean`) concludes at the
container's MEMBER classes — `i < dJ.k` — because that is where its
last step, Bekić's nested form, turns the container's WIDE least tuple
back into its narrow one.  **The identity it is extracted from holds at
every class of the instance**, members and the container's OWN PINS
alike: it is `lfpTuple_set_congr_le`, whose own bound is `i < s`, and
`ofNested_pin_block_wide` spends the member bound only in the two
rewrites after it.

The two theorems below are that identity, stated where the bound is
not spent.  They are the step the route needs at a pin `q` whose mint
group is NOT its instance's ROOT group: the wide identification at the
ROOT group speaks about the copies of the root's own pins through `σ`,
and `q` is one of them (K.41's covering), so `q`'s own reading is the
ROOT's — no per-group identification at `q`, and hence no entry at
`q`'s own `ordF`-right fields, is needed to obtain it.

**Why that matters is recorded in DESIGN's WIDE (f3) row**: `hout` at
an ARBITRARY mint group is FALSE at an accepted block
(`tests/e2e/nested_p04.ndjson`, whose not-own edges `(1,2)` and `(2,0)`
have equal instance labels), and TRUE at a ROOT group, where K.62/K.66
put an `ordF`-right target outside the instance map's image and outside
the mint group and K.41 covers the instance by the two. -/

section WidePin

variable {nP k : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env}
  {memberNames : List Name}
  {nIdxs : List Nat} {ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {W : (Name → Nat) → Nat} {ctorsM : Nat → List (ConstantVal × Nat)} {idxF : Nat → Nat → List Expr}
  {dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → Nat → List (Option Nat)}
  {ksF : Nat → Nat → List RecFieldKind} {tgts : Nat → Nat → Nat → Nat}
  {fvsPF xFvsF : Nat → Nat → List Expr} {xrestF : Nat → Nat → Expr}
  {eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {pins : List PinSyn} {offs : Nat → Nat}
  {mems nFs : List Nat} {tgtsG : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)} {pc : Nat → PinCtors V}
  {ψ : Name → Nat} {ρp : Nat → V}

local notation "DN" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins offs mems nFs
  tgtsG rss tlss Eiss₀ Fss₀ Ess₀ pc)

local notation "ΨN" => nestedΨ (V := V) nP k resSort ppsA W pins offs mems nFs tgtsG rss tlss
  Eiss₀ Fss₀ Ess₀

/-- **THE WIDE IDENTIFICATION, AT EVERY CLASS OF THE INSTANCE**
(task #315 WIDE (f3), lane DOM): the block's auxiliary carrier at the
instance's position `σ i` IS the container's wide least tuple at class
`i`, for EVERY `i < s` — not only at the container's members.

This is `ofNested_pin_block_wide`'s own last line
(`lfpTuple_set_congr_le`, `SetTheory/Derive/LfpCompose.lean`) with its
bound left where the composition lemma puts it.  Neither the mint
group's base `q₀`, nor its contiguity `hroot`, nor the segment bound
`hseg` occurs: they are what the MEMBER extraction needs, and the
identity itself needs none of them. -/
theorem ofNested_wide_at
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)
    {s : Nat} {σ : Nat → Nat} (hσ : ∀ i, i < s → σ i < k + pins.length)
    {IsJ : Nat → V} {ΨJ : (Nat → V) → Nat → V}
    (hmonoJ : MonoTuple ((DN).w ψ) s IsJ ΨJ)
    (hmapsJ : MapsTuple ((DN).w ψ) s IsJ ΨJ)
    (hclJ : ∃ L, IsClosedTuple ((DN).w ψ) s IsJ ΨJ L)
    (hfcJ : ∀ Y, InTupleSpace ((DN).w ψ) s IsJ Y → FibreConst σ s Y → FibreConst σ s (ΨJ Y))
    (hIs : ∀ i, i < s → (DN).idx ψ ρp (σ i) = IsJ i)
    (hΦ : ∀ Y, InTupleSpace ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) Y →
      FibreConst σ s Y →
      TupleLe s (fun i => (DN).idx ψ ρp (σ i)) Y (lfpTuple ((DN).w ψ) s IsJ ΨJ) →
      ∀ i, i < s →
      ΨN ψ ρp (setJoin σ s
          (lfpTuple ((DN).w ψ) (k + pins.length) ((DN).idx ψ ρp) (ΨN ψ ρp)) Y) (σ i)
        = ΨJ Y i)
    {i : Nat} (hi : i < s) :
    lfpTuple ((DN).w ψ) (k + pins.length) ((DN).idx ψ ρp) (ΨN ψ ρp) (σ i)
      = lfpTuple ((DN).w ψ) s IsJ ΨJ i := by
  have hΨ := nestedΨ_functor h
  have hLmem : InTupleSpace ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i))
      (lfpTuple ((DN).w ψ) s IsJ ΨJ) :=
    (inTupleSpace_congr hIs).mpr (lfpTuple_mem _ _ _ _)
  have hmonoJ' : MonoTuple ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) ΨJ := fun X Y hX hY hle =>
    (tupleLe_congr hIs).mpr (hmonoJ X Y ((inTupleSpace_congr hIs).mp hX)
      ((inTupleSpace_congr hIs).mp hY) ((tupleLe_congr hIs).mp hle))
  have hC' : IsClosedTuple ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) ΨJ
      (lfpTuple ((DN).w ψ) s IsJ ΨJ) :=
    ⟨hLmem, (tupleLe_congr hIs).mpr (lfpTuple_closed hclJ hmonoJ)⟩
  have hmapsJ' : MapsTuple ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) ΨJ := fun X hX =>
    (inTupleSpace_congr hIs).mpr (hmapsJ X ((inTupleSpace_congr hIs).mp hX))
  have hIsFC : ∀ a b, a < s → b < s → σ a = σ b → IsJ a = IsJ b := by
    intro a b ha hb hab
    rw [← hIs a ha, ← hIs b hb, hab]
  have hCfc : FibreConst σ s (lfpTuple ((DN).w ψ) s IsJ ΨJ) :=
    fibreConst_lfpTuple_of_fc hIsFC hmonoJ hclJ hfcJ
  have hfcJ' : ∀ Y, InTupleSpace ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) Y →
      FibreConst σ s Y → FibreConst σ s (ΨJ Y) :=
    fun Y hY hfc => hfcJ Y ((inTupleSpace_congr hIs).mp hY) hfc
  have hL'fc : FibreConst σ s (lfpTuple ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i)) ΨJ) := by
    intro a b ha hb hab
    rw [lfpTuple_congr hIs (fun _ _ _ _ => rfl) ha, lfpTuple_congr hIs (fun _ _ _ _ => rfl) hb]
    exact hCfc a b ha hb hab
  have hC : IsClosedTuple ((DN).w ψ) s (fun i => (DN).idx ψ ρp (σ i))
      (setSec (ΨN ψ ρp) σ s
        (lfpTuple ((DN).w ψ) (k + pins.length) ((DN).idx ψ ρp) (ΨN ψ ρp)))
      (lfpTuple ((DN).w ψ) s IsJ ΨJ) := by
    refine ⟨hLmem, fun m hm => ?_⟩
    rw [setSec_apply, hΦ _ hLmem hCfc (TupleLe.refl _ _ _) m hm]
    exact hC'.2 m hm
  exact lfpTuple_set_congr_le hσ hΨ.2.2 hΨ.1 hΨ.2.1 hIs hmonoJ' hmapsJ' hfcJ' hL'fc hC hC' hCfc
    hΦ hi

/-- **AND AT A CLASS OF A STORED CONTAINER, IN `famAt` FORM**
(task #315 WIDE (f3), lane DOM): `ofNested_wide_at` at the container's
own wide operator, composed with `BlockModel.auxLfp_eq_famAt`.

At a MEMBER class this is `ofNested_pin_block_of_wide`'s conclusion
(`famAt` is the narrow least tuple there); at one of the container's
OWN PIN classes it is the container's own pin carrier at its own
carrier — which is what a block pin's `pinLeaf` has to be identified
with, and the reason the theorem is stated: the pins of an instance
that are not the root group's members are read HERE, off the ROOT's
identification, instead of at a per-group one of their own. -/
theorem ofNested_wide_famAt
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)
    {dJ : BlockModel V} {ψJ : Name → Nat} {ρJ : Nat → V} {σ : Nat → Nat}
    (hw : dJ.w ψJ = (DN).w ψ)
    (hσ : ∀ i, i < dJ.k + dJ.nPins → σ i < k + pins.length)
    (hmonoJ : MonoTuple ((DN).w ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ))
    (hmapsJ : MapsTuple ((DN).w ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ))
    (hclJ : ∃ L, IsClosedTuple ((DN).w ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ) L)
    (hfcJ : ∀ Y, InTupleSpace ((DN).w ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      FibreConst σ (dJ.k + dJ.nPins) (dJ.Ψaux ψJ ρJ Y))
    (hIs : ∀ i, i < dJ.k + dJ.nPins → (DN).idx ψ ρp (σ i) = dJ.idx ψJ ρJ i)
    (hΦ : ∀ Y, InTupleSpace ((DN).w ψ) (dJ.k + dJ.nPins) (fun i => (DN).idx ψ ρp (σ i)) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      TupleLe (dJ.k + dJ.nPins) (fun i => (DN).idx ψ ρp (σ i)) Y
        (lfpTuple ((DN).w ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) →
      ∀ i, i < dJ.k + dJ.nPins →
      ΨN ψ ρp (setJoin σ (dJ.k + dJ.nPins)
          (lfpTuple ((DN).w ψ) (k + pins.length) ((DN).idx ψ ρp) (ΨN ψ ρp)) Y) (σ i)
        = dJ.Ψaux ψJ ρJ Y i)
    (hcomp : dJ.Φ ψJ ρJ = composeΦ (dJ.w ψJ) dJ.k dJ.nPins (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ))
    (hpins : ∀ X q, q < dJ.nPins →
      dJ.pinCar ψJ ρJ X q
        = pinsCar (dJ.w ψJ) dJ.k dJ.nPins (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ) X q)
    {i : Nat} (hi : i < dJ.k + dJ.nPins) :
    lfpTuple ((DN).w ψ) (k + pins.length) ((DN).idx ψ ρp) (ΨN ψ ρp) (σ i)
      = dJ.famAt ψJ ρJ (lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ)) i := by
  have hmono' : MonoTuple (dJ.w ψJ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ) := by
    rw [hw]; exact hmonoJ
  have hcl' : ∃ L, IsClosedTuple (dJ.w ψJ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ)
      (dJ.Ψaux ψJ ρJ) L := by
    rw [hw]; exact hclJ
  rw [ofNested_wide_at h hσ hmonoJ hmapsJ hclJ hfcJ hIs hΦ hi, ← hw]
  exact dJ.auxLfp_eq_famAt hmono' hcl' hcomp hpins hi

end WidePin

/-! ## (R2): the ROOT's wide identification, read at a block pin

The two halves are in the tree already and this is the join.  At a
`ClassPinAt` pair `(c, q)` of the instance's root group,
`nestedPinFam_of_classPin` says the pin's own least tuple `pinLfp … q`
IS the root container's extended carrier at class `c`; `ofNested_wide_famAt`
says the BLOCK's auxiliary carrier at position `σ c` is that same
extended carrier.  With `σ c = p.k + q` — the instance closure landing
class `c` on the block pin the pairing named — the two compose into the
identification the rank induction wants AT THE PIN, and it is the
ROOT's identification that produced it: no per-group step at `q`'s own
mint group occurs anywhere in the chain.
-/

section RootClass

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
  {pinsS : List PinSyn} {env₂ : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "GF" => GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "ΨA" => nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
  (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
  (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
  (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
  (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)

/-! ## (2): the covering, at a pin, WITH the closure's landing -/

/-- **K.41's COVERING AT A PIN, WITH `σ`'s LANDING** (task #315 WIDE
(f6), lane DOM): at every pin `q` of the root's instance, the
`ClassPinAt` pair `(c, q)` of the ROOT group *together with*
`σ c = p.k + q`, which is the second half `nestedPinLfp_of_root_class`
asks for and the half `InstanceCovered` does not carry.

The two are one fact because the closure and the covering are read off
the SAME table.  `σ` is the run's instance map lifted over the
container's members (`NestedPinsRun.pinGroupInst_of`,
`NestedInstMap.lean`):

    fun c => if c < dR.k then p.k + r + c else p.k + mm.getD (c - dR.k) 0

so a MEMBER class `c = i` lands on `p.k + (r + i)` by `hroot` and its
pairing is `classPin_of_rootMember`; and a PIN class `c = dR.k + qK`
lands on `p.k + mm.getD qK 0` by `hpinσ`, which is `p.k + q` exactly
when `q` is the map's value there — i.e. exactly at K.75's clause (1)
(`hpool`, the index-level image of the root group), whose `PinCorr` at
that very table position is `NestedPinsRun.instMapPinOwn`'s (`hcorr`)
and whose `ClassPin` is then `classPin_of_blockPinCorr`'s.

`hpool` is stated at the root group's OWN map `mm`: K.75's clause (1)
hands the image of an arbitrary member of the root group, and
`NestedPinsRun.instMapGroup` — the instance map is the GROUP's, not
the member's — moves it to the base.  That transport is the caller's,
because it is a run fact and this statement is not. -/
theorem nestedClassPinAt_of_instMap (m : EnvModel V env₂) {st : ElimState}
    {dJf : Nat → BlockModel V}
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V}
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR)
    {σ : Nat → Nat} {mm : List Nat} {lpsR : List Name}
    (hroot : ∀ c, c < (dJf r).k → σ c = p.k + r + c)
    (hpinσ : ∀ c, ¬ c < (dJf r).k → c < (dJf r).k + (dJf r).nPins →
      σ c = p.k + mm.getD (c - (dJf r).k) 0)
    (hmmLen : mm.length = (dJf r).nPins)
    (hψR : ((D).pinAt r).ψJ ψ = Level.substFn ψ lpsR ((D).pinAt r).lvls)
    (hcorr : ∀ qK, qK < (dJf r).nPins →
      PinCorr ((D).targetView m.acval ψ) m.acval (dJf r) (((D).pinAt r).ψJ ψ)
        (((D).pinAt r).Ds ψ) lpsR ((D).pinAt r).lvls (p.k + mm.getD qK 0) qK)
    {q : Nat} (hq : q < pinsS.length)
    (hpool : (∃ i, i < kR ∧ q = r + i) ∨ mm.contains q = true) :
    ∃ c, c < (dJf r).k + (dJf r).nPins ∧
      ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q ∧
      σ c = p.k + q := by
  have hkR : (dJf r).k = kR := GR.syn.kEq
  rcases hpool with ⟨i, hi, rfl⟩ | hin
  · -- a MEMBER of the root group: its own container member's partner
    refine ⟨i, by omega, ⟨classPin_of_rootMember (pinGroupView_of_syn GR.syn) (hkR ▸ hi),
      fun _ => rfl⟩, ?_⟩
    rw [hroot i (hkR ▸ hi)]; omega
  · -- a pin in the root group's index-level image: K.41's own pin
    obtain ⟨qK, hqKlt, hqKe⟩ : ∃ qK, qK < mm.length ∧ mm.getD qK 0 = q := by
      obtain ⟨qK, hqKlt, hqKe⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hin)
      exact ⟨qK, hqKlt, by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqKlt, hqKe]; rfl⟩
    have hqK : qK < (dJf r).nPins := by omega
    obtain ⟨q₀', kK', i'', ci', hqKe2, hi'', hci', S', -⟩ := hshR _ hqK
    subst hqKe2
    refine ⟨(dJf r).k + (q₀' + i''), by omega, ⟨?_, fun hlt => absurd hlt (by omega)⟩, ?_⟩
    · exact classPin_of_blockPinCorr m hgroups CR S' ((hB _ ci' hci').1.reps) hi'' hq hqK
        (ρp := ρp) (ρR := (D).pinFrame r ψ ρp) (Ds₀ := ((D).pinAt r).Ds ψ)
        (lpsK := lpsR) (lvlsK := ((D).pinAt r).lvls) (hqKe ▸ hcorr _ hqK) rfl hψR
    · rw [hpinσ _ (by omega) (by omega),
        show (dJf r).k + (q₀' + i'') - (dJf r).k = q₀' + i'' from by omega, hqKe]

/-- **(R2): THE ROOT'S IDENTIFICATION, AT A BLOCK PIN OF ITS INSTANCE**
(task #315 WIDE (f3), lane DOM): at a `ClassPinAt` pair `(c, q)` of the
instance's root group `r`, and with the instance closure `σ` taking the
root's class `c` to the block position of pin `q`, the pin's own least
tuple IS the block's auxiliary carrier there.

This is the equality `nestedPinsLe_of_wide`'s `hwide` asks for at `q`
(its `pinCar` form is `ofNested_pinCar_lfp` away), produced at the
ROOT's wide identification instead of at `q`'s own mint group.  Every
hypothesis but `hcp` and `hσc` is `ofNested_wide_famAt`'s, and those
two are K.41's pairing and the closure's own landing. -/
theorem nestedPinLfp_of_root_class {ψ : Name → Nat} {ρp : Nat → V}
    (hOk : NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp))
    (m : EnvModel V env₂) {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    (hρp : Sat V ((D).params ψ).reverse ρp)
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR)
    {σ : Nat → Nat}
    (hw : (dJf r).w (((D).pinAt r).ψJ ψ) = (D).w ψ)
    (hσ : ∀ i, i < (dJf r).k + (dJf r).nPins → σ i < p.k + pinsS.length)
    (hmonoJ : MonoTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hmapsJ : MapsTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hclJ : ∃ L, IsClosedTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) L)
    (hfcJ : ∀ Y, InTupleSpace ((D).w ψ) ((dJf r).k + (dJf r).nPins)
        ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins)
        ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) Y))
    (hIs : ∀ i, i < (dJf r).k + (dJf r).nPins →
      (D).idx ψ ρp (σ i) = (dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) i)
    (hΦ : ∀ Y, InTupleSpace ((D).w ψ) ((dJf r).k + (dJf r).nPins)
        (fun i => (D).idx ψ ρp (σ i)) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins) Y →
      TupleLe ((dJf r).k + (dJf r).nPins) (fun i => (D).idx ψ ρp (σ i)) Y
        (lfpTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
          ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
          ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) →
      ∀ i, i < (dJf r).k + (dJf r).nPins →
      ΨA ψ ρp (setJoin σ ((dJf r).k + (dJf r).nPins)
          (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) Y) (σ i)
        = (dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) Y i)
    (hcomp : (dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
      = composeΦ ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k (dJf r).nPins
          ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
          ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hpins : ∀ X q', q' < (dJf r).nPins →
      (dJf r).pinCar (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) X q'
        = pinsCar ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k (dJf r).nPins
            ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
            ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) X q')
    (c q : Nat) (hcT : c < (dJf r).kT) (hc : c < (dJf r).k + (dJf r).nPins)
    (hcp : ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q)
    (hσc : σ c = p.k + q) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) := by
  have hwide : lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (σ c)
      = (dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
          (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
            ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
            ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c := by
    -- the conclusion is unified with the STATED goal first, which is what
    -- fixes `BlockModel.ofNested`'s twenty implicit lists: `NestedLfpOk`
    -- names only some of them, so an `exact` leaves the rest open
    -- `apply` unifies the CONCLUSION first, which is what fixes the
    -- twenty implicit lists of `BlockModel.ofNested` that `NestedLfpOk`
    -- does not name; the goals then come back in the order `apply`
    -- chooses, so they are closed by name rather than positionally
    apply ofNested_wide_famAt (dJ := dJf r) (σ := σ)
    all_goals first
      | exact hOk | exact hw | exact hσ | exact hmonoJ | exact hmapsJ | exact hclJ
      | exact hfcJ | exact hIs | exact hΦ | exact hcomp | exact hpins | exact hc
  rw [nestedPinFam_of_classPin m dJf hgroups hρp hB hdJfB GR hshR c q hcT hcp, ← hwide, hσc]


/-- **(2) COMPOSED: THE PIN'S IDENTIFICATION FROM THE POOL ALONE**
(task #315 WIDE (f6), lane DOM): `nestedClassPinAt_of_instMap` fed
straight into `nestedPinLfp_of_root_class`, so that the class `c` never
appears in a caller's obligation — what is asked of the run is K.75's
clause (1) at the pin (`hpool`), the closure's two halves
(`hroot`/`hpinσ`), the map's length and the correspondence at its
entries (`hcorr`, `NestedPinsRun.instMapPinOwn`).

This is `nestedPinsLe_of_wide`'s `hwide` at the pin, up to the ONE
object the lane does not own: every wide hypothesis here
(`hw`/`hσ`/`hmonoJ`/`hmapsJ`/`hclJ`/`hfcJ`/`hIs`/`hΦ`/`hcomp`/`hpins`)
is `ofNested_wide_famAt`'s raw list, and the assembly that discharges
them from `ofNested_pin_block_of_wide_inst`'s own list is `hwideFam`
(`NestedFit.lean`, the main lane's) — see DESIGN's WIDE (f6) row. -/
theorem nestedPinLfp_of_pool {ψ : Name → Nat} {ρp : Nat → V}
    (hOk : NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp))
    (m : EnvModel V env₂) {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    (hρp : Sat V ((D).params ψ).reverse ρp)
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR)
    {σ : Nat → Nat}
    (hw : (dJf r).w (((D).pinAt r).ψJ ψ) = (D).w ψ)
    (hσ : ∀ i, i < (dJf r).k + (dJf r).nPins → σ i < p.k + pinsS.length)
    (hmonoJ : MonoTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hmapsJ : MapsTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hclJ : ∃ L, IsClosedTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
      ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) L)
    (hfcJ : ∀ Y, InTupleSpace ((D).w ψ) ((dJf r).k + (dJf r).nPins)
        ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins)
        ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) Y))
    (hIs : ∀ i, i < (dJf r).k + (dJf r).nPins →
      (D).idx ψ ρp (σ i) = (dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) i)
    (hΦ : ∀ Y, InTupleSpace ((D).w ψ) ((dJf r).k + (dJf r).nPins)
        (fun i => (D).idx ψ ρp (σ i)) Y →
      FibreConst σ ((dJf r).k + (dJf r).nPins) Y →
      TupleLe ((dJf r).k + (dJf r).nPins) (fun i => (D).idx ψ ρp (σ i)) Y
        (lfpTuple ((D).w ψ) ((dJf r).k + (dJf r).nPins)
          ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
          ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) →
      ∀ i, i < (dJf r).k + (dJf r).nPins →
      ΨA ψ ρp (setJoin σ ((dJf r).k + (dJf r).nPins)
          (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) Y) (σ i)
        = (dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) Y i)
    (hcomp : (dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
      = composeΦ ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k (dJf r).nPins
          ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
          ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
    (hpins : ∀ X q', q' < (dJf r).nPins →
      (dJf r).pinCar (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) X q'
        = pinsCar ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k (dJf r).nPins
            ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
            ((dJf r).Ψaux (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) X q')
    {mm : List Nat} {lpsR : List Name}
    (hroot : ∀ c, c < (dJf r).k → σ c = p.k + r + c)
    (hpinσ : ∀ c, ¬ c < (dJf r).k → c < (dJf r).k + (dJf r).nPins →
      σ c = p.k + mm.getD (c - (dJf r).k) 0)
    (hmmLen : mm.length = (dJf r).nPins)
    (hψR : ((D).pinAt r).ψJ ψ = Level.substFn ψ lpsR ((D).pinAt r).lvls)
    (hcorr : ∀ qK, qK < (dJf r).nPins →
      PinCorr ((D).targetView m.acval ψ) m.acval (dJf r) (((D).pinAt r).ψJ ψ)
        (((D).pinAt r).Ds ψ) lpsR ((D).pinAt r).lvls (p.k + mm.getD qK 0) qK)
    {q : Nat} (hq : q < pinsS.length)
    (hpool : (∃ i, i < kR ∧ q = r + i) ∨ mm.contains q = true) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) := by
  obtain ⟨c, hc, hcp, hσc⟩ := nestedClassPinAt_of_instMap (ρp := ρp) m hgroups GR CR hB hshR
    hroot hpinσ hmmLen hψR hcorr hq hpool
  exact nestedPinLfp_of_root_class hOk m dJf hgroups hρp hB hdJfB GR hshR hw hσ hmonoJ hmapsJ
    hclJ hfcJ hIs hΦ hcomp hpins c q hc hc hcp hσc

end RootClass

end ConLeche.Model
