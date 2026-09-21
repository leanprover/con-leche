module

import ConLeche.Model.Inductives.ContainerCross
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

Both objects are UNCONSUMED in this tree: their consumers are the
assembly's `hdom₁rec` and `nestedPinWideStep`'s `hent`, both of which
are still named hypotheses at their call sites.
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

end Run

end ConLeche.Model
