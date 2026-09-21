module

import ConLeche.Model.Inductives.NestedAux
public import ConLeche.Model.Inductives.NestedEntryOrd
public section

/-!
# Step (4): `NestedPinsLe` as an induction over the container INSTANCES, at the TRUE frame

`nestedModeled_of_one` (`NestedChain.lean`) takes one model-tier
premise, `NestedPinsLe V μ F` (`NestedPinLeafAll.lean`): at every pin
`q`, the container's own least tuple at the pin's frame (`pinLfp`) lies
below the auxiliary carrier at slot `p.k + q`.  **Step (4)** is the
discharge of that premise on the WIDE route: the induction skeleton is
`nestedPinsLe_of_rank` over K.52's recorded rank, and the per-instance
step is Resolution 1's identification
(`ofNested_pin_block_of_wide_inst`, `NestedFit.lean`) at the TRUE frame
— not `nestedPinInstLe`, whose chain runs through the narrow
`ofNested_pin_block_of_inst`.

This module states the step and proves the ASSEMBLY around it.  What it
does NOT prove is the per-instance step itself: that step is a named
hypothesis (`hwide`) whose inputs are being built by the lane on
`agent/uniform-le` (the σ clause on `NestedPinGroupIds`, `hrowsσ`,
`hpin`).  `nestedPinWideStep` below is the step SPELLED OUT at those
inputs, so that the assembly can be read against the shape the lane is
producing rather than against a guess.

**The reason the file exists is a scope question, and it is answered
here.**  Every object in both statements is at the RECORDED frame
`consList (Ds.map (interp V ρp)) ρp` — no `pinLfpAt`, no `CandParamFit`,
no `CandIdxAgree`, no candidate component family.  The induction's
hypothesis is the EQUALITY at pins of other instances, which
`nestedPinEq_at_of_le` upgrades from the rank induction's own `FamLe`
per pin.

**THE ENTRIES ARE NO LONGER AN INPUT.**  The identification's `hent`
used to be `CopyEntryA` (i.e. `CopyEntryOut`), asked at every
copy-recursive field whose target leaves the mint GROUP — which
includes the copies of the container's OWN pins, inside the INSTANCE,
where `nestedPinsEntry_at`'s route through `nestedTargetReads_L`'s `S`
at the `pinF` arm is exactly what an induction over instances may not
assume.  The wide route spends the entries only through
`CopyEntryOut.ord`, so the identification was weakened to
`CopyEntryAOrd`, whose guard is the container's ORDINARY fields alone;
and `nestedPinsEntryOrd_of` (`NestedEntryOrd.lean`) produces THAT from
the induction's own two (`hIH`/`hPfGroup`) and from `hout`.

**AND `hout` IS NO LONGER AN INPUT EITHER** (task #315 WIDE (f5)).  At
an ARBITRARY mint group `hout` is FALSE — `tests/e2e/nested_p04.ndjson`
is an ACCEPTED block with two `ordF`-right edges whose endpoints carry
equal instance labels — so `nestedPinWideStep` below runs at the
instance's ROOT group instead (`hrootGrp`), where
`nestedPinsOut_of_root` (`NestedEntryOrd.lean`) builds `hout` out of
the EDGE half (`hedgeAt`, the K.32-shaped lookup bridge) and the LABEL
half (`ConLeche.nestedPinOutLabel`, K.66 + K.75's two clauses + the
roots table's constancy on an instance).  The step therefore takes no
entry hypothesis and no `hout`.
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

section Step4

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

/-- **STEP (4), ASSEMBLED** (task #315 WIDE (4)): `NestedPinsLe`'s
conclusion at the run, from K.52's rank record and ONE per-instance
step at the TRUE frame.

* the MEASURE is `nestedPinRankOf` (K.52, `nestedPinRankOk`), consumed
  through `nestedPinsLe_of_rank`/`pins_le_of_instanceLe`; the instance
  partition is `nestedPinInstOf` and the edges `nestedPinEdges`;
* the INDUCTIVE HYPOTHESIS at a pin `q` is: at every pin `q'` reached
  by an edge from `q`'s own instance and lying in ANOTHER instance,
  `pinLfp = L⁺`.  It arrives from the skeleton as a `FamLe` and is
  upgraded to the equality by `nestedPinEq_at_of_le`, which needs
  nothing but step (ii) (`nestedPinsFixed`) at that one pin;
* the PER-INSTANCE STEP is `hwide`, and it is **RE-INDEXED TO THE
  INSTANCE'S ROOT GROUP** (task #315 WIDE (f5), lane DOM): the pin's own
  least tuple at its recorded frame IS the block's auxiliary carrier at
  slot `p.k + q`, for the pin `q` ITSELF and not for `q`'s own mint
  group's members.  That is the shape `nestedPinLfp_of_root_class`
  (`NestedEntryOrd.lean`) produces — the ROOT's wide identification read
  at a `ClassPinAt` pair of the root group, which K.41 covers the whole
  instance by — so the step no longer decomposes `q` into `q₀ + i` and
  no longer speaks of `q`'s own `GroupFacts`.  **The re-indexing is what
  makes the step provable at all**: its entries need `hout`, and `hout`
  is FALSE at a mint group that is not its instance's root
  (`tests/e2e/nested_p04.ndjson`, DESIGN's WIDE (f3) row).

No candidate frame appears: `ρp` is the block's own, the container's is
`consList (Ds.map (interp V ρp)) ρp` throughout, and `pinLfpAt` is not
mentioned. -/
theorem nestedPinsLe_of_wide (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} {stored : List AuxStored}
    (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    (hpinsLen : st.pins.length = pinsS.length)
    (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    (hwide : ∀ edges : List (Nat × Nat × Bool),
      ConLeche.nestedPinEdges env p b st stored = some edges →
      ∀ q, q < pinsS.length →
      (∀ q₀' q', q₀' < pinsS.length → q' < pinsS.length →
        instLabel env p b st stored q₀' = instLabel env p b st stored q →
        (∃ own : Bool, (q₀', q', own) ∈ edges) →
        instLabel env p b st stored q' ≠ instLabel env p b st stored q →
        pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q'
          = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q')) →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)) :
    ∀ q, q < pinsS.length →
      FamLe ((D).idx ψ ρp (p.k + q)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)) := by
  have key := nestedPinsLe_of_rank (V := V) (k := p.k) (Is := (D).idx ψ ρp)
    (P := pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)
    (L := lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) hrank ?_
  · exact fun q hq => key q (by omega)
  · intro edges hed q hq hIH
    have hq' : q < pinsS.length := by omega
    -- the rank induction hands a `FamLe` at the pins of OTHER instances;
    -- step (ii) upgrades each to the equality the wide step consumes
    have hIHeq : ∀ q₀' q', q₀' < pinsS.length → q' < pinsS.length →
        instLabel env p b st stored q₀' = instLabel env p b st stored q →
        (∃ own : Bool, (q₀', q', own) ∈ edges) →
        instLabel env p b st stored q' ≠ instLabel env p b st stored q →
        pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q'
          = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q') := by
      intro q₀' q' h1 h2 h4 h5 h6
      exact nestedPinEq_at_of_le hμ h h3 hbk m hleafM dJf hgroups hρp h2
        (hIH q₀' q' (by omega) (by omega) h4 h5 h6)
    rw [hwide edges hed q hq' hIHeq]
    exact FamLe.refl _ _



/-! ## The per-instance step, SPELLED OUT at the identification's inputs -/

/-- **STEP (4)'s PER-INSTANCE STEP** (task #315 WIDE (4)): `hwide` of
`nestedPinsLe_of_wide` at ONE mint group, from Resolution 1's
identification `ofNested_pin_block_of_wide_inst` (`NestedFit.lean`).

Everything the RUN already holds about a group is discharged here from
`GroupFacts` and from `NestedLfpOk`; what is left in the signature is
exactly what step (4) is waiting for, and every one of them is a fact
about the instance closure `σ` or about the copies' entries.

* **`hinjJ`** — the class reader's injection at the WIDE width.  At a
  member class it is `injT_of_mem` over `NestedPinGroupSyn.inj` and
  `w`; at a copy of one of the container's OWN pins it is the pin
  constructors' own injection, which rides on the container's
  `PinRecLaws`/`PinShapes` and is not on `GroupFacts`.
* **`hσ`/`hroot`/`hIsσ`** — the instance closure itself: the
  container's classes mapped into the block's pins, contiguous on the
  members, index sets matched.  This is the σ CLAUSE the lane is adding
  to `NestedPinGroupIds`/`NestedPinsIdent`'s fourth conjunct.
* **`hrowsσ`** — the container's rows are constant along σ's fibres
  (`rowsσ_of_pin_class`).
* **`hstgt`/`houtσ`** — K.61's and K.62's run halves
  (`NestedPinsRun.copyPinFInstTgt`, `NestedPinsRun.copyOrdFOutside`,
  `NestedInstMap.lean`), read at the group rather than at the run.
* **`hpin`** — the fit at the copies of the container's OWN pins
  (`hfit_wide_pin_of_class` over `pinClassFit_of_transfer`), whose `hρ`
  is route 1's open item.
* **`hleafM`/`hIH`/`hPfGroup`** — what the copies' ENTRIES cost now
  that they are DERIVED and not assumed.  Both are the induction's own:
  the assembly above hands the first as `hIHeq` at `Pf := pinLfp …`
  (its scope is `NestedOutScope`, the same predicate both speak of),
  and the second is the theorem `pinLfp_group`.
* **`hrootGrp`/`hedgeAt`/`hed`/`hrank`/`hK29`/`hK62`/`hK75pool`/`hK75grp`/`hpinsLen`**
  — what `hout` cost once IT became derived too.  `hrootGrp` is the
  root-only restriction: the group `q₀` IS its instance's root group,
  which K.41 (`nestedPinRootPairOk_inv`) hands at every pin.  `hedgeAt`
  is the only PLUMBING item among them — the K.32-shaped lookup bridge
  between the model's spellings and `nestedPinEdges`' own lookups,
  whose theorem (`nestedPinEdges_mem`, `Verify/Inductives/NestedInv.lean`)
  is in the tree and whose matching belongs in `NestedCopyInst.lean`.
  The two K.75 clauses are measured at zero fires on the shadow suite,
  `init-full` and Mathlib in both modes (DESIGN's WIDE (f4) row), and
  clause (2) is carried on its design argument: the corpus does not
  distinguish it from K.62 at the pin.  **`hout` was NOT
  `nestedPinRankOk`'s clause (2)** — that clause's not-own branch is a
  DISJUNCTION, and the rank induction discharges only its second
  alternative; fourteen edges across eight ACCEPTED blocks are
  `ordF`-right targets inside the source's own instance
  (`nestedPinEntryOutEq`'s docstring, DESIGN §U.92 (c)).

NO candidate-frame object occurs in any of them: the container's side
is read at `consList ((((D).pinAt (q₀+i)).Ds ψ).map (interp V ρp)) ρp`
throughout, which is the RECORDED frame, and `pinLfpAt`,
`CandParamFit`, `CandIdxAgree` and `hentR` are absent. -/
theorem nestedPinWideStep (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    {st : ElimState} {stored : List AuxStored} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {σ : Nat → Nat}
    -- the class reader's injection at the WIDE width, at a class of
    -- the wide space (the bound arrived with the widened
    -- `ofNested_pin_block_of_wide_inst`, task #315 WIDE (f3))
    (hinjJ : ∀ i', i' < (dJf q₀).k + (dJf q₀).nPins → ∀ j fs,
      (dJf q₀).injT (dJf q₀).pinCtors (((D).pinAt (q₀ + i)).ψJ ψ) i' j fs
        = injW (f₀.s.eval ψ) j (mkTower (fs ++ [pt])))
    (hrowsσ : ∀ Y, InTupleSpace (f₀.s.eval ψ) ((dJf q₀).k + (dJf q₀).nPins)
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) Y →
      FibreConst σ ((dJf q₀).k + (dJf q₀).nPins) Y →
      FibreConst σ ((dJf q₀).k + (dJf q₀).nPins)
        ((dJf q₀).Ψaux (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) Y))
    (hσ : ∀ i', i' < (dJf q₀).k + (dJf q₀).nPins → σ i' < p.k + pinsS.length)
    (hroot : ∀ i', i' < (dJf q₀).k → σ i' = p.k + q₀ + i')
    (hIsσ : ∀ i', i' < (dJf q₀).k + (dJf q₀).nPins →
      idxSet (nestedU p.k W pinsS ψ (σ i')) ρp (blockIds b.nP ppsF ψ (σ i'))
        = (dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i')
    -- **THE ENTRIES, NO LONGER A HYPOTHESIS** (task #315 WIDE (f3),
    -- lane DOM): `nestedPinsEntryOrd_of` (`NestedEntryOrd.lean`)
    -- produces `CopyEntryAOrd` from the induction's own two and from
    -- `hout` alone -- and **`hout` itself is no longer a hypothesis
    -- either** (task #315 WIDE (f5)).  `hout` is FALSE at an arbitrary
    -- mint group (DESIGN's WIDE (f3) row, `nested_p04`), so the step
    -- runs at the instance's ROOT group: `hrootGrp` says so, and
    -- `nestedPinsOut_of_root` builds `hout` there from the EDGE half
    -- (`hedgeAt`, the K.32-shaped lookup bridge, whose theorem is
    -- `nestedPinEdges_mem` and whose plumbing lives in
    -- `NestedCopyInst.lean`) and the LABEL half
    -- (`ConLeche.nestedPinOutLabel`: K.66, K.75's two clauses and the
    -- roots table's constancy on an instance).
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {edges : List (Nat × Nat × Bool)}
    (hed : ConLeche.nestedPinEdges env p b st stored = some edges)
    (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    (hK29 : ConLeche.nestedGroupsOk env p st = true)
    (hK62 : ConLeche.nestedOrdOutsideOk env p b st stored = true)
    (hK75pool : ∀ q, q < st.pins.length → ∀ g,
      (ConLeche.nestedPinRootGroup env p b st stored).getD q none = some g →
      (st.pins.getD q default).grpBase = g ∨
        ∃ i, i < st.pins.length ∧ (st.pins.getD i default).grpBase = g ∧
          ∃ mi, ConLeche.nestedInstMapAt env st i = some mi ∧ mi.contains q = true)
    (hK75grp : ∀ s' t', (s', t', false) ∈ edges →
      ∀ d, d < (st.pins.getD s' default).grpSize →
      ∀ mi, ConLeche.nestedInstMapAt env st ((st.pins.getD s' default).grpBase + d) = some mi →
        mi.contains t' = false)
    (hpinsLen : st.pins.length = pinsS.length)
    (hrootGrp : (ConLeche.nestedPinRootGroup env p b st stored).getD (q₀ + i) none = some q₀)
    (hedgeAt : ∀ i' j, i' < kJ → j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k →
      ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k < pinsS.length ∧
        (q₀ + i', (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k, false) ∈ edges))
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length →
      NestedOutScope env p b st stored edges pinsS.length (q₀ + i) q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ a kk, GF st m a kk (dJf a) → ∀ i', i' < kk →
      Pf (a + i') = lfpTuple (f₀.s.eval ψ) (dJf a).k
        ((dJf a).idx (((D).pinAt (a + i')).ψJ ψ)
          (consList ((((D).pinAt (a + i')).Ds ψ).map (interp V ρp)) ρp))
        ((dJf a).Φ (((D).pinAt (a + i')).ψJ ψ)
          (consList ((((D).pinAt (a + i')).Ds ψ).map (interp V ρp)) ρp)) i')
    (hstgt : ∀ i', i' < (dJf q₀).k → ∀ j, j < ((dJf q₀).ctorsM i').length → ∀ l,
      l < (((dJf q₀).Fss i' (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss i').getD j []).getD l false = true →
      ¬ (dJf q₀).tgts i' j l < (dJf q₀).k →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = σ ((dJf q₀).tgts i' j l))
    (houtσ : ∀ i', i' < (dJf q₀).k → ∀ j, j < ((dJf q₀).ctorsM i').length → ∀ l,
      l < (((dJf q₀).Fss i' (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ¬ ∃ mm, mm < (dJf q₀).k + (dJf q₀).nPins ∧
        σ mm = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
    (hpin : ∀ Y, InTupleSpace (f₀.s.eval ψ) ((dJf q₀).k + (dJf q₀).nPins)
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) Y →
      FibreConst σ ((dJf q₀).k + (dJf q₀).nPins) Y →
      TupleLe ((dJf q₀).k + (dJf q₀).nPins)
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) Y
        (lfpTuple (f₀.s.eval ψ) ((dJf q₀).k + (dJf q₀).nPins)
          ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          ((dJf q₀).Ψaux (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))) →
      ∀ i', ¬ i' < (dJf q₀).k → i' < (dJf q₀).k + (dJf q₀).nPins → ∀ t,
      t ∈ˢ (dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i' →
      ∀ j fs,
      (b.ownOffset (σ i') + j < (blkFss0 b ctorsA kinds dsF ψ).length ∧
        (mutMems ctorsA.length (mutMemF b)).getD (b.ownOffset (σ i') + j) 0 = σ i' ∧
        FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (σ i') + j) [])
          (fun i'' ρ => slotSet (f₀.s.eval ψ)
            (nestedU p.k W pinsS ψ
              (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (σ i') + j) []).getD i'' 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (σ i') + j) []).getD i'' [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (σ i') + j) []).getD i'' [])
            (setJoin σ ((dJf q₀).k + (dJf q₀).nPins)
              (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) Y
              (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (σ i') + j) []).getD i'' 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (σ i') + j) []) fs ∧
        (∀ l, l < (blockIds b.nP ppsF ψ (σ i')).length →
          interp V (consList fs ρp)
              (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (σ i') + j) []).getD l default)
            = projS l t))
      ↔ (j < ((dJf q₀).ctorsT (dJf q₀).pinCtors i').length ∧
          (dJf q₀).ChainFitT (dJf q₀).pinCtors (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) Y t i' j fs)) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i) := by
  -- **THE SCOPE, SPENT AT ONCE** (task #315 WIDE, the merge session):
  -- `nestedPinsOut_of_root` puts an `ordF`-right target in the rank
  -- induction's scope, `hedgeAt` carries its bound, and `hIH` turns the
  -- pair into the EQUALITY the entry producer now asks for -- `S` is
  -- no longer a premise anywhere below `nestedTargetReads_L`.
  have hscopeOut := nestedPinsOut_of_root m hed hrank hK29 hK62 hK75pool hK75grp hpinsLen
    dJf G hi hrootGrp hedgeAt
  have hent := nestedPinsEntryOrd_of hμ h hbk m hleafM dJf hgroups hρp hPfGroup G hi
    (fun i' j hi' hj l hl h1 h2 h3 =>
      hIH _ (hedgeAt i' j hi' hj l hl h1 h2 h3).1 (hscopeOut i' j hi' hj l hl h1 h2 h3))
  have hkE : (dJf q₀).k = kJ := G.syn.kEq
  subst hkE
  have hseg := G.syn.seg
  have hkpos := G.syn.kpos
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinsBound m dJf hgroups hρp)
  have hρp' : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp := hρp
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored i hi
  have hρJ : Sat V ((dJf q₀).params (((D).pinAt (q₀ + i)).ψJ ψ)).reverse
      (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) := by
    obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
    subst hρe
    exact (dJf q₀).satOfSpine (G.syn.DsFit i hi ψ ρ as hsp)
  have hwide : (D).pinCar ψ ρp
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = lfpTuple ((dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ)) (dJf q₀).k
          ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i :=
    ofNested_pin_block_of_wide_inst (V := V) (m := m) (σ := σ) m.acval
    (dJ := dJf q₀) (ψJ := ((D).pinAt (q₀ + i)).ψJ ψ) (Ds := ((D).pinAt (q₀ + i)).Ds ψ)
    (DsE := ((D).pinAt (q₀ + i)).DsE) (lpsJ := cvT.levelParams)
    (lvlsJ := ((D).pinAt (q₀ + i)).lvls)
    (memberNames := (fms.take p.k).map (·.cvTa.name))
    hOk (nestedShape_of_formers h hbk ψ) (by omega) G.syn.reps (G.syn.typed _)
    (G.syn.pinsTyped _) (by omega) (G.syn.w i hi ψ) hrowsσ hσ hroot hIsσ hinjJ
    (fun i' hi' => by
      rw [Nat.add_assoc, nestedU_pin]; exact G.syn.pinU i hi ψ i' (by omega))
    hρJ (fun i' hi' => G.idx i hi ψ i' (by omega))
    (fun i' hi' j => ownCtors_grp h3 h.lenA ψ (G.syn.ctorCount i' (by omega)) j)
    (fun i' hi' j hj => G.shape i hi cvT caps hfind ψ ρp hρp' i' j (by omega) hj)
    hent hstgt houtσ hpin (i := i) (by omega)
  rw [hwide, pinLfp_group G hi, G.syn.w i hi ψ]

end Step4

end ConLeche.Model
