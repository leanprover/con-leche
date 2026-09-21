module

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
  `nestedPinPairAt_pinσ`.  **That pair of theorems no longer lives
  here** (task #315 WIDE, the merge session): its consumer is in
  `NestedPinLeafAll.lean`, which this module IMPORTS, so
  `copyDomRec_via` and `nestedPinDomRec_of_dom₂` moved there and
  `hdom₁rec` is discharged at the assembly.  The reading they carry is
  unchanged: at a field the container calls recursive the two copies'
  slots are ONE slot up to the family (`CopyCtorShape.slot_container`,
  `copyTarget_u`, `slotSet_congr_below`) and the two families are
  EQUAL by the class equation, so the arm is the OWNER's bound
  `hdom₂` read on the other side, and the ordering it spends is the
  one `dom₂_of_run` already spends — `hY`/`hYC` at the OWNER, with no
  `S` and no `TupleLe` at the group's own pins.

The entry producer IS consumed: `nestedPinWideStep` no longer takes
`hent` at all, and builds it here from `hIH`/`hPfGroup` and `hout`.
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
    {Pf : Nat → V}
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
      Pf ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0) - p.k) = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0) - p.k))) :
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
  exact nestedPinEntryOutEq hμ h hbk m hleafM dJf hgroups hρp G hPfGroup hi hjA hout
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
    {Pf : Nat → V}
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
      Pf ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k) = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k))) :
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
  exact nestedPinsEntryOrd_at hμ h hbk m hleafM dJf hgroups hρp hPfGroup G hi' hj
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
because it is a run fact and this statement is not.

**`hmmIdx` says a VALUE of the map is a value at a CLASS, and that is
what the proof spends** (task #315 WIDE (f8), lane WIRE): the pin
branch needs the position it finds `q` at to be a container class, and
the length bound `mm.length ≤ d.nPins` that stood here before is FALSE
in general — the map is `containerOwnPinsAt`'s table under
`mapM findIdx?` and `ContainerOwnPinsSyn`'s first clause allows that
table to repeat a pin, hence to be longer than `d.nPins`.  The
producible statement, and the one the caller now owes, is
`NestedPinsRun.instMapOwnIdx` (`NestedInstMap.lean`): clause (1) names
the class of the entry found, clause (2) puts the same entry at that
class, and `mapM`'s pointwise structure carries the value across. -/
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
    (hmmIdx : ∀ z, mm.contains z = true → ∃ qK, qK < (dJf r).nPins ∧ mm.getD qK 0 = z)
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
    obtain ⟨qK, hqK, hqKe⟩ := hmmIdx q hin
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
    -- **THE WIDE IDENTIFICATION, AT EVERY CLASS OF THE INSTANCE** (task
    -- #315 WIDE, the merge session): what stood here was
    -- `ofNested_wide_famAt`'s TEN raw hypotheses, which no run-level
    -- caller can supply — `BlockModel.ofNested`'s unnamed lists are open
    -- in them.  `ofNested_pin_block_of_wide_inst_famAt` (`NestedFit.lean`)
    -- is their assembly at the instance, at exactly the arguments the
    -- per-instance step already applies `ofNested_pin_block_of_wide_inst`
    -- at, so the premise is carried in ITS shape and not in theirs.
    (hwideFam : ∀ c, c < (dJf r).k + (dJf r).nPins →
      lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (σ c)
        = (dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
            (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
              ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
              ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c)
    (c q : Nat) (hcT : c < (dJf r).kT) (hc : c < (dJf r).k + (dJf r).nPins)
    (hcp : ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q)
    (hσc : σ c = p.k + q) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) := by
  have hwide := hwideFam c hc
  rw [nestedPinFam_of_classPin m dJf hgroups hρp hB hdJfB GR hshR c q hcT hcp, ← hwide, hσc]


/-- **(2) COMPOSED: THE PIN'S IDENTIFICATION FROM THE POOL ALONE**
(task #315 WIDE (f6), lane DOM): `nestedClassPinAt_of_instMap` fed
straight into `nestedPinLfp_of_root_class`, so that the class `c` never
appears in a caller's obligation — what is asked of the run is K.75's
clause (1) at the pin (`hpool`), the closure's two halves
(`hroot`/`hpinσ`), the map's values being values at classes
(`hmmIdx`, `NestedPinsRun.instMapOwnIdx`) and the correspondence at its
entries (`hcorr`, `NestedPinsRun.instMapPinOwn`).

This is `nestedPinsLe_of_wide`'s `hwide` at the pin, up to the ONE
object the lane does not own: every wide hypothesis here
(`hw`/`hσ`/`hmonoJ`/`hmapsJ`/`hclJ`/`hfcJ`/`hIs`/`hΦ`/`hcomp`/`hpins`)
is `ofNested_wide_famAt`'s raw list, and the assembly that discharges
them from `ofNested_pin_block_of_wide_inst`'s own list is `hwideFam`
(`NestedFit.lean`, the main lane's) — see DESIGN's WIDE (f6) row. -/
theorem nestedPinLfp_of_pool {ψ : Name → Nat} {ρp : Nat → V}
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
    -- **THE WIDE IDENTIFICATION AT EVERY CLASS** — carried in
    -- `ofNested_pin_block_of_wide_inst_famAt`'s shape (`NestedFit.lean`),
    -- which is the per-instance step's own application, and not in
    -- `ofNested_wide_famAt`'s raw one (task #315 WIDE, the merge session)
    (hwideFam : ∀ c, c < (dJf r).k + (dJf r).nPins →
      lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (σ c)
        = (dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
            (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
              ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
              ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c)
    {mm : List Nat} {lpsR : List Name}
    (hroot : ∀ c, c < (dJf r).k → σ c = p.k + r + c)
    (hpinσ : ∀ c, ¬ c < (dJf r).k → c < (dJf r).k + (dJf r).nPins →
      σ c = p.k + mm.getD (c - (dJf r).k) 0)
    (hmmIdx : ∀ z, mm.contains z = true → ∃ qK, qK < (dJf r).nPins ∧ mm.getD qK 0 = z)
    (hψR : ((D).pinAt r).ψJ ψ = Level.substFn ψ lpsR ((D).pinAt r).lvls)
    (hcorr : ∀ qK, qK < (dJf r).nPins →
      PinCorr ((D).targetView m.acval ψ) m.acval (dJf r) (((D).pinAt r).ψJ ψ)
        (((D).pinAt r).Ds ψ) lpsR ((D).pinAt r).lvls (p.k + mm.getD qK 0) qK)
    {q : Nat} (hq : q < pinsS.length)
    (hpool : (∃ i, i < kR ∧ q = r + i) ∨ mm.contains q = true) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) := by
  obtain ⟨c, hc, hcp, hσc⟩ := nestedClassPinAt_of_instMap (ρp := ρp) m hgroups GR CR hB hshR
    hroot hpinσ hmmIdx hψR hcorr hq hpool
  exact nestedPinLfp_of_root_class m dJf hgroups hρp hB hdJfB GR hshR hwideFam
    c q hc hc hcp hσc

end RootClass

end ConLeche.Model
