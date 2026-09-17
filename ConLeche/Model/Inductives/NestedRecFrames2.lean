module

public import ConLeche.Model.Inductives.NestedRecFrames
import ConLeche.Model.Inductives.NestedRecFibre
import ConLeche.Model.Inductives.NestedRecTyped
import ConLeche.Model.Inductives.NestedRecRead
import ConLeche.Model.Inductives.NestedPinLaws
import ConLeche.Model.Inductives.BlockComposed
import ConLeche.Model.Inductives.BlockRecKit
import ConLeche.Model.Inductives.BlockRecTyped
import ConLeche.Model.Inductives.NestedAux
import ConLeche.Model.Inductives.MutualRecsStage
public section

/-!
# The restored readings' FRAMES (task #315, M7-2, PLAN-M7 §1e step 2)

`NestedRecFrames.lean`'s continuation: the nine clauses of
`BlockModel.ReadingFramesT` at a restored recursor type's reading,
and with them the named fact `NestedRecFramesOf` — modulo the three
model faces K.35 (`NestedRecTysAuxOk`), K.36 (`NestedCtorPinNames`)
and `hctorsJ`.

The route is the transfer `NestedTailIn.spineFit_transfer`: a spine
fitting the RESTORED reading fits the SCRATCH one, whose frame
inversion is the MUTUAL `IsBlockModels.spineFit_recData_inv` at the
auxiliary block's own block model `DA`; the frame's semantic clauses
then move to the composed model `D` through the fibre kit
(`NestedRecFibre.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## Kit -/

/-- A spine's entry reads off the tuple it builds. -/
theorem getD_eq_projS_tupW {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) {l : Nat} (hl : l < is.length) :
    is.getD l pt = projS l (tupW u is) := by
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero, projS_pt]
    have hr := spineFit_zero_replicate hI.2 hsp
    rw [hr, List.getD_eq_getElem?_getD,
      List.getElem?_replicate_of_lt (by rw [hr, List.length_replicate] at hl; exact hl)]
    rfl
  · rw [tupW_pos hu, projS_mkTower l is hl, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl]
    rfl

/-- Two lists of one length whose entries are the same projections are
one list. -/
theorem list_ext_projS {E is : List V} {t : V} (hE : E.length = is.length)
    (h1 : ∀ l, l < is.length → E.getD l pt = projS l t)
    (h2 : ∀ l, l < is.length → is.getD l pt = projS l t) : E = is := by
  refine List.ext_getElem hE fun l hl hl' => ?_
  have e1 := h1 l hl'
  have e2 := h2 l hl'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl'] at e2
  exact e1.trans e2.symm


/-! ## The run's section -/

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "ENV2" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- the COMPOSED nested block's block model -/
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- the SCRATCH (auxiliary) block's block model — the MUTUAL one -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

/-- the pins' constructors at the nested block model -/
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- the pin groups at the restored environment's model -/
local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- the composed model's auxiliary tuple operator -/
local notation "ΨN" => (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
  (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
  (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
  (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
  (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ))

/-- the COMPOSED model's extended least tuple -/
local notation "Lcomp" ψ₀:max ρ₀:max => (lfpTuple (f₀.s.eval ψ₀) (p.k + pinsS.length)
  (nestedIs b.nP p.k ppsF W pinsS ψ₀ ρ₀) (ΨN ψ₀ ρ₀))

/-- the SCRATCH block's least tuple -/
local notation "Laux" ψ₀:max ρ₀:max =>
  (lfpTuple (BlockModel.w (DA) ψ₀) (BlockModel.k (DA)) (BlockModel.idx (DA) ψ₀ ρ₀)
    (BlockModel.Φ (DA) ψ₀ ρ₀))

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-! ### The classes' bookkeeping -/

/-- **A CLASS'S CONSTRUCTOR COUNT IS ITS COPY'S**: a member class's
restored constructors are as many as its auxiliary ones
(`NestedStageFacts.ctorsLen`), a pin class's are the copy's
(`nestedPc_ctors_length`). -/
theorem NestedTailIn.ctorsT_length (c : Nat) :
    ((D).ctorsT PC c).length = ((DA).ctorsM c).length := by
  have hown : ((DA).ctorsM c).length = (b.ownCtors c).length := by
    show ((b.ownCtors c).map fun q => ctorsA.getD q.1 default).length = _
    exact List.length_map _
  rw [hown]
  by_cases hck : c < p.k
  · rw [BlockModel.ctorsT_of_mem hck]
    show ((ctorsR.getD c []).map fun cc => (cc.1, cc.2.2)).length = _
    rw [List.length_map]
    exact I.out.stage.ctorsLen c hck
  · rw [BlockModel.ctorsT_of_pin hck]
    show (PC (c - p.k)).ctors.length = _
    rw [nestedPc_ctors_length, Nat.add_sub_cancel' (Nat.le_of_not_lt hck)]

/-- **THE MINOR INDEX IS THE AUXILIARY BLOCK'S** — both the sum of the
earlier classes' constructor counts, which `ctorsT_length` identifies
position by position. -/
theorem NestedTailIn.minorIdxT_eq (c j : Nat) :
    (D).minorIdxT PC c j = (DA).minorIdx c j := by
  rw [mutualBlockModel_minorIdx]
  show ((List.range c).map fun t => ((D).ctorsT PC t).length).sum + j = _
  have hsum : ∀ n, n ≤ c → ((List.range n).map fun t => ((D).ctorsT PC t).length).sum
      = b.ownOffset n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega),
        ConLeche.ownOffset_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      congr 1
      rw [I.ctorsT_length n]
      show ((b.ownCtors n).map fun q => ctorsA.getD q.1 default).length = _
      exact List.length_map _
  rw [hsum c (Nat.le_refl _)]

omit I in
/-- **THE INJECTIONS AGREE**: both the tagged tower at the MEMBER-LOCAL
position over the block's one sort. -/
theorem nestedInjT_eq (ψ : Name → Nat) (c j : Nat) (fs : List V) :
    (D).injT PC ψ c j fs = (DA).inj ψ c j fs := by
  unfold BlockModel.injT
  split <;> rfl

/-! ### The composed carrier -/

/-- The sealed former's premise at a parameter frame of the run. -/
theorem NestedTailIn.lfpOk (ψ : Name → Nat) (ρ : Nat → V) (as : List V)
    (hsp : SpineFit ρ ((D).params ψ) as) :
    NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) ψ (consList as ρ) :=
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  nestedLfpOk_of_formers I.out.facts I.hμ I.out.bk ψ (consList as ρ) hρp
    (nestedPinBound_of mp₂.base2 I.out.stage.groups ψ _ hρp)

/-- **A CLASS'S FAMILY AT THE BLOCK'S CARRIER IS THE COMPOSED LEAST
TUPLE'S COMPONENT** — a member's by Bekić (`ofNested_lfp`), a pin's by
the pins' carriers at the carrier (`ofNested_pinCar_lfp`). -/
theorem NestedTailIn.famAt_lfp (ψ : Name → Nat) (ρ : Nat → V) (as : List V)
    (hsp : SpineFit ρ ((D).params ψ) as) {tgt : Nat} (htgt : tgt < b.k) :
    (D).famAt ψ (consList as ρ)
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) tgt
      = (Lcomp ψ (consList as ρ)) tgt := by
  have hOk := I.lfpOk ψ ρ as hsp
  have hbk := I.out.bk
  have hkk : (D).k = p.k := rfl
  by_cases hck : tgt < (D).k
  · rw [(D).famAt_of_mem hck]
    exact ofNested_lfp hOk (by rw [← hkk]; exact hck)
  · have hck' : ¬ tgt < p.k := by rw [hkk] at hck; exact hck
    have hq : tgt - p.k < pinsS.length := by omega
    have h : (D).pinCar ψ (consList as ρ)
          (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)))
          (tgt - (D).k)
        = (Lcomp ψ (consList as ρ)) (p.k + (tgt - p.k)) :=
      ofNested_pinCar_lfp hOk hq
    rw [(D).famAt_of_pin hck, h, Nat.add_sub_cancel' (Nat.le_of_not_lt hck')]

/-! ### The index spines -/

/-- **A CLASS'S INDEX SPINE, AT THE COMPOSED FRAME AND AT THE
AUXILIARY BLOCK'S**: a member's telescope is the block's own; a pin's
is its container member's, which the group's `idx` identifies with the
copy's under instantiation at the components (`spineFit_instTele`). -/
theorem NestedTailIn.idsT_iff (ψ : Name → Nat) (ρ : Nat → V) (as : List V)
    {c : Nat} (hc : c < b.k) (is : List V) :
    SpineFit ((D).frameT c ψ (consList as ρ)) ((D).IdsT c ψ) is
      ↔ SpineFit (consList as ρ) (blockIds b.nP ppsF ψ c) is := by
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · rw [BlockModel.frameT_of_mem hck, BlockModel.IdsT_of_mem hck]
    exact Iff.rfl
  · rw [hkk] at hck
    obtain ⟨q, rfl⟩ : ∃ q, c = p.k + q := ⟨c - p.k, by omega⟩
    have hq : q < pinsS.length := by have := I.out.bk; omega
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := I.out.stage.groups q hq
    rw [BlockModel.frameT_of_pin (d := (D)) hck, BlockModel.IdsT_of_pin (d := (D)) hck, hkk,
      show p.k + (q₀ + i) - p.k = q₀ + i from by omega, G.pinIds hi ψ,
      show p.k + (q₀ + i) = p.k + q₀ + i from by omega, G.idx i hi ψ i hi]
    have h := spineFit_instTele (V := V) (((D).pinAt (q₀ + i)).Ds ψ) (consList as ρ)
      (dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)) [] is
    rw [List.length_nil] at h
    exact h.symm


/-! ### The constructors' tables -/

/-- A class's constructor at the COMPOSED model, from its copy's. -/
theorem NestedTailIn.ctorsD_get {c : Nat} (hc : c < p.k) {j : Nat}
    (hj : j < ((DA).ctorsM c).length) : ∃ cR, ((D).ctorsM c)[j]? = some cR := by
  have hlen : ((D).ctorsM c).length = ((DA).ctorsM c).length := by
    rw [← I.ctorsT_length c, BlockModel.ctorsT_of_mem (pc := PC) hc]
  exact ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hj)⟩

/-- **A FIELD'S TARGET IS ITS COPY'S**: both the auxiliary block's
kind table at the constructor's global position. -/
theorem NestedTailIn.tgtsT_eq {c : Nat} {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) {l : Nat} (hl : l < cA.2) :
    (D).tgtsT PC c j l = (DA).tgts c j l := by
  obtain ⟨hJl, hcAg, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hnf : mutNFOf ctorsA (b.ownOffset c + j) = cA.2 := by
    show (ctorsA.getD (b.ownOffset c + j) default).2 = cA.2
    rw [List.getD_eq_getElem?_getD, hcAg]
    rfl
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · rw [BlockModel.tgtsT_of_mem hck]
    rfl
  · rw [hkk] at hck
    rw [BlockModel.tgtsT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + (c - p.k)) + j) []).getD l 0 = _
    rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hck)]
    exact mutTgts_getD hJl (by rw [hnf]; exact hl)

/-- **A FIELD'S REFLEXIVE TELESCOPE IS ITS COPY'S**. -/
theorem NestedTailIn.teleAtT_eq (ψ : Name → Nat) {c : Nat} {j : Nat}
    {cA : ConstantVal × Nat} (hjA : ((DA).ctorsM c)[j]? = some cA) (l : Nat) :
    (D).teleAtT PC ψ c j l = ((DA).tssF c j ψ).getD l [] := by
  obtain ⟨hJl, -, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · obtain ⟨cR, hjD⟩ := I.ctorsD_get (by rw [hkk] at hck; exact hck)
      (List.getElem?_eq_some_iff.mp hjA).1
    rw [BlockModel.teleAtT_of_mem hck]
    show (((D).tlss c ψ).getD j []).getD l [] = _
    rw [IsBlockModel.tlss_getD hjD]
    rfl
  · rw [hkk] at hck
    show (((D).tlssT PC ψ c).getD j []).getD l [] = _
    rw [BlockModel.tlssT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show (((mutTlss ctorsA.length tssF ψ).drop (b.ownOffset (p.k + (c - (D).k)))).getD j
      []).getD l [] = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, mutTlss_getD hJl]
    rfl

/-- **A FIELD'S INDEX EXPRESSIONS ARE ITS COPY'S**. -/
theorem NestedTailIn.eisAtT_eq (ψ : Name → Nat) {c : Nat} {j : Nat}
    {cA : ConstantVal × Nat} (hjA : ((DA).ctorsM c)[j]? = some cA) (l : Nat) :
    (D).eisAtT PC ψ c j l = ((DA).eissF c j ψ).getD l [] := by
  obtain ⟨hJl, -, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · obtain ⟨cR, hjD⟩ := I.ctorsD_get (by rw [hkk] at hck; exact hck)
      (List.getElem?_eq_some_iff.mp hjA).1
    rw [BlockModel.eisAtT_of_mem hck]
    show (((D).Eiss c ψ).getD j []).getD l [] = _
    rw [IsBlockModel.Eiss_getD hjD]
    rfl
  · rw [hkk] at hck
    show (((D).EissT PC ψ c).getD j []).getD l [] = _
    rw [BlockModel.EissT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show (((mutEiss0 ctorsA.length eissF ψ).drop (b.ownOffset (p.k + (c - (D).k)))).getD j
      []).getD l [] = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, mutEiss0_getD hJl]
    rfl


/-! ### The recursive slots -/

/-- **THE SCRATCH BLOCK'S RECURSIVE SLOTS ARE THE COMPOSED CLASS'S**:
at every class and every recursive field, the auxiliary block's slot
at ITS least tuple is the extended slot of the nested block model at
the COMPOSED carrier — the two tables are one (`tgtsT_eq`,
`teleAtT_eq`, `eisAtT_eq`) and the two families agree at every index
spine the slot ever reads (`slotSet_congr_appU` at the fibre identity
F3, the readings' fits `rec_eis_fit`/`refl_eis_fit` at the scratch
block). -/
theorem NestedTailIn.slotT_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) {l : Nat} (hl : l < cA.2)
    (hr : (rsOf ((DA).ksF c j)).getD l false = true)
    {fs' : List V} (hfs' : SpineFit (consList as ρ) ((((DA).Fss c ψ).getD j []).take l) fs') :
    (DA).slotAt ψ (Laux ψ (consList as ρ)) c j l (consList fs' (consList as ρ))
      = (D).slotAtT PC ψ ((D).famAt ψ (consList as ρ)
            (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))))
          c j l (consList fs' (consList as ρ)) := by
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ) := hρp
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c hc
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  have hcd := hIA.ctorData hjA
  have hiK : l < ((DA).ksF c j).length := by rw [hcd.ksLen]; exact hl
  have htgt : (DA).tgts c j l < b.k := hIA.tgt_lt hjl hiK rfl
  have hk : ((DA).ksF c j).getD l .ordinary = .recursive ∨
      ((DA).ksF c j).getD l .ordinary = .reflexive := by
    unfold rsOf at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiK,
      Option.map_some, Option.getD_some, decide_eq_true_iff] at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiK]
    exact hr
  rw [(DA).slotAt_of_mem htgt, IsBlockModel.tlss_getD hjA, IsBlockModel.Eiss_getD hjA]
  show _ = slotSet ((D).w ψ) ((D).uT ((D).tgtsT PC c j l) ψ)
      (consList fs' (consList as ρ)) ((D).teleAtT PC ψ c j l) ((D).eisAtT PC ψ c j l)
      ((D).famAt ψ (consList as ρ) (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ))
        ((D).Φ ψ (consList as ρ))) ((D).tgtsT PC c j l))
  rw [I.tgtsT_eq hjA hl, I.teleAtT_eq ψ hjA l, I.eisAtT_eq ψ hjA l,
    I.famAt_lfp ψ ρ as hsp htgt, ofNested_uT]
  refine slotSet_congr_appU fun bs hbs => ?_
  refine I.fibreAt ψ ρ as hsp htgt _ ?_
  rcases hk with hk | hk
  · have htn : ((DA).tssF c j ψ).getD l [] = [] :=
      hcd.tssNone ψ l (by rw [hk]; exact fun hh => nomatch hh)
    rw [htn] at hbs
    cases bs with
    | nil => exact S.reps.rec_eis_fit (S.typed ψ).1 hc hjA hρpA hl htgt hk hfs'
    | cons _ _ => exact hbs.elim
  · exact S.reps.refl_eis_fit (S.typed ψ).1 hc hjA hρpA hl htgt hk hfs' hbs


/-! ### The field lists -/

/-- **A CLASS'S RECURSIVE FLAGS ARE ITS COPY'S** — the auxiliary
block's kind table at the constructor's global position, at a member
and at a pin alike. -/
theorem NestedTailIn.rssT_eq {c : Nat} {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) :
    ((D).rssT PC c).getD j [] = ((DA).rss c).getD j [] := by
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨hJl, -, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  rw [IsBlockModel.rss_getD (d := (DA)) (mm := c) hjl]
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · obtain ⟨cR, hjD⟩ := I.ctorsD_get (by rw [hkk] at hck; exact hck) hjl
    rw [BlockModel.rssT_of_mem hck,
      IsBlockModel.rss_getD (d := (D)) (mm := c) (List.getElem?_eq_some_iff.mp hjD).1]
    rfl
  · rw [hkk] at hck
    rw [BlockModel.rssT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show ((blkRss ctorsA kinds).drop (b.ownOffset (p.k + (c - (D).k)))).getD j [] = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, blkRss_getD hJl]
    rfl

/-- A class's constructor at the COMPOSED model has the copy's field
count (`NestedStageFacts.domFacts`: the restore keeps the telescope's
length). -/
theorem NestedTailIn.nFR_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {c : Nat} (hc : c < p.k) (hcb : c < b.k) {j : Nat} {cR : ConstantVal × Nat}
    (hjD : ((D).ctorsM c)[j]? = some cR) {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) : cR.2 = cA.2 := by
  obtain ⟨cvT, cvR, mI, rP, rules, hID⟩ := I.out.reps c hc
  obtain ⟨cvT', cvR', mI', rP', rules', hIA⟩ := S.reps c hcb
  have hjl : j < (ctorsR.getD c []).length := by
    have hh : j < ((ctorsR.getD c []).map fun cc => (cc.1, cc.2.2)).length :=
      (List.getElem?_eq_some_iff.mp hjD).1
    rwa [List.length_map] at hh
  obtain ⟨hlenEq, -, -⟩ := I.out.stage.domFacts c j (fun _ => 0) hc hjl
  have h1 : ((D).dsF c j (fun _ => 0)).length = (D).nP + cR.2 := (hID.ctorData hjD).len _
  have h2 : ((DA).dsF c j (fun _ => 0)).length = (DA).nP + cA.2 := (hIA.ctorData hjA).len _
  have h3 : ((D).dsF c j (fun _ => 0)).length = ((DA).dsF c j (fun _ => 0)).length := hlenEq
  have h4 : (D).nP = b.nP := rfl
  have h5 : (DA).nP = b.nP := rfl
  omega


/-- **A CLASS'S FIELD COUNT IS ITS COPY'S**: at a member the restore
keeps the telescope's length (`nFR_eq`), at a pin the shadow list is
the copy's field count long. -/
theorem NestedTailIn.FssT_len_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) :
    (((D).FssT PC ψ c).getD j []).length = cA.2 := by
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨hJl, hcAg, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hnf : mutNFOf ctorsA (b.ownOffset c + j) = cA.2 := by
    show (ctorsA.getD (b.ownOffset c + j) default).2 = cA.2
    rw [List.getD_eq_getElem?_getD, hcAg]
    rfl
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · have hck' : c < p.k := by rw [hkk] at hck; exact hck
    obtain ⟨cR, hjD⟩ := I.ctorsD_get hck' hjl
    obtain ⟨cvT, cvR, mI, rP, rules, hID⟩ := I.out.reps c hck'
    rw [BlockModel.FssT_of_mem hck, hID.Fss_length hjD ψ]
    exact I.nFR_eq S hck' hc hjD hjA
  · rw [hkk] at hck
    rw [BlockModel.FssT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show (((blkFss0 b ctorsA kinds dsF ψ).drop (b.ownOffset (p.k + (c - (D).k)))).getD j
      []).length = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, blkFss0_getD hJl,
      shadowFs_length, hnf]

/-- **A CLASS'S ORDINARY FIELD DOMAINS ARE ITS COPY'S**: the restore
touches only the NESTED (hence recursive) field domains
(`NestedStageFacts.domFacts`), and a pin's shadow list is the copy's
domains off the recursive positions. -/
theorem NestedTailIn.FssT_getD_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) {l : Nat} (hl : l < cA.2)
    (hnr : (rsOf ((DA).ksF c j)).getD l false = false) :
    (((D).FssT PC ψ c).getD j []).getD l default
      = (((DA).Fss c ψ).getD j []).getD l default := by
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨hJl, hcAg, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hnf : mutNFOf ctorsA (b.ownOffset c + j) = cA.2 := by
    show (ctorsA.getD (b.ownOffset c + j) default).2 = cA.2
    rw [List.getD_eq_getElem?_getD, hcAg]
    rfl
  obtain ⟨cvT', cvR', mI', rP', rules', hIA⟩ := S.reps c hc
  have hlenA : ((DA).dsF c j ψ).length = b.nP + cA.2 := (hIA.ctorData hjA).len ψ
  have hDA : (((DA).Fss c ψ).getD j []).getD l default
      = (((dsF (b.ownOffset c + j) ψ).drop b.nP).map (·.2.2)).getD l default := by
    rw [IsBlockModel.Fss_getD (d := (DA)) (mm := c) hjA ψ]
    rfl
  have hkk : (D).k = p.k := rfl
  rw [hDA]
  by_cases hck : c < (D).k
  · have hck' : c < p.k := by rw [hkk] at hck; exact hck
    obtain ⟨cR, hjD⟩ := I.ctorsD_get hck' hjl
    have hjlR : j < (ctorsR.getD c []).length := by
      have hh : j < ((ctorsR.getD c []).map fun cc => (cc.1, cc.2.2)).length :=
        (List.getElem?_eq_some_iff.mp hjD).1
      rwa [List.length_map] at hh
    obtain ⟨hlenEq, -, hdom⟩ := I.out.stage.domFacts c j ψ hck' hjlR
    have hlenR : (dsR c j ψ).length = b.nP + cA.2 := by rw [hlenEq]; exact hlenA
    rw [BlockModel.FssT_of_mem hck, IsBlockModel.Fss_getD (d := (D)) (mm := c) hjD ψ]
    show (((dsR c j ψ).drop b.nP).map (·.2.2)).getD l default = _
    rw [fields_getD (by rw [List.length_drop, hlenR]; omega),
      fields_getD (by rw [List.length_drop]; omega), getD_drop, getD_drop]
    have := hdom l (Or.inr hnr)
    rw [this]
  · rw [hkk] at hck
    rw [BlockModel.FssT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show (((blkFss0 b ctorsA kinds dsF ψ).drop
      (b.ownOffset (p.k + (c - (D).k)))).getD j []).getD l default = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, blkFss0_getD hJl,
      List.getD_eq_getElem?_getD, shadowFs_getElem? (by rw [hnf]; exact hl), Option.getD_some,
      if_neg]
    rintro ⟨-, hd⟩
    rw [Nat.add_sub_cancel_left] at hd
    have hiK : l < ((DA).ksF c j).length := by rw [(hIA.ctorData hjA).ksLen]; exact hl
    have h := (rsOf_getD_iff (ks := (DA).ksF c j) hiK).mpr hd
    rw [hnr] at h
    exact Bool.false_ne_true h


/-! ### The field chains -/

/-- **THE BRIDGE** (PLAN-M7 §1e clause 7): a field spine fits class
`c`'s constructor `j` at the COMPOSED carrier exactly when it fits the
copy's constructor at the SCRATCH block's least tuple — position by
position (`fitsFrom_iff_frames_spine`): the flags are one
(`rssT_eq`), a recursive position's two slots are one (`slotT_eq`)
and an ordinary one's two domains are one (`FssT_getD_eq`), with the
scratch side's recursive entry its own real domain
(`real_dom_eq`). -/
theorem NestedTailIn.fitsFrom_iff {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) (fs : List V) :
    FitsFrom (((DA).rss c).getD j []) ((DA).slotAt ψ (Laux ψ (consList as ρ)) c j) 0
        (consList as ρ) (((DA).Fss c ψ).getD j []) fs
      ↔ FitsFrom (((D).rssT PC c).getD j [])
          ((D).slotAtT PC ψ ((D).famAt ψ (consList as ρ)
            (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)))) c j)
          0 (consList as ρ) (((D).FssT PC ψ c).getD j []) fs := by
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ) := hρp
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c hc
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  have hlenA : (((DA).Fss c ψ).getD j []).length = cA.2 := hIA.Fss_length hjA ψ
  have hrsA : ((DA).rss c).getD j [] = rsOf ((DA).ksF c j) :=
    IsBlockModel.rss_getD (d := (DA)) (mm := c) hjl
  refine fitsFrom_iff_frames_spine (by rw [hlenA, I.FssT_len_eq S ψ hc hjA])
    fun l hl fs₁ _ hspine _ _ => ?_
  rw [hlenA] at hl
  simp only [Nat.zero_add]
  by_cases hr : (((DA).rss c).getD j []).getD l false = true
  · have hr' : (rsOf ((DA).ksF c j)).getD l false = true := by rw [← hrsA]; exact hr
    have hreal := S.reps.real_dom_eq (S.typed ψ).1 (PinsTyped.of_noPins rfl ψ) hc hjA hρpA hl hr'
      hspine
    rw [if_pos hr, if_pos (by rw [I.rssT_eq hjA]; exact hr)]
    refine ⟨?_, I.slotT_eq S ψ ρ as hsp hc hjA hl hr' hspine⟩
    rw [hreal]
    exact Subset.refl _
  · have hr0 : (((DA).rss c).getD j []).getD l false = false := by
      cases hh : (((DA).rss c).getD j []).getD l false
      · rfl
      · exact absurd hh hr
    have hr0' : (rsOf ((DA).ksF c j)).getD l false = false := by rw [← hrsA]; exact hr0
    rw [if_neg (by rw [hr0]; exact Bool.false_ne_true),
      if_neg (by rw [I.rssT_eq hjA, hr0]; exact Bool.false_ne_true),
      I.FssT_getD_eq S ψ hc hjA hl hr0']
    exact ⟨Subset.refl _, rfl⟩


/-! ### The major and the motives -/

/-- **THE MAJOR'S FIBRE**: the scratch block's fibre at a class and a
fitting index spine IS the composed class's — F3, with the family
read as the composed least tuple's component (`famAt_lfp`) and the
index tuple at the class's OWN index universe. -/
theorem NestedTailIn.majorAt (ψ : Name → Nat) (ρ : Nat → V) (as : List V)
    (hsp : SpineFit ρ ((D).params ψ) as) {c : Nat} (hc : c < b.k) {is : List V}
    (hi : SpineFit (consList as ρ) ((DA).IdsM c ψ) is) (t : V) :
    t ∈ˢ SetTheory.app ((Laux ψ (consList as ρ)) c) ((DA).tup ψ c is)
      ↔ t ∈ˢ SetTheory.app ((D).famAt ψ (consList as ρ)
          (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) c)
          ((D).tupT ψ c is) := by
  have htup : (D).tupT ψ c is = tupW (nestedU p.k W pinsS ψ c) is := by
    show tupW ((D).uT c ψ) is = _
    rw [ofNested_uT]
  rw [I.famAt_lfp ψ ρ as hsp hc, htup,
    show (DA).tup ψ c is = tupW (W ψ) is from rfl, I.fibreAt ψ ρ as hsp hc is hi]

/-- **THE FRAME'S MOTIVES ARE TYPED AT THE COMPOSED CLASSES**: a
class's index spine and major transfer back to the copy's
(`idsT_iff`, `majorAt`), where the mutual kit types the motive
(`IsBlockModel.motive_app_mem` at the frame's `PrefixFrame.motives`). -/
theorem NestedTailIn.motivesAt {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) {ps Msl : List V} (hsp : SpineFit ρ ((D).params ψ) ps)
    (hmot : ∀ c', c' < (DA).k → Msl.getD c' pt ∈ˢ interp V (consList ps ρ)
      (motiveAVIL (mpA.base2.acval ((DA).memberName c') ψ) ψ (DA).nP ((DA).nIdxAt c') b.elimLevel
        (((DA).ppsM c' ψ).drop (DA).nP))) :
    (D).MotivesTypedT ψ (consList ps ρ) (b.elimLevel.eval ψ)
      (fun c' => if c' < (D).kT then Msl.getD c' pt else pt) := by
  have hρp : Sat V ((D).params ψ).reverse (consList ps ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList ps ρ) := hρp
  intro c' hc' is' hfit x hx
  have hcb : c' < b.k := by rw [← I.kT]; exact hc'
  simp only []
  rw [if_pos hc']
  have hfitA : SpineFit (consList ps ρ) ((DA).IdsM c' ψ) is' :=
    (I.idsT_iff ψ ρ ps hcb is').mp hfit
  have hxA : x ∈ˢ SetTheory.app ((Laux ψ (consList ps ρ)) c') ((DA).tup ψ c' is') :=
    (I.majorAt ψ ρ ps hsp hcb hfitA x).mpr hx
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c' hcb
  have hk0 : (0 : Nat) < (DA).k := by
    show 0 < b.k
    have := I.kpos
    have := I.out.bk
    omega
  exact hIA.motive_app_mem (S.reps.params_length hk0 ψ) hρpA (hmot c' hcb) hfitA hxA


/-! ### The index tuples -/

/-- The pins' recursion laws at the nested block model (lane M7-1). -/
theorem NestedTailIn.pinLaws : PinRecLaws mp₂.base2 (D) PC :=
  nestedPinRecLaws_of I.hμ I.out.facts I.out.grouped I.out.bk mp₂.base2 I.out.stage.groups

/-- Every class's index telescope is graded at its frame — a member's
by its own `idxOk`, a pin's by `PinRecLaws.idxOk`. -/
theorem NestedTailIn.idxOkT (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V ((D).params ψ).reverse ρp) {c : Nat} (hc : c < (D).kT) :
    IdxOk ((D).uT c ψ) ((D).frameT c ψ ρp) ((D).IdsT c ψ) := by
  by_cases hck : c < (D).k
  · obtain ⟨cvT, cvR, mI, rP, rules, hID⟩ := I.out.reps c hck
    rw [BlockModel.uT_of_mem hck, BlockModel.frameT_of_mem hck, BlockModel.IdsT_of_mem hck]
    exact hID.idxOk ψ ρp hρp c hck
  · have hq : c - (D).k < (D).nPins := by unfold BlockModel.kT at hc; omega
    rw [BlockModel.uT_of_pin hck, BlockModel.frameT_of_pin hck, BlockModel.IdsT_of_pin hck]
    exact I.pinLaws.idxOk ψ ρp hρp _ hq

omit I in
/-- A class's index tuple is the tuple of a fitting index spine. -/
theorem nestedIdxT_elim (ψ : Name → Nat) (ρp : Nat → V) {c : Nat} {t : V}
    (ht : t ∈ˢ (D).idxT ψ ρp c) :
    ∃ is, SpineFit ((D).frameT c ψ ρp) ((D).IdsT c ψ) is ∧ t = (D).tupT ψ c is := by
  by_cases hck : c < (D).k
  · rw [BlockModel.idxT_of_mem hck] at ht
    obtain ⟨is, hsp, rfl⟩ :=
      mem_idxSet_elim (show t ∈ˢ idxSet ((D).uM c ψ) ρp ((D).IdsM c ψ) from ht)
    refine ⟨is, ?_, ?_⟩
    · rw [BlockModel.frameT_of_mem hck, BlockModel.IdsT_of_mem hck]; exact hsp
    · rw [BlockModel.tupT, BlockModel.uT_of_mem hck]
  · rw [BlockModel.idxT_of_pin hck] at ht
    obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim
      (show t ∈ˢ idxSet (((D).pinAt (c - (D).k)).u ψ) ((D).pinFrame (c - (D).k) ψ ρp)
        (((D).pinAt (c - (D).k)).Ids ψ) from ht)
    refine ⟨is, ?_, ?_⟩
    · rw [BlockModel.frameT_of_pin hck, BlockModel.IdsT_of_pin hck]; exact hsp
    · rw [BlockModel.tupT, BlockModel.uT_of_pin hck]

/-- **A CLASS'S RESULT INDEX READINGS ARE ITS COPY'S**. -/
theorem NestedTailIn.EssT_eq (ψ : Name → Nat) {c : Nat} {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) :
    ((D).EssT PC ψ c).getD j [] = ((DA).Ess c ψ).getD j [] := by
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨hJl, -, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  rw [IsBlockModel.Ess_getD (d := (DA)) (mm := c) hjA ψ]
  have hkk : (D).k = p.k := rfl
  by_cases hck : c < (D).k
  · obtain ⟨cR, hjD⟩ := I.ctorsD_get (by rw [hkk] at hck; exact hck) hjl
    rw [BlockModel.EssT_of_mem hck, IsBlockModel.Ess_getD (d := (D)) (mm := c) hjD ψ]
    rfl
  · rw [hkk] at hck
    rw [BlockModel.EssT_of_pin (d := (D)) (by rw [hkk]; exact hck)]
    show ((mutEss0 ctorsA.length esF ψ).drop (b.ownOffset (p.k + (c - (D).k)))).getD j [] = _
    rw [hkk, Nat.add_sub_cancel' (Nat.le_of_not_lt hck), getD_drop, mutEss0_getD hJl]
    rfl


/-- The scratch block's minor count is the auxiliary block's
constructor count. -/
theorem NestedTailIn.nCtorsA_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas) : (DA).nCtors = b.ctors.length := by
  rw [S.record.nCtors_eq (ConLeche.checkMutualCore_inv I.haux).2.2.1 I.out.facts.lenA]
  exact I.out.facts.lenA

/-- The minors of the composed classes are the copies'. -/
theorem NestedTailIn.nCtorsT_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas) : (D).nCtorsT PC = (DA).nCtors := by
  rw [I.nCtorsT, I.nCtorsA_eq S]

/-- **THE RESULT INDEX READINGS ARE THE INDEX SPINE**: a `ChainFitT`'s
index equations say the constructor's result index readings ARE the
class's fitting index spine — read at the class's OWN index universe
(`getD_eq_projS_tupW` on both sides) and then at the copy's
(`IsBlockModel.es_eq_is`). -/
theorem NestedTailIn.esMap_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA) {is fs : List V}
    (hisT : SpineFit ((D).frameT c ψ (consList as ρ)) ((D).IdsT c ψ) is)
    (hidx : ∀ l, l < ((D).IdsT c ψ).length →
      interp V (consList fs (consList as ρ)) ((((D).EssT PC ψ c).getD j []).getD l default)
        = Tower.projS l ((D).tupT ψ c is)) :
    ((DA).esF c j ψ).map (interp V (consList fs (consList as ρ))) = is := by
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ) := hρp
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c hc
  have hcT : c < (D).kT := by rw [I.kT]; exact hc
  have hisA : SpineFit (consList as ρ) ((DA).IdsM c ψ) is := (I.idsT_iff ψ ρ as hc is).mp hisT
  have hlenI : ((D).IdsT c ψ).length = ((DA).IdsM c ψ).length := by
    have h1 := hisT.length_eq
    have h2 := hisA.length_eq
    omega
  refine IsBlockModel.es_eq_is hIA hρpA hjA hisA fun l hl => ?_
  have hl' : l < is.length := by rw [hisA.length_eq]; exact hl
  rw [← I.EssT_eq ψ hjA, hidx l (by rw [hlenI]; exact hl)]
  show Tower.projS l (tupW ((D).uT c ψ) is) = Tower.projS l (tupW ((DA).uM c ψ) is)
  rw [← getD_eq_projS_tupW (I.idxOkT ψ (consList as ρ) hρp hcT) hisT hl',
    ← getD_eq_projS_tupW (hIA.idxOk ψ (consList as ρ) hρpA c hc) hisA hl']


/-! ### The inductive hypotheses' domains -/

/-- **AN INDUCTIVE HYPOTHESIS' DOMAIN IS ITS COPY'S**: the field's
telescope and index expressions are the copy's (`teleAtT_eq`,
`eisAtT_eq`), its target is (`tgtsT_eq`), and the target class's index
tuple reads back its fitting spine (`isOfW_tupT` at the index
readings' fit `IsBlockModels.eis_fit`) — the bodies agree at the
FITTING telescope spines only, whence `piTele_congr_acc`. -/
theorem NestedTailIn.ihPi_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {c : Nat} (hc : c < b.k) {j : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM c)[j]? = some cA)
    {fs : List V} (hfs : SpineFit (consList as ρ) (((DA).Fss c ψ).getD j []) fs)
    {i' : Nat} (hi'K : i' < ((DA).ksF c j).length)
    (hr : (rsOf ((DA).ksF c j)).getD i' false = true) (Msl : List V) :
    piTele (b.elimLevel.eval ψ)
        (teleOfFields (consList (fs.take i') (consList as ρ))
          (((D).teleAtT PC ψ c j i').map (·.2.2)))
        (fun bs => SetTheory.app
          ((isOfW ((D).uT ((D).tgtsT PC c j i') ψ) ((D).nIdxT ((D).tgtsT PC c j i'))
            ((D).tupT ψ ((D).tgtsT PC c j i')
              (((D).eisAtT PC ψ c j i').map
                (interp V (consList bs (consList (fs.take i') (consList as ρ))))))).foldl
            SetTheory.app
            (if (D).tgtsT PC c j i' < (D).kT then Msl.getD ((D).tgtsT PC c j i') pt else pt))
          (bs.foldl SetTheory.app (fs.getD i' pt))) []
      = piTele (b.elimLevel.eval ψ)
        (teleOfFields (consList (fs.take i') (consList as ρ))
          ((((DA).tssF c j ψ).getD i' []).map (·.2.2)))
        (fun bs => SetTheory.app
          (((((DA).eissF c j ψ).getD i' []).map
            (interp V (consList bs (consList (fs.take i') (consList as ρ))))).foldl
            SetTheory.app (Msl.getD ((DA).tgts c j i') pt))
          (bs.foldl SetTheory.app (fs.getD i' pt))) [] := by
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ) := hρp
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c hc
  obtain ⟨cvT0, cvR0, mI0, rP0, rules0, hID⟩ := I.out.reps 0 I.kpos
  have hjl : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hjA).1
  have hcd := hIA.ctorData hjA
  have hi'A : i' < cA.2 := by rw [← hcd.ksLen]; exact hi'K
  have htgt : (DA).tgts c j i' < b.k := hIA.tgt_lt hjl hi'K rfl
  have htgtT : (DA).tgts c j i' < (D).kT := by rw [I.kT]; exact htgt
  have hfs' : SpineFit (consList as ρ) ((((DA).Fss c ψ).getD j []).take i') (fs.take i') :=
    spineFit_take' hfs (by rw [hIA.Fss_length hjA]; omega)
  rw [I.teleAtT_eq ψ hjA i', I.eisAtT_eq ψ hjA i', I.tgtsT_eq hjA hi'A, if_pos htgtT]
  refine piTele_congr_acc _ [] fun bs hbs => ?_
  rw [fitsS_teleOfFields] at hbs
  rw [List.nil_append]
  have hEis : SpineFit (consList as ρ) ((DA).IdsM ((DA).tgts c j i') ψ)
      ((((DA).eissF c j ψ).getD i' []).map
        (interp V (consList bs (consList (fs.take i') (consList as ρ))))) :=
    S.reps.eis_fit (S.typed ψ).1 hc hjA hρpA hi'A htgt hr hfs' hbs
  rw [hID.isOfW_tupT I.out.reps I.pinLaws hρp htgtT ((I.idsT_iff ψ ρ as htgt _).mpr hEis)]


/-! ### The minors -/

/-- **THE FRAME'S MINORS ARE TYPED AT THE COMPOSED CLASSES** (PLAN-M7
§1e clause 7): a class's index tuple, field spine and inductive
hypotheses transfer to the copy's (`idxT_elim`, `fitsFrom_iff` +
`spineFit_of_fitsFrom`, `ihPi_eq`), where the mutual kit folds the
minor (`IsBlockModels.minor_fold_mem` at the frame's
`PrefixFrame.minors`); the conclusion comes back by the minor index
(`minorIdxT_eq`), the injection (`nestedInjT_eq`) and the index
readings (`esMap_eq`, `isOfW_tupT`). -/
theorem NestedTailIn.minorsAt {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (ψ : Name → Nat) (ρ : Nat → V) {ps Msl msl : List V}
    (hsp : SpineFit ρ ((D).params ψ) ps) (hMsl : Msl.length = (DA).k)
    (hmsl : msl.length = (DA).nCtors)
    (hmot : ∀ c', c' < (DA).k → Msl.getD c' pt ∈ˢ interp V (consList ps ρ)
      (motiveAVIL (mpA.base2.acval ((DA).memberName c') ψ) ψ (DA).nP ((DA).nIdxAt c') b.elimLevel
        (((DA).ppsM c' ψ).drop (DA).nP)))
    (hmin : ∀ c j cA, c < (DA).k → ((DA).ctorsM c)[j]? = some cA →
      msl.getD ((DA).minorIdx c j) pt ∈ˢ interp V
        (consList (msl.take ((DA).minorIdx c j)) (consList Msl (consList ps ρ)))
        (minorAVAtRM c ((DA).tgts c j) mpA.base2 cA.1.name ψ (DA).nP cA.2
          (pwBit ψ (Level.zeronessOf b.elimLevel)) ((DA).k + (DA).minorIdx c j)
          ((DA).dsF c j ψ) ((DA).esF c j ψ) (ConLeche.recIdxOf ((DA).ksF c j))
          ((DA).tssF c j ψ) ((DA).eissF c j ψ))) :
    (D).MinorsTypedT PC ψ (consList ps ρ) (b.elimLevel.eval ψ)
      (fun c' => if c' < (D).kT then Msl.getD c' pt else pt)
      (fun J => if J < (D).nCtorsT PC then msl.getD J pt else pt) := by
  have hρp : Sat V ((D).params ψ).reverse (consList ps ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList ps ρ) := hρp
  intro c' hc' j hj t' ht' fs hfit vs hvslen hvs
  have hcb : c' < b.k := by rw [← I.kT]; exact hc'
  obtain ⟨cA, hjA⟩ : ∃ cA, ((DA).ctorsM c')[j]? = some cA :=
    ⟨_, List.getElem?_eq_getElem (by rw [← I.ctorsT_length c']; exact hj)⟩
  have hjl : j < ((DA).ctorsM c').length := (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c' hcb
  obtain ⟨cvT0, cvR0, mI0, rP0, rules0, hID⟩ := I.out.reps 0 I.kpos
  obtain ⟨is', hisT, rfl⟩ := nestedIdxT_elim ψ (consList ps ρ) ht'
  have hisA : SpineFit (consList ps ρ) ((DA).IdsM c' ψ) is' :=
    (I.idsT_iff ψ ρ ps hcb is').mp hisT
  have hfitA := (I.fitsFrom_iff S ψ ρ ps hsp hcb hjA fs).mpr hfit.1
  have hspFs : SpineFit (consList ps ρ) (((DA).Fss c' ψ).getD j []) fs :=
    S.reps.spineFit_of_fitsFrom (S.typed ψ).1 (PinsTyped.of_noPins rfl ψ) hcb hjA hρpA
      (lfpTuple_mem _ _ _ _) (TupleLe.refl _ _ _) hfitA
  have hEs : ((DA).esF c' j ψ).map (interp V (consList fs (consList ps ρ))) = is' :=
    I.esMap_eq S ψ ρ ps hsp hcb hjA hisT hfit.2
  have hrecIdx : recIdx (((D).rssT PC c').getD j []) ((((D).FssT PC ψ c').getD j []).length)
      = ConLeche.recIdxOf ((DA).ksF c' j) := by
    rw [I.rssT_eq hjA, I.FssT_len_eq S ψ hcb hjA, ← hIA.Fss_length hjA ψ]
    exact hIA.recIdx_eq hjA ψ
  have hvslenA : vs.length = (ConLeche.recIdxOf ((DA).ksF c' j)).length := by
    rw [hvslen, hrecIdx]
  have ho : Msl.length + (msl.take ((DA).minorIdx c' j)).length
      = (DA).k + (DA).minorIdx c' j := by
    rw [hMsl, List.length_take, hmsl,
      Nat.min_eq_left (Nat.le_of_lt ((DA).minorIdx_lt hcb hjl))]
  have hvsA : ∀ l, l < vs.length →
      vs.getD l pt ∈ˢ piTele (b.elimLevel.eval ψ)
        (teleOfFields
          (consList (fs.take ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0)) (consList ps ρ))
          ((((DA).tssF c' j ψ).getD ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0) []).map
            (·.2.2)))
        (fun bs => SetTheory.app
          (((((DA).eissF c' j ψ).getD ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0) []).map
            (interp V (consList bs
              (consList (fs.take ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0))
                (consList ps ρ))))).foldl SetTheory.app
            (Msl.getD ((DA).tgts c' j ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0)) pt))
          (bs.foldl SetTheory.app
            (fs.getD ((ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0) pt))) [] := by
    intro l hlv
    have h0 := hvs l hlv
    simp only [] at h0
    rw [hrecIdx] at h0
    have hmem : (ConLeche.recIdxOf ((DA).ksF c' j)).getD l 0
        ∈ ConLeche.recIdxOf ((DA).ksF c' j) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [← hvslenA]; exact hlv), Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨hi'K, hkind⟩ := mem_recIdxOf.mp hmem
    rw [I.ihPi_eq S ψ ρ ps hsp hcb hjA hspFs hi'K ((rsOf_getD_iff hi'K).mpr hkind) Msl] at h0
    exact h0
  have hres := S.reps.minor_fold_mem rfl (S.typed ψ).1 hcb hjA hρpA ho hMsl hmot
    (pwBit_zeronessOf ψ b.elimLevel) (hmin c' j cA hcb hjA) hspFs hvslenA hvsA
  simp only []
  rw [I.minorIdxT_eq c' j,
    if_pos (by rw [I.nCtorsT_eq S]; exact (DA).minorIdx_lt hcb hjl), if_pos hc',
    hID.isOfW_tupT I.out.reps I.pinLaws hρp hc' hisT, ← hEs, nestedInjT_eq]
  exact hres


/-! ### The nine clauses -/

/-- **THE READING'S FRAMES AT ONE CLASS** (PLAN-M7 §1e step 2): every
spine fitting class `c`'s RESTORED recursor type's reading decomposes
into the block's frame, with the frame's motives and minors typed
semantically at the COMPOSED classes and the conclusion read off.

By the TRANSFER (`spineFit_transfer`) the spine fits the SCRATCH
reading of the same recursor, whose frame inversion is the mutual
`IsBlockModels.spineFit_recData_inv` at the auxiliary block's own
block model; the frame's clauses then move to the composed model
through `idsT_iff`, `majorAt`, `motivesAt` and `minorsAt`, and the
conclusion by `interp_mutualConcAV_at`. -/
theorem NestedTailIn.framesAt {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored pinsS)
    {c : Nat} (hc : c < b.k) (ψ : Name → Nat) (ρ : Nat → V)
    {rdsR : List (Nat × Nat × AnnotTerm)} {conc : AnnotTerm}
    (hread : denoteMeta mp₂.base2.acval (ENV2) ψ 0 (nestedRecCvAt p.k cvRms cvRns c).type
      = some (mkPisAV rdsR conc))
    (hlenR : rdsR.length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1))) :
    (D).ReadingFramesT PC ψ (b.elimLevel.eval ψ) rdsR conc c ρ := by
  obtain ⟨f, hf⟩ : ∃ f, fms[c]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact hc)⟩
  have hfD : (fms.getD c default).nIdx = f.nIdx := by rw [List.getD_eq_getElem?_getD, hf]; rfl
  have hnI : (DA).nIdxAt c = (fms.getD c default).nIdx := by
    rw [hfD]; exact mutualBlockModel_nIdxAt hf
  -- the conclusion is the class's `mutualConcAV`
  obtain ⟨-, u, rds, -, hspec⟩ := I.classRecTy hc
  obtain ⟨hr, hl, -, -, -⟩ := hspec ψ
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by rw [hlenR, hl]) (Option.some.inj (hread.symm.trans hr))
  intro xs hxs
  have hxsA : SpineFit ρ (((DA).blockRds mpA.base2 b.elimLevel c ψ).map (·.2.2)) xs :=
    (I.spineFit_transfer S hnames hctorsJ hK35 hc ψ ρ hread hlenR xs).mp hxs
  obtain ⟨ps, Msl, msl, is, t, rfl, hF, his, ht⟩ :=
    S.reps.spineFit_recData_inv (S.readings ψ) hc hxsA
  have hisLenA : is.length = (DA).nIdxAt c := by
    obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps c hc
    rw [his.length_eq, hIA.IdsM_length ψ]
  refine ⟨ps, Msl, msl, is, t, rfl, (D).satOfSpine hF.params, ?_, ?_, ?_,
    (I.idsT_iff ψ ρ ps hc is).mpr his, (I.majorAt ψ ρ ps hF.params hc his t).mp ht,
    I.motivesAt S ψ ρ hF.params hF.motives,
    I.minorsAt S ψ ρ hF.params hF.mslLen hF.minsLen hF.motives hF.minors, ?_⟩
  · rw [I.kT]; exact hF.mslLen
  · rw [I.nCtorsT_eq S]; exact hF.minsLen
  · rw [I.nIdxT hc, ← hnI]; exact hisLenA
  · have hcon := interp_mutualConcAV_at (DA) ρ (ps := ps) (Msl := Msl) (msl := msl) (is := is) t
      hF.mslLen hF.minsLen hc hisLenA
    rw [I.nCtorsA_eq S, hnI] at hcon
    exact hcon

/-! ### The readings at the tail -/

/-- **THE READINGS AT THE TAIL, FRAMES AND ALL** (PLAN-M7 §1e): the
fourteen clauses of `NestedRecReadings` at a tail input —
`NestedTailIn.readings`' thirteen, its fourteenth (`ReadingFramesT`)
`framesAt` at the scratch reading `NestedTailIn.scratch` supplies. -/
theorem NestedTailIn.framesOf (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored pinsS) :
    ∃ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM := by
  obtain ⟨mpA, cvRas, S⟩ := I.scratch
  refine I.readingsOf fun rdsM concM hread hlen ψ ρ c hc => ?_
  have hcb : c < b.k := by rw [← I.kT]; exact hc
  refine I.framesAt S hnames hctorsJ hK35 hcb ψ ρ (hread c ψ hc) ?_
  have hlc := hlen c ψ hc
  rw [nestedBlockModel_nP, I.kT, I.nCtorsT, I.nIdxT hcb] at hlc
  omega

end Run

/-! ## The named fact -/

/-- **K.35 AT THE RUN**: every read-back recursor type of a scratch
install of the auxiliary block has, below its parameter prefix, the
restore walk's shape (`NestedRecTysAuxOk`, `NestedRecFrames.lean`).
A KERNEL-SIDE model face (PLAN-M7 §1a). -/
@[expose] def NestedRecTysAuxOf (μ : CheckMode) (F : Nat) : Prop :=
  ∀ (env : Env) (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (pinsS : List PinSyn),
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    pinsS.length = st.pins.length →
    NestedRecTysAuxOk p st b stored pinsS

/-- **K.36 AT THE RUN**: a copy's constructor names round-trip through
the container's (`NestedCtorPinNames`, `NestedRecCtor.lean`, T2).  A
KERNEL-SIDE model face. -/
@[expose] def NestedCtorPinNamesOf (μ : CheckMode) (F : Nat) : Prop :=
  ∀ (env : Env) (p : NestedParts) (st : ElimState) (fmsA ctorsA₀ : List ConstantVal),
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀ →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st →
    ConLeche.nestedContainersOk env st.pins = true →
    NestedCtorPinNames env p st

/-- **THE GROUPS' CONSTRUCTOR NAMES AT THE RUN** (`hctorsJ`, DESIGN
§U.36 (d)): the container block model of a pin group names, at every
component, the container member's own declared constructors.  A model
face until `NestedStageFacts.groups` names the groups' model
`blockOf mp.base2 (baseInfo env st q)`. -/
@[expose] def NestedGroupCtorNamesOf (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) (p : NestedParts) (envOut : Env) (st : ElimState)
    (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (cvRms cvRns : List ConstantVal)
    (rulesM rulesN : List (List RecRule)) (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
    (pinsS : List PinSyn)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env))),
    NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀
      fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR
      xFvsR pinsS mp₂ →
    ∀ (q₀ kJ i : Nat) (dJ : BlockModel V),
      NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
        mp₂.base2 q₀ kJ dJ →
      i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env (pinsS.getD (q₀ + i) default).J = some ci → J ∈ ci.members →
        J.name = (pinsS.getD (q₀ + i) default).J →
        (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name)

/-- **THE FRAMES AT THE RUN** (PLAN-M7 §1e): `NestedRecFramesOf` —
the named fact `nestedRecReadingsOf_of` consumes — discharged at every
tail input, modulo the three model faces K.35 (`NestedRecTysAuxOf`),
K.36 (`NestedCtorPinNamesOf`) and the groups' constructor names
(`NestedGroupCtorNamesOf`). -/
theorem nestedRecFramesOf_of {F : Nat} (hK35 : NestedRecTysAuxOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) (hctorsJ : NestedGroupCtorNamesOf V μ F) :
    NestedRecFramesOf V μ F := by
  intro env mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ I rdsM concM hread hlen ψ ρ c hc
  obtain ⟨mpA, cvRas, S⟩ := I.scratch
  have hcb : c < b.k := by rw [← I.kT]; exact hc
  refine I.framesAt S (hK36 env p st fmsA ctorsA₀ I.hfA I.hcA I.helim I.hcont)
    (fun q₀ kJ i dJ G hi ci J h1 h2 h3 =>
      hctorsJ mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
        ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
        pinsS mp₂ I q₀ kJ i dJ G hi ci J h1 h2 h3)
    (hK35 env p st b envAux stored pinsS I.hb I.haux I.hstored I.out.stage.pinsLen)
    hcb ψ ρ (hread c ψ hc) ?_
  have hlc := hlen c ψ hc
  rw [nestedBlockModel_nP, I.kT, I.nCtorsT, I.nIdxT hcb] at hlc
  omega

/-- **THE READINGS AT THE RUN, FROM THE THREE FACES**: the first of
`nestedTailModeled_of`'s three named facts. -/
theorem nestedRecReadingsOf_of_faces {F : Nat} (hK35 : NestedRecTysAuxOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) (hctorsJ : NestedGroupCtorNamesOf V μ F) :
    NestedRecReadingsOf V μ F :=
  nestedRecReadingsOf_of (nestedRecFramesOf_of hK35 hK36 hctorsJ)

/-- **THE CONSUMER** (consumer-first): the recursors' stage at the run
needs the readings, and this lane supplies them from the three model
faces alone. -/
theorem nestedTailModeled_of_faces {F : Nat} (hK35 : NestedRecTysAuxOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) (hctorsJ : NestedGroupCtorNamesOf V μ F)
    (heqs : NestedRecEqsOf V μ F) (hst : NestedRecsStored V μ F) : NestedTailModeled V μ F :=
  nestedTailModeled_of_frames (nestedRecFramesOf_of hK35 hK36 hctorsJ) heqs hst

end ConLeche.Model
