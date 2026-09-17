module

public import ConLeche.Model.Inductives.NestedRecFrames
public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecTyped
import ConLeche.Model.Inductives.NestedRecRead
import ConLeche.Model.Inductives.NestedPinLaws
import ConLeche.Model.Inductives.BlockComposed
import ConLeche.Model.Inductives.BlockRecKit
import ConLeche.Model.Inductives.BlockRecTyped
import ConLeche.Model.Inductives.NestedAux
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
spine the slot ever reads (`slotSet_congr_app` at the fibre identity
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
  refine slotSet_congr_app fun bs hbs => ?_
  refine I.fibreAt ψ ρ as hsp htgt _ ?_
  rcases hk with hk | hk
  · have htn : ((DA).tssF c j ψ).getD l [] = [] :=
      hcd.tssNone ψ l (by rw [hk]; exact fun hh => nomatch hh)
    rw [htn] at hbs
    cases bs with
    | nil => exact S.reps.rec_eis_fit (S.typed ψ).1 hc hjA hρpA hl htgt hk hfs'
    | cons _ _ => exact hbs.elim
  · exact S.reps.refl_eis_fit (S.typed ψ).1 hc hjA hρpA hl htgt hk hfs' hbs

end Run

end ConLeche.Model
