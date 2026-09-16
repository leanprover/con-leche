module

public import ConLeche.Model.Inductives.NestedRecScratch
public import ConLeche.Model.Inductives.NestedCore
public import ConLeche.Model.Inductives.NestedAux
public import ConLeche.Model.Inductives.NestedFit
public section

/-!
# The fibre kit of the recursors' stage (task #315, M7-2)

PLAN-M7 §1e step 4 and §1c's bridge: the pieces that identify the
SCRATCH (auxiliary) block's semantics with the COMPOSED nested block's
at one and the same stored leaf.

* `IsBlockModels.ctorsTyped` — the constructors of ANY block model of
  an `EnvModelM` are typed at their types' readings (the run's
  `mem_type` at each stored constructor);
* `slotSet_congr_app` (with `piTele_congr`) — a recursive slot only
  sees its family through the applications at FITTING spines;
* `NestedTailIn.fibreAt` — **the fibre identity**: the scratch block's
  least tuple and the composed block's agree pointwise at fitting index
  spines (two folds of the ONE stored member leaf);
* `NestedTailIn.pinCarAt` — the same at a pin: the container's own
  least tuple against the composed one;
* `NestedTailIn.slotAt_aux` — the scratch block's recursive slots at
  its least tuple ARE the composed slots of `CopyCtorInst.fit_iff_at`.
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

/-! ## F1 — the constructors typed at any block model -/

/-- **The constructors are typed** at every block model of an
`EnvModelM`: the stored constructor inhabits its type's reading, which
the block model says is the Π-tower over the constructor's field
telescope ending in the member's leaf at the index readings.  The run's
`mem_type` at `BlockCtorData`'s `read`. -/
theorem IsBlockModels.ctorsTyped {env : Env} (mp : EnvModelM V μ env) {d : BlockModel V}
    (hreps : IsBlockModels mp.base2 d) (ψ : Name → Nat) : CtorsTyped mp.base2 d ψ := by
  intro c hc j cA hj ρ
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps c hc
  obtain ⟨hfind, -, hCD⟩ := hI.ctors c j cA hc hj
  exact mp.mem_type _ (ConLeche.Semantics.Env.find?_mem hfind) ψ _ (hCD.read ψ) ρ

/-! ## F2 — the slot's congruence at fitting spines -/

/-- The nested product over a telescope only sees its body at FITTING
spines. -/
theorem piTele_congr {v : Nat} {B B' : List V → V} :
    ∀ {n : Nat} (T : TeleS V n) (acc : List V),
      (∀ bs, FitsS T bs → B (acc ++ bs) = B' (acc ++ bs)) →
      piTele v T B acc = piTele v T B' acc
  | _, .nil, acc, h => by
    have := h [] (by trivial)
    rw [List.append_nil] at this
    exact this
  | _, .cons A T, acc, h => by
    refine piR_congr fun x hx => piTele_congr (T x) (acc ++ [x]) fun bs hfit => ?_
    rw [List.append_assoc, List.singleton_append]
    exact h (x :: bs) ⟨hx, hfit⟩

/-- **The recursive slot's congruence**: two families whose
applications agree at every spine FITTING the field's telescope give
the same slot. -/
theorem slotSet_congr_app {w u u' : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X X' : V}
    (h : ∀ bs : List V, SpineFit ρ (tl.map (·.2.2)) bs →
      SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ))))
        = SetTheory.app X' (tupW u' (Eis.map (interp V (consList bs ρ))))) :
    slotSet w u ρ tl Eis X = slotSet w u' ρ tl Eis X' := by
  unfold slotSet
  refine piTele_congr _ [] fun bs hfit => ?_
  rw [List.nil_append]
  exact h bs (fitsS_teleOfFields.mp hfit)

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

/-- the COMPOSED nested block's block model -/
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- the SCRATCH (auxiliary) block's block model — the MUTUAL one -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

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

/-- the COMPOSED model's extended least tuple (`NestedFit.lean`'s `L⁺`) -/
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

/-! ## F3 — the fibre identity -/

/-- **THE FIBRE IDENTITY** (PLAN-M7 §1e clause 4): the SCRATCH block's
least tuple and the COMPOSED block's agree POINTWISE, at every class
and every fitting index spine — the two are folds of the ONE stored
member leaf `mutMemberLeaf`, read at the uniform index universe `W` on
the scratch side (`MutualFormersFacts.tupleOk`) and at the
per-component universes `nestedU` on the composed side
(`nestedLfpOk_of_formers` + `nestedPinBound_of`). -/
theorem NestedTailIn.fibreAt (ψ : Name → Nat) (ρ : Nat → V) (as : List V)
    (hsp : SpineFit ρ ((D).params ψ) as) {c : Nat} (hc : c < b.k) (is : List V)
    (hi : SpineFit (consList as ρ) (blockIds b.nP ppsF ψ c) is) :
    SetTheory.app ((Laux ψ (consList as ρ)) c) (tupW (W ψ) is)
      = SetTheory.app ((Lcomp ψ (consList as ρ)) c)
          (tupW (nestedU p.k W pinsS ψ c) is) := by
  have h := I.out.facts
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρp' : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse (consList as ρ) := hρp
  have hOkA := h.tupleOk I.hμ ψ (consList as ρ) hρp'
  have hOk' := nestedLfpOk_of_formers h I.hμ I.out.bk ψ (consList as ρ) hρp'
    (nestedPinBound_of mp₂.base2 I.out.stage.groups ψ _ hρp)
  have hft_c := fms_get (show c < fms.length from by rw [h.lenFms]; exact hc)
  have hnI : ((ppsF c ψ).drop b.nP).length = (fms.getD c default).nIdx := by
    rw [List.length_drop, (h.FD _ _ hft_c).len ψ]
    exact Nat.add_sub_cancel_left _ _
  have hsp_c : SpineFit ρ (((ppsF c ψ).take b.nP).map (·.2.2)) as :=
    spineFit_of_frames
      (by
        simp only [List.length_map, List.length_take]
        rw [(h.FD 0 f₀ h.first).len ψ, (h.FD _ _ hft_c).len ψ]
        omega)
      (fun ρ' => (h.frame c _ hft_c ψ ρ').symm) hsp
  have hi_c : SpineFit (consList as ρ) (((ppsF c ψ).drop b.nP).map (·.2.2)) is := hi
  have hcb : c < p.k + pinsS.length := by rw [← I.out.bk]; exact hc
  have hfoldA := tupleLfpAV_fold (V := V) (pps := ppsF c ψ) (nP := b.nP) hc hOkA rfl hsp_c hi_c
  have hfoldC := tupleLfpAV_fold (V := V) (pps := ppsF c ψ) (nP := b.nP) hcb hOk' rfl hsp_c hi_c
  have hA : mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF c ψ
      = tupleLfpAV (W ψ) (f₀.s.eval ψ) (ppsF c ψ) ((ppsF c ψ).drop b.nP).length b.k
          (blockIds b.nP ppsF ψ) b.ownOffset (mutMems ctorsA.length (mutMemF b))
          (mutNFs ctorsA.length (mutNFOf ctorsA))
          (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
          (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)
          (blkFss0 b ctorsA kinds dsF ψ) (mutEss0 ctorsA.length esF ψ) c := by
    rw [hnI]
    rfl
  have hC : mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF c ψ
      = tupleLfpAV (W ψ) (f₀.s.eval ψ) (ppsF c ψ) ((ppsF c ψ).drop b.nP).length
          (p.k + pinsS.length)
          (blockIds b.nP ppsF ψ) b.ownOffset (mutMems ctorsA.length (mutMemF b))
          (mutNFs ctorsA.length (mutNFOf ctorsA))
          (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
          (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)
          (blkFss0 b ctorsA kinds dsF ψ) (mutEss0 ctorsA.length esF ψ) c := by
    rw [hnI, ← I.out.bk]
    rfl
  rw [← hA] at hfoldA
  rw [← hC] at hfoldC
  exact hfoldA.symm.trans hfoldC

/-! ## F4 — the container's least tuple at a pin -/

/-- **THE PIN'S FIBRE IDENTITY**: the CONTAINER block model `dJ`'s own
least tuple at component `i` and the COMPOSED block's least tuple at
the copy's class `p.k + q₀ + i` agree pointwise at every spine fitting
the container's index telescope — the container's `leaf` at the pin's
components (`IsBlockModel.leaf` at `dJ`) against the pin's leaf at the
block's carrier (`nestedPinLeaf_of`), the carrier read as the extended
least tuple by Bekić (`ofNested_pinCar_lfp`), the universes matched by
`nestedU_pin_group`. -/
theorem NestedTailIn.pinCarAt {q₀ kJ i : Nat} {dJ : BlockModel V}
    (G : PG mp₂.base2 q₀ kJ dJ) (hi : i < kJ)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    (is : List V)
    (hi' : SpineFit
      (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ))) (consList as ρ))
      (dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)) is) :
    SetTheory.app
        (lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ)))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ))) i)
        (tupW (dJ.uM i (((D).pinAt (q₀ + i)).ψJ ψ)) is)
      = SetTheory.app ((Lcomp ψ (consList as ρ)) (p.k + q₀ + i))
          (tupW (nestedU p.k W pinsS ψ (p.k + q₀ + i)) is) := by
  have h := I.out.facts
  have hq : q₀ + i < pinsS.length := by have := G.seg; omega
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρp' : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse (consList as ρ) := hρp
  have hOk' := nestedLfpOk_of_formers h I.hμ I.out.bk ψ (consList as ρ) hρp'
    (nestedPinBound_of mp₂.base2 I.out.stage.groups ψ _ hρp)
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  have hleaf := hI.leaf (((D).pinAt (q₀ + i)).ψJ ψ) (consList as ρ)
    ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ))) is
    (G.DsFit i hi ψ ρ as hsp) hi'
  have htup : dJ.tup (((D).pinAt (q₀ + i)).ψJ ψ) i is
      = tupW (dJ.uM i (((D).pinAt (q₀ + i)).ψJ ψ)) is := rfl
  rw [htup] at hleaf
  have hPL := nestedPinLeaf_of I.hμ h I.out.grouped I.out.bk mp₂.base2 I.out.stage.groups
    (q₀ + i) hq ψ ρ as is hsp (by rw [G.pinIds hi ψ]; exact hi')
  have hpc : (D).pinCar ψ (consList as ρ)
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) (q₀ + i)
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ (consList as ρ))
          (ΨN ψ (consList as ρ)) (p.k + q₀ + i) := by
    rw [show p.k + q₀ + i = p.k + (q₀ + i) from Nat.add_assoc _ _ _]
    exact ofNested_pinCar_lfp hOk' hq
  have hclosed : interp V (consList as ρ)
        (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
      = interp V ρ (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ)) :=
    interp_closed (V := V) (mp₂.base2.cval_closedL _ _) _ _
  have hu : nestedU p.k W pinsS ψ (p.k + q₀ + i) = ((D).pinAt (q₀ + i)).u ψ := by
    rw [Nat.add_assoc]
    exact nestedU_pin p.k W pinsS ψ (q₀ + i)
  rw [← hleaf, hclosed, hPL, hpc, hu]
  rfl

/-! ## F5 — the scratch block's recursive slots are the composed slots -/

/-- **The composed tuple's pin components ARE the container's own least
tuple**, over the WHOLE group at the representative's level assignment
and components (`ofNested_pin_block_of_inst` is stated for every
component `i''` of the group at the ONE `ψJ`/`Ds` the representative
fixes) — F5's in-group step. -/
theorem NestedTailIn.pinSegAt {q₀ kJ i : Nat} {dJ : BlockModel V}
    (G : PG mp₂.base2 q₀ kJ dJ) (hi : i < kJ)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {i'' : Nat} (hi'' : i'' < kJ) :
    (Lcomp ψ (consList as ρ)) (p.k + q₀ + i'')
      = lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ)))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ))) i'' := by
  have h := I.out.facts
  have hq : q₀ + i'' < pinsS.length := by have := G.seg; omega
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρp' : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse (consList as ρ) := hρp
  have hOk' := nestedLfpOk_of_formers h I.hμ I.out.bk ψ (consList as ρ) hρp'
    (nestedPinBound_of mp₂.base2 I.out.stage.groups ψ _ hρp)
  have hpb : (D).pinCar ψ (consList as ρ)
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)))
        (q₀ + i'')
      = lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ)))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
              (consList as ρ))) i'' :=
    ofNested_pin_block_of_inst hOk' (nestedShape_of_formers h I.out.bk ψ) G.seg
    G.reps (G.typed _) (G.pinsTyped _) G.kEq (G.w i hi ψ) (nestedU_pin_group mp₂.base2 G hi ψ)
    (G.inj _) (dJ.satOfSpine (G.DsFit i hi ψ ρ as hsp)) (G.idx i hi ψ)
    (fun i' hi' j => G.grp I.out.grouped h.lenA ψ hi' j) (G.inst i hi ψ _ hρp) hi''
  have hpc : (D).pinCar ψ (consList as ρ)
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)))
        (q₀ + i'')
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ (consList as ρ))
          (ΨN ψ (consList as ρ)) (p.k + q₀ + i'') := by
    rw [show p.k + q₀ + i'' = p.k + (q₀ + i'') from Nat.add_assoc _ _ _]
    exact ofNested_pinCar_lfp hOk' hq
  exact hpc.symm.trans hpb

/-- **THE SCRATCH BLOCK'S RECURSIVE SLOTS ARE THE COMPOSED SLOTS** of
`CopyCtorInst.fit_iff_at`: the auxiliary block's slot at ITS least
tuple is the copy's slot at the tuple `segJoin`ed from the composed
least tuple and the container's own — the two families agree at every
index spine the slot ever reads (`slotSet_congr_app`, the index
readings' fits `IsBlockModels.rec_eis_fit`/`refl_eis_fit` at the
scratch block), by the fibre identity `fibreAt` at a target outside
the group and by `pinSegAt` at a target inside it. -/
theorem NestedTailIn.slotAt_aux {mpA : EnvModelM V μ
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))}
    {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {q₀ kJ i : Nat} {dJ : BlockModel V} (G : PG mp₂.base2 q₀ kJ dJ) (hi : i < kJ)
    (ψ : Name → Nat) (ρ : Nat → V) (as : List V) (hsp : SpineFit ρ ((D).params ψ) as)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ((DA).ctorsM (p.k + q₀ + i))[j]? = some cA)
    {i' : Nat} (hi' : i' < cA.2)
    (hr : (rsOf ((DA).ksF (p.k + q₀ + i) j)).getD i' false = true)
    {fs' : List V}
    (hfs' : SpineFit (consList as ρ) ((((DA).Fss (p.k + q₀ + i) ψ).getD j []).take i') fs') :
    (DA).slotAt ψ (Laux ψ (consList as ρ)) (p.k + q₀ + i) j i'
        (consList fs' (consList as ρ))
      = slotSet (f₀.s.eval ψ)
          (nestedU p.k W pinsS ψ
            (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + i) + j) []).getD i' 0))
          (consList fs' (consList as ρ))
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' [])
          (segJoin (p.k + q₀) kJ (Lcomp ψ (consList as ρ))
            (lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
              (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
                  (consList as ρ)))
              (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
                  (consList as ρ))))
            (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + i) + j) []).getD i' 0)) := by
  have h := I.out.facts
  have hc : p.k + q₀ + i < b.k := by have := G.seg; rw [I.out.bk]; omega
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ) := hρp
  obtain ⟨cvT, cvR, mI, rP, rules, hIA⟩ := S.reps (p.k + q₀ + i) hc
  have hjl : j < ((DA).ctorsM (p.k + q₀ + i)).length := (List.getElem?_eq_some_iff.mp hj).1
  have hcd := hIA.ctorData hj
  have hiK : i' < ((DA).ksF (p.k + q₀ + i) j).length := by rw [hcd.ksLen]; exact hi'
  have htgt : (DA).tgts (p.k + q₀ + i) j i' < b.k := hIA.tgt_lt hjl hiK rfl
  obtain ⟨hJl, hcAg, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped h.lenA hj
  have hnf : mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i) + j) = cA.2 := by
    show (ctorsA.getD (b.ownOffset (p.k + q₀ + i) + j) default).2 = cA.2
    rw [List.getD_eq_getElem?_getD, hcAg]
    rfl
  -- the three table entries: the block model's and the global lists' agree
  have hTG : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i) + j) []).getD i' 0 = (DA).tgts (p.k + q₀ + i) j i' :=
    mutTgts_getD hJl (by rw [hnf]; exact hi')
  have hTL : ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' []
      = (((DA).tlss (p.k + q₀ + i) ψ).getD j []).getD i' [] := by
    rw [mutTlss_getD hJl, IsBlockModel.tlss_getD hj]
    rfl
  have hEI : ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' []
      = (((DA).Eiss (p.k + q₀ + i) ψ).getD j []).getD i' [] := by
    rw [mutEiss0_getD hJl, IsBlockModel.Eiss_getD hj]
    rfl
  -- the kind of the slot
  have hk : ((DA).ksF (p.k + q₀ + i) j).getD i' .ordinary = .recursive ∨
      ((DA).ksF (p.k + q₀ + i) j).getD i' .ordinary = .reflexive := by
    unfold rsOf at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiK,
      Option.map_some, Option.getD_some, decide_eq_true_iff] at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiK]
    exact hr
  -- the target's family, at the scratch tuple and at the composed one
  have key : ∀ tg : Nat, tg < b.k → ∀ eis : List V,
      SpineFit (consList as ρ) (blockIds b.nP ppsF ψ tg) eis →
      SetTheory.app ((Laux ψ (consList as ρ)) tg) (tupW (W ψ) eis)
        = SetTheory.app
            (segJoin (p.k + q₀) kJ (Lcomp ψ (consList as ρ))
              (lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
                (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
                  (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
                    (consList as ρ)))
                (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
                  (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
                    (consList as ρ)))) tg)
            (tupW (nestedU p.k W pinsS ψ tg) eis) := by
    intro tg htg eis heis
    rw [I.fibreAt ψ ρ as hsp htg eis heis]
    by_cases hin : p.k + q₀ ≤ tg ∧ tg < p.k + q₀ + kJ
    · obtain ⟨i'', htg', hi''⟩ : ∃ i'', tg = p.k + q₀ + i'' ∧ i'' < kJ :=
        ⟨tg - (p.k + q₀), by omega, by omega⟩
      subst htg'
      rw [segJoin_add _ _ hi'', ← I.pinSegAt G hi ψ ρ as hsp hi'']
    · rw [segJoin_out _ _ hin]
  -- the slot, at a MEMBER target of the scratch block
  rw [hTG, hTL, hEI, (DA).slotAt_of_mem htgt]
  refine slotSet_congr_app fun bs hbs => ?_
  refine key ((DA).tgts (p.k + q₀ + i) j i') htgt _ ?_
  rcases hk with hk | hk
  · -- a finitary recursive field: the telescope is empty, the spine is
    have htn : ((DA).tssF (p.k + q₀ + i) j ψ).getD i' [] = [] :=
      hcd.tssNone ψ i' (by rw [hk]; exact fun hh => nomatch hh)
    rw [IsBlockModel.tlss_getD hj, htn] at hbs
    cases bs with
    | nil =>
      rw [IsBlockModel.Eiss_getD hj]
      exact S.reps.rec_eis_fit (S.typed ψ).1 hc hj hρpA hi' htgt hk hfs'
    | cons _ _ => exact hbs.elim
  · rw [IsBlockModel.tlss_getD hj] at hbs
    rw [IsBlockModel.Eiss_getD hj]
    exact S.reps.refl_eis_fit (S.typed ψ).1 hc hj hρpA hi' htgt hk hfs' hbs

end Run

end ConLeche.Model
