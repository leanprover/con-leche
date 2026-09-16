module

public import ConLeche.Model.Inductives.NestedCore
public import ConLeche.Model.Inductives.NestedRecTyped
import ConLeche.Model.Inductives.NestedAux
public section

/-!
# The pins' recursion laws at the nested block model (task #315, M7-1)

`PinRecLaws` (`NestedRecCand.lean`, lane L-D) at the block model of a
nested run — `nestedBlockModel` (`NestedCore.lean`), the composed
operator `BlockModel.ofNested` at the auxiliary block's lists — with
the pins' constructor data `nestedPc` read off the AUXILIARY lists at
the copies' positions `b.ownOffset (k + q) + j`
(`blkFss0`/`blkRss`/`mutTgts`/`mutTlss`/`mutEiss0`/`mutEss0`), the
injection the tagged tower at the member-local position (DESIGN §U.25
(e) 1).

Two layers, as everywhere on the nested route:

* the COMPOSED-OPERATOR layer (`ofNested_pin_fibre`,
  `ofNested_pin_ind`), stated in `BlockComposed.lean`'s spelling: a
  pin's carrier at a tuple below the carrier is the sealed operator's
  fibre at the EXTENDED tuple (the pins' fixed-point law
  `app_pinsCar_eq` of `SetTheory/Derive/LfpCompose.lean`, pure), and
  the pins' carriers are the least families closed under those fibres
  (`pinsCar_induction`, `lfpTuple_induction` at `pinsOp X`);
* the RUN layer (`nestedPinRecLaws_of`): the per-constructor
  bookkeeping (the copies' global positions against `nestedPc`'s
  member-local ones — `NestedPinGroup.grp`), the pins' index
  telescopes graded at the pins' frames (the container's `idxOk` at
  `NestedPinGroup.DsFit`), the targets below `k + nPins` (the
  auxiliary block's kinds, `MutualFormersFacts.ksJ`) and the
  injections' laws (`injW_zero`/`injW_pos` + `mkTower_inj`).

**The finding** (DESIGN §U.28): `PinRecLaws.fibre` is FALSE at
`nestedBlockModel` for a tuple `X` that is NOT below the block's
carrier — the composed model's pins' operator reads the members
CLAMPED (`meetT`, `LfpCompose.lean`'s module docstring), so a spine
whose member fields carry junk above the carrier fits at `X` and its
value is not in the pin's carrier there.  The kit's clause therefore
carries the premise `TupleLe d.k (d.idx ψ ρp) X L`; its three live
consumers read it at the carrier.
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

omit [SetTheory V] in
/-- A dropped list's entry is the original's, shifted. -/
theorem getD_drop {α : Type _} (l : List α) (n j : Nat) (a : α) :
    (l.drop n).getD j a = l.getD (n + j) a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ## The composed operator's pins: the fibre and the induction -/

section Nested

variable {nP k : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env} {memberNames : List Name}
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
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

local notation "D" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins offs mems nFs
  tgtsG rss tlss Eiss₀ Fss₀ Ess₀)

local notation "ΨA" => nestedΨ (V := V) nP k resSort ppsA W pins offs mems nFs tgtsG rss tlss
  Eiss₀ Fss₀ Ess₀

variable {ψ : Name → Nat} {ρp : Nat → V}
  (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
    (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
    (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)

include h

/-- **`fibre` for the block model at a PIN, at the auxiliary lists**:
below the block's carrier, pin `q`'s carrier at `(X, t)` is the set of
the tagged towers of the spines fitting one of the auxiliary block's
constructors `offs (k + q) + j` of the copy `k + q` at the EXTENDED
tuple — `ofNested_fibre`'s pin twin, through the pins' fixed-point law
(`app_pinsCar_eq`) and Bekić's nested form at the members
(`lfpTuple_composeΦ`, which identifies the block's carrier with the
auxiliary one below which the clamp is invisible). -/
theorem ofNested_pin_fibre (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs
      tgtsG rss (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ))
    {X : Nat → V} (hX : InTupleSpace ((D).w ψ) k ((D).idx ψ ρp) X)
    (hXL : TupleLe k ((D).idx ψ ρp) X (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)))
    {q : Nat} (hq : q < pins.length) {t : V} (ht : t ∈ˢ (D).idx ψ ρp (k + q)) (x : V) :
    x ∈ˢ SetTheory.app ((D).pinCar ψ ρp X q) t ↔
      ∃ j fs, offs (k + q) + j < (Fss₀ ψ).length ∧ mems.getD (offs (k + q) + j) 0 = k + q ∧
        FitsFrom (rss.getD (offs (k + q) + j) []) (fun i ρ => slotSet ((D).w ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (k + q) + j) []).getD i 0)) ρ
            (((tlss ψ).getD (offs (k + q) + j) []).getD i [])
            (((Eiss₀ ψ).getD (offs (k + q) + j) []).getD i [])
            (extT ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) X
              ((tgtsG.getD (offs (k + q) + j) []).getD i 0)))
          0 ρp ((Fss₀ ψ).getD (offs (k + q) + j) []) fs ∧
        (∀ l, l < ((D).IdsM (k + q) ψ).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q) + j) []).getD l default)
            = projS l t) ∧
        x = injW ((D).w ψ) j (mkTower (fs ++ [pt])) := by
  have hΨ := nestedΨ_functor h
  have hXL' : TupleLe k ((D).idx ψ ρp) X
      (lfpTuple ((D).w ψ) (k + pins.length) ((D).idx ψ ρp) (ΨA ψ ρp)) := by
    intro m hm
    have hm' := hXL m hm
    rwa [ofNested_lfp h hm] at hm'
  rw [ofNested_pinCar, ofNested_w, ofNested_idx, app_pinsCar_eq hΨ.1 hΨ.2.1 hΨ.2.2 hX hXL' hq ht]
  exact tupleLfpΦ_fibre h hS (extT_mem hX) (by omega) ht x

/-- **The pins' induction for the block model**: the pins' carriers at
a tuple `X` of the space are the LEAST families closed under the
auxiliary operator's pin fibres, the members read at `X` and the pins
at the separated carriers (`pinsCar_induction`, the pure half). -/
theorem ofNested_pin_ind
    (hPinIdx : ∀ q, q < pins.length → (D).pinIdx q ψ ρp = (D).idx ψ ρp (k + q))
    {X : Nat → V} (hX : InTupleSpace ((D).w ψ) k ((D).idx ψ ρp) X) (P : Nat → V → V → Prop)
    (hP : ∀ q, q < pins.length → ∀ t, t ∈ˢ (D).idx ψ ρp (k + q) → ∀ x,
      x ∈ˢ SetTheory.app
          (ΨA ψ ρp (segJoin k pins.length X ((D).sepPins ψ ρp X P)) (k + q)) t → P q t x) :
    ∀ q, q < pins.length → ∀ t, t ∈ˢ (D).pinIdx q ψ ρp → ∀ x,
      x ∈ˢ SetTheory.app ((D).pinCar ψ ρp X q) t → P q t x := by
  have hΨ := nestedΨ_functor h
  have hsep : segJoin k pins.length X
      (sepTuple ((D).w ψ) pins.length (fun q => (D).idx ψ ρp (k + q))
        (pinsOp ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) X) P)
      = segJoin k pins.length X ((D).sepPins ψ ρp X P) := by
    funext j
    by_cases hin : k ≤ j ∧ j < k + pins.length
    · rw [segJoin_in _ _ hin, segJoin_in _ _ hin]
      unfold BlockModel.sepPins sepTuple
      rw [hPinIdx (j - k) (by omega)]
      rfl
    · rw [segJoin_out _ _ hin, segJoin_out _ _ hin]
  intro q hq t ht x hx
  rw [hPinIdx q hq] at ht
  refine pinsCar_induction (w := (D).w ψ) (k := k) (n := pins.length) (Is := (D).idx ψ ρp)
    (Ψ := ΨA ψ ρp) hΨ.1 hΨ.2.2 hX P (fun q' hq' t' ht' x' hx' => ?_) q hq t ht x hx
  exact hP q' hq' t' ht' x' (by rwa [hsep] at hx')

end Nested

/-! ## The pins' constructor data at the run -/

/-- **The pins' constructors at the run's data** (DESIGN §U.25 (e) 1):
pin `q`'s data is the AUXILIARY block's at the copy's positions
`b.ownOffset (k + q) + j` — the copy's constructors (`b.ownCtors (k +
q)`, as `ctorsA` entries), its shadow domains, flags, targets,
telescopes and index expressions and its results' index readings, all
dropped to the copy's first position so that the member-local index
`j` reads the global one — with the injection the tagged tower at `j`
(the member-local tag inside the seal, §U.16). -/
@[expose] noncomputable def nestedPc (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat))) (k : Nat) (resSort : Level)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (q : Nat) : PinCtors V where
  ctors := (b.ownCtors (k + q)).map fun jc => ctorsA.getD jc.1 default
  Fss := fun ψ => (blkFss0 b ctorsA kinds dsF ψ).drop (b.ownOffset (k + q))
  rss := (blkRss ctorsA kinds).drop (b.ownOffset (k + q))
  tgts := fun j i =>
    ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (k + q) + j)
      []).getD i 0
  tlss := fun ψ => (mutTlss ctorsA.length tssF ψ).drop (b.ownOffset (k + q))
  Eiss := fun ψ => (mutEiss0 ctorsA.length eissF ψ).drop (b.ownOffset (k + q))
  Ess := fun ψ => (mutEss0 ctorsA.length esF ψ).drop (b.ownOffset (k + q))
  inj := fun ψ j fs => injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))

/-! ## The pins' recursion laws at the nested block model -/

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
  {pinsS : List PinSyn} {env₂ : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- **`PinRecLaws` at the nested block's block model** (DESIGN §U.25 (e)
1, §U.28): the pins' constructor data `nestedPc` satisfies the
recursor kit's laws at `nestedBlockModel` — the fibre through the
pins' fixed-point law at the extended tuple, the induction through the
pins' section's leastness, the targets from the auxiliary block's
kinds, the index telescopes from the container's `idxOk` at the pin's
frame, and the injections' laws from the tagged towers. -/
theorem nestedPinRecLaws_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ) :
    PinRecLaws m (D) PC := by
  have hkT : b.k = fms.length := h.lenFms.symm
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  -- the operator's premise and the lists' shape, at every parameter frame
  have hOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V ((D).params ψ).reverse ρp →
      NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) ψ ρp :=
    fun ψ ρp hρp =>
      nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinBound_of m hgroups ψ ρp hρp)
  have hS : ∀ ψ : Name → Nat,
      TupleLfpShape (p.k + pinsS.length) (blockIds b.nP ppsF ψ) (mutMems ctorsA.length (mutMemF b))
        (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (mutEiss0 ctorsA.length eissF ψ) (blkFss0 b ctorsA kinds dsF ψ)
        (mutEss0 ctorsA.length esF ψ) := fun ψ => nestedShape_of_formers h hbk ψ
  -- the pins' index-tuple sets are the copies'
  have hPinIdx : ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      (D).pinIdx q ψ ρp = (D).idx ψ ρp (p.k + q) := by
    intro q hq ψ ρp
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    show idxSet (((D).pinAt (q₀ + i)).u ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) (((D).pinAt (q₀ + i)).Ids ψ)
      = idxSet (nestedU p.k W pinsS ψ (p.k + (q₀ + i))) ρp (blockIds b.nP ppsF ψ (p.k + (q₀ + i)))
    have hu : nestedU p.k W pinsS ψ (p.k + (q₀ + i)) = ((D).pinAt (q₀ + i)).u ψ :=
      nestedU_pin p.k W pinsS ψ (q₀ + i)
    rw [hu, G.pinIds hi ψ, ← Nat.add_assoc, G.idx i hi ψ i hi, idxSet_instTele Iff.rfl]
  -- every target is a class
  have htgtLt : ∀ q J i : Nat, q < pinsS.length →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD J []).getD i 0
        < p.k + pinsS.length := by
    intro q J i hq
    have hz : (0 : Nat) < p.k + pinsS.length := by omega
    by_cases hJ : J < ctorsA.length
    · by_cases hi : i < mutNFOf ctorsA J
      · rw [mutTgts_getD hJ hi]
        have hb := (h.ksJ J _ (ctorsA_get hJ)).2.2 i
        rw [← hkT, hbk] at hb
        exact hb
      · have hlen : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD J []).length
            = mutNFOf ctorsA J := by
          simp [mutTgts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega),
          Option.getD_none]
        exact hz
    · have hnil : (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD J [] = [] := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp only [mutTgts, List.length_map, List.length_range]; omega),
          Option.getD_none]
      rw [hnil, List.getD_nil]
      exact hz
  -- the pins' index telescopes have the copies' length
  have hIds : ∀ (ψ : Name → Nat) (q : Nat), q < pinsS.length →
      ((D).IdsM (p.k + q) ψ).length = ((D).IdsT ((D).k + q) ψ).length := by
    intro ψ q hq
    have hnk : ¬ (D).k + q < (D).k := by omega
    rw [BlockModel.IdsT_of_pin hnk, Nat.add_sub_cancel_left]
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    show (blockIds b.nP ppsF ψ (p.k + (q₀ + i))).length = (((D).pinAt (q₀ + i)).Ids ψ).length
    rw [← Nat.add_assoc, G.idx i hi ψ i hi, G.pinIds hi ψ, instTele_length]
  -- a member-local constructor position is a copy's, and conversely
  have hcount : ∀ (ψ : Name → Nat) (q j : Nat), q < pinsS.length →
      ((b.ownOffset (p.k + q) + j < (blkFss0 b ctorsA kinds dsF ψ).length ∧
        (mutMems ctorsA.length (mutMemF b)).getD (b.ownOffset (p.k + q) + j) 0 = p.k + q)
        ↔ j < ((PC q).ctors).length) := by
    intro ψ q j hq
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    have hlenC : ((PC (q₀ + i)).ctors).length = (dJ.ctorsM i).length := by
      show ((b.ownCtors (p.k + (q₀ + i))).map _).length = _
      rw [List.length_map, ← Nat.add_assoc, ← G.ctorCount i hi]
    rw [hlenC, ← Nat.add_assoc]
    exact G.grp h3 hlenA ψ hi j
  -- the auxiliary constructor's fit IS the class's `ChainFitT`
  have hchain : ∀ (ψ : Name → Nat) (ρp : Nat → V) (q : Nat), q < pinsS.length →
      ∀ Z Y : Nat → V, (∀ tgt, tgt < p.k + pinsS.length → Z tgt = Y tgt) →
      ∀ (t : V) (j : Nat) (fs : List V),
      (FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q) + j) [])
          (fun i ρ => slotSet ((D).w ψ)
            (nestedU p.k W pinsS ψ
              (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q) + j) []).getD i 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
            (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q) + j) []).getD i 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q) + j) []) fs ∧
        (∀ l, l < ((D).IdsM (p.k + q) ψ).length →
          interp V (consList fs ρp)
              (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q) + j) []).getD l default)
            = projS l t))
      ↔ (D).ChainFitT PC ψ ρp Y t ((D).k + q) j fs := by
    intro ψ ρp q hq Z Y hZY t j fs
    have hnk : ¬ (D).k + q < (D).k := by omega
    have hslot : (fun (i : Nat) (ρ : Nat → V) => slotSet ((D).w ψ)
          (nestedU p.k W pinsS ψ
            (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q) + j) []).getD i 0)) ρ
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
          (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q) + j) []).getD i 0)))
        = (D).slotAtT PC ψ Y ((D).k + q) j := by
      funext i ρ
      rw [hZY _ (htgtLt q _ _ hq)]
      unfold BlockModel.slotAtT BlockModel.teleAtT BlockModel.eisAtT
      rw [BlockModel.tgtsT_of_pin hnk, BlockModel.tlssT_of_pin hnk, BlockModel.EissT_of_pin hnk,
        Nat.add_sub_cancel_left, ofNested_uT]
      simp only [nestedPc, getD_drop]
    unfold BlockModel.ChainFitT
    rw [BlockModel.rssT_of_pin hnk, BlockModel.FssT_of_pin hnk, BlockModel.EssT_of_pin hnk,
      Nat.add_sub_cancel_left, ← hslot, hIds ψ q hq]
    simp only [nestedPc, getD_drop]
  refine { tgtsLt := ?_, idxOk := ?_, fibre := ?_, mkZero := ?_, mkInj := ?_, ind := ?_ }
  · -- tgtsLt: the auxiliary block's kinds target a class
    intro ψ q j i hq _ _
    exact htgtLt q _ _ hq
  · -- idxOk: the container's index telescope at the pin's frame
    intro ψ ρp hρp q hq
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
    obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
    have hJ := hI.idxOk _ _ (dJ.satOfSpine (G.DsFit i hi ψ ρ as hsp)) i (G.kEq ▸ hi)
    rw [G.pinU i hi ψ i hi, G.pinIds hi ψ]
    exact hJ
  · -- fibre: the pins' fixed-point law at the extended tuple
    intro ψ ρp hρp X hX hXL q hq t ht x
    have ht' : t ∈ˢ (D).idx ψ ρp (p.k + q) := by rw [← hPinIdx q hq ψ ρp]; exact ht
    rw [ofNested_pin_fibre (hOk ψ ρp hρp) (hS ψ) hX hXL hq ht' x]
    have hZY : ∀ tgt, tgt < p.k + pinsS.length →
        extT ((D).w ψ) p.k pinsS.length ((D).idx ψ ρp)
            (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
              (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
              (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
              (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
              (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)
              ψ ρp) X tgt
          = (D).famAt ψ ρp X tgt :=
      fun tgt htgt => (ofNested_famAt ψ ρp X htgt).symm
    constructor
    · rintro ⟨j, fs, hJl, hmem, hfit, heqs, rfl⟩
      exact ⟨j, fs, (hcount ψ q j hq).mp ⟨hJl, hmem⟩,
        (hchain ψ ρp q hq _ _ hZY t j fs).mp ⟨hfit, heqs⟩, rfl⟩
    · rintro ⟨j, fs, hj, hcf, rfl⟩
      obtain ⟨hJl, hmem⟩ := (hcount ψ q j hq).mpr hj
      obtain ⟨hfit, heqs⟩ := (hchain ψ ρp q hq _ _ hZY t j fs).mpr hcf
      exact ⟨j, fs, hJl, hmem, hfit, heqs, rfl⟩
  · -- mkZero
    intro ψ hw q j fs
    show injW (f₀.s.eval ψ) j (mkTower (fs ++ [pt])) = pt
    rw [show f₀.s.eval ψ = 0 from hw, injW_zero]
  · -- mkInj
    intro ψ hw q hq j fs j' fs' hj hj' hlen hlen' heq
    have hw' : f₀.s.eval ψ ≠ 0 := hw
    change injW (f₀.s.eval ψ) j (mkTower (fs ++ [pt]))
      = injW (f₀.s.eval ψ) j' (mkTower (fs' ++ [pt])) at heq
    rw [injW_pos hw', injW_pos hw'] at heq
    obtain ⟨rfl, h2⟩ := inj_inj heq
    exact ⟨rfl, List.append_cancel_right (mkTower_inj (by simp [hlen, hlen']) h2)⟩
  · -- ind: the pins' section's leastness
    intro ψ ρp hρp X hX P hstep q hq t ht x hx
    have hOk' := hOk ψ ρp hρp
    refine ofNested_pin_ind hOk' (fun q' hq' => hPinIdx q' hq' ψ ρp) hX P ?_ q hq t ht x hx
    intro q' hq' t' ht' x' hx'
    have hSmem : InTupleSpace ((D).w ψ) pinsS.length (fun q'' => (D).idx ψ ρp (p.k + q''))
        ((D).sepPins ψ ρp X P) := by
      intro q'' hq''
      show (D).sepPins ψ ρp X P q'' ∈ˢ famSpace ((D).w ψ) ((D).idx ψ ρp (p.k + q''))
      rw [← hPinIdx q'' hq'' ψ ρp]
      unfold BlockModel.sepPins
      exact graph_mem_famSpace fun t'' ht'' =>
        univ_sep_mem (famSpace_app (ofNested_pinMem hq'' (hPinIdx q'' hq'' ψ ρp)) ht'')
    obtain ⟨j, fs, hJl, hmem, hfit, heqs, rfl⟩ :=
      (tupleLfpΦ_fibre hOk' (hS ψ) (inTupleSpace_join hX hSmem)
        (show p.k + q' < p.k + pinsS.length by omega) ht' x').mp hx'
    have hZY : ∀ tgt, tgt < p.k + pinsS.length →
        segJoin p.k pinsS.length X ((D).sepPins ψ ρp X P) tgt
          = segJoin p.k pinsS.length ((D).famAt ψ ρp X) ((D).sepPins ψ ρp X P) tgt := by
      intro tgt htgt
      by_cases hin : p.k ≤ tgt ∧ tgt < p.k + pinsS.length
      · rw [segJoin_in _ _ hin, segJoin_in _ _ hin]
      · rw [segJoin_out _ _ hin, segJoin_out _ _ hin,
          (D).famAt_of_mem (lt_of_not_seg htgt hin)]
    exact hstep q' hq' t' (by rw [hPinIdx q' hq' ψ ρp]; exact ht') j fs
      ((hcount ψ q' j hq').mp ⟨hJl, hmem⟩)
      ((hchain ψ ρp q' hq' _ _ hZY t' j fs).mp ⟨hfit, heqs⟩)

/-! ### The kit, instantiated at the nested block -/

section Consumers

/-- **`nestedRecs`'s `hcand` at the nested block** — the kit's
`IsBlockModel.hcandT` (lane L-D) instantiated at `nestedBlockModel`
and `nestedPc` through `nestedPinRecLaws_of`: the candidate tuple's
`k + nPins` components are typed at the restored recursor types'
readings.  Its remaining premises are the readings' — M7's next step
(DESIGN §U.25 (e) 2), named there, not here. -/
theorem nestedHcandT_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true) (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ)
    (hreps : IsBlockModels m (D)) {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {mm : Nat}
    (hI : IsBlockModel m T cvT cvR mI rP rules (D) mm) {ℓ : (Name → Nat) → Nat}
    (hwℓ : ∀ ψ, (D).w ψ = 0 → ℓ ψ = 0)
    {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
    (hne : ∀ c ψ, c < (D).kT → rdsM c ψ ≠ [])
    (hbits : ∀ c ψ, c < (D).kT → ∀ e ∈ rdsM c ψ, (ℓ ψ = 0 ↔ e.2.1 = 0))
    (hfr : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (D).kT →
      (D).ReadingFramesT PC ψ (ℓ ψ) (rdsM c ψ) (concM c) c ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (D).kT →
      (D).blockCandT PC ψ (ℓ ψ) (rdsM c ψ) c ρ ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)) :=
  hI.hcandT hreps (nestedPinRecLaws_of hμ h h3 hbk m hgroups) hwℓ hne hbits hfr

/-- **The induction over the nested block's classes**, instantiated:
a property closed under every class's constructors — the members' AND
the pins' — holds of every value of the extended tuple at the carrier
(`IsBlockModel.classInd_all` at `nestedPinRecLaws_of`). -/
theorem nestedClassInd_all (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true) (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {mm : Nat} (hI : IsBlockModel m T cvT cvR mI rP rules (D) mm) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V ((D).params ψ).reverse ρp) {P : Nat → V → V → Prop}
    (hstep : (D).ClassStep PC ψ ρp P) :
    ∀ c, c < (D).kT → ∀ t, t ∈ˢ (D).idxT ψ ρp c → ∀ x,
      x ∈ˢ SetTheory.app
        ((D).famAt ψ ρp (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp)) c) t → P c t x :=
  hI.classInd_all (nestedPinRecLaws_of hμ h h3 hbk m hgroups) hρp hstep

end Consumers

end Assembly

end ConLeche.Model

