module

public import ConLeche.Model.Inductives.BlockRepMutual
public import ConLeche.SetTheory.Derive.LfpCompose
public section

/-!
# The uniform block model of a NESTED block — `BlockModel.ofNested` (task #315, M6)

`ofMutual`'s twin (`BlockRepMutual.lean`) for a block of `k` members
with `n` pins (`Tree ::= node (List Tree)`: one member, one pin `List
Tree`).  The block model's operator and pins' carriers are the
COMPOSED operator of `ConLeche/SetTheory/Derive/LfpCompose.lean` at the
AUXILIARY tuple operator — the sealed `tupleLfpΦ` on `k + n`
components over the ELIMINATED block's readings: the members'
constructors with their fields' targets in members ++ pins, and at
pin `q` the container's constructors instantiated at the pin (K.12's
annotated elimination), whose kinds are K.26's re-keyed ones.  No
auxiliary block is installed or modelled: `Ψ` is a set-level object
the elimination's readings denote, and the block model's clauses are
about the ORIGINAL block's stored constants.

* the members' index telescopes are the first `k` of the `k + n`
  telescopes `ppsA` (the auxiliary formers' readings; `ppsM := ppsA`),
  so the composed operator's tuple space is the block model's
  (`ofNested_idx`, by `rfl`); a pin's index-tuple set in the block
  model (`pinIdx`: the container's OWN telescope at the pin's frame)
  is the copy's telescope at the block's frame by the substitution
  behind the elimination — ONE hypothesis of the pins' laws
  (`hPinIdx`), the assembly's;
* `functor` is `composeΦ_mono/_maps/_closed_exists` at
  `tupleLfpΦ_functor` on `k + n` (`ofNested_functor`); `pinMem`/`pinMono`
  are `pinsCar_mem/_mono` (`ofNested_pinMem/_pinMono`); `fibre` is
  `tupleLfpΦ_fibre` at the EXTENDED tuple, whose slot at a target is
  the block model's `famAt` (`ofNested_fibre`, `ofNested_famAt`); the
  per-constructor bookkeeping (member-local position ↔ global
  position, `fitsFrom_congr` with `slotAt_of_mem`/`slotAt_of_pin`) is
  the assembly's, exactly as for the mutual block;
* `leaf` is the interp law `tupleLfpAV_fold` at the `k + n`-ary former
  — the term-level leaf of a nested member IS the restored former's
  component — followed by Bekić's nested form (`lfpTuple_composeΦ`):
  the composed least tuple's member is the auxiliary's
  (`ofNested_leaf`);
* the pins' carriers at the block's carrier are the auxiliary least
  tuple's pin components (`ofNested_pinCar_lfp`) — what `pinLeaf`'s
  assembly consumes (M6 s3): a pin's component is, by Bekić at the
  copies' segment (`lfpTuple_seg`), the least tuple of the container's
  block at the pin's components, and the copy readings' congruence
  closes it.

`ofMutual` is the case `n = 0` (an empty segment joins nothing:
`composeΦ` is `Ψ` at the members).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The auxiliary tuple's index sets and operator -/

/-- The `k + n` index-tuple sets at a parameter frame: every component
over the block's index universe `W`, the members' and the copies'
telescopes read off `ppsA`. -/
@[expose] noncomputable def nestedIs (nP : Nat) (ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (W : (Name → Nat) → Nat) (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun m => idxSet (W ψ) ρp (blockIds nP ppsA ψ m)

/-- **The auxiliary tuple operator**: the sealed `k`-ary former's
operator at `k + n` components over the eliminated block's readings. -/
@[expose] noncomputable def nestedΨ (nP k n : Nat) (resSort : Level)
    (ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (mems nFs : List Nat) (tgtsG : List (List Nat)) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)) (ψ : Name → Nat) (ρp : Nat → V) :
    (Nat → V) → Nat → V :=
  tupleLfpΦ (W ψ) (resSort.eval ψ) ρp (k + n) (blockIds nP ppsA ψ) mems nFs tgtsG rss (tlss ψ)
    (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)

/-! ## The block model -/

/-- **The uniform block model of a nested block** (see the module
docstring): `ofMutual`'s data with the pins, the `k + n` telescopes
`ppsA`, the auxiliary block's constructor data in GLOBAL order (the
members' constructors first, then the copies' — `tupleLfpAV`'s
arguments at `k + n`), the operator the COMPOSED one and the pins'
carriers the pins' least tuple (`LfpCompose.lean`), the injections the
tagged towers at the global position. -/
@[expose] noncomputable def BlockModel.ofNested (nP k : Nat) (resSort : Level) (isProp large : Bool)
    (env₀ : Env) (memberNames : List Name) (nIdxs : List Nat)
    (ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (ctorsM : Nat → List (ConstantVal × Nat)) (idxF : Nat → Nat → List Expr)
    (dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → Nat → List (Option Nat))
    (ksF : Nat → Nat → List RecFieldKind) (tgts : Nat → Nat → Nat → Nat)
    (fvsPF xFvsF : Nat → Nat → List Expr) (xrestF : Nat → Nat → Expr)
    (eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (pins : List PinSyn)
    (mems nFs : List Nat) (tgtsG : List (List Nat)) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)) : BlockModel V where
  nP := nP
  k := k
  resSort := resSort
  isProp := isProp
  large := large
  env₀ := env₀
  memberNames := memberNames
  nIdxs := nIdxs
  ppsM := ppsA
  uM := fun _ ψ => W ψ
  ctorsM := ctorsM
  idxF := idxF
  dsF := dsF
  esF := esF
  srcsF := srcsF
  ksF := ksF
  tgts := tgts
  fvsPF := fvsPF
  xFvsF := xFvsF
  xrestF := xrestF
  eissF := eissF
  tssF := tssF
  pins := pins
  Φ := fun ψ ρp =>
    composeΦ (resSort.eval ψ) k pins.length (nestedIs nP ppsA W ψ ρp)
      (nestedΨ nP k pins.length resSort ppsA W mems nFs tgtsG rss tlss Eiss₀ Fss₀ Ess₀ ψ ρp)
  pinCar := fun ψ ρp X q =>
    pinsCar (resSort.eval ψ) k pins.length (nestedIs nP ppsA W ψ ρp)
      (nestedΨ nP k pins.length resSort ppsA W mems nFs tgtsG rss tlss Eiss₀ Fss₀ Ess₀ ψ ρp) X q
  inj := fun ψ mm j fs => injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt]))

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
  {pins : List PinSyn}
  {mems nFs : List Nat} {tgtsG : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

local notation "D" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins mems nFs tgtsG
  rss tlss Eiss₀ Fss₀ Ess₀)

local notation "ΨA" => nestedΨ (V := V) nP k pins.length resSort ppsA W mems nFs tgtsG rss tlss Eiss₀
  Fss₀ Ess₀

/-- **The premise at a parameter frame**: the sealed former's premise
at the `k + n` components — the members' AND the copies' index
telescopes graded at `W`, the auxiliary block's chains graded. -/
@[expose] def NestedLfpOk (ψ : Name → Nat) (ρp : Nat → V) : Prop :=
  TupleLfpOk (W ψ) (resSort.eval ψ) ρp (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss
    (tlss ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)

/-- The block model's index telescopes are the `k + n` telescopes'. -/
theorem ofNested_IdsM (mm : Nat) (ψ : Name → Nat) : (D).IdsM mm ψ = blockIds nP ppsA ψ mm := rfl

/-- The block model's index-tuple sets are the auxiliary tuple's (at
every position, by construction). -/
theorem ofNested_idx (ψ : Name → Nat) (ρp : Nat → V) : (D).idx ψ ρp = nestedIs nP ppsA W ψ ρp := rfl

theorem ofNested_pins : (D).pins = pins := rfl

theorem ofNested_nPins : (D).nPins = pins.length := rfl

theorem ofNested_w (ψ : Name → Nat) : (D).w ψ = resSort.eval ψ := rfl

/-- The block model's operator: the composed one. -/
theorem ofNested_Φ (ψ : Name → Nat) (ρp : Nat → V) :
    (D).Φ ψ ρp = composeΦ ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) := rfl

/-- The block model's pins' carriers: the pins' least tuple. -/
theorem ofNested_pinCar (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (q : Nat) :
    (D).pinCar ψ ρp X q = pinsCar ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) X q := rfl

theorem ofNested_inj (ψ : Name → Nat) (mm j : Nat) (fs : List V) :
    (D).inj ψ mm j fs = injW ((D).w ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt])) := rfl

theorem ofNested_minorIdx (mm j : Nat) : (D).minorIdx mm j = blockMinorIdx ctorsM mm j := rfl

theorem ofNested_tup {ψ : Name → Nat} (hW : W ψ ≠ 0) (mm : Nat) (is : List V) :
    (D).tup ψ mm is = mkTower is :=
  tupW_pos hW is

/-- **A target's family at the tuple is the extended tuple's
component** — the nested slot reads the pin's carrier. -/
theorem ofNested_famAt (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) {tgt : Nat}
    (h : tgt < k + pins.length) :
    (D).famAt ψ ρp X tgt = extT ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) X tgt :=
  (extT_eq_famAt h).symm

section Frame

variable {ψ : Name → Nat} {ρp : Nat → V}
  (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
    (pins := pins) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss) (tlss := tlss)
    (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)

include h

/-- The auxiliary operator's laws at the frame. -/
theorem nestedΨ_functor :
    MonoTuple (resSort.eval ψ) (k + pins.length) (nestedIs nP ppsA W ψ ρp) (ΨA ψ ρp) ∧
    MapsTuple (resSort.eval ψ) (k + pins.length) (nestedIs nP ppsA W ψ ρp) (ΨA ψ ρp) ∧
    ∃ L, IsClosedTuple (resSort.eval ψ) (k + pins.length) (nestedIs nP ppsA W ψ ρp) (ΨA ψ ρp) L :=
  tupleLfpΦ_functor h

/-- **`functor` for the block model**: the composed operator is a
monotone, space-preserving tuple functor with a closed tuple, from the
auxiliary one's laws — (W) composed from (W) auxiliary. -/
theorem ofNested_functor :
    MonoTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    MapsTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    ∃ L, IsClosedTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  have hΨ := nestedΨ_functor h
  ⟨composeΦ_mono hΨ.1 hΨ.2.2, composeΦ_maps hΨ.2.1, composeΦ_closed_exists hΨ.1 hΨ.2.2⟩

omit h in
/-- **`pinMem` for the block model**, given the pin's index-tuple set
is the copy's (`hPinIdx`, the substitution behind the elimination);
no law of `Ψ` is consumed (the least tuple is in the space
unconditionally). -/
theorem ofNested_pinMem {X : Nat → V} {q : Nat} (hq : q < pins.length)
    (hPinIdx : (D).pinIdx q ψ ρp = (D).idx ψ ρp (k + q)) :
    (D).pinCar ψ ρp X q ∈ˢ famSpace ((D).w ψ) ((D).pinIdx q ψ ρp) := by
  rw [hPinIdx, ofNested_pinCar]
  exact pinsCar_mem (w := (D).w ψ) (k := k) (n := pins.length) (Is := (D).idx ψ ρp) (Ψ := ΨA ψ ρp)
    X q hq

/-- **`pinMono` for the block model**: the pins' carriers are monotone
in the tuple. -/
theorem ofNested_pinMono {X Y : Nat → V} (hX : InTupleSpace ((D).w ψ) k ((D).idx ψ ρp) X)
    (hY : InTupleSpace ((D).w ψ) k ((D).idx ψ ρp) Y) (hle : TupleLe k ((D).idx ψ ρp) X Y)
    {q : Nat} (hq : q < pins.length) (hPinIdx : (D).pinIdx q ψ ρp = (D).idx ψ ρp (k + q)) :
    FamLe ((D).pinIdx q ψ ρp) ((D).pinCar ψ ρp X q) ((D).pinCar ψ ρp Y q) := by
  have hΨ := nestedΨ_functor h
  rw [hPinIdx, ofNested_pinCar, ofNested_pinCar]
  exact pinsCar_mono hΨ.1 hΨ.2.2 hX hY hle q hq

/-- **`fibre` for the block model, at the auxiliary lists**: component
`mm`'s fibre at `(X, t)` is the set of the tagged towers of the spines
fitting one of the auxiliary block's constructors `J` of member `mm`
at the EXTENDED tuple — a recursive field read at its target's
component of `extT X`, i.e. at the target member's component of `X` or
the target pin's carrier at `X` (`ofNested_famAt`).  The
per-constructor bookkeeping to the block model's `ChainFit` (global
position `J` ↔ member-local `j`, `fitsFrom_congr` with
`slotAt_of_mem`/`slotAt_of_pin`) is the assembly's. -/
theorem ofNested_fibre (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss
      (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ))
    {X : Nat → V} (hX : InTupleSpace ((D).w ψ) k ((D).idx ψ ρp) X) {mm : Nat} (hmm : mm < k)
    {t : V} (ht : t ∈ˢ (D).idx ψ ρp mm) (x : V) :
    x ∈ˢ SetTheory.app ((D).Φ ψ ρp X mm) t ↔
      ∃ J fs, J < (Fss₀ ψ).length ∧ mems.getD J 0 = mm ∧
        FitsFrom (rss.getD J []) (fun i ρ => slotSet ((D).w ψ) (W ψ) ρ
            (((tlss ψ).getD J []).getD i []) (((Eiss₀ ψ).getD J []).getD i [])
            (extT ((D).w ψ) k pins.length ((D).idx ψ ρp) (ΨA ψ ρp) X ((tgtsG.getD J []).getD i 0)))
          0 ρp ((Fss₀ ψ).getD J []) fs ∧
        (∀ l, l < ((D).IdsM mm ψ).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD J []).getD l default) = projS l t) ∧
        x = injW ((D).w ψ) J (mkTower (fs ++ [pt])) := by
  rw [ofNested_Φ, composeΦ_apply]
  exact tupleLfpΦ_fibre h hS (extT_mem hX) (by omega) ht x

/-- **The pins' carriers at the block's carrier are the auxiliary
least tuple's pin components** (Bekić, the nested form) — `pinLeaf`'s
assembly reads a pin here. -/
theorem ofNested_pinCar_lfp {q : Nat} (hq : q < pins.length) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)) q
      = lfpTuple ((D).w ψ) (k + pins.length) ((D).idx ψ ρp) (ΨA ψ ρp) (k + q) := by
  have hΨ := nestedΨ_functor h
  rw [ofNested_pinCar, ofNested_Φ]
  exact pinsCar_lfp hΨ.1 hΨ.2.2 hq


/-- **A pin's carrier at the block's carrier is the least tuple of ITS
CONTAINER's block** — the theorem `pinLeaf`'s assembly instantiates
(M6 s3).  The container's copies occupy the segment `[k + q₀, k + q₀ +
kJ)` of the auxiliary tuple; when that segment's section at the
auxiliary least tuple agrees, on the container's tuple space, with the
container's own operator `ΦJ` over ITS index sets `IsJ` (the copy
readings' congruence at the pin's components, read at the carrier),
pin `q₀ + i`'s carrier at the block's carrier is `ΦJ`'s least tuple's
component `i` — which the container's `IsBlockModel.leaf` turns into
its stored reading at the pin. -/
theorem ofNested_pin_block {q₀ kJ : Nat} (hseg : q₀ + kJ ≤ pins.length) {IsJ : Nat → V}
    {ΦJ : (Nat → V) → Nat → V}
    (hIs : ∀ i, i < kJ → (D).idx ψ ρp (k + q₀ + i) = IsJ i)
    (hΦ : ∀ Y, InTupleSpace ((D).w ψ) kJ (fun i => (D).idx ψ ρp (k + q₀ + i)) Y → ∀ i, i < kJ →
      ΨA ψ ρp (segJoin (k + q₀) kJ (lfpTuple ((D).w ψ) (k + pins.length) ((D).idx ψ ρp) (ΨA ψ ρp)) Y)
          (k + q₀ + i)
        = ΦJ Y i)
    {i : Nat} (hi : i < kJ) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = lfpTuple ((D).w ψ) kJ IsJ ΦJ i := by
  have hΨ := nestedΨ_functor h
  rw [ofNested_pinCar_lfp h (by omega), ← Nat.add_assoc]
  exact lfpTuple_seg_congr hΨ.2.2 hΨ.1 (by omega) hIs hΦ hi

/-- **The block's carrier is the auxiliary least tuple's members**
(Bekić, the nested form). -/
theorem ofNested_lfp {mm : Nat} (hmm : mm < k) :
    lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) mm
      = lfpTuple ((D).w ψ) (k + pins.length) ((D).idx ψ ρp) (ΨA ψ ρp) mm := by
  have hΨ := nestedΨ_functor h
  rw [ofNested_Φ]
  exact lfpTuple_composeΦ hΨ.1 hΨ.2.2 hmm

end Frame

/-- **`leaf` for the block model**: member `mm`'s term-level leaf — the
`k + n`-ary former's component `mm` (`tupleLfpAV` at the auxiliary
lists: the restored former) — at fitting parameters and indices is the
COMPOSED least tuple's component `mm` at the index tuple: the interp
law `tupleLfpAV_fold` at `k + n`, then Bekić's nested form.  The
parameter spine fits the member's own telescope (`hsp`); the
identification with the block's `params` is the assembly's. -/
theorem ofNested_leaf {ψ : Name → Nat} {ρ : Nat → V} {as is : List V} {mm : Nat} (hmm : mm < k)
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss) (tlss := tlss)
      (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ (consList as ρ))
    (hsp : SpineFit ρ (((ppsA mm ψ).take nP).map (·.2.2)) as)
    (hi : SpineFit (consList as ρ) ((D).IdsM mm ψ) is) :
    (as ++ is).foldl SetTheory.app (interp V ρ
        (tupleLfpAV (W ψ) ((D).w ψ) (ppsA mm ψ) ((ppsA mm ψ).drop nP).length (k + pins.length)
          (blockIds nP ppsA ψ) mems nFs tgtsG rss (tlss ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ) mm))
      = SetTheory.app (lfpTuple ((D).w ψ) k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)) mm)
          ((D).tup ψ mm is) := by
  rw [ofNested_tup h.W_pos, ofNested_lfp h hmm]
  exact tupleLfpAV_fold (by omega) h rfl hsp hi

/-- `mkZero` for the block model: at a `Prop`-valued block every
injection is the point. -/
theorem ofNested_mkZero (ψ : Name → Nat) (hw : (D).w ψ = 0) (mm j : Nat) (fs : List V) :
    (D).inj ψ mm j fs = pt := by
  show injW (resSort.eval ψ) _ _ = pt
  have hw' : resSort.eval ψ = 0 := hw
  rw [hw', injW_zero]

/-- `mkInj` for the block model, within a member: the global positions
of a member's constructors are distinct, and the towers are injective
at equal lengths. -/
theorem ofNested_mkInj (ψ : Name → Nat) (hw : (D).w ψ ≠ 0) {mm j j' : Nat} {fs fs' : List V}
    (hlen : fs.length = (((D).Fss mm ψ).getD j []).length)
    (hlen' : fs'.length = (((D).Fss mm ψ).getD j' []).length)
    (h : (D).inj ψ mm j fs = (D).inj ψ mm j' fs') : j = j' ∧ fs = fs' := by
  have hw' : resSort.eval ψ ≠ 0 := hw
  change injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt]))
    = injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j') (mkTower (fs' ++ [pt])) at h
  rw [injW_pos hw', injW_pos hw'] at h
  obtain ⟨hJ, h2⟩ := inj_inj h
  have hj : j = j' := by
    unfold blockMinorIdx at hJ
    omega
  subst hj
  refine ⟨rfl, ?_⟩
  have := mkTower_inj (by simp [hlen, hlen']) h2
  exact List.append_cancel_right this

end Nested

end ConLeche.Model
