module

import ConLeche.Model.Inductives.NestedFit
public import ConLeche.Model.Inductives.NestedPremise
public import ConLeche.Model.Inductives.MutualCore
import ConLeche.Kernel.Inductives.NestedParts
import ConLeche.Model.Inductives.NestedAux
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedRecNames
public section

/-!
# The nested block's block model at the restored environment (task #315, M6 s6)

`blockReps_of`'s nested twin (`MutualCore.lean`): the composed block
model `BlockModel.ofNested` (`BlockComposed.lean`) instantiated at the
auxiliary block's lists (`nestedBlockModel`), with the RESTORED
constructors as the members' constructors, holds at every member
(`IsBlockModels`) at a model of the restored environment, given

* the auxiliary block's formers' facts (`MutualFormersFacts` at the
  scratch install, DESIGN §U.18 (a): the grade-generic stage);
* the restored constructors' stage (`NestedCtorsStaged`, NAMED — the
  model of the restored environment with the members' leaves the
  auxiliary block's and the restored constructors read through the
  nested arm's `BlockCtorData`, DESIGN §U.18 (c));
* the pins' groups (`NestedPinGroup`, NAMED — the container's block
  model at the group, the copy-instantiation identities of K.28's
  pre-image; the pins' recorded index universes are the containers'
  own, `pinU`, DESIGN §U.22 — the per-component index universes inside
  the seal closed §U.17 (g) 1's gap).

Every clause of `IsBlockModel` is then discharged here: the operator's
laws through `BlockComposed`, `pinLeaf` through `ofNested_pinLeaf_of`
(`NestedFit.lean`), the constructors' injections through the auxiliary
leaves and the pin identification at the fields.
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

/-! ## The block model of the nested run -/

/-- **The nested block's block model at the run's data**: `BlockModel.ofNested`
at the auxiliary block's lists (the members' constructors first, one
copy per pin after), the members' constructors the RESTORED ones
(`ctorsR`, whose readings `dsR`/`xFvsR` the constructors' stage
chooses; everything else of a restored constructor's data is its
auxiliary constructor's — the restore touches only the nested field
domains), the pins' records `pinsS`. -/
noncomputable abbrev nestedBlockModel (p : NestedParts) (b : MutualBlock)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat))) (env : Env)
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR : Nat → Nat → List Expr) (pinsS : List PinSyn) : BlockModel V :=
  BlockModel.ofNested b.nP p.k f₀.s (Level.isEquiv f₀.s .zero == some true) b.large env
    ((fms.take p.k).map (·.cvTa.name)) ((fms.take p.k).map (·.nIdx)) ppsF W
    (fun t => (ctorsR.getD t []).map fun c => (c.1, c.2.2))
    (fun mm j => idxF (b.ownOffset mm + j)) dsR
    (fun mm j => esF (b.ownOffset mm + j)) (fun mm j => srcsF (b.ownOffset mm + j))
    (fun mm j => kindsOf (mutKsOf kinds (b.ownOffset mm + j)))
    (fun mm j i => tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    (fun mm j => fvsPF (b.ownOffset mm + j)) xFvsR (fun mm j => xrestF (b.ownOffset mm + j))
    (fun mm j => eissF (b.ownOffset mm + j)) (fun mm j => tssF (b.ownOffset mm + j))
    pinsS b.ownOffset (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
    (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
    (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
    (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)

/-! ## Kit: spine fits across agreeing domains, and under instantiation -/

/-- `FitsFrom` with no recursive flag is `SpineFit`. -/
theorem fitsFrom_nil_iff {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {fs : List V},
      FitsFrom [] slot i ρ Fs fs ↔ SpineFit ρ Fs fs
  | _, _, [], [] => Iff.rfl
  | _, _, [], _ :: _ => Iff.rfl
  | _, _, _ :: _, [] => Iff.rfl
  | i, ρ, F :: Fs, a :: fs => by
    show (a ∈ˢ (if ([] : List Bool).getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom [] slot (i + 1) (cons a ρ) Fs fs) ↔
      (a ∈ˢ interp V ρ F ∧ SpineFit (cons a ρ) Fs fs)
    simp only [List.getD_nil, Bool.false_eq_true, if_false]
    exact and_congr Iff.rfl fitsFrom_nil_iff

/-- **A spine fits two domain lists alike** when, at every position and
every prefix fitting both, the two domains read alike. -/
theorem spineFit_iff_agree {Fs Fs' : List AnnotTerm} {ρ : Nat → V} (hlen : Fs.length = Fs'.length)
    (hag : ∀ l, l < Fs.length → ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ρ (Fs.take l) fs₁ → SpineFit ρ (Fs'.take l) fs₁ →
      interp V (consList fs₁ ρ) (Fs.getD l default) = interp V (consList fs₁ ρ) (Fs'.getD l default))
    (fs : List V) : SpineFit ρ Fs fs ↔ SpineFit ρ Fs' fs := by
  rw [← fitsFrom_nil_iff (slot := fun _ _ => pt) (i := 0),
    ← fitsFrom_nil_iff (slot := fun _ _ => pt) (i := 0)]
  refine fitsFrom_iff_frames hlen fun l hl fs₁ hl₁ hf hf' => ?_
  simp only [List.getD_nil, Bool.false_eq_true, if_false]
  exact hag l hl fs₁ hl₁ (fitsFrom_nil_iff.mp hf) (fitsFrom_nil_iff.mp hf')

/-- **A spine fits an instantiated telescope at the block's frame iff it
fits the telescope at the pin's frame** (`interp_instAll` along the
telescope). -/
theorem spineFit_instTele (Ds : List AnnotTerm) (ρ' : Nat → V) :
    ∀ (Ids : List AnnotTerm) (fs₁ is : List V),
      SpineFit (consList fs₁ ρ') (instTele Ds fs₁.length Ids) is ↔
        SpineFit (consList fs₁ (consList (Ds.map (interp V ρ')) ρ')) Ids is
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | T :: Ids, fs₁, a :: is => by
    show (a ∈ˢ interp V (consList fs₁ ρ') (AnnotTerm.instAll Ds fs₁.length T) ∧
        SpineFit (cons a (consList fs₁ ρ')) (instTele Ds (fs₁.length + 1) Ids) is) ↔
      (a ∈ˢ interp V (consList fs₁ (consList (Ds.map (interp V ρ')) ρ')) T ∧
        SpineFit (cons a (consList fs₁ (consList (Ds.map (interp V ρ')) ρ'))) Ids is)
    rw [interp_instAll]
    have h := spineFit_instTele Ds ρ' Ids (fs₁ ++ [a]) is
    rw [List.length_append, List.length_singleton, consList_append, consList_append] at h
    exact and_congr Iff.rfl h


/-- Two frames from spines of one length over one base agree only on
equal spines. -/
private theorem consList_inj_len {as bs : List V} {ρ : Nat → V} (hl : as.length = bs.length)
    (h : consList as ρ = consList bs ρ) : as = bs := by
  apply List.ext_getElem hl
  intro i hi₁ hi₂
  have hk : as.length - 1 - i < as.length := by omega
  have := congrFun h (as.length - 1 - i)
  rw [consList_getD_lt as ρ _ hk, consList_getD_lt bs ρ _ (by omega),
    show as.length - 1 - (as.length - 1 - i) = i from by omega,
    show bs.length - 1 - (as.length - 1 - i) = i from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi₂] at this
  exact this

/-! ## The assembly -/

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

/-- **A pin group's facts** (NAMED, DESIGN §U.18 (d)): the copies
`[q₀, q₀ + kJ)` of the auxiliary block are the members of ONE
container block model `dJ` at the model `m` of the restored
environment — its pin list FREE (a container that is itself nested,
task #315 L-C, DESIGN §U.24) — `IsBlockModel` at every member (the
pins' records naming those members), its members and pins typed, with
the member-local tag shape — and the copy-instantiation identities of
K.28's pre-image at every constructor of the group (`CopyCtorInst`,
the index telescopes, the constructor counts, the components' fit),
the same-universe fact `w` and the pins' recorded index universes
`pinU` — each the container's own, at the group's level assignment
(§U.22; the agreement `u` of §U.17 (g) 1 is gone with the uniform
universe it compared). -/
structure NestedPinGroup (m : EnvModel V env₂) (q₀ kJ : Nat) (dJ : BlockModel V) : Prop where
  seg : q₀ + kJ ≤ pinsS.length
  kpos : 0 < kJ
  reps : IsBlockModels m dJ
  kEq : dJ.k = kJ
  rep : ∀ i, i < kJ → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    IsBlockModel m ((D).pinAt (q₀ + i)).J cvT cvR mI rP rules dJ i
  typed : ∀ ψ : Name → Nat, FormersTyped m dJ ψ
  pinsTyped : ∀ ψ : Name → Nat, PinsTyped m dJ ψ
  inj : ∀ (ψJ : Name → Nat) (mm' j : Nat) (fs : List V),
    dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt]))
  pinU : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    ((D).pinAt (q₀ + i')).u ψ = dJ.uM i' (((D).pinAt (q₀ + i)).ψJ ψ)
  pinNP : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).nPJ = dJ.nP
  pinNIdx : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).nIdx = dJ.nIdxAt i
  pinPps : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).pps = dJ.ppsM i
  pinDsLen : ∀ i, i < kJ → ∀ ψ : Name → Nat, (((D).pinAt (q₀ + i)).Ds ψ).length = dJ.nP
  w : ∀ i, i < kJ → ∀ ψ : Name → Nat, dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ
  /-- the group's pins share their level assignment and their components'
  readings (task #315 L-E: `PinGroupView.same`) -/
  same : ∀ i, i < kJ → ∀ ψ : Name → Nat,
    ((D).pinAt (q₀ + i)).ψJ ψ = ((D).pinAt q₀).ψJ ψ ∧ ((D).pinAt (q₀ + i)).Ds ψ = ((D).pinAt q₀).Ds ψ
  idx : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    blockIds b.nP ppsF ψ (p.k + q₀ + i')
      = instTele (((D).pinAt (q₀ + i)).Ds ψ) 0 (dJ.IdsM i' (((D).pinAt (q₀ + i)).ψJ ψ))
  ctorCount : ∀ i', i' < kJ → (dJ.ctorsM i').length = (b.ownCtors (p.k + q₀ + i')).length
  DsFit : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
    SpineFit ρ ((D).params ψ) as →
    SpineFit (consList as ρ) (dJ.params (((D).pinAt (q₀ + i)).ψJ ψ))
      ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
  /-- the copies' constructor SHAPES (lane L-B) -/
  shape :
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyShapeA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (memberNames := (D).memberNames)
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        m.acval dJ (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
        q₀ kJ i' j
  /-- the copies' ENTRIES at the auxiliary carrier (`nestedPinLeaf_all`) -/
  entry :
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        dJ (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ) q₀ kJ i' j

/-! ### The pin groups' consequences -/

section Groups

variable {m : EnvModel V env₂} {q₀ kJ : Nat} {dJ : BlockModel V}
  (G : NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF) (esF := esF)
    (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
    (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) m q₀ kJ dJ)
include G

/-- The pin's index telescope is the container member's at the pin's
level assignment. -/
theorem NestedPinGroup.pinIds {i : Nat} (hi : i < kJ) (ψ : Name → Nat) :
    ((D).pinAt (q₀ + i)).Ids ψ = dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ) := by
  unfold PinSyn.Ids
  rw [G.pinPps i hi, G.pinNP i hi]
  rfl

/-- The pin's container is stored at the model's environment. -/
theorem NestedPinGroup.found {i : Nat} (hi : i < kJ) :
    ∃ (cv : ConstantVal) (caps : IndCaps),
      env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cv caps) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  have := hI.memsFound i (G.kEq ▸ hi)
  rwa [hI.member] at this

/-- **The grouping of the copies' constructors**: the auxiliary block's
constructor `offs (k + q₀ + i') + j` is member `k + q₀ + i'`'s iff `j`
is below the container member's constructor count. -/
theorem NestedPinGroup.grp (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (ψ : Name → Nat) {i' : Nat} (hi' : i' < kJ) (j : Nat) :
    (b.ownOffset (p.k + q₀ + i') + j < (blkFss0 b ctorsA kinds dsF ψ).length ∧
      (mutMems ctorsA.length (mutMemF b)).getD (b.ownOffset (p.k + q₀ + i') + j) 0
        = p.k + q₀ + i') ↔ j < (dJ.ctorsM i').length := by
  rw [G.ctorCount i' hi']
  have hlenF : (blkFss0 b ctorsA kinds dsF ψ).length = ctorsA.length := by
    show ((List.range ctorsA.length).map _).length = _; simp
  rw [hlenF]
  constructor
  · rintro ⟨hJl, hmem⟩
    rw [mutMems_getD hJl] at hmem
    have hJb : b.ownOffset (p.k + q₀ + i') + j < b.ctors.length := by rw [← hlenA]; exact hJl
    have hc : b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJb]; rfl
    obtain ⟨-, hown⟩ := ownCtors_of_ctors h3 hc
    have hmem' : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).member = p.k + q₀ + i' :=
      hmem
    rw [hmem', Nat.add_sub_cancel_left] at hown
    exact (List.getElem?_eq_some_iff.mp hown).1
  · intro hj
    have hj' : (b.ownCtors (p.k + q₀ + i'))[j]? = some ((b.ownCtors (p.k + q₀ + i'))[j]) :=
      List.getElem?_eq_getElem hj
    rcases hx : (b.ownCtors (p.k + q₀ + i'))[j] with ⟨J', c⟩
    rw [hx] at hj'
    have hJ' := ownCtors_getElem?_idx h3 hj'
    obtain ⟨hc, hmemc⟩ := ownCtors_getElem?_ctors hj'
    subst hJ'
    have hJl : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length := by
      rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hc).1
    refine ⟨hJl, ?_⟩
    rw [mutMems_getD hJl]
    show (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).member = _
    rw [List.getD_eq_getElem?_getD, hc]
    exact hmemc

end Groups


/-! ### The nested field's index readings fit the pin (the `nest_fit`
argument at the pieces, before the block model exists) -/

/-- A graded application of a pin's container at the lifted components
and index readings: the index readings fit the container's index
telescope at the pin's frame. -/
theorem nestedFit_of_wd {m : EnvModel V env₂} {dJ : BlockModel V} {i : Nat} {J : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hI : IsBlockModel m J cvT cvR mI rP rules dJ i) {ψJ : Name → Nat}
    (hFT : FormersTyped m dJ ψJ) {ρp : Nat → V} {as₀ : List V} {e : Nat} (he : as₀.length = e)
    {Ds Eis : List AnnotTerm} (hDl : Ds.length = dJ.nP) (hEl : Eis.length = dJ.nIdxAt i)
    (hwd : WellDenoted V (consList as₀ ρp)
      (AnnotTerm.mkAppN (m.acval J ψJ) (Ds.map (·.liftN e 0) ++ Eis))) :
    SpineFit (consList (Ds.map (interp V ρp)) ρp) (dJ.IdsM i ψJ)
      (Eis.map (interp V (consList as₀ ρp))) := by
  have hFT' := hFT i hI.memberLt ρp
  rw [hI.member] at hFT'
  have hfit := spineFit_of_wellDenoted_mkAppN_pis (C := .sort (dJ.w ψJ)) (ds := dJ.ppsM i ψJ)
    (σ := ρp) (ρ := consList as₀ ρp) (fv := interp V ρp (m.acval J ψJ))
    (fun d' hd' => hI.former.bits ψJ d' hd')
    (by rw [List.length_append, List.length_map, hDl, hEl, hI.ppsM_length]; exact Nat.le_refl _)
    hwd (interp_closed (V := V) (m.cval_closedL _ _) _ _) hFT'
  rw [List.length_append, List.length_map, hDl, hEl, ← hI.ppsM_length ψJ, List.take_length,
    ← List.take_append_drop dJ.nP (dJ.ppsM i ψJ), List.map_append, List.map_append,
    List.map_map] at hfit
  have hlift : Ds.map (interp V (consList as₀ ρp) ∘ fun Dc => Dc.liftN e 0) = Ds.map (interp V ρp) :=
    List.map_congr_left fun Dc _ => by
      show interp V (consList as₀ ρp) (Dc.liftN e 0) = interp V ρp Dc
      subst he
      exact interp_liftN_consList Dc as₀ ρp
  rw [hlift] at hfit
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
  have hlen₁ : as₁.length = (Ds.map (interp V ρp)).length := by
    rw [h1.length_eq, List.length_map, List.length_take, hI.ppsM_length, List.length_map, hDl]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hlen₁.symm
  exact h2


/-! ### The block model at every member -/

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- A frame satisfying the block's parameters is a fitting spine over a
base (`satOfSpine`'s converse). -/
theorem spineOfSat_params (d : BlockModel V) {ψ : Name → Nat} {ρp : Nat → V}
    (h : Sat V (d.params ψ).reverse ρp) :
    ∃ (ρ : Nat → V) (as : List V), ρp = consList as ρ ∧ SpineFit ρ (d.params ψ) as := by
  refine ⟨fun i => ρp (i + (d.params ψ).length), (List.range (d.params ψ).length).reverse.map ρp,
    (consList_range_reverse _ _).symm, ?_⟩
  exact spineFit_of_sat (Δ₀ := []) (Ds := d.params ψ) (ρ := ρp) (by rw [List.append_nil]; exact h)

/-- **A pin's recorded universe is its group's component's**: the
block model's `nestedU` at the pin's component is the pin record's
`u`, which the group says is the container's (`pinU`). -/
theorem nestedU_pin_group (m : EnvModel V env₂) {q₀ kJ i : Nat} {dJ : BlockModel V}
    (G : PG m q₀ kJ dJ) (hi : i < kJ) (ψ : Name → Nat) :
    ∀ i', i' < kJ →
      nestedU p.k W pinsS ψ (p.k + q₀ + i') = dJ.uM i' (((D).pinAt (q₀ + i)).ψJ ψ) := by
  intro i' hi'
  rw [Nat.add_assoc, nestedU_pin]
  exact G.pinU i hi ψ i' hi'

/-- **The pins' index telescopes at the squash regime are bounded**: a
pin whose container's index universe is `0` has its copy's index
telescope a list of truth values at the block's frame — the
container's `idxOk` at the pin's frame (the components fit, `DsFit`),
transported along the instantiation identity `idx`
(`fieldsBound_instTele`).  What `NestedLfpOk`'s per-component premise
asks beyond the auxiliary block's uniform one (DESIGN §U.22). -/
theorem nestedPinBound_of (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ)
    (ψ : Name → Nat) (ρp : Nat → V) (hρp : Sat V ((D).params ψ).reverse ρp) :
    ∀ q, q < pinsS.length → ((D).pinAt q).u ψ = 0 →
      FieldsBound 0 ρp (blockIds b.nP ppsF ψ (p.k + q)) := by
  intro q hq hz
  obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hDsFit := G.DsFit i hi ψ ρ as hsp
  have hJ := (hI.idxOk _ _ (dJ.satOfSpine hDsFit) i (G.kEq ▸ hi)).2
  rw [← G.pinU i hi ψ i hi, hz] at hJ
  rw [← Nat.add_assoc, G.idx i hi ψ i hi]
  have := (fieldsBound_instTele 0 (((D).pinAt (q₀ + i)).Ds ψ) (consList as ρ)
    (dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)) []).mpr (by simpa only [consList_nil] using hJ)
  simpa only [consList_nil, List.length_nil] using this

/-- **`pinLeaf` as a fact of the block model**, at ANY model carrying the
groups (`nestedBlockReps_of` reads it at the run's model; the
constructors' loop needs it at every intermediate one): the pin's
container read at its components and index spine is the pin's
component of the block's least fixed point, at the tuple of the
spine at the pin's own index universe. -/
theorem nestedPinLeaf_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ) :
    ∀ q, q < (D).nPins → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
      SpineFit ρ ((D).params ψ) as →
      SpineFit ((D).pinFrame q ψ (consList as ρ)) (((D).pinAt q).Ids ψ) is →
      ((((D).pinAt q).Ds ψ).map (interp V (consList as ρ)) ++ is).foldl SetTheory.app
          (interp V ρ (m.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ)))
        = SetTheory.app ((D).pinCar ψ (consList as ρ)
              (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) q)
            (tupW (((D).pinAt q).u ψ) is) := by
  intro q hq ψ ρ as is hsp hisFit
  obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  exact ofNested_pinLeaf_of m.acval hI
    (nestedLfpOk_of_formers h hμ hbk ψ (consList as ρ) hρp (nestedPinBound_of m hgroups ψ _ hρp))
    (nestedShape_of_formers h hbk ψ) G.seg hi G.reps (G.typed _) (G.pinsTyped _)
    G.kEq (G.w i hi ψ) (nestedU_pin_group m G hi ψ) (G.inj _) (G.idx i hi ψ)
    (fun i' hi' j => G.grp h3 h.lenA ψ hi' j)
    (G.shape i hi ψ _ hρp) (G.entry i hi ψ _ hρp) rfl rfl rfl (G.pinIds hi ψ)
    (G.DsFit i hi ψ ρ as hsp) hisFit

/-- **The nested-entry identity**, at ANY model carrying the groups: the
container's leaf at the lifted components and the index readings reads
like the copy's leaf at the parameter variables and the same readings,
at every frame `consList fs₂ (consList as ρ)` at which the application
is graded.  This is what a nested field's restored domain buys: the
restore's entry and the auxiliary block's entry denote alike. -/
theorem nestedIdent_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ) :
    ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((D).params ψ) as →
      ∀ (e : Nat) (fs₂ : List V) (Eis : List AnnotTerm), fs₂.length = e →
        Eis.length = ((D).pinAt q).nIdx →
        WellDenoted V (consList fs₂ (consList as ρ))
          (AnnotTerm.mkAppN (m.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map (·.liftN e 0) ++ Eis)) →
        interp V (consList fs₂ (consList as ρ))
            (AnnotTerm.mkAppN (m.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
              ((((D).pinAt q).Ds ψ).map (·.liftN e 0) ++ Eis))
          = interp V (consList fs₂ (consList as ρ))
            (AnnotTerm.mkAppN
              (mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF (p.k + q) ψ)
              (paramBvarsAt b.nP (b.nP + e) ++ Eis)) := by
  -- the readers the assembly also derives
  have hkT : b.k = fms.length := h.lenFms.symm
  have hplen : ∀ ψ : Name → Nat, ((D).params ψ).length = b.nP := by
    intro ψ
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  have hframeT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ' : Nat → V),
        Sat V ((D).params ψ).reverse ρ' ↔ Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ' :=
    fun t f hft ψ ρ' => (h.frame t f hft ψ ρ').symm
  have hpinLeaf := nestedPinLeaf_of hμ h h3 hbk m hgroups
  intro q hq ψ ρ as hsp e fs₂ Eis he hEl hwd
  obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  subst he
  rw [show p.k + (q₀ + i) = p.k + q₀ + i from (Nat.add_assoc _ _ _).symm]
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
  have hlenAs : as.length = b.nP := by rw [hsp.length_eq, hplen]
  have hOk' := nestedLfpOk_of_formers h hμ hbk ψ (consList as ρ) hρp
    (nestedPinBound_of m hgroups ψ _ hρp)
  have hEl' : Eis.length = dJ.nIdxAt i := by rw [hEl, G.pinNIdx i hi]
  have htgt : p.k + q₀ + i < p.k + pinsS.length := by omega
  have htl : p.k + q₀ + i < fms.length := by rw [← hkT, hbk]; exact htgt
  have hft_t := fms_get htl
  have hisFit := nestedFit_of_wd hI (G.typed _) rfl (G.pinDsLen i hi ψ) hEl' hwd
  -- the left side: the pin's leaf at the block's carrier
  have hlift : (((D).pinAt (q₀ + i)).Ds ψ).map
      (interp V (consList fs₂ (consList as ρ)) ∘ fun Dc => Dc.liftN fs₂.length 0)
      = (((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)) :=
    List.map_congr_left fun Dc _ => by
      show interp V (consList fs₂ (consList as ρ)) (Dc.liftN fs₂.length 0) = _
      exact interp_liftN_consList Dc fs₂ (consList as ρ)
  rw [interp_mkAppN_foldl, List.map_append, List.map_map, hlift,
    interp_closed (V := V) (m.cval_closedL _ _) _ ρ]
  have hPL := hpinLeaf (q₀ + i) (by show q₀ + i < pinsS.length; omega) ψ ρ as
    (Eis.map (interp V (consList fs₂ (consList as ρ)))) hsp
    (by
      show SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
        (consList as ρ)) (((D).pinAt (q₀ + i)).Ids ψ) _
      rw [G.pinIds hi ψ]
      exact hisFit)
  have hpc : (D).pinCar ψ (consList as ρ)
      (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)))
      (q₀ + i)
    = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ (consList as ρ))
      (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
        (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)
        ψ (consList as ρ)) (p.k + (q₀ + i)) :=
    ofNested_pinCar_lfp hOk' (by show q₀ + i < pinsS.length; omega)
  rw [hPL, hpc]
  -- the right side: the copy's leaf at the auxiliary carrier
  unfold mutMemberLeaf
  rw [interp_mkAppN_foldl, List.map_append,
    map_paramBvarsAt_interp (ρp := consList as ρ) (fun j' => consList_apply_add fs₂ _ j'),
    interp_closed (V := V) (tupleLfpAV_below h.blockOk b.ownOffset
      ((h.FD _ _ hft_t).below ψ) ((h.FD _ _ hft_t).len ψ) ψ) _ ρ]
  have hrng : (List.range b.nP).reverse.map (consList as ρ) = as := by
    have h1 := consList_range_reverse b.nP (consList as ρ)
    have h2 : (fun j' => consList as ρ (j' + b.nP)) = ρ := by
      funext j'; rw [← hlenAs]; exact consList_apply_add as ρ j'
    rw [h2] at h1
    exact consList_inj_len (by simp [hlenAs]) h1
  rw [hrng]
  have hnI : ((ppsF (p.k + q₀ + i) ψ).drop b.nP).length
      = (fms.getD (p.k + q₀ + i) default).nIdx := by
    rw [List.length_drop, (h.FD _ _ hft_t).len ψ]
    exact Nat.add_sub_cancel_left _ _
  have hsp_t : SpineFit ρ (((ppsF (p.k + q₀ + i) ψ).take b.nP).map (·.2.2)) as :=
    spineFit_of_frames (by
        rw [hplen, List.length_map, List.length_take, (h.FD _ _ hft_t).len ψ]; omega)
      (fun ρ' => hframeT _ _ hft_t ψ ρ') hsp
  have hi_t : SpineFit (consList as ρ) (((ppsF (p.k + q₀ + i) ψ).drop b.nP).map (·.2.2))
      (Eis.map (interp V (consList fs₂ (consList as ρ)))) := by
    show SpineFit (consList as ρ) (blockIds b.nP ppsF ψ (p.k + q₀ + i)) _
    rw [G.idx i hi ψ i hi]
    have := (spineFit_instTele (((D).pinAt (q₀ + i)).Ds ψ) (consList as ρ)
      (dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)) []
      (Eis.map (interp V (consList fs₂ (consList as ρ))))).mpr hisFit
    simpa using this
  rw [← hnI,
    show mutRss ctorsA.length (mutKsOf kinds) = blkRss ctorsA kinds from rfl,
    show mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ
      = blkFss0 b ctorsA kinds dsF ψ from rfl, hbk]
  -- the copy's leaf read at the PER-COMPONENT index sets: the one term, the nested premise
  have hu : nestedU p.k W pinsS ψ (p.k + q₀ + i) = ((D).pinAt (q₀ + i)).u ψ := by
    rw [Nat.add_assoc]; exact nestedU_pin p.k W pinsS ψ (q₀ + i)
  rw [tupleLfpAV_fold htgt hOk' rfl hsp_t hi_t, ← Nat.add_assoc, hu]
  rfl

/-- **The nested block's block model at the restored environment, at
every member** (`blockReps_of`'s nested twin): from the auxiliary
block's formers' facts, the constructors' stage's outputs at the model
`mp₂` of the restored environment (the members' records and leaves,
the restored constructors' records, leaves and readings through the
nested arm), and the pins' groups. -/
theorem nestedBlockReps_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (mp₂ : EnvModelM V μ env₂)
    (hfindM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      env₂.find? f.cvTa.name = some (.indInfo f.cvTa {}))
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₂.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    (hFD₂ : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      FormerData mp₂.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t))
    (hctorsLen : ∀ mm, mm < p.k → (ctorsR.getD mm []).length = (b.ownCtors mm).length)
    (hctorsR : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
      (ctorsR.getD mm [])[j]? = some c →
      ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 ∧
        (∀ ψ : Name → Nat, mp₂.base2.acval c.1.name ψ
          = sumMkAV (f₀.s.eval ψ) j (dsF (b.ownOffset mm + j) ψ)
              (((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2))
              (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm)))) ∧
        (∀ e ∈ idxF (b.ownOffset mm + j), e.constsResolve env₂ = true) ∧
        BlockCtorFacts mp₂.base2 (D) b.lps mm j (c.1, c.2.2))
    (hdsR : ∀ (mm j : Nat) (ψ : Name → Nat), mm < p.k → j < (ctorsR.getD mm []).length →
      (dsR mm j ψ).length = (dsF (b.ownOffset mm + j) ψ).length ∧
      (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP ∧
      ∀ i, ((D).nestOf mm j i = none ∨
          (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) →
        (dsR mm j ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ dJ) :
    IsBlockModels mp₂.base2 (D) ∧
    ∀ ψ : Name → Nat,
      FormersTyped mp₂.base2 (D) ψ ∧ CtorsTyped mp₂.base2 (D) ψ ∧ PinsTyped mp₂.base2 (D) ψ := by
  -- the readers
  have hkT : b.k = fms.length := h.lenFms.symm
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  have hkle : p.k ≤ fms.length := by rw [← hkT, hbk]; exact Nat.le_add_right _ _
  have hName : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (D).memberName t = f.cvTa.name := by
    intro t f ht hft
    show ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = f.cvTa.name
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, hft]
    rfl
  have hNIdx : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (D).nIdxAt t = f.nIdx := by
    intro t f ht hft
    show ((fms.take p.k).map (·.nIdx)).getD t 0 = f.nIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, hft]
    rfl
  have hparams : ∀ ψ : Name → Nat, (D).params ψ = ((ppsF 0 ψ).take b.nP).map (·.2.2) :=
    fun _ => rfl
  have hplen : ∀ ψ : Name → Nat, ((D).params ψ).length = b.nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  -- a member's constructor, in the restored list and at the auxiliary block
  have hctorJ : ∀ (mm j : Nat) (cA : ConstantVal × Nat), ((D).ctorsM mm)[j]? = some cA →
      ∃ c : ConstantVal × Nat × Nat, (ctorsR.getD mm [])[j]? = some c ∧ cA = (c.1, c.2.2) := by
    intro mm j cA hj
    change ((ctorsR.getD mm []).map fun c => (c.1, c.2.2))[j]? = some cA at hj
    rw [List.getElem?_map] at hj
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hj
    exact ⟨c, hc, rfl⟩
  have hownJ : ∀ (mm j : Nat), mm < p.k → j < (ctorsR.getD mm []).length →
      b.ownOffset mm + j < ctorsA.length ∧ mutMemF b (b.ownOffset mm + j) = mm := by
    intro mm j hmm hjR
    have hjl : j < (b.ownCtors mm).length := by rw [← hctorsLen mm hmm]; exact hjR
    rcases hx : (b.ownCtors mm)[j] with ⟨J', c'⟩
    have hj' : (b.ownCtors mm)[j]? = some (J', c') := by rw [List.getElem?_eq_getElem hjl, hx]
    have hJ' := ownCtors_getElem?_idx h3 hj'
    obtain ⟨hcJ, hmemc⟩ := ownCtors_getElem?_ctors hj'
    subst hJ'
    refine ⟨by rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hcJ).1, ?_⟩
    show (b.ctors.getD (b.ownOffset mm + j) default).member = mm
    rw [List.getD_eq_getElem?_getD, hcJ]
    exact hmemc
  have hctorA : ∀ (mm j : Nat) (cA : ConstantVal × Nat), mm < p.k → ((D).ctorsM mm)[j]? = some cA →
      b.ownOffset mm + j < ctorsA.length ∧
      ctorsA[b.ownOffset mm + j]? = some (ctorsA.getD (b.ownOffset mm + j) default) ∧
      mutMemF b (b.ownOffset mm + j) = mm ∧ (ctorsA.getD (b.ownOffset mm + j) default).2 = cA.2 := by
    intro mm j cA hmm hj
    obtain ⟨c, hc, rfl⟩ := hctorJ mm j cA hj
    obtain ⟨cA', hJ, hnF, -⟩ := hctorsR mm j c hmm hc
    obtain ⟨hJl, hmem⟩ := hownJ mm j hmm (List.getElem?_eq_some_iff.mp hc).1
    have hgd : ctorsA.getD (b.ownOffset mm + j) default = cA' := by
      rw [List.getD_eq_getElem?_getD, hJ]; rfl
    exact ⟨hJl, ctorsA_get hJl, hmem, by rw [hgd]; exact hnF.symm⟩
  -- a checked constructor of a member, positionally in the restored list
  have hofCtor : ∀ J, J < ctorsA.length → mutMemF b J < p.k →
      b.ownOffset (mutMemF b J) ≤ J ∧
      ∃ cA : ConstantVal × Nat,
        ((D).ctorsM (mutMemF b J))[J - b.ownOffset (mutMemF b J)]? = some cA ∧
        cA.2 = (ctorsA.getD J default).2 := by
    intro J hJ hmemk
    have hJb : J < b.ctors.length := by rw [← hlenA]; exact hJ
    have hc : b.ctors[J]? = some (b.ctors.getD J default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJb]; rfl
    obtain ⟨hle, hown⟩ := ownCtors_of_ctors h3 hc
    have hmemF : (b.ctors.getD J default).member = mutMemF b J := rfl
    rw [hmemF] at hle hown
    refine ⟨hle, ?_⟩
    have hjl : J - b.ownOffset (mutMemF b J) < (ctorsR.getD (mutMemF b J) []).length := by
      rw [hctorsLen _ hmemk]; exact (List.getElem?_eq_some_iff.mp hown).1
    obtain ⟨c, hc'⟩ : ∃ c, (ctorsR.getD (mutMemF b J) [])[J - b.ownOffset (mutMemF b J)]? = some c :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨cA', hJ', hnF, -⟩ := hctorsR _ _ _ hmemk hc'
    rw [Nat.add_sub_cancel' hle] at hJ'
    refine ⟨(c.1, c.2.2), ?_, ?_⟩
    · change ((ctorsR.getD (mutMemF b J) []).map fun c => (c.1, c.2.2))[J - b.ownOffset (mutMemF b J)]?
        = _
      rw [List.getElem?_map, hc']
      rfl
    · show c.2.2 = _
      rw [hnF, List.getD_eq_getElem?_getD, hJ']
      rfl
  -- the frames
  have hframeT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((D).params ψ).reverse ρ ↔ Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ :=
    fun t f hft ψ ρ => (h.frame t f hft ψ ρ).symm
  have hframeC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((D).params ψ).reverse ρ ↔ Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ := by
    intro J cA hJ ψ ρ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    exact (hframeT _ _ (fms_get (h.motLt J hJl)) ψ ρ).trans ((h.framesJ hμ hJl).1 ψ ρ)
  -- the operator's premise and the lists' shape
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
      nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinBound_of mp₂.base2 hgroups ψ ρp hρp)
  have hS : ∀ ψ : Name → Nat,
      TupleLfpShape (p.k + pinsS.length) (blockIds b.nP ppsF ψ) (mutMems ctorsA.length (mutMemF b))
        (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (mutEiss0 ctorsA.length eissF ψ) (blkFss0 b ctorsA kinds dsF ψ)
        (mutEss0 ctorsA.length esF ψ) := fun ψ => nestedShape_of_formers h hbk ψ
  have hlenF : ∀ ψ : Name → Nat, (blkFss0 b ctorsA kinds dsF ψ).length = ctorsA.length := by
    intro ψ; show ((List.range ctorsA.length).map _).length = _; simp
  -- the pins: typed, shaped, their index sets the copies'
  have hPT : ∀ ψ : Name → Nat, PinsTyped mp₂.base2 (D) ψ := by
    intro ψ q hq ρ
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    have hFT := G.typed (((D).pinAt (q₀ + i)).ψJ ψ) i (G.kEq ▸ hi) ρ
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
    rw [hI.member] at hFT
    show interp V ρ (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
      ∈ˢ interp V ρ (mkPisAV (((D).pinAt (q₀ + i)).pps (((D).pinAt (q₀ + i)).ψJ ψ))
        (.sort (f₀.s.eval ψ)))
    rw [G.pinPps i hi, ← G.w i hi ψ]
    exact hFT
  have hpinShape : ∀ q, q < (D).nPins → ∀ ψ : Name → Nat,
      (∀ d' ∈ ((D).pinAt q).pps (((D).pinAt q).ψJ ψ), d'.2.1 ≠ 0) ∧
      (((D).pinAt q).Ds ψ).length = ((D).pinAt q).nPJ ∧
      (((D).pinAt q).pps (((D).pinAt q).ψJ ψ)).length = ((D).pinAt q).nPJ + ((D).pinAt q).nIdx := by
    intro q hq ψ
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
    rw [G.pinPps i hi, G.pinNP i hi, G.pinNIdx i hi, G.pinDsLen i hi ψ]
    exact ⟨fun d' hd' => hI.former.bits _ d' hd', rfl, hI.former.len _⟩
  have hPinIdx : ∀ q, q < (D).nPins → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      (D).pinIdx q ψ ρp = (D).idx ψ ρp (p.k + q) := by
    intro q hq ψ ρp
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    show idxSet (((D).pinAt (q₀ + i)).u ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) (((D).pinAt (q₀ + i)).Ids ψ)
      = idxSet (nestedU p.k W pinsS ψ (p.k + (q₀ + i))) ρp (blockIds b.nP ppsF ψ (p.k + (q₀ + i)))
    have hu : nestedU p.k W pinsS ψ (p.k + (q₀ + i)) = ((D).pinAt (q₀ + i)).u ψ :=
      nestedU_pin p.k W pinsS ψ (q₀ + i)
    rw [hu, G.pinIds hi ψ, ← Nat.add_assoc, G.idx i hi ψ i hi, idxSet_instTele Iff.rfl]
  -- `pinLeaf`, as a fact of the block model (also read by the constructors' clause)
  have hpinLeaf := nestedPinLeaf_of hμ h h3 hbk mp₂.base2 hgroups
  -- a member's constructor: its auxiliary constructor's data
  have hctorData : ∀ (mm j : Nat) (cA : ConstantVal × Nat), mm < p.k →
      ((D).ctorsM mm)[j]? = some cA → ∃ c : ConstantVal × Nat × Nat,
        (ctorsR.getD mm [])[j]? = some c ∧ cA = (c.1, c.2.2) ∧
        ctorsA[b.ownOffset mm + j]? = some (ctorsA.getD (b.ownOffset mm + j) default) ∧
        (ctorsA.getD (b.ownOffset mm + j) default).2 = c.2.2 ∧
        BlockCtorFacts mp₂.base2 (D) b.lps mm j (c.1, c.2.2) := by
    intro mm j cA hmm hj
    obtain ⟨c, hc, rfl⟩ := hctorJ mm j cA hj
    obtain ⟨cA', hJ, hnF, -, -, hBF⟩ := hctorsR mm j c hmm hc
    have hgd : ctorsA.getD (b.ownOffset mm + j) default = cA' := by
      rw [List.getD_eq_getElem?_getD, hJ]; rfl
    exact ⟨c, hc, rfl, by rw [hgd]; exact hJ, by rw [hgd]; exact hnF.symm, hBF⟩
  -- the entries of the restored and the auxiliary domain lists
  have hgetD : ∀ (l : List (Nat × Nat × AnnotTerm)) (n i : Nat), n + i < l.length →
      ((l.drop n).map (·.2.2)).getD i default = (l.getD (n + i) default).2.2 := by
    intro l n i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  -- the per-member facts
  have hrep : ∀ mm, mm < (D).k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel mp₂.base2 ((D).memberName mm) cvT cvR mI rP rules (D) mm := by
    intro mm hmm
    have hmmF : mm < fms.length := Nat.lt_of_lt_of_le hmm hkle
    have hft := fms_get hmmF
    have hlpsT : (fms.getD mm default).cvTa.levelParams = b.lps := h.lps _ _ hft
    refine ⟨(fms.getD mm default).cvTa, default, (D).nP + (D).k + (D).nCtors + (D).nIdxAt mm,
      (D).nP + (D).k + (D).nCtors, [], ?_⟩
    refine
      { memberLt := hmm, member := rfl, strip := ?_, isProp := rfl, mI := rfl, rP := rfl
        rules := fun hne => absurd rfl hne, former := ?_, ctors := ?_, memsFound := ?_
        pinsFound := ?_, tgtsLt := ?_, idxRes := ?_, uParams := ?_, paramsIff := ?_, idxOk := ?_
        functor := ?_, fibre := ?_, pinShape := hpinShape, pinMem := ?_, pinMono := ?_
        pinLeaf := hpinLeaf, leaf := ?_, ctor := ?_, mkZero := ofNested_mkZero, mkInj := ?_ }
    · -- strip
      obtain ⟨bs, hstrip⟩ := h.strip _ _ hft
      rw [hNIdx _ _ hmm hft]
      exact ⟨bs, _, hstrip, h.sEq _ _ hft⟩
    · -- former
      rw [hNIdx _ _ hmm hft]
      exact hFD₂ _ _ hmm hft
    · -- ctors
      intro mm' j cA hmm' hj
      obtain ⟨c, -, rfl, -, -, hBF⟩ := hctorData mm' j cA hmm' hj
      rw [hlpsT]
      exact hBF
    · -- memsFound
      intro mm' hmm'
      have hft' := fms_get (Nat.lt_of_lt_of_le hmm' hkle)
      rw [hName _ _ hmm' hft']
      exact ⟨_, _, hfindM _ _ hmm' hft'⟩
    · -- pinsFound
      intro q hq
      obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
      exact G.found hi
    · -- tgtsLt
      intro mm' j i hmm' hj _
      have hj' : ((D).ctorsM mm')[j]? = some (((D).ctorsM mm').getD j default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      obtain ⟨-, hJ, -, -⟩ := hctorA mm' j _ hmm' hj'
      show tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i < p.k + pinsS.length
      rw [← hbk, hkT]
      exact (h.ksJ _ _ hJ).2.2 i
    · -- idxRes
      intro mm' j cA hmm' hj e he
      obtain ⟨c, hc, rfl⟩ := hctorJ mm' j cA hj
      obtain ⟨-, -, -, -, hres, -⟩ := hctorsR mm' j c hmm' hc
      exact hres e he
    · -- uParams
      intro mm' hmm' ψ₁ ψ₂ hφ
      rw [hlpsT] at hφ
      show nestedU p.k W pinsS ψ₁ mm' = nestedU p.k W pinsS ψ₂ mm'
      rw [nestedU_mem (k := p.k) (W := W) (pins := pinsS) (ψ := ψ₁) hmm',
        nestedU_mem (k := p.k) (W := W) (pins := pinsS) (ψ := ψ₂) hmm']
      exact (h.blockOk.params hφ).1
    · -- paramsIff
      intro mm' j cA hmm' hj ψ ρ
      obtain ⟨c, hc, rfl, hJ, -, -⟩ := hctorData mm' j cA hmm' hj
      have hjR : j < (ctorsR.getD mm' []).length := (List.getElem?_eq_some_iff.mp hc).1
      show Sat V ((D).params ψ).reverse ρ ↔ Sat V (((dsR mm' j ψ).take b.nP).map (·.2.2)).reverse ρ
      rw [(hdsR mm' j ψ hmm' hjR).2.1]
      exact hframeC _ _ hJ ψ ρ
    · -- idxOk
      intro ψ ρp hρp mm' hmm'
      show IdxOk (nestedU p.k W pinsS ψ mm') ρp _
      rw [nestedU_mem (k := p.k) (W := W) (pins := pinsS) (ψ := ψ) hmm']
      exact TupleLfpOk.idxOk (hOk ψ ρp hρp) (Nat.lt_of_lt_of_le hmm' (Nat.le_add_right _ _))
    · -- functor
      intro ψ ρp hρp
      exact ofNested_functor (hOk ψ ρp hρp)
    · -- fibre
      intro ψ ρp hρp X hX mm' hmm' t ht x
      have hOk' := hOk ψ ρp hρp
      have hS' := hS ψ
      -- the fit at a constructor's global position, against the block model's
      have hfitJ : ∀ (j : Nat) (cA : ConstantVal × Nat), ((D).ctorsM mm')[j]? = some cA →
          ∀ fs : List V,
          FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset mm' + j) [])
              (fun i ρ => slotSet (f₀.s.eval ψ)
                (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                  (b.ownOffset mm' + j) []).getD i 0)) ρ
                (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset mm' + j) []).getD i [])
                (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset mm' + j) []).getD i [])
                (extT (f₀.s.eval ψ) p.k pinsS.length ((D).idx ψ ρp)
                  (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
                    (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
                    (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
                    (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
                    (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)
                    ψ ρp)
                  X (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                    (b.ownOffset mm' + j) []).getD i 0)))
              0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset mm' + j) []) fs ↔
            FitsFrom (((D).rss mm').getD j []) ((D).slotAt ψ X mm' j) 0 ρp
              (((D).Fss mm' ψ).getD j []) fs := by
        intro j cA hj fs
        obtain ⟨c, hc, rfl, hJ, hnF, hBF⟩ := hctorData mm' j cA hmm' hj
        have hJl : b.ownOffset mm' + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        have hjR : j < (ctorsR.getD mm' []).length := (List.getElem?_eq_some_iff.mp hc).1
        have hjl : j < ((D).ctorsM mm').length := (List.getElem?_eq_some_iff.mp hj).1
        have hCD := hBF.2.2
        have hlenDs : (dsF (b.ownOffset mm' + j) ψ).length = b.nP + c.2.2 := by
          rw [← hnF]; exact (h.CD _ _ hJ).len ψ
        have hlenR : (dsR mm' j ψ).length = b.nP + c.2.2 := hCD.len ψ
        have hksl : (mutKsOf kinds (b.ownOffset mm' + j)).length = c.2.2 := by
          rw [← hnF]; exact (h.ksJ _ _ hJ).1
        have hnFm : mutNFOf ctorsA (b.ownOffset mm' + j) = c.2.2 := by
          rw [mutNFOf_eq hJ]; exact hnF
        rw [IsBlockModel.rss_getD hjl, IsBlockModel.Fss_getD hj ψ, blkRss_getD hJl, blkFss0_getD hJl]
        show FitsFrom (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))) _ 0 ρp _ fs ↔
          FitsFrom (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))) _ 0 ρp
            (((dsR mm' j ψ).drop b.nP).map (·.2.2)) fs
        refine fitsFrom_iff_frames (by
            rw [shadowFs_length, List.length_map, List.length_drop, hlenR, hnFm]; omega)
          (fun l hl fs₁ hl₁ _ _ => ?_)
        rw [shadowFs_length, hnFm] at hl
        simp only [Nat.zero_add]
        by_cases hr : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))).getD l false = true
        · rw [if_pos hr, if_pos hr]
          have htgt : (D).tgts mm' j l < p.k + pinsS.length := by
            show tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) l < p.k + pinsS.length
            rw [← hbk, hkT]; exact (h.ksJ _ _ hJ).2.2 l
          have hfr : (fun n => consList fs₁ ρp (n + l)) = ρp := by
            funext n; rw [← hl₁]; exact consList_apply_add fs₁ ρp n
          have huT : (D).uT ((D).tgts mm' j l) ψ = nestedU p.k W pinsS ψ ((D).tgts mm' j l) :=
            ofNested_uT _ _
          show slotSet _ _ _ _ _ _ = slotSet ((D).w ψ) ((D).uT ((D).tgts mm' j l) ψ) (consList fs₁ ρp)
            ((((D).tlss mm' ψ).getD j []).getD l []) ((((D).Eiss mm' ψ).getD j []).getD l [])
            ((D).famAt ψ (fun n => consList fs₁ ρp (n + l)) X ((D).tgts mm' j l))
          rw [huT, hfr, ofNested_famAt ψ ρp X htgt, IsBlockModel.tlss_getD hj ψ,
            IsBlockModel.Eiss_getD hj ψ, mutTlss_getD hJl, mutEiss0_getD hJl,
            mutTgts_getD hJl (by rw [hnFm]; exact hl)]
          rfl
        · rw [if_neg hr, if_neg hr]
          have hr' : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))).getD l false = false := by
            simpa using hr
          rw [shadowFs_getD (by rw [hnFm]; exact hl), if_neg]
          · rw [hgetD _ _ _ (by rw [hlenDs]; omega), hgetD _ _ _ (by rw [hlenR]; omega),
              (hdsR mm' j ψ hmm' hjR).2.2 l (Or.inr hr')]
          · intro hrec
            have hkind := hrec.2
            rw [Nat.add_sub_cancel_left] at hkind
            have := (rsOf_getD_iff (ks := kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))
              (by rw [kindsOf_length, hksl]; exact hl)).mpr hkind
            rw [hr'] at this
            exact Bool.false_ne_true this
      have htermJ : ∀ (j : Nat) (cA : ConstantVal × Nat), ((D).ctorsM mm')[j]? = some cA →
          b.ownOffset mm' + j < ctorsA.length → ∀ fs : List V,
          (∀ l, l < (blockIds b.nP ppsF ψ mm').length →
            interp V (consList fs ρp)
                (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset mm' + j) []).getD l default)
              = projS l t) ↔
          ∀ l, l < ((D).IdsM mm' ψ).length →
            interp V (consList fs ρp) ((((D).Ess mm' ψ).getD j []).getD l default) = projS l t := by
        intro j cA hj hJl fs
        rw [IsBlockModel.Ess_getD hj ψ, mutEss0_getD hJl]
        exact Iff.rfl
      rw [ofNested_fibre hOk' hS' hX hmm' ht x]
      constructor
      · rintro ⟨j, fs, hJ, hmemJ, hfit, heqs, rfl⟩
        rw [hlenF] at hJ
        rw [mutMems_getD hJ] at hmemJ
        have hmemk : mutMemF b (b.ownOffset mm' + j) < p.k := by rw [hmemJ]; exact hmm'
        obtain ⟨-, cA, hj, -⟩ := hofCtor _ hJ hmemk
        rw [hmemJ, Nat.add_sub_cancel_left] at hj
        exact ⟨j, fs, (List.getElem?_eq_some_iff.mp hj).1,
          ⟨(hfitJ j cA hj fs).mp hfit, (htermJ j cA hj hJ fs).mp heqs⟩, rfl⟩
      · rintro ⟨j, fs, hjl, ⟨hfit, heqs⟩, rfl⟩
        have hj : ((D).ctorsM mm')[j]? = some (((D).ctorsM mm').getD j default) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
        obtain ⟨hJl, -, hmemJ, -⟩ := hctorA mm' j _ hmm' hj
        refine ⟨j, fs, by rw [hlenF]; exact hJl, by rw [mutMems_getD hJl]; exact hmemJ,
          (hfitJ j _ hj fs).mpr hfit, (htermJ j _ hj hJl fs).mpr heqs, rfl⟩
    · -- pinMem
      intro ψ ρp hρp X hX q hq
      exact ofNested_pinMem hq (hPinIdx q hq ψ ρp)
    · -- pinMono
      intro ψ ρp hρp X Y hX hY hle q hq
      exact ofNested_pinMono (hOk ψ ρp hρp) hX hY hle hq (hPinIdx q hq ψ ρp)
    · -- leaf
      intro ψ ρ as is hsp hi
      rw [hName _ _ hmm hft, hleafM _ _ hmm hft]
      unfold mutMemberLeaf
      have hsp' : SpineFit ρ (((ppsF mm ψ).take b.nP).map (·.2.2)) as :=
        spineFit_of_frames (by
            rw [hplen, List.length_map, List.length_take, (h.FD _ _ hft).len ψ]; omega)
          (fun ρ' => hframeT _ _ hft ψ ρ') hsp
      have hnI : ((ppsF mm ψ).drop b.nP).length = (fms.getD mm default).nIdx := by
        rw [List.length_drop, (h.FD _ _ hft).len ψ]
        exact Nat.add_sub_cancel_left _ _
      rw [← hnI, hbk]
      exact ofNested_leaf hmm (hOk ψ (consList as ρ) ((D).satOfSpine hsp)) hsp' hi
    · -- ctor
      intro mm' j cA hmm' hj ψ ρ as fs hsp hsp₂
      obtain ⟨c, hc, rfl, hJ, hnF, hBF⟩ := hctorData mm' j cA hmm' hj
      obtain ⟨-, -, -, hleaf, -, -⟩ := hctorsR mm' j c hmm' hc
      have hJl : b.ownOffset mm' + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      have hjR : j < (ctorsR.getD mm' []).length := (List.getElem?_eq_some_iff.mp hc).1
      have hCD := hBF.2.2
      have hρp : Sat V ((D).params ψ).reverse (consList as ρ) := (D).satOfSpine hsp
      rw [hleaf ψ]
      show (as ++ fs).foldl SetTheory.app (interp V ρ (sumMkAV (f₀.s.eval ψ) j
          (dsF (b.ownOffset mm' + j) ψ) (((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2))
          (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm')))))
        = injW (f₀.s.eval ψ) j (mkTower (fs ++ [pt]))
      by_cases hw0 : f₀.s.eval ψ = 0
      · rw [hw0, sumMkAV_zero, foldl_app_pt, injW_zero]
      · have hlenDs : (dsF (b.ownOffset mm' + j) ψ).length = b.nP + c.2.2 := by
          rw [← hnF]; exact (h.CD _ _ hJ).len ψ
        have hlenR : (dsR mm' j ψ).length = b.nP + c.2.2 := hCD.len ψ
        have hksl : (mutKsOf kinds (b.ownOffset mm' + j)).length = c.2.2 := by
          rw [← hnF]; exact (h.ksJ _ _ hJ).1
        -- the restored fields are graded at every fitting prefix
        have hFok : FieldsOkB 0 (consList as ρ) (((dsR mm' j ψ).drop b.nP).map (·.2.2)) := by
          have hok : WellDenoted V (fun i => consList as ρ (i + b.nP))
              (mkPisAV (dsR mm' j ψ) (ctorBodyAVI mp₂.base2 ((D).memberName mm') b.nP c.2.2 ψ
                (esF (b.ownOffset mm' + j) ψ))) :=
            (hCD.okTy ψ (fun i => consList as ρ (i + b.nP))).1
          rw [← List.take_append_drop b.nP (dsR mm' j ψ), mkPisAV_append] at hok
          have hpfit : SpineFit (fun i => consList as ρ (i + b.nP))
              (((dsR mm' j ψ).take b.nP).map (·.2.2)) ((List.range b.nP).reverse.map (consList as ρ)) := by
            have hsat := (hframeC _ _ hJ ψ (consList as ρ)).mp hρp
            rw [← (hdsR mm' j ψ hmm' hjR).2.1] at hsat
            have hlen : (((dsR mm' j ψ).take b.nP).map (·.2.2)).length = b.nP := by
              rw [List.length_map, List.length_take, hlenR]
              exact Nat.min_eq_left (Nat.le_add_right _ _)
            have := spineFit_of_sat (Δ₀ := []) (Ds := ((dsR mm' j ψ).take b.nP).map (·.2.2))
              (ρ := consList as ρ) (by rw [List.append_nil]; exact hsat)
            rw [hlen] at this
            exact this
          have h1 := (WellDenoted_mkPisAV_inv hok).2 _ hpfit
          rw [consList_range_reverse] at h1
          exact (WellDenoted_mkPisAV_inv h1).1
        -- the two domain lists read alike at every fitting prefix
        have hsp₂' : SpineFit (consList as ρ) (((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2)) fs := by
          rw [IsBlockModel.Fss_getD hj ψ] at hsp₂
          change SpineFit (consList as ρ) (((dsR mm' j ψ).drop b.nP).map (·.2.2)) fs at hsp₂
          refine (spineFit_iff_agree (by rw [List.length_map, List.length_drop, List.length_map,
            List.length_drop, hlenR, hlenDs]) (fun l hl fs₁ hl₁ hfR _ => ?_) fs).mp hsp₂
          rw [List.length_map, List.length_drop, hlenR, Nat.add_sub_cancel_left] at hl
          rw [hgetD _ _ _ (by rw [hlenR]; omega), hgetD _ _ _ (by rw [hlenDs]; omega)]
          by_cases hplain : (D).nestOf mm' j l = none ∨
              (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))).getD l false = false
          · rw [(hdsR mm' j ψ hmm' hjR).2.2 l hplain]
          · -- a nested field: the container at the pin's components, the copy's leaf
            have hr : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))).getD l false = true := by
              cases hb : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))).getD l false
              · exact absurd (Or.inr hb) hplain
              · rfl
            have hnt : ¬ (D).tgts mm' j l < p.k := by
              intro hlt
              exact hplain (Or.inl ((D).nestOf_none hlt))
            have hq : (D).nestOf mm' j l = some ((D).tgts mm' j l - p.k) := (D).nestOf_some hnt
            have htgt : (D).tgts mm' j l < p.k + pinsS.length := by
              show tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) l < p.k + pinsS.length
              rw [← hbk, hkT]; exact (h.ksJ _ _ hJ).2.2 l
            have hqlt : (D).tgts mm' j l - p.k < pinsS.length := by omega
            obtain ⟨q₀, kJ, i, dJ, hqeq, hi, G⟩ := hgroups _ hqlt
            have hkl : l < (kindsOf (mutKsOf kinds (b.ownOffset mm' + j))).length := by
              rw [kindsOf_length, hksl]; exact hl
            have hkind := (rsOf_getD_iff hkl).mp hr
            -- the target copy's leaf
            have htl : (D).tgts mm' j l < fms.length := by rw [← hkT, hbk]; exact htgt
            have hft_t := fms_get htl
            have hleafT : mp₁.base2.acval (mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) l))
                = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF ((D).tgts mm' j l) := by
              rw [show tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) l = (D).tgts mm' j l from rfl,
                (h.memT _ _ hft_t).1, h.leaf _ _ hft_t]
            rw [hqeq] at hq
            have htqEq : p.k + q₀ + i = (D).tgts mm' j l := by omega
            -- the pin's index readings fit, and the nested body's two readings agree
            have hEisLen : ∀ Eis : List AnnotTerm, Eis.length = ((D).pinAt (q₀ + i)).nIdx →
                Eis.length = dJ.nIdxAt i := fun Eis hE => by rw [hE, G.pinNIdx i hi]
            have hbody : ∀ (e : Nat) (fs₂ : List V) (Eis : List AnnotTerm), fs₂.length = e →
                Eis.length = dJ.nIdxAt i →
                WellDenoted V (consList fs₂ (consList as ρ))
                  (AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                    ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN e 0) ++ Eis)) →
                interp V (consList fs₂ (consList as ρ))
                    (AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                      ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN e 0) ++ Eis))
                  = interp V (consList fs₂ (consList as ρ))
                    (AnnotTerm.mkAppN
                      (mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF ((D).tgts mm' j l) ψ)
                      (paramBvarsAt b.nP (b.nP + e) ++ Eis)) := by
              have hb := nestedIdent_of hμ h h3 hbk mp₂.base2 hgroups (q₀ + i) (by omega) ψ ρ as hsp
              rw [← Nat.add_assoc, htqEq] at hb
              intro e fs₂ Eis he hEl hwd
              exact hb e fs₂ Eis he (by rw [G.pinNIdx i hi]; exact hEl) hwd
            rcases hkind with hk | hk
            · -- a finitary nested field
              have hk' : kindAt (mutKsOf kinds (b.ownOffset mm' + j)) l = .recursive := by
                rw [← kindsOf_getD']; exact hk
              have hlF : l < c.2.2 := hl
              have hlA : l < (ctorsA.getD (b.ownOffset mm' + j) default).2 := by rw [hnF]; exact hl
              have hL : ((dsR mm' j ψ).getD (b.nP + l) default).2.2
                  = AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                    ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN l 0) ++ (eissF (b.ownOffset mm' + j) ψ).getD l []) :=
                hCD.nestEntry ψ l (q₀ + i) hq hk hlF
              have hR := (h.CD _ _ hJ).recEntry ψ l hk' (by rw [hnF]; exact hl)
              rw [hL, hR, hleafT]
              have hEl := hEisLen _ (hCD.nestEisLen ψ l _ hq hk hlF)
              refine hbody l fs₁ _ hl₁ hEl ?_
              have := fieldsOkB_getD hFok (by
                rw [List.length_map, List.length_drop, hlenR, Nat.add_sub_cancel_left]; exact hl) hfR
              rw [hgetD _ _ _ (by rw [hlenR]; omega), hL] at this
              exact this
            · -- a reflexive nested field
              have hk' : kindAt (mutKsOf kinds (b.ownOffset mm' + j)) l = .reflexive := by
                rw [← kindsOf_getD']; exact hk
              have hlF : l < c.2.2 := hl
              have hL : ((dsR mm' j ψ).getD (b.nP + l) default).2.2
                  = mkPisAV ((tssF (b.ownOffset mm' + j) ψ).getD l [])
                    (AnnotTerm.mkAppN
                      (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                      ((((D).pinAt (q₀ + i)).Ds ψ).map
                          (·.liftN (l + ((tssF (b.ownOffset mm' + j) ψ).getD l []).length) 0)
                        ++ (eissF (b.ownOffset mm' + j) ψ).getD l [])) :=
                hCD.nestReflEntry ψ l (q₀ + i) hq hk hlF
              have hR := (h.CD _ _ hJ).reflEntry ψ l hk' (by rw [hnF]; exact hl)
              have hEl := hEisLen _ (hCD.nestEisLenRefl ψ l _ hq hk hlF)
              have hwdE := fieldsOkB_getD hFok (by
                rw [List.length_map, List.length_drop, hlenR, Nat.add_sub_cancel_left]; exact hl) hfR
              rw [hgetD _ _ _ (by rw [hlenR]; omega), hL] at hwdE
              rw [hL, hR, hleafT]
              have hbits : ∀ d ∈ (tssF (b.ownOffset mm' + j) ψ).getD l [],
                  (d.2.1 = 0 ↔ f₀.s.eval ψ = 0) :=
                fun d hd => hCD.tssBits ψ l d hd
              rw [interp_mkPisAV_piTele (v := f₀.s.eval ψ) (acc := [])
                (B := fun ys => interp V (consList ys (consList fs₁ (consList as ρ)))
                  (AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                    ((((D).pinAt (q₀ + i)).Ds ψ).map
                        (·.liftN (l + ((tssF (b.ownOffset mm' + j) ψ).getD l []).length) 0)
                      ++ (eissF (b.ownOffset mm' + j) ψ).getD l [])))
                hbits (fun ys _ => by simp),
                interp_mkPisAV_piTele (v := f₀.s.eval ψ) (acc := [])
                (B := fun ys => interp V (consList ys (consList fs₁ (consList as ρ)))
                  (AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))
                    ((((D).pinAt (q₀ + i)).Ds ψ).map
                        (·.liftN (l + ((tssF (b.ownOffset mm' + j) ψ).getD l []).length) 0)
                      ++ (eissF (b.ownOffset mm' + j) ψ).getD l [])))
                hbits (fun ys hys => ?_)]
              simp only [List.nil_append]
              have hysl : ys.length = ((tssF (b.ownOffset mm' + j) ψ).getD l []).length := by
                rw [hys.length_eq, List.length_map]
              have hwd' := (WellDenoted_mkPisAV_inv hwdE).2 ys hys
              rw [← consList_append] at hwd' ⊢
              have := hbody (l + ((tssF (b.ownOffset mm' + j) ψ).getD l []).length) (fs₁ ++ ys) _
                (by rw [List.length_append, hl₁, hysl]) hEl hwd'
              rw [← Nat.add_assoc] at this
              exact this.symm
        -- the auxiliary constructor's fold at the fitting spines
        have hsp₁ : SpineFit ρ (((dsF (b.ownOffset mm' + j) ψ).take b.nP).map (·.2.2)) as :=
          spineFit_of_frames (by
              rw [hplen, List.length_map, List.length_take, hlenDs]; omega)
            (fun ρ' => hframeC _ _ hJ ψ ρ') hsp
        have hsat : Sat V (((dsF (b.ownOffset mm' + j) ψ).take b.nP).map (·.2.2)).reverse
            (consList as ρ) := by
          have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
          rwa [List.append_nil] at this
        have hok : SumFieldsOkB (f₀.s.eval ψ) (consList as ρ)
            (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm'))) :=
          SumFieldsOkB_uChains fun Fs hFs =>
            (h.fssOkP hμ hJl ψ (consList as ρ) hsat).1 Fs (List.mem_of_mem_drop hFs)
        have hFsJ : (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm')))[j]?
            = some ((((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2)) ++ [idxEqAV []]) := by
          rw [uChains_getElem?, List.getElem?_drop, List.getElem?_eq_getElem (show b.ownOffset mm' + j
            < (mutFss b.nP ctorsA.length dsF ψ).length from by rw [mutFss_length]; exact hJl)]
          have hgd := mutFss_getD (n := ctorsA.length) (nP := b.nP) (dsF := dsF) (ψ := ψ) hJl
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show b.ownOffset mm' + j
            < (mutFss b.nP ctorsA.length dsF ψ).length from by rw [mutFss_length]; exact hJl),
            Option.getD_some] at hgd
          rw [hgd]
          rfl
        have hsplit : (dsF (b.ownOffset mm' + j) ψ).take b.nP ++ (dsF (b.ownOffset mm' + j) ψ).drop b.nP
            = dsF (b.ownOffset mm' + j) ψ := List.take_append_drop _ _
        have := sumMkAV_fold (V := V) (j := j) hw0
          (pds := (dsF (b.ownOffset mm' + j) ψ).take b.nP)
          (fds := (dsF (b.ownOffset mm' + j) ψ).drop b.nP)
          (Fss := uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm')))
          hsp₁ hsp₂' hok hFsJ
        rw [hsplit] at this
        rw [this, injW_pos hw0]
    · -- mkInj
      intro ψ hw' mm' hmm' j fs j' fs' hj hj' hlen hlen' heq
      exact ofNested_mkInj ψ hw' hlen hlen' heq
  refine ⟨hrep, fun ψ => ⟨?_, ?_, hPT ψ⟩⟩
  · -- FormersTyped
    intro t ht ρ
    have hft := fms_get (Nat.lt_of_lt_of_le ht hkle)
    rw [hName _ _ ht hft]
    have hread := (hFD₂ _ _ ht hft).read ψ
    exact mp₂.mem_type _ (ConLeche.Semantics.Env.find?_mem (hfindM _ _ ht hft)) ψ _ hread ρ
  · -- CtorsTyped
    intro c hc j cA hj ρ
    obtain ⟨cR, -, rfl, -, -, hBF⟩ := hctorData c j cA hc hj
    have hread := hBF.2.2.read ψ
    exact mp₂.mem_type _ (ConLeche.Semantics.Env.find?_mem hBF.1) ψ _ hread ρ


/-! ## The stage's outputs -/

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- **The restored constructors' stage's outputs** at a model `mp₂` of
the restored environment (the members re-consed with the records the
scratch install stored, the restored constructors after them) — the
inputs of `nestedBlockReps_of`, and the run-level readers
`nestedCoreModeled_of` needs beyond them (the pins' records, the
members' names, the agreement off the block).  Fields named after the
data they constrain: `pinsLen`/`pinRec` (the pin records are the
elimination's pins), `names`, `agree`, `findM`/`leafM`/`FD` (the
members at `mp₂`), `ctorsLen`/`ctorFacts`/`domFacts` (the restored
constructors: THE RESTORE READING LAW), `groups` (the pin groups). -/
structure NestedStageFacts (st : ElimState) (mp₂ : EnvModelM V μ ENV₂) : Prop where
  pinsLen : pinsS.length = st.pins.length
  pinRec : ∀ (q : Nat) (pin : NestedPin), st.pins[q]? = some pin →
    ((D).pinAt q).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container ((D).pinAt q).lvls) ((D).pinAt q).DsE
  names : (fms.take p.k).map (·.cvTa.name) = p.memberNames
  agree : ∀ n, n ∉ p.memberNames ++ p.ctors.map (·.cv.name) →
    ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ
  findM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    (ENV₂).find? f.cvTa.name = some (ConstantInfo.indInfo f.cvTa {})
  leafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    mp₂.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t
  FD : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    FormerData mp₂.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)
  ctorsLen : ∀ mm, mm < p.k → (ctorsR.getD mm []).length = (b.ownCtors mm).length
  ctorFacts : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 ∧
      (∀ ψ : Name → Nat, mp₂.base2.acval c.1.name ψ
        = sumMkAV (f₀.s.eval ψ) j (dsF (b.ownOffset mm + j) ψ)
            (((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2))
            (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm)))) ∧
      (∀ e ∈ idxF (b.ownOffset mm + j), e.constsResolve ENV₂ = true) ∧
      BlockCtorFacts mp₂.base2 (D) b.lps mm j (c.1, c.2.2)
  domFacts : ∀ (mm j : Nat) (ψ : Name → Nat), mm < p.k → j < (ctorsR.getD mm []).length →
    (dsR mm j ψ).length = (dsF (b.ownOffset mm + j) ψ).length ∧
    (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP ∧
    ∀ i, ((D).nestOf mm j i = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) →
      (dsR mm j ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default
  groups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
    q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ dJ

/-- **The restored constructors' LOOP's outputs** — what the named fact
`NestedCtorsStaged` supplies, at a model `mp₁` of the members' prefix
environment (the formers' stage at the prefix, `stageTupleFormers`)
and the model `mp₂` it conses: the pin records, the extension facts of
the constructors' conses (`find`, `hde`: a reading at the prefix model
survives), the members' leaves untouched, the agreement off the
restored constructors' names, the reading law (`ctorFacts`/`domFacts`)
and the pin groups.  `NestedStageFacts` is derived from it
(`nestedStageFacts_of`). -/
structure NestedLoopFacts (st : ElimState) (mp₁ : EnvModelM V μ ENV₁) (mp₂ : EnvModelM V μ ENV₂) :
    Prop where
  pinsLen : pinsS.length = st.pins.length
  pinRec : ∀ (q : Nat) (pin : NestedPin), st.pins[q]? = some pin →
    ((D).pinAt q).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container ((D).pinAt q).lvls) ((D).pinAt q).DsE
  find : FindPreserved ENV₁ ENV₂
  hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
    denoteMeta mp₁.base2.acval ENV₁ ψ dp e = some ea →
    denoteMeta mp₂.base2.acval ENV₂ ψ dp e = some ea
  leafKeep : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    mp₂.base2.acval f.cvTa.name = mp₁.base2.acval f.cvTa.name
  agreeC : ∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
    mp₂.base2.acval n = mp₁.base2.acval n
  ctorFacts : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 ∧
      (∀ ψ : Name → Nat, mp₂.base2.acval c.1.name ψ
        = sumMkAV (f₀.s.eval ψ) j (dsF (b.ownOffset mm + j) ψ)
            (((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2))
            (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm)))) ∧
      (∀ e ∈ idxF (b.ownOffset mm + j), e.constsResolve ENV₂ = true) ∧
      BlockCtorFacts mp₂.base2 (D) b.lps mm j (c.1, c.2.2)
  domFacts : ∀ (mm j : Nat) (ψ : Name → Nat), mm < p.k → j < (ctorsR.getD mm []).length →
    (dsR mm j ψ).length = (dsF (b.ownOffset mm + j) ψ).length ∧
    (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP ∧
    ∀ i, ((D).nestOf mm j i = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) →
      (dsR mm j ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default
  groups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
    q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ dJ

end Assembly

/-! ## The named fact -/

/-- **The restored constructors' loop** (NAMED, DESIGN §U.19 (c)): at
the run's conjuncts through `restoreCtors`, the auxiliary block's
formers' facts (`MutualFormersFacts` at the `auxRoute` grade), and a
model of the members' PREFIX environment whose leaves are the
auxiliary members' (the formers' stage at the prefix), the restored
constructors cons a model with their leaves the AUXILIARY leaves and
their types read through the nested arm (`NestedLoopFacts`).
Consumer: `nestedStageFacts_of` → `nestedCoreModeled_of`. -/
@[expose] def NestedCtorsStaged (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
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
    ConLeche.nestedPinKindsOk p b st stored = true →
    -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the prefix
    -- formers' environment (`consNestedFormers_take_eq`)
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok () →
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
    ∃ (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (xFvsR : Nat → Nat → List Expr) (pinsS : List PinSyn),
      NestedLoopFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) st mp₁' mp₂

section Stage

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

/-- **The stage's outputs from the loop's** (the derivable fields of
DESIGN §U.18 (c)): the members' prefix stage (`stageTupleFormers` at
`mutualFormersG_take`) supplies the loop's model of the prefix
environment; the members' records, leaves and data at `mp₂` are the
prefix stage's crossed by the loop's extension facts; the names are
the elimination's; the constructors' counts are the read-back's; the
agreement off the block composes the two stages'. -/
theorem nestedStageFacts_of (hst : NestedCtorsStaged V μ F) (hμ : μ.verifiedChecks = true)
    (hE : ConLeche.EtaFamiliesClosed env) {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
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
    (hkinds : ConLeche.nestedPinKindsOk p b st stored = true)
    (hpins₁ : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok ())
    (hnd : b.blockNames.Nodup) (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
      = .ok (ConLeche.consMutualFormers fms env, fms))
    (hctorsA : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
      = .ok (ctorsA, sortss))
    (h : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + st.pins.length)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR) :
    ∃ (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (xFvsR : Nat → Nat → List Expr) (pinsS : List PinSyn),
      NestedStageFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (mp := mp) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) st mp₂ := by
  -- the members' names are the block's, nodup
  have hndM : (fms.map (·.cvTa.name)).Nodup := by
    rw [h.names]
    have hnd' := hnd
    unfold ConLeche.MutualBlock.blockNames at hnd'
    exact (List.nodup_append.mp (List.nodup_append.mp hnd').1).1
  have hndF : ((fms.take p.k).map (·.cvTa.name)).Nodup := by
    rw [List.map_take]
    exact List.Nodup.sublist (List.take_sublist _ _) hndM
  have hkle : p.k ≤ fms.length := by rw [h.lenFms, hbk]; exact Nat.le_add_right _ _
  -- the formers' stage at the prefix
  obtain ⟨mp₁', hleaf₁, hoff₁, hstored₁⟩ := stageTupleFormers (V := V) (μ := μ) (F := F) h.blockOk
    b.ownOffset mp hE (ConLeche.mutualFormersG_take hformers p.k) hndF (fun t f hft => by
      have ht : t < p.k := by
        have := (List.getElem?_eq_some_iff.mp hft).1
        rw [List.length_take] at this
        omega
      rw [List.getElem?_take_of_lt ht] at hft
      exact ⟨h.lps t f hft, h.FD₀ t f hft, h.stageOk t f hft⟩)
  have hleafM' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t := by
    intro t f ht hft
    rw [hleaf₁ t f (by rw [List.getElem?_take_of_lt ht]; exact hft)]
    funext ψ
    unfold mutMemberLeaf
    rw [show (fms.getD t default).nIdx = f.nIdx by rw [List.getD_eq_getElem?_getD, hft]; rfl]
  have hoff' : ∀ n : Name,
      (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n := by
    intro n hn
    refine hoff₁ n fun t f hft => ?_
    have ht : t < p.k := by
      have := (List.getElem?_eq_some_iff.mp hft).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt ht] at hft
    exact hn t f ht hft
  have hfind' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (ConLeche.consMutualFormers (fms.take p.k) env).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
      FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t) := by
    intro t f ht hft
    obtain ⟨hf, hFD, -⟩ := hstored₁ t f (by rw [List.getElem?_take_of_lt ht]; exact hft)
    exact ⟨hf, hFD⟩
  -- the loop
  obtain ⟨mp₂, dsR, xFvsR, pinsS, L⟩ := hst hμ mp hE p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' hPM h0 h1
    hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hkinds hpins₁
    hformers h hbk h3 hnd hctorsA hleafM' hoff' hfind' hctors
  -- the names
  have hnames : (fms.take p.k).map (·.cvTa.name) = p.memberNames := by
    rw [List.map_take, h.names]
    exact ConLeche.auxBlock_memberNames hfA helim hb
  -- the restored constructors, positionally
  obtain ⟨hlenR, hposR⟩ := ConLeche.mapM_except_inv hctors
  have hlenS : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hlenT : (stored.take p.k).length = p.k := by
    rw [List.length_take, hlenS]; omega
  have hmemR : ∀ mm, mm < p.k → ∃ (a : AuxStored) (cs : List (ConstantVal × Nat × Nat)),
      stored[mm]? = some a ∧ ctorsR[mm]? = some cs ∧
      ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps a.ctors
        = .ok cs := by
    intro mm hmm
    obtain ⟨a, cs, ha, hcs, hrun⟩ := hposR mm (by rw [hlenT]; exact hmm)
    rw [List.getElem?_take_of_lt hmm] at ha
    exact ⟨a, cs, ha, hcs, hrun⟩
  have hctorsLen : ∀ mm, mm < p.k → (ctorsR.getD mm []).length = (b.ownCtors mm).length := by
    intro mm hmm
    obtain ⟨a, cs, ha, hcs, hrun⟩ := hmemR mm hmm
    rw [List.getD_eq_getElem?_getD, hcs, Option.getD_some, (ConLeche.restoreCtors_id hrun).1]
    exact (ConLeche.auxStored_ctor_eq haux hformers hctorsA h3 hstored ha).1
  -- a restored constructor's name is one of the block's constructors'
  have hnameR : ∀ c ∈ ctorsR.flatten, c.1.name ∈ p.ctors.map (·.cv.name) := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hcs
    have hmmk : mm < p.k := by
      have := (List.getElem?_eq_some_iff.mp hmm).1
      rw [hlenR, hlenT] at this
      exact this
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hmemR mm hmmk
    obtain rfl : cs' = cs := Option.some.inj (hcs'.symm.trans hmm)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcin
    have hjl : j < a.ctors.length := by
      rw [← (ConLeche.restoreCtors_id hrun).1]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[j]? = some c₀ := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨ty, -, hco⟩ := (ConLeche.restoreCtors_id hrun).2 j c₀ c hc₀ hj
    obtain ⟨cA, hcA', hc1, -, -⟩ :=
      (ConLeche.auxStored_ctor_eq haux hformers hctorsA h3 hstored ha).2 j c₀ hc₀
    have hname : c.1.name = cA.1.name := by rw [hco, ← hc1]
    rw [hname]
    have hJl : b.ownOffset mm + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hcA').1
    have hJb : b.ownOffset mm + j < b.ctors.length := by rw [← h.lenA]; exact hJl
    have hcJ : b.ctors[b.ownOffset mm + j]? = some (b.ctors.getD (b.ownOffset mm + j) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJb]; rfl
    have hnm : cA.1.name = (b.ctors.getD (b.ownOffset mm + j) default).cv.name := by
      have := congrArg (fun l => l[b.ownOffset mm + j]?) h.namesC
      simp only [List.getElem?_map, hcA', hcJ, Option.map_some] at this
      exact Option.some.inj this
    rw [hnm]
    refine ConLeche.auxBlock_ctorName_mem hfA hcA helim hb _ _ hcJ ?_
    obtain ⟨-, hown⟩ := ConLeche.ownCtors_of_ctors h3 hcJ
    have hjl' : j < (b.ownCtors mm).length := by rw [← hctorsLen mm hmmk, List.getD_eq_getElem?_getD, hmm]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hown' : (b.ownCtors mm)[j]? = some ((b.ownCtors mm)[j]) := List.getElem?_eq_getElem hjl'
    rcases hx : (b.ownCtors mm)[j] with ⟨J', c'⟩
    rw [hx] at hown'
    have hJ' := ConLeche.ownCtors_getElem?_idx h3 hown'
    obtain ⟨hcJ', hmemc⟩ := ConLeche.ownCtors_getElem?_ctors hown'
    subst hJ'
    rw [hcJ] at hcJ'
    obtain rfl := Option.some.inj hcJ'
    rw [hmemc]
    exact hmmk
  refine ⟨mp₂, dsR, xFvsR, pinsS,
    { pinsLen := L.pinsLen, pinRec := L.pinRec, names := hnames, agree := ?_
      findM := fun t f ht hft => L.find (hfind' t f ht hft).1
      leafM := fun t f ht hft => (L.leafKeep t f ht hft).trans (hleafM' t f ht hft)
      FD := fun t f ht hft => FormerData.crossEnv' L.hde (hfind' t f ht hft).2
      ctorsLen := hctorsLen, ctorFacts := L.ctorFacts, domFacts := L.domFacts
      groups := L.groups }⟩
  intro n hn ψ
  have hnM : n ∉ p.memberNames := fun hm => hn (List.mem_append_left _ hm)
  have hnC : n ∉ p.ctors.map (·.cv.name) := fun hc => hn (List.mem_append_right _ hc)
  rw [L.agreeC n (fun c hc heq => hnC (heq ▸ hnameR c hc)),
    hoff' n (fun t f ht hft heq => hnM (by
      rw [← hnames, heq]
      exact List.mem_map_of_mem (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt ht]; exact hft))))]

end Stage

end ConLeche.Model
