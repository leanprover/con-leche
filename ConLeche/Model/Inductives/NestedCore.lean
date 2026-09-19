module

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

omit [SetTheory V] in
/-- A dropped list's entry is the original's, shifted. -/
theorem getD_drop {α : Type _} (l : List α) (n j : Nat) (a : α) :
    (l.drop n).getD j a = l.getD (n + j) a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

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
    (nestedPc b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

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

/-- A `getD` inside a long enough prefix. -/
private theorem getD_take {α : Type} [Inhabited α] {L : List α} {k l : Nat} (h : l < k) :
    (L.take k).getD l default = L.getD l default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

/-- **THE PREFIXES FIT ALIKE** when two equally long domain lists read
alike at every prefix fitting both — `spineFit_iff_agree` at the
truncations. -/
theorem spineFit_take_iff_agree {FsA FsR : List AnnotTerm} {ρ : Nat → V} {nF : Nat}
    (hlenA : FsA.length = nF) (hlenR : FsR.length = nF)
    (hag : ∀ l, l < nF → ∀ fs : List V, fs.length = l →
      SpineFit ρ (FsA.take l) fs → SpineFit ρ (FsR.take l) fs →
      interp V (consList fs ρ) (FsA.getD l default)
        = interp V (consList fs ρ) (FsR.getD l default)) :
    ∀ k, k ≤ nF → ∀ fs : List V, SpineFit ρ (FsA.take k) fs ↔ SpineFit ρ (FsR.take k) fs := by
  intro k hk fs
  refine spineFit_iff_agree (by rw [List.length_take, List.length_take, hlenA, hlenR]) ?_ fs
  intro l hl fs₁ hl₁ h1 h2
  rw [List.length_take, hlenA] at hl
  have hlk : l < k := by omega
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlk)] at h1 h2
  rw [getD_take hlk, getD_take hlk]
  exact hag l (by omega) fs₁ hl₁ h1 h2

/-- The length a spine fitting a prefix has. -/
private theorem spineFitTake_length {Fs : List AnnotTerm} {ρ : Nat → V} {nF k : Nat}
    (hlen : Fs.length = nF) (hk : k ≤ nF) {fs : List V} (hsp : SpineFit ρ (Fs.take k) fs) :
    fs.length = k := by
  have h := SpineFit.length_eq hsp
  rw [List.length_take, hlen] at h
  omega

/-- **`FieldsBound` TRANSPORTS ALONG THE AGREEMENT**: two equally long
domain lists that read alike at every prefix fitting both are bounded
alike. -/
theorem fieldsBound_of_agree {w nF : Nat} {FsA FsR : List AnnotTerm} {ρ : Nat → V}
    (hlenA : FsA.length = nF) (hlenR : FsR.length = nF)
    (hag : ∀ l, l < nF → ∀ fs : List V, fs.length = l →
      SpineFit ρ (FsA.take l) fs → SpineFit ρ (FsR.take l) fs →
      interp V (consList fs ρ) (FsA.getD l default)
        = interp V (consList fs ρ) (FsR.getD l default))
    (hA : FieldsBound w ρ FsA) : FieldsBound w ρ FsR := by
  refine fieldsBound_of_pointwise fun i hi as hsp => ?_
  have hiN : i < nF := by rw [← hlenR]; exact hi
  have hspA : SpineFit ρ (FsA.take i) as :=
    (spineFit_take_iff_agree hlenA hlenR hag i (Nat.le_of_lt hiN) as).mpr hsp
  rw [← hag i hiN as (spineFitTake_length hlenA (Nat.le_of_lt hiN) hspA) hspA hsp]
  exact fieldsBound_getD hA i (by rw [hlenA]; exact hiN) as hspA

/-- **`FieldsOkB` TRANSPORTS ALONG THE AGREEMENT**, given the restored
list's own truthfulness (`FieldsOkB 0`, which its Π-tower's
`WellDenoted` gives): the truthfulness half is the restored list's,
the bound half the auxiliary list's, carried by the agreement. -/
theorem fieldsOkB_of_agree {w nF : Nat} {FsA FsR : List AnnotTerm} {ρ : Nat → V}
    (hlenA : FsA.length = nF) (hlenR : FsR.length = nF)
    (hag : ∀ l, l < nF → ∀ fs : List V, fs.length = l →
      SpineFit ρ (FsA.take l) fs → SpineFit ρ (FsR.take l) fs →
      interp V (consList fs ρ) (FsA.getD l default)
        = interp V (consList fs ρ) (FsR.getD l default))
    (hA : FieldsOkB w ρ FsA) (hR0 : FieldsOkB 0 ρ FsR) : FieldsOkB w ρ FsR := by
  refine fieldsOkB_of_pointwise fun i hi as hsp =>
    ⟨FieldsOkB.wellDenoted_at hR0 i hi as hsp, fun hw => ?_⟩
  have hiN : i < nF := by rw [← hlenR]; exact hi
  have hspA : SpineFit ρ (FsA.take i) as :=
    (spineFit_take_iff_agree hlenA hlenR hag i (Nat.le_of_lt hiN) as).mpr hsp
  rw [← hag i hiN as (spineFitTake_length hlenA (Nat.le_of_lt hiN) hspA) hspA hsp]
  exact fieldsBound_getD (hA.toBound hw) i (by rw [hlenA]; exact hiN) as hspA

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

/-- The entries of a domain list's field part. -/
theorem fieldsGetD (l : List (Nat × Nat × AnnotTerm)) (n i : Nat) (hi : n + i < l.length) :
    ((l.drop n).map (·.2.2)).getD i default = (l.getD (n + i) default).2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

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

/-- **THE INSTANCE MAP, AS THE ASSEMBLY'S σ** (task #315 WIDE (3′),
K.61/K.62/K.66 consumed): the function taking a class of the
container's own WIDE space — its members first, then its own pins — to
the class of the block's auxiliary tuple the expansion minted for it,
with the six facts `ofNested_pin_block_of_wide_inst` reads off it.

`σ` is EXISTENTIAL because the witness is the kernel's own instance
map at the group's base pin (`nestedInstMapAt`, K.61), lifted over the
members by `hroot`, and this structure carries no `ElimState`.  The
six clauses are, in the order that theorem takes them: `hroot`, `hσ`,
`hmemσ`, `hidxσ`, `hstgt`, `houtσ` — and, beside them, `hpinσ`.

**`hpinσ` is the row the CONTAINER's side of the correspondence reads**
(task #315 WIDE, lane `uniform-carry`).  `hstgt` says the copy's field
lands on `σ` of the container's own pin CLASS; the collapse-aware
correspondence between the two copies of one container at two
instantiations has to compare the block's pick with the CONTAINER's,
and neither side's INDEX is a handle for that — they index different
lists, and two own pins that collapse at one instantiation need not
collapse at the other.  So the comparison is made at the pin's DATA,
and this clause carries it: the class `σ` names is the block pin `q'`,
whose container, index universe, index telescope and components are
the container's own pin's at the group's instantiation.  It is
`PinCorr` minus its `EA` clause, which `targetRead_of_pin` rebuilds
from the three that are here — and minus it on purpose, because `EA`
is the only one that reads a model and this residual carries none.

**`hIsσ` is NOT here on purpose.**  It is the only one of the seven
that is not a fact about the run: it equates two INDEX SETS, and every
consumer that needs it already holds the group facts it is proved
from.  Putting it here would make this residual depend on the group
records it sits beside. -/
@[expose] def PinGroupInst (q₀ kJ : Nat) (dJ : BlockModel V) : Prop :=
  ∃ σ : Nat → Nat,
    -- `hroot`: the container's MEMBERS are the mint group, contiguous
    (∀ c, c < dJ.k → σ c = p.k + q₀ + c) ∧
    -- `hσ`: every class has a block class
    (∀ c, c < dJ.k + dJ.nPins → σ c < p.k + pinsS.length) ∧
    -- `hmemσ`: no member class shares a block pin with a pin class
    (∀ c c', c < dJ.k → ¬ c' < dJ.k → c' < dJ.k + dJ.nPins → σ c ≠ σ c') ∧
    -- `hidxσ`: two pin classes that COLLAPSE have one index-tuple set
    (∀ c c', ¬ c < dJ.k → c < dJ.k + dJ.nPins → ¬ c' < dJ.k → c' < dJ.k + dJ.nPins →
      σ c = σ c' → ∀ (ψ : Name → Nat) (ρp : Nat → V),
        dJ.idx (((D).pinAt q₀).ψJ ψ) ((D).pinFrame q₀ ψ ρp) c
          = dJ.idx (((D).pinAt q₀).ψJ ψ) ((D).pinFrame q₀ ψ ρp) c') ∧
    -- `hstgt`: a container-recursive field at one of the container's OWN
    -- pins lands on `σ` of that class
    (∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = true →
      ¬ dJ.tgts i' j l < dJ.k →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = σ (dJ.tgts i' j l)) ∧
    -- `houtσ`: a rewritten container-ORDINARY field leaves the instance
    (∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ¬ ∃ c, c < dJ.k + dJ.nPins ∧
        σ c = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) ∧
    -- `hpinσ`: AND THAT CLASS IS A PIN OF THE BLOCK, WITH THE
    -- CONTAINER'S OWN PIN'S DATA (task #315 WIDE, lane `uniform-carry`)
    (∀ (ψ : Name → Nat) (i' : Nat), i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = true →
      ¬ dJ.tgts i' j l < dJ.k →
      ∃ q', q' < pinsS.length ∧ σ (dJ.tgts i' j l) = p.k + q' ∧
        ((D).pinAt q').J = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J ∧
        ∀ φ : Name → Nat,
          ((D).pinAt q').u φ = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).u (((D).pinAt q₀).ψJ φ) ∧
          ((D).pinAt q').Ids φ = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ids (((D).pinAt q₀).ψJ φ) ∧
          ((D).pinAt q').Ds φ
            = ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds (((D).pinAt q₀).ψJ φ)).map
                (AnnotTerm.instAll (((D).pinAt q₀).Ds φ) 0))

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
  /-- the group's pins share their level arguments (task #315 L-E) -/
  lvls : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).lvls = ((D).pinAt q₀).lvls
  /-- the group's pins share their components SYNTACTICALLY (task #315
  L-E: `NestedPinGroupSyn.same`'s second half, which `ofParts` used to
  drop — `nestedPinShapes_of` reads it at the tail's groups) -/
  sameE : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).DsE = ((D).pinAt q₀).DsE
  /-- the pin's container is stored, and the pin's level assignment is
  the substitution at its level parameters (task #315 L-E, step (iii)) -/
  stored : ∀ i, i < kJ → ∃ (cvT : ConstantVal) (caps : IndCaps),
    env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cvT caps) ∧
    ∀ ψ : Name → Nat,
      ((D).pinAt (q₀ + i)).ψJ ψ = Level.substFn ψ cvT.levelParams ((D).pinAt (q₀ + i)).lvls
  idx : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    blockIds b.nP ppsF ψ (p.k + q₀ + i')
      = instTele (((D).pinAt (q₀ + i)).Ds ψ) 0 (dJ.IdsM i' (((D).pinAt (q₀ + i)).ψJ ψ))
  ctorCount : ∀ i', i' < kJ → (dJ.ctorsM i').length = (b.ownCtors (p.k + q₀ + i')).length
  /-- **the group's model names the container member's own constructors**,
  by name and in order, and the parameter counts agree (task #315 L-B's
  `NestedPinGroupSyn.ctorsOf`, exported here): the face `hctorsJ` of the
  recursors' stage (DESIGN §U.36 (d)) is this field, and the readings and
  the equations need no model face for it. -/
  ctorsOf : ∀ i', i' < kJ → ∀ (ciJ : ContainerInfo) (J : ContainerMember),
    ConLeche.containerInfo? env ((D).pinAt (q₀ + i')).J = some ciJ →
    J ∈ ciJ.members → J.name = ((D).pinAt (q₀ + i')).J →
    (dJ.ctorsM i').map (·.1.name) = J.ctors.map (·.name) ∧ dJ.nP = ciJ.nP
  DsFit : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
    SpineFit ρ ((D).params ψ) as →
    SpineFit (consList as ρ) (dJ.params (((D).pinAt (q₀ + i)).ψJ ψ))
      ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
  /-- the copies' constructor SHAPES (lane L-B) -/
  shape :
    ∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cvT caps) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
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
        ((D).pinAt (q₀ + i)).DsE cvT.levelParams ((D).pinAt (q₀ + i)).lvls q₀ kJ i' j
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
  /-- **the instance map, as the assembly's σ** (task #315 WIDE (3′)) -/
  inst : PinGroupInst (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) q₀ kJ dJ

/-! ### The pin groups' consequences -/

/-- **The grouping of a copy's constructors, at any member count**: the
auxiliary block's constructor `offs mm + j` is member `mm`'s iff `j` is
below the member's own constructor count (`mutualCtorsGrouped`). -/
theorem ownCtors_grp (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (ψ : Name → Nat) {mm nC : Nat}
    (hcount : nC = (b.ownCtors mm).length) (j : Nat) :
    (b.ownOffset mm + j < (blkFss0 b ctorsA kinds dsF ψ).length ∧
      (mutMems ctorsA.length (mutMemF b)).getD (b.ownOffset mm + j) 0 = mm) ↔ j < nC := by
  rw [hcount]
  have hlenF : (blkFss0 b ctorsA kinds dsF ψ).length = ctorsA.length := by
    show ((List.range ctorsA.length).map _).length = _; simp
  rw [hlenF]
  constructor
  · rintro ⟨hJl, hmem⟩
    rw [mutMems_getD hJl] at hmem
    have hJb : b.ownOffset (mm) + j < b.ctors.length := by rw [← hlenA]; exact hJl
    have hc : b.ctors[b.ownOffset (mm) + j]?
        = some (b.ctors.getD (b.ownOffset (mm) + j) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJb]; rfl
    obtain ⟨-, hown⟩ := ownCtors_of_ctors h3 hc
    have hmem' : (b.ctors.getD (b.ownOffset (mm) + j) default).member = mm :=
      hmem
    rw [hmem', Nat.add_sub_cancel_left] at hown
    exact (List.getElem?_eq_some_iff.mp hown).1
  · intro hj
    have hj' : (b.ownCtors (mm))[j]? = some ((b.ownCtors (mm))[j]) :=
      List.getElem?_eq_getElem hj
    rcases hx : (b.ownCtors (mm))[j] with ⟨J', c⟩
    rw [hx] at hj'
    have hJ' := ownCtors_getElem?_idx h3 hj'
    obtain ⟨hc, hmemc⟩ := ownCtors_getElem?_ctors hj'
    subst hJ'
    have hJl : b.ownOffset (mm) + j < ctorsA.length := by
      rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hc).1
    refine ⟨hJl, ?_⟩
    rw [mutMems_getD hJl]
    show (b.ctors.getD (b.ownOffset (mm) + j) default).member = _
    rw [List.getD_eq_getElem?_getD, hc]
    exact hmemc


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
        = p.k + q₀ + i') ↔ j < (dJ.ctorsM i').length :=
  ownCtors_grp h3 hlenA ψ (G.ctorCount i' hi') j

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
  obtain ⟨cvT', caps', hf', -⟩ := G.stored i hi
  exact ofNested_pinLeaf_of m.acval hI
    (nestedLfpOk_of_formers h hμ hbk ψ (consList as ρ) hρp (nestedPinBound_of m hgroups ψ _ hρp))
    (nestedShape_of_formers h hbk ψ) G.seg hi G.reps (G.typed _) (G.pinsTyped _)
    G.kEq (G.w i hi ψ) (nestedU_pin_group m G hi ψ) (G.inj _) (G.idx i hi ψ)
    (fun i' hi' j => G.grp h3 h.lenA ψ hi' j)
    (G.shape i hi cvT' caps' hf' ψ _ hρp) (G.entry i hi ψ _ hρp) rfl rfl rfl (G.pinIds hi ψ)
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

/-- **THE TWO DOMAIN LISTS READ ALIKE AT EVERY FITTING PREFIX**, at ANY
model carrying the groups: at a plain position the restored entry IS
the auxiliary one; at a nested position the auxiliary entry is the
COPY's leaf at the parameter variables and the restored entry the
CONTAINER's leaf at the pin's components, and those read alike by the
pin identification `nestedIdent_of` — in the finitary and in the
reflexive shape.

The restored constructors' loop spends it at its own intermediate
model (`ReadCtx.agree_of`, `NestedCtorRead.lean`); the recursors'
stage spends it at the restored constructors' one
(`NestedTailIn.domAgree`), where it is what carries the constructor
stage's FIELD facts — the grading, the bounds and the field sorts'
universes — across the restore.  The body of the restored
constructor's Π-tower is irrelevant (only its domains' grading is
read), so `hokR` is stated at an arbitrary `R`. -/
theorem nestedDomAgree_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ)
    {mm j : Nat} {cA : ConstantVal × Nat} {R : (Name → Nat) → AnnotTerm}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hmemJ : mutMemF b (b.ownOffset mm + j) = mm)
    (hlenR : ∀ ψ : Name → Nat, (dsR mm j ψ).length = b.nP + cA.2)
    (hokR : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (mkPisAV (dsR mm j ψ) (R ψ)))
    (htake : ∀ ψ : Name → Nat, (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP)
    (hplain : ∀ (ψ : Name → Nat) (l : Nat), l < cA.2 →
      ((D).nestOf mm j l = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD l false = false) →
      (dsR mm j ψ).getD (b.nP + l) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default)
    (hnest : ∀ (ψ : Name → Nat) (l q : Nat), l < cA.2 → (D).nestOf mm j l = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD l .ordinary = .recursive →
      ((dsR mm j ψ).getD (b.nP + l) default).2.2
        = AnnotTerm.mkAppN (m.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map (·.liftN l 0) ++ (eissF (b.ownOffset mm + j) ψ).getD l []) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD l []).length = ((D).pinAt q).nIdx)
    (hnestRefl : ∀ (ψ : Name → Nat) (l q : Nat), l < cA.2 → (D).nestOf mm j l = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD l .ordinary = .reflexive →
      ((dsR mm j ψ).getD (b.nP + l) default).2.2
        = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD l [])
          (AnnotTerm.mkAppN (m.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map
                (·.liftN (l + ((tssF (b.ownOffset mm + j) ψ).getD l []).length) 0)
              ++ (eissF (b.ownOffset mm + j) ψ).getD l [])) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD l []).length = ((D).pinAt q).nIdx) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsR mm j ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsR mm j ψ).getD (b.nP + l) default).2.2 := by
  intro ψ ρ hsat l hl fs₁ hl₁ _ hfR
  have hJl : b.ownOffset mm + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hkT : b.k = fms.length := h.lenFms.symm
  have hbk' : b.k = p.k + pinsS.length := hbk
  have hlenDs : (dsF (b.ownOffset mm + j) ψ).length = b.nP + cA.2 := (h.CD _ _ hJ).len ψ
  have hksl : (mutKsOf kinds (b.ownOffset mm + j)).length = cA.2 := (h.ksJ _ _ hJ).1
  -- the parameter frame as a fitting spine at the block's parameters
  have hplen : ∀ ψ : Name → Nat, ((D).params ψ).length = b.nP := by
    intro ψ
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  have hframeC : ∀ ρ' : Nat → V,
      Sat V ((D).params ψ).reverse ρ' ↔
        Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ' := by
    intro ρ'
    exact ((h.frame _ _ (fms_get (h.motLt _ hJl)) ψ ρ').symm).trans ((h.framesJ hμ hJl).1 ψ ρ')
  have hlenTake : (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).length = b.nP := by
    rw [List.length_map, List.length_take, hlenDs]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hspA := spineFit_of_sat (Δ₀ := []) (Ds := ((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2))
    (ρ := ρ) (by rw [List.append_nil]; exact hsat)
  rw [hlenTake] at hspA
  have hρ : consList ((List.range b.nP).reverse.map ρ) (fun i => ρ (i + b.nP)) = ρ :=
    consList_range_reverse b.nP ρ
  have hsp : SpineFit (fun i => ρ (i + b.nP)) ((D).params ψ) ((List.range b.nP).reverse.map ρ) :=
    spineFit_of_frames (by rw [hlenTake, hplen]) (fun ρ' => (hframeC ρ').symm) hspA
  -- the restored fields are graded at every fitting prefix
  have hFok : FieldsOkB 0 ρ (((dsR mm j ψ).drop b.nP).map (·.2.2)) := by
    have hok := hokR ψ (fun i => ρ (i + b.nP))
    rw [← List.take_append_drop b.nP (dsR mm j ψ), mkPisAV_append] at hok
    have hpfit : SpineFit (fun i => ρ (i + b.nP))
        (((dsR mm j ψ).take b.nP).map (·.2.2)) ((List.range b.nP).reverse.map ρ) := by
      rw [htake]; exact hspA
    have h1 := (WellDenoted_mkPisAV_inv hok).2 _ hpfit
    rw [hρ] at h1
    exact (WellDenoted_mkPisAV_inv h1).1
  have hlR : b.nP + l < (dsR mm j ψ).length := by rw [hlenR]; omega
  have hlA : b.nP + l < (dsF (b.ownOffset mm + j) ψ).length := by rw [hlenDs]; omega
  have hwdE := fieldsOkB_getD hFok (by
    rw [List.length_map, List.length_drop, hlenR, Nat.add_sub_cancel_left]; exact hl) hfR
  rw [fieldsGetD _ _ _ hlR] at hwdE
  rcases Decidable.em ((D).nestOf mm j l = none ∨
      (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD l false = false) with hpl | hpl
  · rw [hplain ψ l hl hpl]
  -- a nested field: the container at the pin's components, the copy's leaf
  have hr : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD l false = true := by
    cases hb : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD l false
    · exact absurd (Or.inr hb) hpl
    · rfl
  have hnt : ¬ (D).tgts mm j l < p.k := by
    intro hlt
    exact hpl (Or.inl ((D).nestOf_none hlt))
  have hq : (D).nestOf mm j l = some ((D).tgts mm j l - p.k) := (D).nestOf_some hnt
  have htgt : (D).tgts mm j l < p.k + pinsS.length := by
    show tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l < p.k + pinsS.length
    rw [← hbk', hkT]; exact (h.ksJ _ _ hJ).2.2 l
  have hqlt : (D).tgts mm j l - p.k < pinsS.length := by omega
  have hkl : l < (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).length := by
    rw [kindsOf_length, hksl]; exact hl
  have hkind := (rsOf_getD_iff hkl).mp hr
  have htl : (D).tgts mm j l < fms.length := by rw [← hkT, hbk']; exact htgt
  have hft_t := fms_get htl
  have hleafT : mp₁.base2.acval (mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l))
      = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF ((D).tgts mm j l) := by
    rw [show tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l = (D).tgts mm j l from rfl,
      (h.memT _ _ hft_t).1, h.leaf _ _ hft_t]
  have hident := nestedIdent_of hμ h h3 hbk' m hgroups ((D).tgts mm j l - p.k) hqlt ψ
    (fun i => ρ (i + b.nP)) ((List.range b.nP).reverse.map ρ) hsp
  rw [show p.k + ((D).tgts mm j l - p.k) = (D).tgts mm j l from by omega, hρ] at hident
  have hnameT : (fms.getD (mutMemF b (b.ownOffset mm + j)) default).cvTa.name
      = (fms.getD mm default).cvTa.name := by rw [hmemJ]
  rcases hkind with hk | hk
  · -- a finitary nested field
    have hk' : kindAt (mutKsOf kinds (b.ownOffset mm + j)) l = .recursive := by
      rw [← kindsOf_getD']; exact hk
    obtain ⟨hL, hEl⟩ := hnest ψ l _ hl hq hk
    have hR := (h.CD _ _ hJ).recEntry ψ l hk' hl
    rw [hL, hR, hleafT]
    rw [hL] at hwdE
    exact (hident l fs₁ _ hl₁ hEl hwdE).symm
  · -- a reflexive nested field
    have hk' : kindAt (mutKsOf kinds (b.ownOffset mm + j)) l = .reflexive := by
      rw [← kindsOf_getD']; exact hk
    obtain ⟨hL, hEl⟩ := hnestRefl ψ l _ hl hq hk
    have hR := (h.CD _ _ hJ).reflEntry ψ l hk' hl
    rw [hL] at hwdE
    rw [hL, hR, hleafT]
    have hbits : ∀ d ∈ (tssF (b.ownOffset mm + j) ψ).getD l [], (d.2.1 = 0 ↔ f₀.s.eval ψ = 0) := by
      intro d hd
      have := (h.CD _ _ hJ).tssBits ψ l d hd
      rw [h.sEq _ _ (fms_get (h.motLt _ hJl)) ψ] at this
      exact this
    rw [interp_mkPisAV_piTele (v := f₀.s.eval ψ) (acc := [])
      (B := fun ys => interp V (consList ys (consList fs₁ ρ))
        (AnnotTerm.mkAppN (m.acval ((D).pinAt ((D).tgts mm j l - p.k)).J
            (((D).pinAt ((D).tgts mm j l - p.k)).ψJ ψ))
          ((((D).pinAt ((D).tgts mm j l - p.k)).Ds ψ).map
              (·.liftN (l + ((tssF (b.ownOffset mm + j) ψ).getD l []).length) 0)
            ++ (eissF (b.ownOffset mm + j) ψ).getD l [])))
      hbits (fun ys _ => rfl),
      interp_mkPisAV_piTele (v := f₀.s.eval ψ) (acc := [])
      (B := fun ys => interp V (consList ys (consList fs₁ ρ))
        (AnnotTerm.mkAppN (m.acval ((D).pinAt ((D).tgts mm j l - p.k)).J
            (((D).pinAt ((D).tgts mm j l - p.k)).ψJ ψ))
          ((((D).pinAt ((D).tgts mm j l - p.k)).Ds ψ).map
              (·.liftN (l + ((tssF (b.ownOffset mm + j) ψ).getD l []).length) 0)
            ++ (eissF (b.ownOffset mm + j) ψ).getD l [])))
      hbits (fun ys hys => ?_)]
    simp only [List.nil_append]
    have hysl : ys.length = ((tssF (b.ownOffset mm + j) ψ).getD l []).length := by
      rw [hys.length_eq, List.length_map]
    have hwd' := (WellDenoted_mkPisAV_inv hwdE).2 ys hys
    rw [← consList_append] at hwd' ⊢
    have := hident (l + ((tssF (b.ownOffset mm + j) ψ).getD l []).length) (fs₁ ++ ys) _
      (by rw [List.length_append, hl₁, hysl]) hEl hwd'
    rw [← Nat.add_assoc] at this
    exact this.symm

/-- **The nested block's block model at the restored environment, at
every member** (`blockReps_of`'s nested twin): from the auxiliary
block's formers' facts, the constructors' stage's outputs at the model
`mp₂` of the restored environment (the members' records and leaves,
the restored constructors' records, leaves and readings through the
nested arm), and the pins' groups.

The representation is published in the NAMED form
(`IsBlockModelsAt`, task #315 M7-3 session 11): the assembly builds it
at the members' OWN auxiliary constants `(fms.getD mm default).cvTa`,
and `ContainerModeled.member` — the read-back's record — demands it
there, so the existential form would lose exactly what the install's
tail has to cross.  `IsBlockModelsAt.toIsBlockModels` is the
projection where the weaker form is enough. -/
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
    IsBlockModelsAt mp₂.base2 (D) (fun mm => (fms.getD mm default).cvTa) ∧
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
  -- every field's target is a class
  have htgtsLtM : ∀ c j i, c < (D).k → j < ((D).ctorsM c).length →
      (D).tgts c j i < (D).k + (D).nPins := by
    intro c j i hc hj
    have hj' : ((D).ctorsM c)[j]? = some (((D).ctorsM c).getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    obtain ⟨-, hJ, -, -⟩ := hctorA c j _ hc hj'
    show tgtAt (mutKsOf kinds (b.ownOffset c + j)) i < p.k + pinsS.length
    rw [← hbk, hkT]
    exact (h.ksJ _ _ hJ).2.2 i
  -- **the WIDE fibre** (task #315, Resolution 1): the auxiliary
  -- operator's decomposition at EVERY class and EVERY tuple of the wide
  -- tuple space — the members' rows against the block model's readers,
  -- the copies' against the pins' constructor data `nestedPc`.  The
  -- narrow `fibre` is this at the members and the EXTENDED tuple.
  have hPC : (D).pinCtors = nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF := rfl
  have htgtLtG : ∀ J i : Nat, 0 < p.k + pinsS.length →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD J []).getD i 0
        < p.k + pinsS.length := by
    intro J i hz
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
  -- a copy's index telescope has the container's instantiated length
  have hIdsP : ∀ (ψ : Name → Nat) (q : Nat), q < pinsS.length →
      ((D).IdsM (p.k + q) ψ).length = ((D).IdsT ((D).k + q) ψ).length := by
    intro ψ q hq
    have hnk : ¬ (D).k + q < (D).k := by omega
    rw [BlockModel.IdsT_of_pin hnk, Nat.add_sub_cancel_left]
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := hgroups q hq
    show (blockIds b.nP ppsF ψ (p.k + (q₀ + i))).length = (((D).pinAt (q₀ + i)).Ids ψ).length
    rw [← Nat.add_assoc, G.idx i hi ψ i hi, G.pinIds hi ψ, instTele_length]
  -- the auxiliary constructor's fit at a COPY is the class's `ChainFitT`
  have hchainP : ∀ (ψ : Name → Nat) (ρp : Nat → V) (q : Nat), q < pinsS.length →
      ∀ (Z : Nat → V) (t : V) (j : Nat) (fs : List V),
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
      ↔ (D).ChainFitT (D).pinCtors ψ ρp Z t ((D).k + q) j fs := by
    intro ψ ρp q hq Z t j fs
    have hnk : ¬ (D).k + q < (D).k := by omega
    have hslot : (fun (i : Nat) (ρ : Nat → V) => slotSet ((D).w ψ)
          (nestedU p.k W pinsS ψ
            (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q) + j) []).getD i 0)) ρ
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q) + j) []).getD i [])
          (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q) + j) []).getD i 0)))
        = (D).slotAtT (D).pinCtors ψ Z ((D).k + q) j := by
      funext i ρ
      unfold BlockModel.slotAtT BlockModel.teleAtT BlockModel.eisAtT
      rw [BlockModel.tgtsT_of_pin hnk, BlockModel.tlssT_of_pin hnk, BlockModel.EissT_of_pin hnk,
        Nat.add_sub_cancel_left, ofNested_uT, hPC]
      simp only [nestedPc, getD_drop]
    unfold BlockModel.ChainFitT
    rw [BlockModel.rssT_of_pin hnk, BlockModel.FssT_of_pin hnk, BlockModel.EssT_of_pin hnk,
      Nat.add_sub_cancel_left, ← hslot, hIdsP ψ q hq, hPC]
    simp only [nestedPc, getD_drop]
  -- the auxiliary constructor's fit at a MEMBER is the class's `ChainFitT`
  have hfitZ : ∀ (ψ : Name → Nat) (ρp : Nat → V) (mm' j : Nat) (cA : ConstantVal × Nat),
      mm' < p.k → ((D).ctorsM mm')[j]? = some cA → ∀ (Z : Nat → V) (fs : List V),
      FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset mm' + j) [])
          (fun i ρ => slotSet ((D).w ψ)
            (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset mm' + j) []).getD i 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset mm' + j) []).getD i [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset mm' + j) []).getD i [])
            (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset mm' + j) []).getD i 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset mm' + j) []) fs ↔
        FitsFrom (((D).rss mm').getD j []) ((D).slotAtT (D).pinCtors ψ Z mm' j) 0 ρp
          (((D).Fss mm' ψ).getD j []) fs := by
    intro ψ ρp mm' j cA hmm' hj Z fs
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
      have huT : (D).uT ((D).tgts mm' j l) ψ = nestedU p.k W pinsS ψ ((D).tgts mm' j l) :=
        ofNested_uT _ _
      show slotSet _ _ _ _ _ _ = slotSet ((D).w ψ) ((D).uT ((D).tgtsT (D).pinCtors mm' j l) ψ)
        (consList fs₁ ρp) ((((D).tlssT (D).pinCtors ψ mm').getD j []).getD l [])
        ((((D).EissT (D).pinCtors ψ mm').getD j []).getD l [])
        (Z ((D).tgtsT (D).pinCtors mm' j l))
      rw [BlockModel.tgtsT_of_mem hmm', BlockModel.tlssT_of_mem hmm',
        BlockModel.EissT_of_mem hmm', huT, IsBlockModel.tlss_getD hj ψ,
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
  -- the result's index readings at a MEMBER
  have htermZ : ∀ (ψ : Name → Nat) (ρp : Nat → V) (mm' j : Nat) (cA : ConstantVal × Nat),
      ((D).ctorsM mm')[j]? = some cA → b.ownOffset mm' + j < ctorsA.length →
      ∀ (t : V) (fs : List V),
      (∀ l, l < (blockIds b.nP ppsF ψ mm').length →
        interp V (consList fs ρp)
            (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset mm' + j) []).getD l default)
          = projS l t) ↔
      ∀ l, l < ((D).IdsM mm' ψ).length →
        interp V (consList fs ρp) ((((D).Ess mm' ψ).getD j []).getD l default) = projS l t := by
    intro ψ ρp mm' j cA hj hJl t fs
    rw [IsBlockModel.Ess_getD hj ψ, mutEss0_getD hJl]
    exact Iff.rfl
  have hfibZ : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V ((D).params ψ).reverse ρp →
      ∀ Z, InTupleSpace ((D).w ψ) ((D).k + (D).nPins) ((D).idx ψ ρp) Z →
      ∀ c, c < (D).k + (D).nPins → ∀ t, t ∈ˢ (D).idx ψ ρp c → ∀ x,
        x ∈ˢ SetTheory.app ((D).Ψaux ψ ρp Z c) t ↔
          ∃ j fs, j < ((D).ctorsT (D).pinCtors c).length ∧
            (D).ChainFitT (D).pinCtors ψ ρp Z t c j fs ∧
            x = (D).injT (D).pinCtors ψ c j fs := by
    intro ψ ρp hρp Z hZ c hc t ht x
    rw [ofNested_auxFibre_raw (hOk ψ ρp hρp) (hS ψ) hZ hc ht x]
    by_cases hck : c < p.k
    · -- a member's row
      rw [BlockModel.ctorsT_of_mem hck, BlockModel.injT_of_mem hck]
      constructor
      · rintro ⟨j, fs, hJ, hmemJ, hfit, heqs, rfl⟩
        rw [hlenF ψ] at hJ
        rw [mutMems_getD hJ] at hmemJ
        have hmemk : mutMemF b (b.ownOffset c + j) < p.k := by rw [hmemJ]; exact hck
        obtain ⟨-, cA, hj, -⟩ := hofCtor _ hJ hmemk
        rw [hmemJ, Nat.add_sub_cancel_left] at hj
        refine ⟨j, fs, (List.getElem?_eq_some_iff.mp hj).1, ⟨?_, ?_⟩, rfl⟩
        · rw [BlockModel.rssT_of_mem hck, BlockModel.FssT_of_mem hck]
          exact (hfitZ ψ ρp c j cA hck hj Z fs).mp hfit
        · rw [BlockModel.IdsT_of_mem hck, BlockModel.EssT_of_mem hck]
          exact (htermZ ψ ρp c j cA hj hJ t fs).mp heqs
      · rintro ⟨j, fs, hjl, ⟨hfit, heqs⟩, rfl⟩
        have hj : ((D).ctorsM c)[j]? = some (((D).ctorsM c).getD j default) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
        obtain ⟨hJl, -, hmemJ, -⟩ := hctorA c j _ hck hj
        rw [BlockModel.rssT_of_mem hck, BlockModel.FssT_of_mem hck] at hfit
        rw [BlockModel.IdsT_of_mem hck, BlockModel.EssT_of_mem hck] at heqs
        exact ⟨j, fs, by rw [hlenF ψ]; exact hJl, by rw [mutMems_getD hJl]; exact hmemJ,
          (hfitZ ψ ρp c j _ hck hj Z fs).mpr hfit, (htermZ ψ ρp c j _ hj hJl t fs).mpr heqs, rfl⟩
    · -- a copy's row
      obtain ⟨q, rfl⟩ : ∃ q, c = p.k + q := ⟨c - p.k, by omega⟩
      have hq : q < pinsS.length := by
        have : p.k + q < p.k + pinsS.length := hc
        omega
      have hnk : ¬ p.k + q < (D).k := by
        show ¬ p.k + q < p.k
        omega
      have hsub : p.k + q - (D).k = q := by show p.k + q - p.k = q; omega
      rw [BlockModel.ctorsT_of_pin hnk, BlockModel.injT_of_pin hnk, hsub, hPC]
      constructor
      · rintro ⟨j, fs, hJ, hmemJ, hfit, heqs, rfl⟩
        refine ⟨j, fs, ?_, (hchainP ψ ρp q hq Z t j fs).mp ⟨hfit, heqs⟩, rfl⟩
        have hcnt := (ownCtors_grp h3 hlenA ψ (mm := p.k + q)
          (nC := (b.ownCtors (p.k + q)).length) rfl j).mp ⟨hJ, hmemJ⟩
        simpa [nestedPc] using hcnt
      · rintro ⟨j, fs, hjl, hcf, rfl⟩
        obtain ⟨hfit, heqs⟩ := (hchainP ψ ρp q hq Z t j fs).mpr hcf
        have hjl' : j < (b.ownCtors (p.k + q)).length := by simpa [nestedPc] using hjl
        obtain ⟨hJ, hmemJ⟩ := (ownCtors_grp h3 hlenA ψ (mm := p.k + q)
          (nC := (b.ownCtors (p.k + q)).length) rfl j).mpr hjl'
        exact ⟨j, fs, hJ, hmemJ, hfit, heqs, rfl⟩
  -- the per-member facts
  have hrep : IsBlockModelsAt mp₂.base2 (D) (fun mm => (fms.getD mm default).cvTa) := by
    intro mm hmm
    have hmmF : mm < fms.length := Nat.lt_of_lt_of_le hmm hkle
    have hft := fms_get hmmF
    have hlpsT : (fms.getD mm default).cvTa.levelParams = b.lps := h.lps _ _ hft
    refine ⟨default, (D).nP + (D).k + (D).nCtors + (D).nIdxAt mm,
      (D).nP + (D).k + (D).nCtors, [], ?_⟩
    refine
      { memberLt := hmm, member := rfl, strip := ?_, isProp := rfl, mI := rfl, rP := rfl
        rules := fun hne => absurd rfl hne, former := ?_, ctors := ?_, memsFound := ?_
        pinsFound := ?_, tgtsLt := ?_, idxRes := ?_, uParams := ?_, paramsIff := ?_, idxOk := ?_
        functor := ?_
        fibre := (D).fibre_of_auxFibre (fun ψ ρp => ofNested_auxCompose ψ ρp)
          (fun ψ ρp X q _ => ofNested_auxPinsCar ψ ρp X q) htgtsLtM hfibZ
        pinShape := hpinShape, pinMem := ?_, pinMono := ?_
        auxFunctor := fun ψ ρp hρp => ofNested_auxFunctor (hOk ψ ρp hρp)
        auxCompose := fun ψ ρp => ofNested_auxCompose ψ ρp
        auxPinsCar := fun ψ ρp X q _ => ofNested_auxPinsCar ψ ρp X q
        auxPinIdx := fun q hq ψ ρp => (hPinIdx q hq ψ ρp).symm
        auxFibre := hfibZ
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

/-- A read spine transfers along a per-term reading transfer (the loop's
`hde`: a reading at the prefix model is one at the restored model). -/
theorem DenoteMetaSpine.transfer {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {dp : Nat}
    (hde : ∀ (e : Expr) {ea : AnnotTerm}, denoteMeta acval₁ env₁ φ dp e = some ea →
      denoteMeta acval₂ env₂ φ dp e = some ea) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval₁ env₁ φ dp as vs →
      DenoteMetaSpine acval₂ env₂ φ dp as vs
  | _, _, .nil => .nil
  | _, _, .cons ha hrest => .cons (hde _ ha) (DenoteMetaSpine.transfer hde hrest)

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
  /-- **a pin's parameter count is the one `containerInfo?` reads of
  its container**, at the PRE-BLOCK environment (task #315 M7-3
  session 11, DESIGN §U.67 (c) 5): the pins' own record's
  (`NestedPinFacts.pinNP`, off the group's `pinNP` and `modeled`),
  carried across the `NestedCtorsStaged` boundary because
  `ContainerModeled.pinNP` — a clause of the nested block's OWN
  read-back — demands it at `d.env₀ = env`, and nothing below the
  boundary can recover it. -/
  pinNP : ∀ q, q < pinsS.length → ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env ((D).pinAt q).J = some ci → ((D).pinAt q).nPJ = ci.nP
  /-- the pins' components read at the block's parameter depth, at the
  restored model (task #315 M7-2: the recursors' readings' walk needs
  the components' syntactic form `DsE` tied to their readings `Ds`) -/
  pinDs : ∀ q, q < pinsS.length → ∀ ψ : Name → Nat,
    DenoteMetaSpine mp₂.base2.acval ENV₂ ψ b.nP (pinsS.getD q default).DsE
      ((pinsS.getD q default).Ds ψ)
  /-- **the pins' components are GRADED at the block's parameter frame**
  (task #315 M7-2): `nestedPinsOk`'s own `inferType` runs at the
  block's PARAMETER context, which is the guard a grading needs; the
  nested rule's pin conjunct spends the clause at the recursor's
  padded frame -/
  pinWd : ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V ((D).params ψ).reverse ρ →
    ∀ A ∈ (pinsS.getD q default).Ds ψ, WellDenotedV V ρ A
  /-- the restored environment extends the prefix environment (M7-2) -/
  find : FindPreserved ENV₁ ENV₂
  /-- the pins' level assignment is the container's level parameters
  instantiated at the pin's levels (task #315 M7-2: the constructor
  pins' readings at the restored model need it) -/
  pinψ : ∀ q, q < pinsS.length → ∀ (cvT : ConstantVal) (caps : IndCaps),
    (ENV₁).find? (pinsS.getD q default).J = some (.indInfo cvT caps) →
    (pinsS.getD q default).lvls.length = cvT.levelParams.length ∧
    ∀ ψ : Name → Nat, (pinsS.getD q default).ψJ ψ
      = Level.substFn ψ cvT.levelParams (pinsS.getD q default).lvls
  /-- the copy's index count is the pin's (task #315 M7-2: the model's
  arity function at a restore key, `nestedArityK`) -/
  pinNIdx : ∀ q, q < pinsS.length →
    (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx
  names : (fms.take p.k).map (·.cvTa.name) = p.memberNames
  agree : ∀ n, n ∉ p.memberNames ++ p.ctors.map (·.cv.name) →
    ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ
  /-- the agreement off the RESTORED constructors' names and the
  block's own members' (task #315 M7-2: the restore walk's leaf clause
  classifies a name by the AUXILIARY block's lists, which the
  declaration's own `memberNames`/`ctors` need not cover) -/
  agreeR : ∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
    (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
    mp₂.base2.acval n = mp.base2.acval n
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
  /-- **A NESTED FINITARY FIELD'S PARAMETER ARGUMENTS ARE THE RESTORED
  PIN'S** (task #315 PINF): carried from `NestedCtorRead.pinArgs`,
  because `BlockOpened.nestF` drops the parameter part of a nested
  field's spine and `ContainerModeled.nestArgsMention` needs it.  The
  mention step itself is the consumer's (`nestedContainerModeled`): it
  needs K.30 and K.44, which live above this tier. -/
  pinArgs : ∀ (mm j l : Nat) (x pin : Expr) (q : Nat), mm < p.k →
    j < (ctorsR.getD mm []).length → ((D).xFvsF mm j)[l]? = some x →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    x.fvarTypeD.getAppArgs.take ((D).pinAt q).nPJ
      = (Expr.instSeq ((D).fvsPF mm j) ((D).nP - 1)
          (Expr.abstractRange pin 0 p.nP 0)).getAppArgs
  /-- **AND THE SAME ON THE ABSTRACT DOMAIN** (task #315 PINF):
  carried beside `pinArgs` because the transport between the two sides
  runs only abstract ⟹ opened, and K.60's guard reads the abstract
  one.  At SPINE strength (task #315 WIDE (1′)): the whole domain as
  the pin lifted by the DEFINITE `l`, applied to a remainder, with the
  pin's own argument count beside it — the `getAppArgs.take` form the
  mention consumer reads is one `List.take_left'` away, and the wide
  identification's consumer, an equation under `instantiateList … l`,
  needs the definite depth. -/
  pinArgsAbs : ∀ (mm j l : Nat) (c : ConstantVal × Nat × Nat)
      (bs : List (Expr × BinderMeta)) (r : Expr) (dom : Expr × BinderMeta)
      (pin : Expr) (q : Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0).getAppArgs.length
          = ((D).pinAt q).nPJ ∧
      dom.1 = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0) rest
  /-- **AND THE SAME AT A REFLEXIVE NESTED FIELD** (task #315 K.63):
  carried beside `pinArgsAbs` because K.63's guard reads the stored
  domain's `Π`-BODY, where K.60's claims nothing by construction.  At
  `pinArgsAbs`' strength, with the pin lifted past both towers. -/
  pinArgsAbsRefl : ∀ (mm j l : Nat) (c : ConstantVal × Nat × Nat)
      (bs : List (Expr × BinderMeta)) (r : Expr) (dom : Expr × BinderMeta)
      (pin : Expr) (q : Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .reflexive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
          (l + ConLeche.domPiDepth dom.1) 0).getAppArgs.length = ((D).pinAt q).nPJ ∧
      ConLeche.stripDomPis dom.1
        = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
            (l + ConLeche.domPiDepth dom.1) 0) rest
  /-- **THE RESTORED CONSTRUCTOR'S STORED TYPE HAS ITS `.proj` SLOTS AT
  THE MEMBERS' PREFIX ENVIRONMENT** (task #315 PINF): the front door's
  own `slots`, kept because it is the only place the fact is TRUE.
  `ProjSlotsOk` is not antitone in the environment — its `.proj` node is
  a `findProj?` `.isSome` — so `ConstWF` at a later environment cannot
  supply it, and at ENV₁ the block's members are `.indInfo` with no
  projection table, which is what makes it say
  "no `.proj` node names a member".

  Carried raw rather than as the `NoProjAt` the consumer wants:
  turning the empty slot into a `NoProjAt` needs `ProjOkT` at the
  pre-block environment and the members' freshness, and those meet the
  clause at `nestedContainerModeled`. -/
  ctorSlots : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c → ConLeche.Expr.ProjSlotsOk ENV₁ c.1.type
  groups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
    q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ dJ
  /-- **the groups with their block model NAMED by the environment
  model's own assignment** (task #315 M7-3 session 12): `groups` keyed
  by the reading `containerInfo?` makes of the pin's container at the
  PRE-BLOCK environment, which is where the core has it
  (`NestedPinFacts.groupsAt`).  `NestedTailOut.groups` ASSUMED this
  form until now; `declNested_of` reads it here instead, and carries
  it to the output environment's reading through
  `NestedTailOut.conts`. -/
  groupsAt : ∀ q, q < pinsS.length → ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env ((D).pinAt q).J = some ci →
    ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ (blockOf mp.base2 ci)

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
  /-- **a pin's parameter count is the one `containerInfo?` reads of
  its container**, at the PRE-BLOCK environment (task #315 M7-3
  session 11, DESIGN §U.67 (c) 5): the pins' own record's
  (`NestedPinFacts.pinNP`, off the group's `pinNP` and `modeled`),
  carried across the `NestedCtorsStaged` boundary because
  `ContainerModeled.pinNP` — a clause of the nested block's OWN
  read-back — demands it at `d.env₀ = env`, and nothing below the
  boundary can recover it. -/
  pinNP : ∀ q, q < pinsS.length → ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env ((D).pinAt q).J = some ci → ((D).pinAt q).nPJ = ci.nP
  /-- the pins' components read at the restored model (M7-2) -/
  pinDs : ∀ q, q < pinsS.length → ∀ ψ : Name → Nat,
    DenoteMetaSpine mp₂.base2.acval ENV₂ ψ b.nP (pinsS.getD q default).DsE
      ((pinsS.getD q default).Ds ψ)
  /-- **the pins' components are GRADED at the block's parameter frame**
  (task #315 M7-2): `nestedPinsOk`'s own `inferType` runs at the
  block's PARAMETER context, which is the guard a grading needs; the
  nested rule's pin conjunct spends the clause at the recursor's
  padded frame -/
  pinWd : ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V ((D).params ψ).reverse ρ →
    ∀ A ∈ (pinsS.getD q default).Ds ψ, WellDenotedV V ρ A
  find : FindPreserved ENV₁ ENV₂
  /-- the pins' level assignment is the container's level parameters
  instantiated at the pin's levels (task #315 M7-2: the constructor
  pins' readings at the restored model need it) -/
  pinψ : ∀ q, q < pinsS.length → ∀ (cvT : ConstantVal) (caps : IndCaps),
    (ENV₁).find? (pinsS.getD q default).J = some (.indInfo cvT caps) →
    (pinsS.getD q default).lvls.length = cvT.levelParams.length ∧
    ∀ ψ : Name → Nat, (pinsS.getD q default).ψJ ψ
      = Level.substFn ψ cvT.levelParams (pinsS.getD q default).lvls
  /-- the copy's index count is the pin's (task #315 M7-2: the model's
  arity function at a restore key, `nestedArityK`) -/
  pinNIdx : ∀ q, q < pinsS.length →
    (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx
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
  /-- **A NESTED FINITARY FIELD'S PARAMETER ARGUMENTS ARE THE RESTORED
  PIN'S** (task #315 PINF): carried from `NestedCtorRead.pinArgs`,
  because `BlockOpened.nestF` drops the parameter part of a nested
  field's spine and `ContainerModeled.nestArgsMention` needs it.  The
  mention step itself is the consumer's (`nestedContainerModeled`): it
  needs K.30 and K.44, which live above this tier. -/
  pinArgs : ∀ (mm j l : Nat) (x pin : Expr) (q : Nat), mm < p.k →
    j < (ctorsR.getD mm []).length → ((D).xFvsF mm j)[l]? = some x →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    x.fvarTypeD.getAppArgs.take ((D).pinAt q).nPJ
      = (Expr.instSeq ((D).fvsPF mm j) ((D).nP - 1)
          (Expr.abstractRange pin 0 p.nP 0)).getAppArgs
  /-- **AND THE SAME ON THE ABSTRACT DOMAIN** (task #315 PINF):
  carried beside `pinArgs` because the transport between the two sides
  runs only abstract ⟹ opened, and K.60's guard reads the abstract
  one.  At SPINE strength (task #315 WIDE (1′)): the whole domain as
  the pin lifted by the DEFINITE `l`, applied to a remainder, with the
  pin's own argument count beside it — the `getAppArgs.take` form the
  mention consumer reads is one `List.take_left'` away, and the wide
  identification's consumer, an equation under `instantiateList … l`,
  needs the definite depth. -/
  pinArgsAbs : ∀ (mm j l : Nat) (c : ConstantVal × Nat × Nat)
      (bs : List (Expr × BinderMeta)) (r : Expr) (dom : Expr × BinderMeta)
      (pin : Expr) (q : Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .recursive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0).getAppArgs.length
          = ((D).pinAt q).nPJ ∧
      dom.1 = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars l 0) rest
  /-- **AND THE SAME AT A REFLEXIVE NESTED FIELD** (task #315 K.63):
  carried beside `pinArgsAbs` because K.63's guard reads the stored
  domain's `Π`-BODY, where K.60's claims nothing by construction.  At
  `pinArgsAbs`' strength, with the pin lifted past both towers. -/
  pinArgsAbsRefl : ∀ (mm j l : Nat) (c : ConstantVal × Nat × Nat)
      (bs : List (Expr × BinderMeta)) (r : Expr) (dom : Expr × BinderMeta)
      (pin : Expr) (q : Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c →
    c.1.type.stripPis ((D).nP + c.2.2) = some (bs, r) →
    bs[(D).nP + l]? = some dom →
    pin = Expr.mkAppN (.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE →
    (D).nestOf mm j l = some q →
    ((D).ksF mm j).getD l .ordinary = .reflexive →
    ∃ rest : List Expr,
      ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
          (l + ConLeche.domPiDepth dom.1) 0).getAppArgs.length = ((D).pinAt q).nPJ ∧
      ConLeche.stripDomPis dom.1
        = Expr.mkAppN ((Expr.abstractRange pin 0 p.nP 0).liftLooseBVars
            (l + ConLeche.domPiDepth dom.1) 0) rest
  /-- **THE RESTORED CONSTRUCTOR'S STORED TYPE HAS ITS `.proj` SLOTS AT
  THE MEMBERS' PREFIX ENVIRONMENT** (task #315 PINF): the front door's
  own `slots`, kept because it is the only place the fact is TRUE.
  `ProjSlotsOk` is not antitone in the environment — its `.proj` node is
  a `findProj?` `.isSome` — so `ConstWF` at a later environment cannot
  supply it, and at ENV₁ the block's members are `.indInfo` with no
  projection table, which is what makes it say
  "no `.proj` node names a member".

  Carried raw rather than as the `NoProjAt` the consumer wants:
  turning the empty slot into a `NoProjAt` needs `ProjOkT` at the
  pre-block environment and the members' freshness, and those meet the
  clause at `nestedContainerModeled`. -/
  ctorSlots : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
    (ctorsR.getD mm [])[j]? = some c → ConLeche.Expr.ProjSlotsOk ENV₁ c.1.type
  groups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
    q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ dJ
  /-- **the groups with their block model NAMED by the environment
  model's own assignment** (task #315 M7-3 session 12): `groups` keyed
  by the reading `containerInfo?` makes of the pin's container at the
  PRE-BLOCK environment, which is where the core has it
  (`NestedPinFacts.groupsAt`).  `NestedTailOut.groups` ASSUMED this
  form until now; `declNested_of` reads it here instead, and carries
  it to the output environment's reading through
  `NestedTailOut.conts`. -/
  groupsAt : ∀ q, q < pinsS.length → ∀ ci : ConLeche.ContainerInfo,
    ConLeche.containerInfo? env ((D).pinAt q).J = some ci →
    ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ (blockOf mp.base2 ci)

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
    -- **THE COPIES' TARGETS** (K.32, task #315 L-E, DESIGN §U.64): a
    -- copy's group-internal recursive field points at the copy of the
    -- container member its own field points at, which the copies'
    -- identities read on the `ordF` arm (lane L-B's `NestedPinsShape`)
    ConLeche.nestedCopyTargetsOk env p b st stored = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    ConLeche.nestedPinRankOk env p b st stored = true →
    -- **THE POSITIVITY NORMALISATION ON THE MINTED COPY** (K.42, task
    -- #315, lane L-B): at every ORDINARY field of every copy's
    -- constructor, the stored domain IS the positivity normalisation of
    -- the MINTED one, which the copies' identities read on the
    -- `ordF`-LEFT arm (lane L-B's `NestedPinsShape`)
    (∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2)) →
    -- **THE SAME WALK AT A PIN TARGET, REWRITTEN** (K.51, task #315,
    -- lane L-B): a copy field whose target is a MIMIC has a stored
    -- domain headed by that mimic, so the normalisation of the MINTED
    -- domain is rewritten before the comparison — which lets the
    -- `ordF`-RIGHT arm read a pin target off the minted domain with no
    -- `pinLeaf` anywhere (lane L-B's `NestedPinsShape`)
    (∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
      (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored
          (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true) →
    -- K.60: a container's nested field lands on a block pin
    ConLeche.nestedCopyPinFieldsOk env p b st stored = true →
    -- K.63: the same, one `Π`-tower down — a container's REFLEXIVE
    -- nested field lands on a block pin, where K.60's guard (a `.const`
    -- head on the stored domain) claims nothing
    ConLeche.nestedCopyReflFieldsOk env p b st stored = true →
    -- K.61: the container instance map — a pin's container's own pins,
    -- instantiated at that pin's levels and components, ARE pins of the
    -- block, and a copy's field sitting at one of those own pins records
    -- the map's value as its target (the wide identification's σ)
    ConLeche.nestedInstMapOk env p b st stored = true →
    -- K.62: a rewritten ORDINARY field's target is OUTSIDE that map's
    -- image (the wide identification's `houtσ`)
    ConLeche.nestedOrdOutsideOk env p b st stored = true →
    -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the prefix
    -- formers' environment (`consNestedFormers_take_eq`)
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok () →
    -- **THE PINS' CONSTANTS RESOLVE** (K.64): at that same environment
    -- — the guard a container's pins' components' READINGS need to
    -- cross a later install's projection table
    ConLeche.pinsResolve (ConLeche.consMutualFormers (fms.take p.k) env) st.pins = true →
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
      NestedLoopFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
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
    (hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true)
    (hkinds : ConLeche.nestedPinKindsOk p b st stored = true)
    (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    (hK42 : ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2))
    (hK51 : ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
      (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored
          (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true)
    (hK60 : ConLeche.nestedCopyPinFieldsOk env p b st stored = true)
    (hK63 : ConLeche.nestedCopyReflFieldsOk env p b st stored = true)
    (hK61 : ConLeche.nestedInstMapOk env p b st stored = true)
    (hK62 : ConLeche.nestedOrdOutsideOk env p b st stored = true)
    (hpins₁ : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok ())
    (hK64 : ConLeche.pinsResolve (ConLeche.consMutualFormers (fms.take p.k) env) st.pins = true)
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
    hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32
    hkinds hrank hK42 hK51 hK60 hK63 hK61 hK62 hpins₁ hK64 hformers h hbk h3 hnd hctorsA hleafM'
    hoff' hfind' hctors
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
    { pinsLen := L.pinsLen, pinRec := L.pinRec, pinDs := L.pinDs, pinWd := L.pinWd
      pinNP := L.pinNP
      find := L.find, pinψ := L.pinψ
      pinNIdx := L.pinNIdx
      names := hnames, agree := ?_
      agreeR := fun n hnC hnM => (L.agreeC n hnC).trans (hoff' n hnM)
      findM := fun t f ht hft => L.find (hfind' t f ht hft).1
      leafM := fun t f ht hft => (L.leafKeep t f ht hft).trans (hleafM' t f ht hft)
      FD := fun t f ht hft => FormerData.crossEnv' L.hde (hfind' t f ht hft).2
      ctorsLen := hctorsLen, ctorFacts := L.ctorFacts, domFacts := L.domFacts
      pinArgs := L.pinArgs, pinArgsAbs := L.pinArgsAbs, pinArgsAbsRefl := L.pinArgsAbsRefl
      ctorSlots := L.ctorSlots
      groups := L.groups, groupsAt := L.groupsAt }⟩
  intro n hn ψ
  have hnM : n ∉ p.memberNames := fun hm => hn (List.mem_append_left _ hm)
  have hnC : n ∉ p.ctors.map (·.cv.name) := fun hc => hn (List.mem_append_right _ hc)
  rw [L.agreeC n (fun c hc heq => hnC (heq ▸ hnameR c hc)),
    hoff' n (fun t f ht hft heq => hnM (by
      rw [← hnames, heq]
      exact List.mem_map_of_mem (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt ht]; exact hft))))]

end Stage

end ConLeche.Model
