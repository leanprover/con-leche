module

public import ConLeche.Model.Inductives.NestedPinLaws
public section

/-!
# The block's pins as a stored block's pins, and the global entry theorem (task #315, L-E)

Two things live here, both stated at the nested run's block model
`nestedBlockModel` with its pins' constructors `nestedPc`
(`NestedPinLaws.lean`):

* **the pins' SHAPES of the block being installed** — `PinShapes`
  (`NestedPremise.lean`) at an assignment `B` whose value at every pin
  group's container is the group's block model (`nestedPinShapes_of`),
  from the groups carrying the per-group shapes (`NestedPinGroup.shape`,
  lane L-B's `NestedPinsShape`); with M7-1's `PinRecLaws`
  (`nestedPinRecLaws_of`) and the block's own `ContainerModeled` (K.34's
  read-back, the tail's) this is the block's `BlockAt` at the output
  model (`nestedBlockAt_of`) — what `EnvModelB.blocks` asks of the
  nested route (DESIGN §U.36);
* **the global entry theorem** `nestedPinLeaf_all` (DESIGN §U.36): the
  entries `CopyEntryA` at the auxiliary carrier for EVERY group at once,
  from the shapes of the block's pins and the containers' `BlockAt` —
  the residual `NestedPinsEntry` names.  Its plan: `P q` := pin `q`'s
  container's least tuple at the pin's frame; (i) `P` is a fixed point
  of the pins' section of the auxiliary operator at the carrier's
  members, from the shapes with the entries read at `P`
  (`copyEntryAt_of_read` at the containers' `leaf`); (ii) `L⁺`'s pin
  segment lies below `P` (`lfpTuple_le` at the section); (iii) `P` lies
  below the segment by induction on the pin's expression, a self-nested
  container's cycle closed by its own `PinRecLaws.ind` at the segment;
  (iv) `P q = L⁺ (k + q)` is every `pinLeaf` and every entry.
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

/-- **The block model's target view IS the auxiliary lists'**: every
field by construction except the index universes, which agree by
`ofNested_uT`. -/
theorem nestedBlockModel_targetView (m : EnvModel V env₂) (ψ : Name → Nat) :
    (D).targetView m.acval ψ
      = nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS m.acval (D).memberNames ψ := by
  unfold BlockModel.targetView nestedTV
  congr 1
  funext t
  exact ofNested_uT t ψ

/-- **The pins' shapes of the block being installed**, at an assignment
`B` whose value at every pin's container's group is the group's block
model (`hgroupsB`: the groups, with their model NAMED by `B`): pin `q`'s
constructors `nestedPc` have `CopyCtorShape` against `B ci` — the
group's `shape` field (lane L-B's `NestedPinsShape`) read at the
group's base pin through `same`, the auxiliary lists' positions
against the dropped ones (`getD_drop`), and the target view's
identity. -/
theorem nestedPinShapes_of (m : EnvModel V env₂) {B : ContainerInfo → BlockModel V}
    (hgroupsB : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci →
      ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ (B ci))
    (hcont : ∀ q, q < pinsS.length →
      ∃ ci : ContainerInfo, ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci) :
    PinShapes m B (D) PC := by
  intro q hq
  obtain ⟨ci, hci⟩ := hcont q hq
  obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := hgroupsB q hq ci hci
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci, ?_, ?_⟩
  · -- the group, viewed
    have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
    refine ⟨G.seg, G.kpos, G.kEq, fun i' hi' => ?_, G.same, fun i' hi' ψ => ?_, G.pinNP,
      G.pinNIdx, G.pinPps, fun ψ => ?_, fun ψ => ?_, fun ψ ρ as hsp => ?_⟩
    · obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i' hi'
      exact hI.member.symm
    · have := G.pinU 0 G.kpos ψ i' hi'
      rwa [h0] at this
    · have := G.pinDsLen 0 G.kpos ψ
      rwa [h0] at this
    · have := G.w 0 G.kpos ψ
      rwa [h0] at this
    · have := G.DsFit 0 G.kpos ψ ρ as hsp
      rwa [h0] at this
  · -- the shape, at the base pin's record and the dropped lists
    intro ψ ρp hρp i' j hi' hj
    have hsh := G.shape 0 G.kpos ψ ρp hρp i' hi' j hj
    rw [Nat.add_zero] at hsh
    unfold CopyShapeA at hsh
    rw [nestedBlockModel_targetView m ψ]
    simp only [nestedPc, getD_drop, ← Nat.add_assoc]
    exact hsh

/-- **The block's obligation at the output model**: its own
`ContainerModeled` (K.34's read-back, the tail's), M7-1's `PinRecLaws`
and the shapes above, at an assignment carrying the block at its
group. -/
theorem nestedBlockAt_of (m : EnvModel V env₂) {B : ContainerInfo → BlockModel V}
    {ci : ContainerInfo} (hB : B ci = D) (C : ContainerModeled m ci (D))
    (hL : PinRecLaws m (D) PC) (hS : PinShapes m B (D) PC) : BlockAt m B ci := by
  rw [BlockAt, hB]
  exact ⟨C, PC, hL, hS⟩

end Assembly

end ConLeche.Model
