module

public import ConLeche.SetTheory.Derive.LfpTuple
import ConLeche.SetTheory.Derive.Graphs
@[expose] public section

/-!
# The composed operator of a nested block, and Bekić at segments (task #315, M6)

A NESTED block (`Tree ::= node (List Tree)`) is modelled by the
uniform block model with its `k` members' tuple operator `Φ` and its
`n` pins' carriers `pinCar` DEFINED from the AUXILIARY tuple operator
`Ψ` on `k + n` components — the members followed by one copy per pin,
the operator the elimination's readings denote (`tupleLfpΦ` at the
extended lists; no auxiliary block is installed or modelled).  This
module is the pure half: given `Ψ` monotone and space-preserving with
a closed tuple on `k + n` components,

* the **pins' carriers at a members' tuple `X`** are the least
  pre-fixed tuple of the pins' SECTION of `Ψ` at `X` — all pins solved
  simultaneously (`pinsCar`); a pin's own carrier is then the least
  pre-fixed family of ITS section at the other pins' carriers by the
  segment form of Bekić below (`lfpTuple_seg`), which is how the
  assembly identifies a pin's carrier with the container's;
* the **composed operator** reads `Ψ` at the members' tuple extended
  by the pins' carriers (`composeΦ`, `extT`);
* it is monotone, space-preserving and has a closed tuple
  (`composeΦ_mono/_maps/_closed_exists`), the pins' carriers are in
  the family space and monotone in the tuple (`pinsCar_mem/_mono`) —
  the block model's `functor`, `pinMem` and `pinMono` clauses;
* **the composed least pre-fixed tuple IS the auxiliary one**
  (`lfpTuple_composeΦ`, `pinsCar_lfp`): its members are `Ψ`'s least
  tuple's members and the pins' carriers at it are that tuple's pin
  components — Bekić in the nested form, which is what the `leaf` and
  `pinLeaf` clauses consume (the term-level leaf of a nested member is
  the `k + n`-ary former's component).

**The clamp.**  A pin's carrier at `X` is the pins' least tuple at
`X ⊓ L⁺`, the members' tuple met with the auxiliary carrier `L⁺ =
lfpTuple (k + n) Ψ` (`meetT`).  Monotonicity of `pinsCar` in `X` needs
a CLOSED tuple of the pins' section at the larger tuple, and `Ψ`'s one
closed tuple gives one only below `L⁺`; the meet makes every section
solved one below `L⁺`, where `L⁺`'s pin components close it.  Below
`L⁺` the clamp is the identity (`meetT_eq_of_le`), so at the carrier —
the only tuple any consumer reads a pin at — the pins' carriers are
the honest sections' least tuples; above it nothing observes them.
(The unclamped operator would need a closed tuple of the pins'
section at EVERY members' tuple: a container presentation of the
pins' components with the member-targeting fields as shape data,
inside the sealed former — available at that cost if a consumer ever
reads a pin above the carrier; none does.)

**Segments.**  `segJoin a s Z Y` is the tuple `Z` with the components
`a, …, a + s - 1` replaced by `Y 0, …, Y (s - 1)`; `segSec Ψ a s Z` is
`Ψ`'s section at that segment with the complement held at `Z`, an
operator on `s` components; `lfpTuple_seg` is Bekić for it — the
least tuple's segment is the least tuple of the segment's section at
the least tuple itself (`lfpTuple_eq_section` is the case `s = 1`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Segments of a tuple -/

/-- The tuple `Z` with the segment `[a, a + s)` replaced by `Y`,
re-indexed from `0`. -/
def segJoin (a s : Nat) (Z Y : Nat → V) : Nat → V :=
  fun j => if a ≤ j ∧ j < a + s then Y (j - a) else Z j

/-- The segment `[a, a + s)` of a tuple, re-indexed from `0`. -/
def segOf (a : Nat) (Z : Nat → V) : Nat → V := fun q => Z (a + q)

omit [SetTheory V] in
theorem segJoin_in {a s j : Nat} (Z Y : Nat → V) (h : a ≤ j ∧ j < a + s) :
    segJoin a s Z Y j = Y (j - a) := by
  simp [segJoin, h]

omit [SetTheory V] in
theorem segJoin_out {a s j : Nat} (Z Y : Nat → V) (h : ¬ (a ≤ j ∧ j < a + s)) :
    segJoin a s Z Y j = Z j := by
  simp [segJoin, h]

omit [SetTheory V] in
theorem segJoin_add {a s q : Nat} (Z Y : Nat → V) (hq : q < s) :
    segJoin a s Z Y (a + q) = Y q := by
  rw [segJoin_in Z Y ⟨Nat.le_add_right a q, by omega⟩, Nat.add_sub_cancel_left]

omit [SetTheory V] in
theorem segJoin_lt {a s j : Nat} (Z Y : Nat → V) (hj : j < a) :
    segJoin a s Z Y j = Z j :=
  segJoin_out Z Y fun h => by omega

omit [SetTheory V] in
theorem segOf_apply (a : Nat) (Z : Nat → V) (q : Nat) : segOf a Z q = Z (a + q) := rfl

omit [SetTheory V] in
/-- A tuple is the join of its complement and its segment. -/
theorem segJoin_segOf (a s : Nat) (Z : Nat → V) : segJoin a s Z (segOf a Z) = Z := by
  funext j
  by_cases h : a ≤ j ∧ j < a + s
  · rw [segJoin_in Z _ h, segOf_apply, Nat.add_sub_cancel' h.1]
  · exact segJoin_out Z _ h

section Segments

variable {w N a s : Nat} {Is : Nat → V}

omit [SetTheory V] in
/-- A position below `a + s` outside the segment is below `a`. -/
theorem lt_of_not_seg {a s j : Nat} (hj : j < a + s) (h : ¬ (a ≤ j ∧ j < a + s)) : j < a := by
  rcases Nat.lt_or_ge j a with h' | h'
  · exact h'
  · exact absurd ⟨h', hj⟩ h

/-- The join is in the tuple space when the complement is in it OFF the
segment (the segment positions of `Z` are never read). -/
theorem inTupleSpace_segJoin' {Z Y : Nat → V}
    (hZ : ∀ j, j < N → ¬ (a ≤ j ∧ j < a + s) → Z j ∈ˢ famSpace w (Is j))
    (hY : InTupleSpace w s (fun q => Is (a + q)) Y) : InTupleSpace w N Is (segJoin a s Z Y) := by
  intro j hj
  by_cases h : a ≤ j ∧ j < a + s
  · rw [segJoin_in Z Y h]
    have := hY (j - a) (by omega)
    simp only [Nat.add_sub_cancel' h.1] at this; exact this
  · rw [segJoin_out Z Y h]; exact hZ j hj h

theorem inTupleSpace_segJoin {Z Y : Nat → V} (hZ : InTupleSpace w N Is Z)
    (hY : InTupleSpace w s (fun q => Is (a + q)) Y) : InTupleSpace w N Is (segJoin a s Z Y) :=
  inTupleSpace_segJoin' (fun j hj _ => hZ j hj) hY

theorem inTupleSpace_segOf (hN : a + s ≤ N) {Z : Nat → V} (hZ : InTupleSpace w N Is Z) :
    InTupleSpace w s (fun q => Is (a + q)) (segOf a Z) :=
  fun q hq => hZ (a + q) (by omega)

theorem tupleLe_segJoin {Z Z' Y Y' : Nat → V} (hZ : TupleLe N Is Z Z')
    (hY : TupleLe s (fun q => Is (a + q)) Y Y') :
    TupleLe N Is (segJoin a s Z Y) (segJoin a s Z' Y') := by
  intro j hj
  by_cases h : a ≤ j ∧ j < a + s
  · rw [segJoin_in Z Y h, segJoin_in Z' Y' h]
    have := hY (j - a) (by omega)
    simp only [Nat.add_sub_cancel' h.1] at this; exact this
  · rw [segJoin_out Z Y h, segJoin_out Z' Y' h]; exact hZ j hj

theorem tupleLe_segOf (hN : a + s ≤ N) {Z Z' : Nat → V} (h : TupleLe N Is Z Z') :
    TupleLe s (fun q => Is (a + q)) (segOf a Z) (segOf a Z') :=
  fun q hq => h (a + q) (by omega)

/-- The join is below `Z` when its segment part is below `Z`'s
segment. -/
theorem tupleLe_segJoin_of_le {Z Y : Nat → V} (hY : TupleLe s (fun q => Is (a + q)) Y (segOf a Z)) :
    TupleLe N Is (segJoin a s Z Y) Z := by
  have := tupleLe_segJoin (N := N) (TupleLe.refl N Is Z) hY
  rwa [segJoin_segOf] at this

/-- `Z` is below the join when `Z`'s segment is below the segment part. -/
theorem tupleLe_of_segJoin_le {Z Y : Nat → V} (hY : TupleLe s (fun q => Is (a + q)) (segOf a Z) Y) :
    TupleLe N Is Z (segJoin a s Z Y) := by
  have := tupleLe_segJoin (N := N) (TupleLe.refl N Is Z) hY
  rwa [segJoin_segOf] at this

end Segments

/-! ## The segment's section, and Bekić at a segment -/

/-- **The section of `Ψ` at the segment `[a, a + s)`** with the
complement held at `Z`: an operator on `s` components. -/
def segSec (Ψ : (Nat → V) → Nat → V) (a s : Nat) (Z : Nat → V) : (Nat → V) → Nat → V :=
  fun Y q => Ψ (segJoin a s Z Y) (a + q)

section SegSec

variable {w N a s : Nat} {Is : Nat → V} {Ψ : (Nat → V) → Nat → V}

omit [SetTheory V] in
theorem segSec_apply (Z Y : Nat → V) (q : Nat) : segSec Ψ a s Z Y q = Ψ (segJoin a s Z Y) (a + q) :=
  rfl

theorem segSec_mono (hmono : MonoTuple w N Is Ψ) (hN : a + s ≤ N) {Z : Nat → V}
    (hZ : InTupleSpace w N Is Z) : MonoTuple w s (fun q => Is (a + q)) (segSec Ψ a s Z) := by
  intro Y Y' hY hY' hle q hq
  exact hmono _ _ (inTupleSpace_segJoin hZ hY) (inTupleSpace_segJoin hZ hY')
    (tupleLe_segJoin (TupleLe.refl N Is Z) hle) (a + q) (by omega)

theorem segSec_maps (hmaps : MapsTuple w N Is Ψ) (hN : a + s ≤ N) {Z : Nat → V}
    (hZ : InTupleSpace w N Is Z) : MapsTuple w s (fun q => Is (a + q)) (segSec Ψ a s Z) :=
  fun Y hY q hq => hmaps _ (inTupleSpace_segJoin hZ hY) (a + q) (by omega)

/-- The section is monotone in its complement. -/
theorem segSec_le_of_le (hmono : MonoTuple w N Is Ψ) (hN : a + s ≤ N) {Z Z' : Nat → V}
    (hZ : InTupleSpace w N Is Z) (hZ' : InTupleSpace w N Is Z') (hle : TupleLe N Is Z Z')
    {Y : Nat → V} (hY : InTupleSpace w s (fun q => Is (a + q)) Y) :
    TupleLe s (fun q => Is (a + q)) (segSec Ψ a s Z Y) (segSec Ψ a s Z' Y) :=
  fun q hq => hmono _ _ (inTupleSpace_segJoin hZ hY) (inTupleSpace_segJoin hZ' hY)
    (tupleLe_segJoin hle (TupleLe.refl _ _ _)) (a + q) (by omega)

/-- A closed tuple's segment is a closed tuple of the segment's
section at it. -/
theorem isClosedTuple_segSec_of_closed (hN : a + s ≤ N) {L : Nat → V}
    (hL : IsClosedTuple w N Is Ψ L) :
    IsClosedTuple w s (fun q => Is (a + q)) (segSec Ψ a s L) (segOf a L) := by
  refine ⟨inTupleSpace_segOf hN hL.1, fun q hq => ?_⟩
  rw [segSec_apply, segJoin_segOf]
  exact hL.2 (a + q) (by omega)

/-- **Bekić at a segment.**  The least pre-fixed tuple's segment is the
least pre-fixed tuple of the segment's section at the least tuple
itself (`lfpTuple_eq_section` is the case `s = 1`). -/
theorem lfpTuple_seg (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ)
    (hN : a + s ≤ N) {q : Nat} (hq : q < s) :
    lfpTuple w N Is Ψ (a + q)
      = lfpTuple w s (fun q => Is (a + q)) (segSec Ψ a s (lfpTuple w N Is Ψ)) q := by
  have hLmem := lfpTuple_mem w N Is Ψ
  have hLcl := lfpTuple_isClosed h hmono
  have hsecCl : ∃ P, IsClosedTuple w s (fun q => Is (a + q)) (segSec Ψ a s (lfpTuple w N Is Ψ)) P :=
    ⟨_, isClosedTuple_segSec_of_closed hN hLcl⟩
  have hsecMono := segSec_mono hmono hN hLmem
  have hSmem := lfpTuple_mem w s (fun q => Is (a + q)) (segSec Ψ a s (lfpTuple w N Is Ψ))
  -- the section's least tuple is below the segment
  have hSle : TupleLe s (fun q => Is (a + q))
      (lfpTuple w s (fun q => Is (a + q)) (segSec Ψ a s (lfpTuple w N Is Ψ)))
      (segOf a (lfpTuple w N Is Ψ)) :=
    lfpTuple_le (isClosedTuple_segSec_of_closed hN hLcl)
  -- the join of the least tuple and the section's least tuple is closed
  have hU : IsClosedTuple w N Is Ψ
      (segJoin a s (lfpTuple w N Is Ψ)
        (lfpTuple w s (fun q => Is (a + q)) (segSec Ψ a s (lfpTuple w N Is Ψ)))) := by
    refine ⟨inTupleSpace_segJoin hLmem hSmem, fun j hj => ?_⟩
    by_cases hin : a ≤ j ∧ j < a + s
    · rw [segJoin_in _ _ hin]
      have := lfpTuple_closed hsecCl hsecMono (j - a) (by omega)
      simp only [segSec_apply, Nat.add_sub_cancel' hin.1] at this
      exact this
    · rw [segJoin_out _ _ hin]
      refine FamLe.trans ?_ (hLcl.2 j hj)
      exact hmono _ _ (inTupleSpace_segJoin hLmem hSmem) hLmem (tupleLe_segJoin_of_le hSle) j hj
  have hLle := lfpTuple_le hU (a + q) (by omega)
  rw [segJoin_add _ _ hq] at hLle
  exact famSpace_ext (hLmem (a + q) (by omega)) (hSmem q hq) fun i hi =>
    Subset.antisymm (hLle i hi) (hSle q hq i hi)

end SegSec

/-! ## Congruence: the least tuple reads its operator and index sets below `k` only -/

section Congr

variable {w k : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- Two presentations agreeing below `k` have the same closed tuples. -/
theorem isClosedTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {X : Nat → V} :
    IsClosedTuple w k Is Φ X ↔ IsClosedTuple w k Is' Φ' X := by
  have hsp : InTupleSpace w k Is X ↔ InTupleSpace w k Is' X := by
    constructor
    · intro h m hm; rw [← hIs m hm]; exact h m hm
    · intro h m hm; rw [hIs m hm]; exact h m hm
  constructor
  · rintro ⟨hX, hle⟩
    refine ⟨hsp.mp hX, fun m hm => ?_⟩
    rw [← hIs m hm, ← hΦ X hX m hm]; exact hle m hm
  · rintro ⟨hX, hle⟩
    have hX' := hsp.mpr hX
    refine ⟨hX', fun m hm => ?_⟩
    rw [hIs m hm, hΦ X hX' m hm]; exact hle m hm

/-- **The least tuple is a congruence** in the operator (on the tuple
space) and the index sets, below `k`. -/
theorem lfpTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpTuple w k Is' Φ' m := by
  have hcl : (∃ L, IsClosedTuple w k Is Φ L) ↔ ∃ L, IsClosedTuple w k Is' Φ' L :=
    ⟨fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mp hL⟩,
      fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mpr hL⟩⟩
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · have h' := hcl.mp h
    refine famSpace_ext (lfpTuple_mem w k Is Φ m hm) (by rw [hIs m hm]; exact lfpTuple_mem w k Is' Φ' m hm)
      fun i hi => ?_
    apply SetTheory.ext
    intro x
    rw [mem_app_lfpTuple h hi, mem_app_lfpTuple h' (by rw [← hIs m hm]; exact hi)]
    constructor
    · intro hx X hX; exact hx X ((isClosedTuple_congr hIs hΦ).mpr hX)
    · intro hx X hX; exact hx X ((isClosedTuple_congr hIs hΦ).mp hX)
  · rw [lfpTuple_of_not h, lfpTuple_of_not (fun h' => h (hcl.mpr h')), hIs m hm]

end Congr

/-- **Bekić at a segment, against another presentation of the
section**: when the segment's section at the least tuple agrees, on
the segment's tuple space, with an operator `Φ'` over index sets
`Is'` — a CONTAINER's own block operator at a pin, say — the least
tuple's segment is `Φ'`'s least tuple.  This is the theorem a pin's
`pinLeaf` instantiates: the copies' section reads as the container's
operator at the pin's components (the copy readings' congruence), and
the container's block model turns the least tuple into its stored
reading. -/
theorem lfpTuple_seg_congr {w N a s : Nat} {Is Is' : Nat → V} {Ψ Φ' : (Nat → V) → Nat → V}
    (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ) (hN : a + s ≤ N)
    (hIs : ∀ i, i < s → Is (a + i) = Is' i)
    (hΦ : ∀ Y, InTupleSpace w s (fun i => Is (a + i)) Y → ∀ i, i < s →
      Ψ (segJoin a s (lfpTuple w N Is Ψ) Y) (a + i) = Φ' Y i)
    {i : Nat} (hi : i < s) :
    lfpTuple w N Is Ψ (a + i) = lfpTuple w s Is' Φ' i := by
  rw [lfpTuple_seg h hmono hN hi]
  exact lfpTuple_congr hIs (fun Y hY i hi => hΦ Y hY i hi) hi

/-! ## Segments given by an INDEX SET -/

section IdxSet

variable {w N s : Nat} {Is : Nat → V} {σ : Nat → Nat} {Ψ : (Nat → V) → Nat → V}

open Classical in
/-- **The tuple `Z` with the positions `σ 0, …, σ (s-1)` replaced by
`Y 0, …, Y (s-1)`.**  `segJoin a s` is the case `σ = (a + ·)`
(`setJoin_ofAdd`); the general form is what a CONTAINER INSTANCE needs,
whose copies the block's worklist may interleave with another
instance's, so that they are not a contiguous range. -/
noncomputable def setJoin (σ : Nat → Nat) (s : Nat) (Z Y : Nat → V) : Nat → V :=
  fun j => if h : ∃ i, i < s ∧ σ i = j then Y (Classical.choose h) else Z j

/-- The positions `σ` picks out of a tuple, re-indexed from `0`
(`segOf a` is the case `σ = (a + ·)`). -/
def setPick (σ : Nat → Nat) (Z : Nat → V) : Nat → V := fun i => Z (σ i)

/-- `σ` is injective on `[0, s)`.  **Not what the replaced positions
need** — see `FibreConst` — but the special case every non-collapsing
instance is in, and what `setJoin_ofAdd` uses at `σ = (a + ·)`. -/
def InjOn (σ : Nat → Nat) (s : Nat) : Prop :=
  ∀ i i', i < s → i' < s → σ i = σ i' → i = i'

/-- **A tuple is CONSTANT ON `σ`'s FIBRES**: two positions of `[0, s)`
that `σ` sends to one carry the same family.

**This, and not `InjOn`, is what reading a joined position back
needs.**  `setJoin` puts `s` families at the positions `σ 0 … σ (s-1)`;
when `σ` collapses two of them the joined tuple has ONE slot where the
`s`-tuple has two, so `setJoin σ s Z Y (σ i) = Y i` is available for
exactly the tuples that do not tell those two apart.  Injectivity is
the brutal way to get that — it makes the hypothesis vacuous — and it
is stronger than the fixpoint theory needs, in the same way whole-space
agreement was stronger than the congruence needed.

The right reading is that a collapsing `σ` makes the compared space a
QUOTIENT of the `s`-tuple space, and the least tuple lives on the
quotient: `setSec`'s value at a position depends on `i` only through
`σ i` (`fibreConst_setSec`), so its least tuple is fibre-constant by
its own fixpoint law (`fibreConst_lfpTuple`) whatever the tuples around
it do.  Nothing has to be assumed of `σ` at all; what has to be known
of the OTHER presentation is that it too factors through the quotient
(`fibreConst_lfpTuple`'s `hfc`), and `fcNorm` is the projection. -/
def FibreConst (σ : Nat → Nat) (s : Nat) (Y : Nat → V) : Prop :=
  ∀ i i', i < s → i' < s → σ i = σ i' → Y i = Y i'

omit [SetTheory V] in
theorem FibreConst.of_injOn (hinj : InjOn σ s) (Y : Nat → V) : FibreConst σ s Y :=
  fun i i' hi hi' he => by rw [hinj i i' hi hi' he]

open Classical in
/-- `σ`'s chosen representative of the fibre OVER A POSITION `j` — the
witness `setJoin` itself reads there. -/
noncomputable def fcRepAt (σ : Nat → Nat) (s : Nat) (j : Nat) : Nat :=
  if h : ∃ i, i < s ∧ σ i = j then Classical.choose h else j

/-- `σ`'s chosen representative of `i`'s own fibre: `fcRepAt` at `σ i`,
so that two positions `σ` identifies get the SAME representative by
`rfl` under the identification. -/
noncomputable def fcRep (σ : Nat → Nat) (s : Nat) (i : Nat) : Nat := fcRepAt σ s (σ i)

omit [SetTheory V] in
theorem fcRep_lt {i : Nat} (hi : i < s) : fcRep σ s i < s := by
  have h : ∃ i', i' < s ∧ σ i' = σ i := ⟨i, hi, rfl⟩
  show (if h : ∃ i', i' < s ∧ σ i' = σ i then Classical.choose h else σ i) < s
  rw [dif_pos h]; exact (Classical.choose_spec h).1

omit [SetTheory V] in
theorem fcRep_eq {i : Nat} (hi : i < s) : σ (fcRep σ s i) = σ i := by
  have h : ∃ i', i' < s ∧ σ i' = σ i := ⟨i, hi, rfl⟩
  show σ (if h : ∃ i', i' < s ∧ σ i' = σ i then Classical.choose h else σ i) = σ i
  rw [dif_pos h]; exact (Classical.choose_spec h).2

/-- **The projection onto the fibre quotient**: `Y` with every position
replaced by its fibre's representative.  It is what the join actually
reads (`setJoin_at_norm`), it is fibre-constant (`fibreConst_fcNorm`),
and it is the identity on fibre-constant tuples
(`fcNorm_of_fibreConst`). -/
noncomputable def fcNorm (σ : Nat → Nat) (s : Nat) (Y : Nat → V) : Nat → V :=
  fun i => Y (fcRep σ s i)

omit [SetTheory V] in
theorem fcNorm_apply (Y : Nat → V) (i : Nat) : fcNorm σ s Y i = Y (fcRep σ s i) := rfl

omit [SetTheory V] in
theorem setJoin_out (Z Y : Nat → V) {j : Nat} (h : ¬ ∃ i, i < s ∧ σ i = j) :
    setJoin σ s Z Y j = Z j := dif_neg h

omit [SetTheory V] in
/-- **What the join reads at a replaced position**: the fibre's
representative, unconditionally.  `setJoin_at` is this at a tuple that
cannot tell the fibre apart. -/
theorem setJoin_at_norm (Z Y : Nat → V) {i : Nat} (hi : i < s) :
    setJoin σ s Z Y (σ i) = fcNorm σ s Y i := by
  have h : ∃ i', i' < s ∧ σ i' = σ i := ⟨i, hi, rfl⟩
  show (if h : ∃ i', i' < s ∧ σ i' = σ i then Y (Classical.choose h) else Z (σ i))
      = Y (if h : ∃ i', i' < s ∧ σ i' = σ i then Classical.choose h else σ i)
  rw [dif_pos h, dif_pos h]

omit [SetTheory V] in
theorem fibreConst_fcNorm (Y : Nat → V) : FibreConst σ s (fcNorm σ s Y) := by
  intro i i' _ _ he
  show Y (fcRepAt σ s (σ i)) = Y (fcRepAt σ s (σ i'))
  rw [he]

omit [SetTheory V] in
theorem fcNorm_of_fibreConst {Y : Nat → V} (hfc : FibreConst σ s Y) {i : Nat} (hi : i < s) :
    fcNorm σ s Y i = Y i :=
  hfc _ _ (fcRep_lt hi) hi (fcRep_eq hi)

omit [SetTheory V] in
theorem setJoin_at_fc {Y : Nat → V} (hfc : FibreConst σ s Y) (Z : Nat → V) {i : Nat}
    (hi : i < s) : setJoin σ s Z Y (σ i) = Y i :=
  (setJoin_at_norm Z Y hi).trans (fcNorm_of_fibreConst hfc hi)

omit [SetTheory V] in
theorem setJoin_at (hinj : InjOn σ s) (Z Y : Nat → V) {i : Nat} (hi : i < s) :
    setJoin σ s Z Y (σ i) = Y i :=
  setJoin_at_fc (FibreConst.of_injOn hinj Y) Z hi

omit [SetTheory V] in
/-- **The join only ever sees the projection.** -/
theorem setJoin_fcNorm (Z Y : Nat → V) :
    setJoin σ s Z (fcNorm σ s Y) = setJoin σ s Z Y := by
  funext j
  by_cases h : ∃ i, i < s ∧ σ i = j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [setJoin_at_fc (fibreConst_fcNorm Y) Z hi, setJoin_at_norm Z Y hi]
  · rw [setJoin_out Z _ h, setJoin_out Z Y h]

omit [SetTheory V] in
theorem setPick_apply (σ : Nat → Nat) (Z : Nat → V) (i : Nat) : setPick σ Z i = Z (σ i) := rfl

omit [SetTheory V] in
/-- A tuple is the join of itself and its own picked positions. -/
theorem setJoin_setPick (σ : Nat → Nat) (s : Nat) (Z : Nat → V) :
    setJoin σ s Z (setPick σ Z) = Z := by
  funext j
  by_cases h : ∃ i, i < s ∧ σ i = j
  · show (if h : ∃ i, i < s ∧ σ i = j then setPick σ Z (Classical.choose h) else Z j) = Z j
    rw [dif_pos h, setPick_apply, (Classical.choose_spec h).2]
  · exact setJoin_out Z _ h

omit [SetTheory V] in
/-- **The index-set join is the contiguous one at `σ = (a + ·)`** — so
the theorems below cover `segJoin`'s. -/
theorem setJoin_ofAdd (a s : Nat) (Z Y : Nat → V) :
    setJoin (fun i => a + i) s Z Y = segJoin a s Z Y := by
  funext j
  by_cases h : ∃ i, i < s ∧ a + i = j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [setJoin_at (fun _ _ _ _ he => by omega) Z Y hi, segJoin_add Z Y hi]
  · rw [setJoin_out Z Y h, segJoin_out Z Y (fun hc => h ⟨j - a, by omega, by omega⟩)]

/-- **The projection stays in the space** — the representative's
position has the same index set. -/
theorem inTupleSpace_fcNorm {Is' : Nat → V}
    (hIs' : ∀ i i', i < s → i' < s → σ i = σ i' → Is' i = Is' i')
    {Y : Nat → V} (hY : InTupleSpace w s Is' Y) : InTupleSpace w s Is' (fcNorm σ s Y) := by
  intro i hi
  rw [fcNorm_apply Y i, hIs' i (fcRep σ s i) hi (fcRep_lt hi) (fcRep_eq hi).symm]
  exact hY _ (fcRep_lt hi)

/-- **The projection is monotone.** -/
theorem tupleLe_fcNorm {Is' : Nat → V}
    (hIs' : ∀ i i', i < s → i' < s → σ i = σ i' → Is' i = Is' i')
    {Y Y' : Nat → V} (h : TupleLe s Is' Y Y') :
    TupleLe s Is' (fcNorm σ s Y) (fcNorm σ s Y') := by
  intro i hi
  rw [fcNorm_apply Y i, fcNorm_apply Y' i,
    hIs' i (fcRep σ s i) hi (fcRep_lt hi) (fcRep_eq hi).symm]
  exact h _ (fcRep_lt hi)

/-- **The projection of a tuple below a FIBRE-CONSTANT bound is below
it too** — the bound cannot tell the representative from the position. -/
theorem tupleLe_fcNorm_of_le {Is' : Nat → V}
    (hIs' : ∀ i i', i < s → i' < s → σ i = σ i' → Is' i = Is' i')
    {Y C : Nat → V} (hC : FibreConst σ s C) (h : TupleLe s Is' Y C) :
    TupleLe s Is' (fcNorm σ s Y) C := by
  intro i hi
  rw [fcNorm_apply Y i, hIs' i (fcRep σ s i) hi (fcRep_lt hi) (fcRep_eq hi).symm,
    ← hC _ _ (fcRep_lt hi) hi (fcRep_eq hi)]
  exact h _ (fcRep_lt hi)

omit [SetTheory V] in
/-- The index sets a joined instance is compared at are fibre-invariant
by construction. -/
theorem fibreInv_comp (Is : Nat → V) :
    ∀ i i', i < s → i' < s → σ i = σ i' → (fun i => Is (σ i)) i = (fun i => Is (σ i)) i' :=
  fun _ _ _ _ he => by simp only; rw [he]

/-- **No hypothesis on `σ`.**  At a replaced position the join reads a
family of the fibre, whose index set is the position's. -/
theorem inTupleSpace_setJoin {Z Y : Nat → V}
    (hZ : InTupleSpace w N Is Z) (hY : InTupleSpace w s (fun i => Is (σ i)) Y) :
    InTupleSpace w N Is (setJoin σ s Z Y) := by
  intro j hj
  by_cases h : ∃ i, i < s ∧ σ i = j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [setJoin_at_norm Z Y hi]
    exact inTupleSpace_fcNorm (fibreInv_comp Is) hY i hi
  · rw [setJoin_out Z Y h]; exact hZ j hj

theorem inTupleSpace_setPick (hσ : ∀ i, i < s → σ i < N) {Z : Nat → V}
    (hZ : InTupleSpace w N Is Z) : InTupleSpace w s (fun i => Is (σ i)) (setPick σ Z) :=
  fun i hi => hZ (σ i) (hσ i hi)

theorem tupleLe_setJoin {Z Z' Y Y' : Nat → V} (hZ : TupleLe N Is Z Z')
    (hY : TupleLe s (fun i => Is (σ i)) Y Y') :
    TupleLe N Is (setJoin σ s Z Y) (setJoin σ s Z' Y') := by
  intro j hj
  by_cases h : ∃ i, i < s ∧ σ i = j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [setJoin_at_norm Z Y hi, setJoin_at_norm Z' Y' hi]
    exact tupleLe_fcNorm (fibreInv_comp Is) hY i hi
  · rw [setJoin_out Z Y h, setJoin_out Z' Y' h]; exact hZ j hj

theorem tupleLe_setPick (hσ : ∀ i, i < s → σ i < N) {Z Z' : Nat → V} (h : TupleLe N Is Z Z') :
    TupleLe s (fun i => Is (σ i)) (setPick σ Z) (setPick σ Z') :=
  fun i hi => h (σ i) (hσ i hi)

/-- The join is below `Z` when its replaced part is below `Z`'s. -/
theorem tupleLe_setJoin_of_le {Z Y : Nat → V}
    (hY : TupleLe s (fun i => Is (σ i)) Y (setPick σ Z)) : TupleLe N Is (setJoin σ s Z Y) Z := by
  have := tupleLe_setJoin (N := N) (Is := Is) (TupleLe.refl N Is Z) hY
  rwa [setJoin_setPick] at this

/-- **The section of `Ψ` at the index set `σ`** with everything else
held at `Z`: an operator on `s` components. -/
noncomputable def setSec (Ψ : (Nat → V) → Nat → V) (σ : Nat → Nat) (s : Nat) (Z : Nat → V) :
    (Nat → V) → Nat → V :=
  fun Y i => Ψ (setJoin σ s Z Y) (σ i)

omit [SetTheory V] in
theorem setSec_apply (Z Y : Nat → V) (i : Nat) :
    setSec Ψ σ s Z Y i = Ψ (setJoin σ s Z Y) (σ i) := rfl

theorem setSec_mono (hmono : MonoTuple w N Is Ψ)
    (hσ : ∀ i, i < s → σ i < N) {Z : Nat → V} (hZ : InTupleSpace w N Is Z) :
    MonoTuple w s (fun i => Is (σ i)) (setSec Ψ σ s Z) := by
  intro Y Y' hY hY' hle i hi
  exact hmono _ _ (inTupleSpace_setJoin hZ hY) (inTupleSpace_setJoin hZ hY')
    (tupleLe_setJoin (TupleLe.refl N Is Z) hle) (σ i) (hσ i hi)

theorem setSec_maps (hmaps : MapsTuple w N Is Ψ)
    (hσ : ∀ i, i < s → σ i < N) {Z : Nat → V} (hZ : InTupleSpace w N Is Z) :
    MapsTuple w s (fun i => Is (σ i)) (setSec Ψ σ s Z) :=
  fun _ hY i hi => hmaps _ (inTupleSpace_setJoin hZ hY) (σ i) (hσ i hi)

omit [SetTheory V] in
/-- **The section factors through the fibre quotient**: its value at a
position depends on the position only through `σ`.  This is why the
collapse costs the theory nothing — the section never had more than
`σ`'s image many rows. -/
theorem fibreConst_setSec (Z Y : Nat → V) : FibreConst σ s (setSec Ψ σ s Z Y) := by
  intro i i' _ _ he
  show Ψ (setJoin σ s Z Y) (σ i) = Ψ (setJoin σ s Z Y) (σ i')
  rw [he]

/-- **An operator that factors through the quotient has a
fibre-constant least tuple** — by its own fixpoint law, with nothing
assumed of `σ`.  The agreement is asked of the tuples of the SPACE
only, which is where the fixpoint law reads it. -/
theorem fibreConst_lfpTuple {Is' : Nat → V} {Φ : (Nat → V) → Nat → V}
    (h : ∃ L, IsClosedTuple w s Is' Φ L) (hmono : MonoTuple w s Is' Φ)
    (hmaps : MapsTuple w s Is' Φ)
    (hfc : ∀ Y, InTupleSpace w s Is' Y → FibreConst σ s (Φ Y)) :
    FibreConst σ s (lfpTuple w s Is' Φ) := by
  intro i i' hi hi' he
  rw [← lfpTuple_eq h hmono hmaps hi, ← lfpTuple_eq h hmono hmaps hi']
  exact hfc _ (lfpTuple_mem w s Is' Φ) i i' hi hi' he

/-- A closed tuple's picked positions are a closed tuple of the
section at it. -/
theorem isClosedTuple_setSec_of_closed (hσ : ∀ i, i < s → σ i < N) {L : Nat → V}
    (hL : IsClosedTuple w N Is Ψ L) :
    IsClosedTuple w s (fun i => Is (σ i)) (setSec Ψ σ s L) (setPick σ L) := by
  refine ⟨inTupleSpace_setPick hσ hL.1, fun i hi => ?_⟩
  rw [setSec_apply, setJoin_setPick]
  exact hL.2 (σ i) (hσ i hi)

/-- **Bekić at an index set.**  `lfpTuple_seg` with the contiguous
segment `[a, a + s)` replaced by the image of a map
`σ : [0, s) → [0, N)`: the least pre-fixed tuple's positions `σ i` are
the least pre-fixed tuple of the section at the least tuple itself.

**`σ` need not be injective**, and that is not a strengthening of the
statement but a correction of it (task #315, lane WIDE (f1)): the
section's value at a position depends on the position only through
`σ i`, so its least tuple is constant on `σ`'s fibres by its own
fixpoint law (`fibreConst_setSec`, `fibreConst_lfpTuple`), which is
exactly what reading a joined position back needs.  A collapsing `σ`
makes the comparison a QUOTIENT of the `s`-tuple space and the least
tuple lives on the quotient; injectivity only made the quotient
trivial.  `hmaps` is what the fixpoint law costs. -/
theorem lfpTuple_set (hσ : ∀ i, i < s → σ i < N)
    (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ)
    (hmaps : MapsTuple w N Is Ψ) {i : Nat} (hi : i < s) :
    lfpTuple w N Is Ψ (σ i)
      = lfpTuple w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ)) i := by
  have hLmem := lfpTuple_mem w N Is Ψ
  have hLcl := lfpTuple_isClosed h hmono
  have hsecCl : ∃ P, IsClosedTuple w s (fun i => Is (σ i))
      (setSec Ψ σ s (lfpTuple w N Is Ψ)) P := ⟨_, isClosedTuple_setSec_of_closed hσ hLcl⟩
  have hsecMono := setSec_mono hmono hσ hLmem
  have hsecMaps := setSec_maps hmaps hσ hLmem
  have hSmem := lfpTuple_mem w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ))
  have hSfc : FibreConst σ s
      (lfpTuple w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ))) :=
    fibreConst_lfpTuple hsecCl hsecMono hsecMaps (fun Y _ => fibreConst_setSec _ Y)
  have hSle : TupleLe s (fun i => Is (σ i))
      (lfpTuple w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ)))
      (setPick σ (lfpTuple w N Is Ψ)) :=
    lfpTuple_le (isClosedTuple_setSec_of_closed hσ hLcl)
  have hU : IsClosedTuple w N Is Ψ
      (setJoin σ s (lfpTuple w N Is Ψ)
        (lfpTuple w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ)))) := by
    refine ⟨inTupleSpace_setJoin hLmem hSmem, fun j hj => ?_⟩
    by_cases hin : ∃ i, i < s ∧ σ i = j
    · obtain ⟨i, hi', rfl⟩ := hin
      rw [setJoin_at_fc hSfc _ hi']
      exact lfpTuple_closed hsecCl hsecMono i hi'
    · rw [setJoin_out _ _ hin]
      refine FamLe.trans ?_ (hLcl.2 j hj)
      exact hmono _ _ (inTupleSpace_setJoin hLmem hSmem) hLmem
        (tupleLe_setJoin_of_le hSle) j hj
  have hLle := lfpTuple_le hU (σ i) (hσ i hi)
  rw [setJoin_at_fc hSfc _ hi] at hLle
  exact famSpace_ext (hLmem (σ i) (hσ i hi)) (hSmem i hi) fun t ht =>
    Subset.antisymm (hLle t ht) (hSle i hi t ht)

/-- **The other presentation, read through the quotient, has the SAME
least tuple** — when it too factors through `σ`'s fibres.  This is what
lets the congruence be stated at the projection `fcNorm` and still
conclude about `Φ'` itself: `Φ' ∘ fcNorm`'s least tuple is `Φ'`-closed
(both are fibre-constant, so the projection changes nothing below
them), and `Φ'`'s is `Φ' ∘ fcNorm`-closed for the same reason.

`hfc'` is asked only of the tuples that are in the space AND already
fibre-constant — which is the strength an operator reading its
argument at the classes' own positions can have, and all the composite
ever hands it (`fcNorm`'s images are both).  What the weaker
hypothesis no longer produces is `Φ'`'s own least tuple's
fibre-constancy, so that is `hL'fc`, a hypothesis of its own. -/
theorem lfpTuple_fcNorm_comp {Is' : Nat → V} {Φ' : (Nat → V) → Nat → V}
    (hIs' : ∀ i i', i < s → i' < s → σ i = σ i' → Is' i = Is' i')
    (hmono' : MonoTuple w s Is' Φ') (hmaps' : MapsTuple w s Is' Φ')
    (hcl' : ∃ L, IsClosedTuple w s Is' Φ' L)
    (hfc' : ∀ Y, InTupleSpace w s Is' Y → FibreConst σ s Y → FibreConst σ s (Φ' Y))
    (hL'fc : FibreConst σ s (lfpTuple w s Is' Φ'))
    {i : Nat} (hi : i < s) :
    lfpTuple w s Is' (fun Y => Φ' (fcNorm σ s Y)) i = lfpTuple w s Is' Φ' i := by
  have hmonoN : MonoTuple w s Is' (fun Y => Φ' (fcNorm σ s Y)) := fun Y Y' hY hY' hle =>
    hmono' _ _ (inTupleSpace_fcNorm hIs' hY) (inTupleSpace_fcNorm hIs' hY')
      (tupleLe_fcNorm hIs' hle)
  have hmapsN : MapsTuple w s Is' (fun Y => Φ' (fcNorm σ s Y)) :=
    fun _ hY => hmaps' _ (inTupleSpace_fcNorm hIs' hY)
  have hfcN : ∀ Y, InTupleSpace w s Is' Y → FibreConst σ s (Φ' (fcNorm σ s Y)) :=
    fun Y hY => hfc' _ (inTupleSpace_fcNorm hIs' hY) (fibreConst_fcNorm Y)
  -- the projection is the identity, both ways, at a fibre-constant tuple
  have hid : ∀ X : Nat → V, FibreConst σ s X →
      TupleLe s Is' (fcNorm σ s X) X ∧ TupleLe s Is' X (fcNorm σ s X) := by
    intro X hX
    constructor <;> intro m hm <;>
      rw [fcNorm_apply X m, hX _ _ (fcRep_lt hm) hm (fcRep_eq hm)] <;>
      exact FamLe.refl _ _
  -- `Φ'`'s least tuple is closed under the composite
  have hclN : IsClosedTuple w s Is' (fun Y => Φ' (fcNorm σ s Y)) (lfpTuple w s Is' Φ') := by
    refine ⟨lfpTuple_mem w s Is' Φ', TupleLe.trans ?_ (lfpTuple_closed hcl' hmono')⟩
    exact hmono' _ _ (inTupleSpace_fcNorm hIs' (lfpTuple_mem w s Is' Φ'))
      (lfpTuple_mem w s Is' Φ') (hid _ hL'fc).1
  -- the composite's least tuple is closed under `Φ'`
  have hMfc : FibreConst σ s (lfpTuple w s Is' (fun Y => Φ' (fcNorm σ s Y))) :=
    fibreConst_lfpTuple ⟨_, hclN⟩ hmonoN hmapsN hfcN
  have hclM : IsClosedTuple w s Is' Φ'
      (lfpTuple w s Is' (fun Y => Φ' (fcNorm σ s Y))) := by
    refine ⟨lfpTuple_mem w s Is' _, TupleLe.trans ?_ (lfpTuple_closed ⟨_, hclN⟩ hmonoN)⟩
    exact hmono' _ _ (lfpTuple_mem w s Is' _)
      (inTupleSpace_fcNorm hIs' (lfpTuple_mem w s Is' _)) (hid _ hMfc).2
  exact famSpace_ext (lfpTuple_mem w s Is' _ i hi) (lfpTuple_mem w s Is' Φ' i hi) fun t ht =>
    Subset.antisymm (lfpTuple_le hclN i hi t ht) (lfpTuple_le hclM i hi t ht)

/-- **Bekić at an index set, against another presentation of the
section** — `lfpTuple_seg_congr` with the contiguous segment replaced
by the image of an injection `σ : [0, s) → [0, N)`.  Stated in the same
vocabulary, so it substitutes for `lfpTuple_seg_congr` at a call site
whose positions are not a range (`setJoin_ofAdd` makes the contiguous
case literally this one). -/
theorem lfpTuple_set_congr {w N s : Nat} {Is Is' : Nat → V} {Ψ Φ' : (Nat → V) → Nat → V}
    {σ : Nat → Nat} (hσ : ∀ i, i < s → σ i < N)
    (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ)
    (hmaps : MapsTuple w N Is Ψ)
    (hIs : ∀ i, i < s → Is (σ i) = Is' i)
    (hΦ : ∀ Y, InTupleSpace w s (fun i => Is (σ i)) Y → ∀ i, i < s →
      Ψ (setJoin σ s (lfpTuple w N Is Ψ) Y) (σ i) = Φ' Y i)
    {i : Nat} (hi : i < s) :
    lfpTuple w N Is Ψ (σ i) = lfpTuple w s Is' Φ' i := by
  rw [lfpTuple_set hσ h hmono hmaps hi]
  exact lfpTuple_congr hIs (fun Y hY i hi => hΦ Y hY i hi) hi

end IdxSet

/-! ## Congruence AT THE CARRIER: agreement at the other presentation's least tuple -/

section CongrAt

variable {w s : Nat} {Is : Nat → V} {S Φ' : (Nat → V) → Nat → V}

/-- The tuple space and the order transport along equal index sets. -/
theorem inTupleSpace_congr {k : Nat} {Is Is' : Nat → V} (hIs : ∀ m, m < k → Is m = Is' m)
    {X : Nat → V} : InTupleSpace w k Is X ↔ InTupleSpace w k Is' X :=
  ⟨fun h m hm => by rw [← hIs m hm]; exact h m hm, fun h m hm => by rw [hIs m hm]; exact h m hm⟩

theorem tupleLe_congr {k : Nat} {Is Is' : Nat → V} (hIs : ∀ m, m < k → Is m = Is' m)
    {X Y : Nat → V} : TupleLe k Is X Y ↔ TupleLe k Is' X Y :=
  ⟨fun h m hm => by rw [← hIs m hm]; exact h m hm, fun h m hm => by rw [hIs m hm]; exact h m hm⟩

/-- **Two least tuples agree when the operators agree AT one's carrier
and are ordered BELOW it**: `S`'s least tuple is `Φ'`'s when `S` reads
as `Φ'` at `Φ'`'s least tuple `L'` and dominates `Φ'` on the tuples of
the space below `L'`.  (Task #315 L-C: a nested container's copies read
the container's own pins as CONSTANTS — the auxiliary carrier's pin
components — where the container's operator reads its pins' carriers
AT THE TUPLE; the two agree at the carrier and are ordered below it,
and are equal nowhere else, so `lfpTuple_congr`'s agreement on the
whole space is not available.)  `L'` is `S`-closed since `S L' = Φ' L'
≤ L'`, and `S`'s least tuple is `Φ'`-closed since it is below `L'`, where
`Φ' ≤ S`. -/
theorem lfpTuple_eq_of_at (hmonoS : MonoTuple w s Is S) (hclS : ∃ L, IsClosedTuple w s Is S L)
    (hmono' : MonoTuple w s Is Φ') (hcl' : ∃ L', IsClosedTuple w s Is Φ' L')
    (hat : ∀ i, i < s → S (lfpTuple w s Is Φ') i = Φ' (lfpTuple w s Is Φ') i)
    (hle : ∀ Y, InTupleSpace w s Is Y → TupleLe s Is Y (lfpTuple w s Is Φ') →
      TupleLe s Is (Φ' Y) (S Y))
    {i : Nat} (hi : i < s) : lfpTuple w s Is S i = lfpTuple w s Is Φ' i := by
  have hL'mem := lfpTuple_mem w s Is Φ'
  have hSmem := lfpTuple_mem w s Is S
  -- `L'` is `S`-closed: `S L' = Φ' L' ≤ L'`
  have hSle : TupleLe s Is (lfpTuple w s Is S) (lfpTuple w s Is Φ') :=
    lfpTuple_le ⟨hL'mem, fun j hj => by rw [hat j hj]; exact lfpTuple_closed hcl' hmono' j hj⟩
  -- `S`'s least tuple is `Φ'`-closed: `Φ' LS ≤ S LS ≤ LS`
  have h'le : TupleLe s Is (lfpTuple w s Is Φ') (lfpTuple w s Is S) :=
    lfpTuple_le ⟨hSmem, fun j hj =>
      (hle _ hSmem hSle j hj).trans (lfpTuple_closed hclS hmonoS j hj)⟩
  exact famSpace_ext (hSmem i hi) (hL'mem i hi) fun t ht =>
    Subset.antisymm (hSle i hi t ht) (h'le i hi t ht)

end CongrAt

/-- **Bekić at a segment, against a presentation agreeing AT ITS CARRIER**
(`lfpTuple_seg_congr`'s twin, task #315 L-C): when the segment's section
at the least tuple agrees with `Φ'` AT `Φ'`'s least tuple and dominates
`Φ'` on the segment's tuple space BELOW it, the least tuple's segment is
`Φ'`'s least tuple.  This is the theorem a pin of a container that is
ITSELF nested instantiates: the copies' section reads the container's
own pins as the auxiliary carrier's components, the container's
operator reads them as its pins' carriers at the tuple, and the two
agree at the container's carrier only (`pinMono` orders them below). -/
theorem lfpTuple_seg_congr_at {w N a s : Nat} {Is Is' : Nat → V} {Ψ Φ' : (Nat → V) → Nat → V}
    (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ) (hN : a + s ≤ N)
    (hIs : ∀ i, i < s → Is (a + i) = Is' i)
    (hmono' : MonoTuple w s Is' Φ') (hcl' : ∃ L', IsClosedTuple w s Is' Φ' L')
    (hat : ∀ i, i < s →
      Ψ (segJoin a s (lfpTuple w N Is Ψ) (lfpTuple w s Is' Φ')) (a + i)
        = Φ' (lfpTuple w s Is' Φ') i)
    (hle : ∀ Y, InTupleSpace w s Is' Y → TupleLe s Is' Y (lfpTuple w s Is' Φ') → ∀ i, i < s →
      FamLe (Is' i) (Φ' Y i) (Ψ (segJoin a s (lfpTuple w N Is Ψ) Y) (a + i)))
    {i : Nat} (hi : i < s) :
    lfpTuple w N Is Ψ (a + i) = lfpTuple w s Is' Φ' i := by
  rw [lfpTuple_seg h hmono hN hi, lfpTuple_congr hIs (fun _ _ _ _ => rfl) hi]
  have hLmem := lfpTuple_mem w N Is Ψ
  -- the section's laws, transported to `Is'`
  have hmonoS : MonoTuple w s Is' (segSec Ψ a s (lfpTuple w N Is Ψ)) := by
    intro X Y hX hY hXY
    exact (tupleLe_congr hIs).mp (segSec_mono hmono hN hLmem X Y ((inTupleSpace_congr hIs).mpr hX)
      ((inTupleSpace_congr hIs).mpr hY) ((tupleLe_congr hIs).mpr hXY))
  have hclS : ∃ L, IsClosedTuple w s Is' (segSec Ψ a s (lfpTuple w N Is Ψ)) L :=
    ⟨_, (isClosedTuple_congr hIs (fun _ _ _ _ => rfl)).mp
      (isClosedTuple_segSec_of_closed hN (lfpTuple_isClosed h hmono))⟩
  exact lfpTuple_eq_of_at hmonoS hclS hmono' hcl' hat (fun Y hY hYle j hj => hle Y hY hYle j hj) hi

/-! ## The meet of families, and the clamp -/

/-- The pointwise meet of two families over `I`. -/
noncomputable def famMeet (I A B : V) : V := graph (fun i => sep (app A i) fun x => x ∈ˢ app B i) I

theorem app_famMeet {I A B i : V} (hi : i ∈ˢ I) :
    app (famMeet I A B) i = sep (app A i) fun x => x ∈ˢ app B i :=
  app_graph hi

theorem famMeet_mem {w : Nat} {I A B : V} (hA : A ∈ˢ famSpace w I) :
    famMeet I A B ∈ˢ famSpace w I :=
  graph_mem_famSpace fun _ hi => univ_sep_mem (famSpace_app hA hi)

theorem famMeet_le_left (I A B : V) : FamLe I (famMeet I A B) A := by
  intro i hi
  rw [app_famMeet hi]
  exact sep_subset

theorem famMeet_le_right (I A B : V) : FamLe I (famMeet I A B) B := by
  intro i hi x hx
  rw [app_famMeet hi] at hx
  exact (mem_sep.mp hx).2

theorem famLe_famMeet {I C A B : V} (h₁ : FamLe I C A) (h₂ : FamLe I C B) :
    FamLe I C (famMeet I A B) := by
  intro i hi x hx
  rw [app_famMeet hi]
  exact mem_sep.mpr ⟨h₁ i hi x hx, h₂ i hi x hx⟩

theorem famMeet_mono {I A A' B B' : V} (h₁ : FamLe I A A') (h₂ : FamLe I B B') :
    FamLe I (famMeet I A B) (famMeet I A' B') :=
  famLe_famMeet ((famMeet_le_left I A B).trans h₁) ((famMeet_le_right I A B).trans h₂)

/-- The meet of the components of two tuples (the first `k`). -/
noncomputable def meetT (Is : Nat → V) (X L : Nat → V) : Nat → V :=
  fun m => famMeet (Is m) (X m) (L m)

section Meet

variable {w k : Nat} {Is : Nat → V}

theorem inTupleSpace_meetT {X : Nat → V} (hX : InTupleSpace w k Is X) (L : Nat → V) :
    InTupleSpace w k Is (meetT Is X L) :=
  fun m hm => famMeet_mem (hX m hm)

theorem meetT_le_left (X L : Nat → V) : TupleLe k Is (meetT Is X L) X :=
  fun _ _ => famMeet_le_left _ _ _

theorem meetT_le_right (X L : Nat → V) : TupleLe k Is (meetT Is X L) L :=
  fun _ _ => famMeet_le_right _ _ _

theorem tupleLe_meetT {C X L : Nat → V} (h₁ : TupleLe k Is C X) (h₂ : TupleLe k Is C L) :
    TupleLe k Is C (meetT Is X L) :=
  fun m hm => famLe_famMeet (h₁ m hm) (h₂ m hm)

theorem meetT_mono {X X' L L' : Nat → V} (h₁ : TupleLe k Is X X') (h₂ : TupleLe k Is L L') :
    TupleLe k Is (meetT Is X L) (meetT Is X' L') :=
  fun m hm => famMeet_mono (h₁ m hm) (h₂ m hm)

/-- **Below `L` the clamp is the identity** (as tuples on the first `k`
components: both orders). -/
theorem meetT_eq_of_le {X L : Nat → V} (h : TupleLe k Is X L) :
    TupleLe k Is X (meetT Is X L) :=
  tupleLe_meetT (TupleLe.refl k Is X) h

end Meet

/-! ## THE LEAST TUPLE'S OWN FIBRE-CONSTANCY, from the WEAKENED row law

`fibreConst_lfpTuple` reads its hypothesis at the least tuple and
nowhere else, so it asks the rows to factor through `σ`'s fibres at
EVERY tuple of the space.  An operator read off a block model's
constructor data does not: its rows agree on the tuples that do not
tell two identified classes apart and differ elsewhere (a three-line
block exhibits it), so what a producer can supply is the weakened law

    ∀ Y, InTupleSpace … Y → FibreConst σ s Y → FibreConst σ s (Φ' Y)

— and at that strength the fixpoint argument is circular: it would
need the least tuple's fibre-constancy to get the rows at it.

The repair is the FIBRE MEET.  `L' i := ⨅ { L i' | σ i' = σ i }` is
fibre-constant by construction and below `L`, so `Φ' L'` is
fibre-constant by the weakened law and, at each `i'` of the fibre,
below `Φ' L i' = L i'` — hence below the meet.  `L'` is therefore
closed, `L ≤ L'` by leastness, and the two are equal.

`hL'fc` — `lfpTuple_fcNorm_comp`'s and `lfpTuple_set_congr_le`'s
hypothesis of that name — is thus a THEOREM at the hypotheses they
already take. -/

section FibreMeet

variable {w s : Nat} {σ : Nat → Nat}

omit [SetTheory V] in
/-- `i`'s fibre under `σ`, as the list of positions below `s` that `σ`
sends where it sends `i`.  It depends on `i` only through `σ i`. -/
def fcFibre (σ : Nat → Nat) (s i : Nat) : List Nat :=
  (List.range s).filter (fun i' => σ i' == σ i)

omit [SetTheory V] in
theorem mem_fcFibre {i i' : Nat} : i' ∈ fcFibre σ s i ↔ i' < s ∧ σ i' = σ i := by
  simp [fcFibre, List.mem_filter, List.mem_range]

/-- A finite meet of families over ONE index set. -/
noncomputable def famMeetList (I : V) (f : Nat → V) : List Nat → V → V
  | [], b => b
  | i :: l, b => famMeetList I f l (famMeet I b (f i))

theorem famMeetList_mem {I : V} {f : Nat → V} :
    ∀ (l : List Nat) {b : V}, b ∈ˢ famSpace w I → famMeetList I f l b ∈ˢ famSpace w I
  | [], _, hb => hb
  | _ :: l, _, hb => famMeetList_mem l (famMeet_mem hb)

theorem famMeetList_le_base {I : V} {f : Nat → V} :
    ∀ (l : List Nat) (b : V), FamLe I (famMeetList I f l b) b
  | [], b => FamLe.refl I b
  | i :: l, b =>
    (famMeetList_le_base l (famMeet I b (f i))).trans (famMeet_le_left I b (f i))

theorem famMeetList_le_mem {I : V} {f : Nat → V} :
    ∀ (l : List Nat) (b : V) {i : Nat}, i ∈ l → FamLe I (famMeetList I f l b) (f i)
  | [], _, _, hi => absurd hi (by simp)
  | j :: l, b, i, hi => by
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact (famMeetList_le_base l (famMeet I b (f i))).trans (famMeet_le_right I b (f i))
    · exact famMeetList_le_mem l (famMeet I b (f j)) hi'

theorem famLe_famMeetList {I C : V} {f : Nat → V} :
    ∀ (l : List Nat) (b : V), FamLe I C b → (∀ i ∈ l, FamLe I C (f i)) →
      FamLe I C (famMeetList I f l b)
  | [], _, hb, _ => hb
  | i :: l, b, hb, hl =>
    famLe_famMeetList l (famMeet I b (f i)) (famLe_famMeet hb (hl i (by simp)))
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))

/-- **THE FIBRE MEET**: `L` with every position replaced by the meet of
its whole fibre, based at the fibre's chosen representative so that the
whole expression depends on the position only through `σ`. -/
noncomputable def fcMeet (σ : Nat → Nat) (s : Nat) (Is L : Nat → V) : Nat → V :=
  fun i => famMeetList (Is (fcRep σ s i)) L (fcFibre σ s i) (L (fcRep σ s i))

theorem fibreConst_fcMeet (Is L : Nat → V) : FibreConst σ s (fcMeet σ s Is L) := by
  intro i i' _ _ he
  show famMeetList (Is (fcRepAt σ s (σ i))) L ((List.range s).filter (fun x => σ x == σ i))
      (L (fcRepAt σ s (σ i)))
    = famMeetList (Is (fcRepAt σ s (σ i'))) L ((List.range s).filter (fun x => σ x == σ i'))
      (L (fcRepAt σ s (σ i')))
  rw [he]

/-- **THE LEAST TUPLE IS FIBRE-CONSTANT, at the WEAKENED law** (task
#315 WIDE (3′)): `fibreConst_lfpTuple` with its hypothesis asked only
of the tuples that are in the space AND already fibre-constant —
which is the strength an operator read off a block model's constructor
data has, and the strength `lfpTuple_fcNorm_comp` and
`lfpTuple_set_congr_le` ask of the OTHER presentation.  Their `hL'fc`
is this. -/
theorem fibreConst_lfpTuple_of_fc {Is' : Nat → V} {Φ' : (Nat → V) → Nat → V}
    (hIs' : ∀ i i', i < s → i' < s → σ i = σ i' → Is' i = Is' i')
    (hmono' : MonoTuple w s Is' Φ') (hcl' : ∃ L, IsClosedTuple w s Is' Φ' L)
    (hfc' : ∀ Y, InTupleSpace w s Is' Y → FibreConst σ s Y → FibreConst σ s (Φ' Y)) :
    FibreConst σ s (lfpTuple w s Is' Φ') := by
  have hLmem := lfpTuple_mem w s Is' Φ'
  have hIsrep : ∀ i, i < s → Is' (fcRep σ s i) = Is' i :=
    fun i hi => hIs' _ _ (fcRep_lt hi) hi (fcRep_eq hi)
  have hMmem : InTupleSpace w s Is' (fcMeet σ s Is' (lfpTuple w s Is' Φ')) := by
    intro i hi
    rw [← hIsrep i hi]
    exact famMeetList_mem _ (hLmem _ (fcRep_lt hi))
  have hMfc : FibreConst σ s (fcMeet σ s Is' (lfpTuple w s Is' Φ')) :=
    fibreConst_fcMeet Is' _
  have hMle : TupleLe s Is' (fcMeet σ s Is' (lfpTuple w s Is' Φ')) (lfpTuple w s Is' Φ') := by
    intro i hi
    rw [← hIsrep i hi]
    exact famMeetList_le_mem _ _ (mem_fcFibre.mpr ⟨hi, rfl⟩)
  -- at every position of the fibre the image is below the least tuple there
  have hstep : ∀ i, i < s → ∀ i', i' < s → σ i' = σ i →
      FamLe (Is' (fcRep σ s i)) (Φ' (fcMeet σ s Is' (lfpTuple w s Is' Φ')) i)
        (lfpTuple w s Is' Φ' i') := by
    intro i hi i' hi' he
    have hIeq : Is' (fcRep σ s i) = Is' i' := by
      rw [hIsrep i hi]; exact (hIs' i' i hi' hi he).symm
    rw [hIeq, hfc' _ hMmem hMfc i i' hi hi' he.symm]
    exact (hmono' _ _ hMmem hLmem hMle i' hi').trans (lfpTuple_closed hcl' hmono' i' hi')
  have hclM : IsClosedTuple w s Is' Φ' (fcMeet σ s Is' (lfpTuple w s Is' Φ')) := by
    refine ⟨hMmem, fun i hi => ?_⟩
    rw [← hIsrep i hi]
    refine famLe_famMeetList _ _ (hstep i hi _ (fcRep_lt hi) (fcRep_eq hi)) (fun i' hi' => ?_)
    obtain ⟨hi'lt, hi'e⟩ := mem_fcFibre.mp hi'
    exact hstep i hi i' hi'lt hi'e
  intro i i' hi hi' he
  have hEq : ∀ j, j < s → lfpTuple w s Is' Φ' j = fcMeet σ s Is' (lfpTuple w s Is' Φ') j :=
    fun j hj => famSpace_ext (hLmem j hj) (hMmem j hj)
      (fun t ht => Subset.antisymm (lfpTuple_le hclM j hj t ht) (hMle j hj t ht))
  rw [hEq i hi, hEq i' hi']
  exact hMfc i i' hi hi' he

end FibreMeet


/-! ## Congruence BELOW A CLOSED TUPLE -/

section CongrLe

variable {w k : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- **The clamp of a closed tuple is closed**: `X ⊓ C` is closed under
a monotone `Φ` when `X` and `C` are, because `Φ (X ⊓ C)` is below both
`Φ X ⊆ X` and `Φ C ⊆ C`. -/
theorem isClosedTuple_meetT (hmono : MonoTuple w k Is Φ) {X C : Nat → V}
    (hX : IsClosedTuple w k Is Φ X) (hC : IsClosedTuple w k Is Φ C) :
    IsClosedTuple w k Is Φ (meetT Is X C) :=
  ⟨inTupleSpace_meetT hX.1 C,
    tupleLe_meetT
      ((hmono _ _ (inTupleSpace_meetT hX.1 C) hX.1 (meetT_le_left X C)).trans hX.2)
      ((hmono _ _ (inTupleSpace_meetT hX.1 C) hC.1 (meetT_le_right X C)).trans hC.2)⟩

/-- **Two presentations agreeing BELOW a common closed tuple have the
same least tuple.**  This is the strength the fixpoint theory actually
asks for, and `lfpTuple_congr`'s whole-space hypothesis is more than it
needs: a least tuple is the intersection of the closed tuples, every
closed tuple may be CLAMPED to `C` without changing that intersection
(`isClosedTuple_meetT`, `meetT_le_left`), and below `C` the two
operators are the same function — so they have the same clamped closed
tuples and the same intersection.

The consumer is a CONTAINER INSTANCE's identification (`docs/NESTED.md`,
Resolution 1): the block's copies and the container's own wide operator
are compared through readings that the run states at frames fitting the
container's domains — that is, below the container's own carrier — and
`C` is that carrier.  It is a bound on the tuples compared, not a
domination between the operators: nothing about another component of
the block enters it. -/
theorem lfpTuple_congr_le_same (hmono : MonoTuple w k Is Φ) (hmono' : MonoTuple w k Is Φ')
    {C : Nat → V} (hC : IsClosedTuple w k Is Φ C) (hC' : IsClosedTuple w k Is Φ' C)
    (hΦ : ∀ X, InTupleSpace w k Is X → TupleLe k Is X C → ∀ m, m < k → Φ X m = Φ' X m)
    {m : Nat} (hm : m < k) : lfpTuple w k Is Φ m = lfpTuple w k Is Φ' m := by
  -- the clamp of a closed tuple of either operator is closed under BOTH
  have hclamp : ∀ X, IsClosedTuple w k Is Φ X → IsClosedTuple w k Is Φ' (meetT Is X C) := by
    intro X hX
    have hmeet := isClosedTuple_meetT hmono hX hC
    refine ⟨hmeet.1, fun m' hm' => ?_⟩
    rw [← hΦ _ hmeet.1 (meetT_le_right X C) m' hm']
    exact hmeet.2 m' hm'
  have hclamp' : ∀ X, IsClosedTuple w k Is Φ' X → IsClosedTuple w k Is Φ (meetT Is X C) := by
    intro X hX
    have hmeet := isClosedTuple_meetT hmono' hX hC'
    refine ⟨hmeet.1, fun m' hm' => ?_⟩
    rw [hΦ _ hmeet.1 (meetT_le_right X C) m' hm']
    exact hmeet.2 m' hm'
  refine famSpace_ext (lfpTuple_mem w k Is Φ m hm) (lfpTuple_mem w k Is Φ' m hm) fun i hi => ?_
  apply SetTheory.ext
  intro x
  rw [mem_app_lfpTuple ⟨C, hC⟩ hi, mem_app_lfpTuple ⟨C, hC'⟩ hi]
  constructor
  · intro hx X hX
    exact meetT_le_left (Is := Is) X C m hm i hi x (hx _ (hclamp' X hX))
  · intro hx X hX
    exact meetT_le_left (Is := Is) X C m hm i hi x (hx _ (hclamp X hX))

/-- `lfpTuple_congr_le_same` with the second presentation's index sets
renamed, as `lfpTuple_congr` has them. -/
theorem lfpTuple_congr_le (hIs : ∀ m, m < k → Is m = Is' m)
    (hmono : MonoTuple w k Is Φ) (hmono' : MonoTuple w k Is Φ')
    {C : Nat → V} (hC : IsClosedTuple w k Is Φ C) (hC' : IsClosedTuple w k Is Φ' C)
    (hΦ : ∀ X, InTupleSpace w k Is X → TupleLe k Is X C → ∀ m, m < k → Φ X m = Φ' X m)
    {m : Nat} (hm : m < k) : lfpTuple w k Is Φ m = lfpTuple w k Is' Φ' m :=
  (lfpTuple_congr_le_same hmono hmono' hC hC' hΦ hm).trans
    (lfpTuple_congr hIs (fun _ _ _ _ => rfl) hm)

/-- **Bekić at an index set, against another presentation of the
section, BELOW A CLOSED TUPLE** — `lfpTuple_set_congr` at the
congruence's correct strength.  The agreement `hΦ` is asked only of the
tuples of the instance's space that lie below `C`, and `C` — the other
presentation's own carrier at the call site — must be closed under
both, which for `Φ'` is its fixpoint law and for the section follows
from the agreement AT `C`.

`hfc'` — that `Φ'` factors through `σ`'s fibres — is likewise asked
only of the tuples of the space that are already fibre-constant, which
is the strength an operator whose rows read the classes' own positions
can have; `hL'fc`, `Φ'`'s own least tuple's fibre-constancy, is then a
hypothesis rather than a consequence. -/
theorem lfpTuple_set_congr_le {w N s : Nat} {Is Is' : Nat → V} {Ψ Φ' : (Nat → V) → Nat → V}
    {σ : Nat → Nat} (hσ : ∀ i, i < s → σ i < N)
    (h : ∃ L, IsClosedTuple w N Is Ψ L) (hmono : MonoTuple w N Is Ψ)
    (hmaps : MapsTuple w N Is Ψ)
    (hIs : ∀ i, i < s → Is (σ i) = Is' i)
    (hmono' : MonoTuple w s (fun i => Is (σ i)) Φ')
    (hmaps' : MapsTuple w s (fun i => Is (σ i)) Φ')
    (hfc' : ∀ Y, InTupleSpace w s (fun i => Is (σ i)) Y → FibreConst σ s Y →
      FibreConst σ s (Φ' Y))
    (hL'fc : FibreConst σ s (lfpTuple w s (fun i => Is (σ i)) Φ'))
    {C : Nat → V}
    (hC : IsClosedTuple w s (fun i => Is (σ i)) (setSec Ψ σ s (lfpTuple w N Is Ψ)) C)
    (hC' : IsClosedTuple w s (fun i => Is (σ i)) Φ' C)
    (hCfc : FibreConst σ s C)
    (hΦ : ∀ Y, InTupleSpace w s (fun i => Is (σ i)) Y → FibreConst σ s Y →
      TupleLe s (fun i => Is (σ i)) Y C →
      ∀ i, i < s → Ψ (setJoin σ s (lfpTuple w N Is Ψ) Y) (σ i) = Φ' Y i)
    {i : Nat} (hi : i < s) :
    lfpTuple w N Is Ψ (σ i) = lfpTuple w s Is' Φ' i := by
  have hIsFC := fibreInv_comp (σ := σ) (s := s) Is
  -- the composite reads the projection, which the join alone already does
  have hC'N : IsClosedTuple w s (fun i => Is (σ i)) (fun Y => Φ' (fcNorm σ s Y)) C := by
    refine ⟨hC'.1, TupleLe.trans ?_ hC'.2⟩
    exact hmono' _ _ (inTupleSpace_fcNorm hIsFC hC'.1) hC'.1
      (fun m hm => by
        rw [fcNorm_apply C m, hCfc _ _ (fcRep_lt hm) hm (fcRep_eq hm)]; exact FamLe.refl _ _)
  have hagree : ∀ X, InTupleSpace w s (fun i => Is (σ i)) X →
      TupleLe s (fun i => Is (σ i)) X C → ∀ m, m < s →
      setSec Ψ σ s (lfpTuple w N Is Ψ) X m = Φ' (fcNorm σ s X) m := by
    intro X hX hXC m hm
    show Ψ (setJoin σ s (lfpTuple w N Is Ψ) X) (σ m) = _
    rw [← setJoin_fcNorm (lfpTuple w N Is Ψ) X]
    exact hΦ (fcNorm σ s X) (inTupleSpace_fcNorm hIsFC hX) (fibreConst_fcNorm X)
      (tupleLe_fcNorm_of_le hIsFC hCfc hXC) m hm
  rw [lfpTuple_set hσ h hmono hmaps hi]
  refine (lfpTuple_congr_le_same (setSec_mono hmono hσ (lfpTuple_mem w N Is Ψ))
    (fun Y Y' hY hY' hle => hmono' _ _ (inTupleSpace_fcNorm hIsFC hY)
      (inTupleSpace_fcNorm hIsFC hY') (tupleLe_fcNorm hIsFC hle))
    hC hC'N hagree hi).trans ?_
  exact (lfpTuple_fcNorm_comp hIsFC hmono' hmaps' ⟨C, hC'⟩ hfc' hL'fc hi).trans
    (lfpTuple_congr hIs (fun _ _ _ _ => rfl) hi)

end CongrLe

/-! ## The composed operator -/

section Compose

variable (w k n : Nat) (Is : Nat → V) (Ψ : (Nat → V) → Nat → V)

/-- **The pins' operator at a members' tuple `X`**: the pins' section of
`Ψ` (the segment `[k, k + n)`) with the members held at `X ⊓ L⁺`
(the clamp, see the module docstring). -/
noncomputable def pinsOp (X : Nat → V) : (Nat → V) → Nat → V :=
  segSec Ψ k n (meetT Is X (lfpTuple w (k + n) Is Ψ))

/-- **The pins' carriers at a members' tuple `X`**: the least pre-fixed
tuple of the pins' operator at `X`. -/
noncomputable def pinsCar (X : Nat → V) : Nat → V :=
  lfpTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X)

/-- **The extended tuple**: the members at `X`, the pins at their
carriers at `X`. -/
noncomputable def extT (X : Nat → V) : Nat → V := segJoin k n X (pinsCar w k n Is Ψ X)

/-- **The composed operator**: `Ψ` at the extended tuple (read at the
members). -/
noncomputable def composeΦ (X : Nat → V) : Nat → V := Ψ (extT w k n Is Ψ X)

variable {w k n Is Ψ}

theorem extT_lt {X : Nat → V} {m : Nat} (hm : m < k) : extT w k n Is Ψ X m = X m :=
  segJoin_lt _ _ hm

theorem extT_add {X : Nat → V} {q : Nat} (hq : q < n) :
    extT w k n Is Ψ X (k + q) = pinsCar w k n Is Ψ X q :=
  segJoin_add _ _ hq

/-- The extended tuple at a target below `k + n`, in the block model's
`famAt` spelling. -/
theorem extT_eq_famAt {X : Nat → V} {tgt : Nat} (h : tgt < k + n) :
    extT w k n Is Ψ X tgt = if tgt < k then X tgt else pinsCar w k n Is Ψ X (tgt - k) := by
  by_cases hk : tgt < k
  · rw [if_pos hk, extT_lt hk]
  · rw [if_neg hk]
    have h' := extT_add (w := w) (k := k) (n := n) (Is := Is) (Ψ := Ψ) (X := X) (q := tgt - k) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : k ≤ tgt)] at h'

theorem composeΦ_apply (X : Nat → V) (m : Nat) :
    composeΦ w k n Is Ψ X m = Ψ (extT w k n Is Ψ X) m := rfl

/-- **At no pins the extension is the identity**: an empty segment
joins nothing. -/
theorem extT_zero (X : Nat → V) : extT w k 0 Is Ψ X = X := by
  funext j; exact segJoin_out _ _ fun h => by omega

/-- **At no pins the composition is the operator itself.**  This is
what a block WITHOUT pins needs to present its own `k`-tuple operator
as its wide operator (`BlockModel.ofNative`, `BlockModel.ofMutual`):
there is nothing to solve internally. -/
theorem composeΦ_zero : composeΦ w k 0 Is Ψ = Ψ := by
  funext X
  show Ψ (extT w k 0 Is Ψ X) = Ψ X
  rw [extT_zero]

/-- The pins' carriers are in the pins' tuple space, unconditionally. -/
theorem pinsCar_mem (X : Nat → V) : InTupleSpace w n (fun q => Is (k + q)) (pinsCar w k n Is Ψ X) :=
  lfpTuple_mem _ _ _ _

theorem extT_mem {X : Nat → V} (hX : InTupleSpace w k Is X) :
    InTupleSpace w (k + n) Is (extT w k n Is Ψ X) := by
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [extT, segJoin_in _ _ hin]
    have := pinsCar_mem (w := w) (k := k) (n := n) (Is := Is) (Ψ := Ψ) X (j - k) (by omega)
    simp only [Nat.add_sub_cancel' hin.1] at this; exact this
  · rw [extT, segJoin_out _ _ hin]
    exact hX j (lt_of_not_seg hj hin)

section Laws

variable (hmono : MonoTuple w (k + n) Is Ψ) (hmaps : MapsTuple w (k + n) Is Ψ)
  (hcl : ∃ L, IsClosedTuple w (k + n) Is Ψ L)

include hmono hcl

/-- **The auxiliary carrier's pins close the pins' operator at every
`X`** — the clamp's purpose. -/
theorem isClosedTuple_pinsOp_aux {X : Nat → V} (hX : InTupleSpace w k Is X) :
    IsClosedTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X)
      (segOf k (lfpTuple w (k + n) Is Ψ)) := by
  have hLmem := lfpTuple_mem w (k + n) Is Ψ
  have hLcl := lfpTuple_isClosed hcl hmono
  refine ⟨inTupleSpace_segOf (Nat.le_refl _) hLmem, fun q hq => ?_⟩
  rw [pinsOp, segSec_apply]
  refine FamLe.trans ?_ (hLcl.2 (k + q) (by omega))
  refine hmono _ _ (inTupleSpace_segJoin' (fun j hj hout => inTupleSpace_meetT hX _ j (lt_of_not_seg hj hout))
    (inTupleSpace_segOf (Nat.le_refl _) hLmem)) hLmem ?_ (k + q) (by omega)
  -- below `L⁺`: the members by the clamp, the pins equal
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [segJoin_in _ _ hin, segOf_apply, Nat.add_sub_cancel' hin.1]; exact FamLe.refl _ _
  · rw [segJoin_out _ _ hin]
    exact meetT_le_right (k := k) X _ j (lt_of_not_seg hj hin)

theorem pinsOp_closed_exists {X : Nat → V} (hX : InTupleSpace w k Is X) :
    ∃ P, IsClosedTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) P :=
  ⟨_, isClosedTuple_pinsOp_aux hmono hcl hX⟩

omit hcl in
theorem pinsOp_mono {X : Nat → V} (hX : InTupleSpace w k Is X) :
    MonoTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) :=
  fun Y Y' hY hY' hle q hq =>
    hmono _ _ (inTupleSpace_segJoin' (fun j hj hout => inTupleSpace_meetT hX _ j (lt_of_not_seg hj hout)) hY)
      (inTupleSpace_segJoin' (fun j hj hout => inTupleSpace_meetT hX _ j (lt_of_not_seg hj hout)) hY')
      (tupleLe_segJoin (TupleLe.refl _ _ _) hle) (k + q) (by omega)

/-- The pins' carriers at `X` are below the auxiliary carrier's pins. -/
theorem pinsCar_le_aux {X : Nat → V} (hX : InTupleSpace w k Is X) :
    TupleLe n (fun q => Is (k + q)) (pinsCar w k n Is Ψ X) (segOf k (lfpTuple w (k + n) Is Ψ)) :=
  lfpTuple_le (isClosedTuple_pinsOp_aux hmono hcl hX)

/-- **The pins' carriers are monotone in the members' tuple** (the block
model's `pinMono`): the carriers at `Y` close the pins' operator at
`X ≤ Y`. -/
theorem pinsCar_mono {X Y : Nat → V} (hX : InTupleSpace w k Is X) (hY : InTupleSpace w k Is Y)
    (hle : TupleLe k Is X Y) :
    TupleLe n (fun q => Is (k + q)) (pinsCar w k n Is Ψ X) (pinsCar w k n Is Ψ Y) := by
  refine lfpTuple_le ⟨pinsCar_mem Y, fun q hq => ?_⟩
  refine FamLe.trans ?_ (lfpTuple_closed (pinsOp_closed_exists hmono hcl hY) (pinsOp_mono hmono hY) q hq)
  rw [pinsOp, pinsOp, segSec_apply, segSec_apply]
  have hspace : ∀ Z, InTupleSpace w k Is Z →
      InTupleSpace w (k + n) Is
        (segJoin k n (meetT Is Z (lfpTuple w (k + n) Is Ψ)) (pinsCar w k n Is Ψ Y)) := by
    intro Z hZ j hj
    by_cases hin : k ≤ j ∧ j < k + n
    · rw [segJoin_in _ _ hin]
      have := pinsCar_mem (w := w) (k := k) (n := n) (Is := Is) (Ψ := Ψ) Y (j - k) (by omega)
      simp only [Nat.add_sub_cancel' hin.1] at this; exact this
    · rw [segJoin_out _ _ hin]
      exact inTupleSpace_meetT hZ _ j (lt_of_not_seg hj hin)
  refine hmono _ _ (hspace X hX) (hspace Y hY) ?_ (k + q) (by omega)
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [segJoin_in _ _ hin, segJoin_in _ _ hin]; exact FamLe.refl _ _
  · rw [segJoin_out _ _ hin, segJoin_out _ _ hin]
    exact meetT_mono (k := k) hle (TupleLe.refl _ _ _) j (lt_of_not_seg hj hin)

theorem extT_le {X Y : Nat → V} (hX : InTupleSpace w k Is X) (hY : InTupleSpace w k Is Y)
    (hle : TupleLe k Is X Y) : TupleLe (k + n) Is (extT w k n Is Ψ X) (extT w k n Is Ψ Y) := by
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [extT, extT, segJoin_in _ _ hin, segJoin_in _ _ hin]
    have := pinsCar_mono hmono hcl hX hY hle (j - k) (by omega)
    simp only [Nat.add_sub_cancel' hin.1] at this; exact this
  · rw [extT, extT, segJoin_out _ _ hin, segJoin_out _ _ hin]
    exact hle j (lt_of_not_seg hj hin)

/-- **The composed operator is monotone** (the block model's `functor`,
first half). -/
theorem composeΦ_mono : MonoTuple w k Is (composeΦ w k n Is Ψ) :=
  fun X Y hX hY hle m hm =>
    hmono _ _ (extT_mem hX) (extT_mem hY) (extT_le hmono hcl hX hY hle) m (by omega)

omit hmono hcl in
include hmaps in
/-- **The composed operator preserves the tuple space** (the block
model's `functor`, second half). -/
theorem composeΦ_maps : MapsTuple w k Is (composeΦ w k n Is Ψ) :=
  fun X hX m hm => hmaps _ (extT_mem hX) m (by omega)

/-- The extended tuple at the auxiliary carrier's members is below the
auxiliary carrier. -/
theorem extT_aux_le :
    TupleLe (k + n) Is (extT w k n Is Ψ (lfpTuple w (k + n) Is Ψ)) (lfpTuple w (k + n) Is Ψ) := by
  have hLmem := lfpTuple_mem w (k + n) Is Ψ
  have hLk : InTupleSpace w k Is (lfpTuple w (k + n) Is Ψ) := fun m hm => hLmem m (by omega)
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [extT, segJoin_in _ _ hin]
    have := pinsCar_le_aux hmono hcl hLk (j - k) (by omega)
    simp only [segOf_apply, Nat.add_sub_cancel' hin.1] at this
    exact this
  · rw [extT, segJoin_out _ _ hin]; exact FamLe.refl _ _

/-- **The auxiliary carrier closes the composed operator** (the block
model's `functor`, third half — (W) composed, from (W) auxiliary). -/
theorem isClosedTuple_composeΦ_aux :
    IsClosedTuple w k Is (composeΦ w k n Is Ψ) (lfpTuple w (k + n) Is Ψ) := by
  have hLmem := lfpTuple_mem w (k + n) Is Ψ
  have hLcl := lfpTuple_isClosed hcl hmono
  refine ⟨fun m hm => hLmem m (by omega), fun m hm => ?_⟩
  rw [composeΦ_apply]
  refine FamLe.trans ?_ (hLcl.2 m (by omega))
  exact hmono _ _ (extT_mem fun m hm => hLmem m (by omega)) hLmem (extT_aux_le hmono hcl) m (by omega)

theorem composeΦ_closed_exists : ∃ L, IsClosedTuple w k Is (composeΦ w k n Is Ψ) L :=
  ⟨_, isClosedTuple_composeΦ_aux hmono hcl⟩

/-! ### Bekić, the nested form: the composed least tuple is the auxiliary one -/

/-- The composed least tuple is below the auxiliary carrier's members. -/
theorem lfpTuple_composeΦ_le :
    TupleLe k Is (lfpTuple w k Is (composeΦ w k n Is Ψ)) (lfpTuple w (k + n) Is Ψ) :=
  lfpTuple_le (isClosedTuple_composeΦ_aux hmono hcl)

/-- The extended tuple at the composed least tuple is closed under `Ψ`:
the members by the composed operator's closure, the pins by the pins'
operator's (the clamp is the identity below the auxiliary carrier). -/
theorem isClosedTuple_extT_lfp :
    IsClosedTuple w (k + n) Is Ψ (extT w k n Is Ψ (lfpTuple w k Is (composeΦ w k n Is Ψ))) := by
  have hLk := lfpTuple_mem w k Is (composeΦ w k n Is Ψ)
  have hcmono := composeΦ_mono hmono hcl
  have hccl := composeΦ_closed_exists hmono hcl
  refine ⟨extT_mem hLk, fun j hj => ?_⟩
  by_cases hin : k ≤ j ∧ j < k + n
  · -- a pin: the pins' operator at the composed least tuple
    have hq : j - k < n := by omega
    have hcl' := lfpTuple_closed (pinsOp_closed_exists hmono hcl hLk) (pinsOp_mono hmono hLk) (j - k) hq
    simp only [pinsOp, segSec_apply, Nat.add_sub_cancel' hin.1] at hcl'
    rw [extT, segJoin_in _ _ hin]
    refine FamLe.trans ?_ hcl'
    -- the clamped members are ABOVE the composed least tuple (it is below `L⁺`)
    have hspace1 : InTupleSpace w (k + n) Is
        (segJoin k n (lfpTuple w k Is (composeΦ w k n Is Ψ))
          (pinsCar w k n Is Ψ (lfpTuple w k Is (composeΦ w k n Is Ψ)))) := extT_mem hLk
    have hspace2 : InTupleSpace w (k + n) Is
        (segJoin k n (meetT Is (lfpTuple w k Is (composeΦ w k n Is Ψ)) (lfpTuple w (k + n) Is Ψ))
          (pinsCar w k n Is Ψ (lfpTuple w k Is (composeΦ w k n Is Ψ)))) := by
      intro j' hj'
      by_cases hin' : k ≤ j' ∧ j' < k + n
      · rw [segJoin_in _ _ hin']
        have := pinsCar_mem (w := w) (k := k) (n := n) (Is := Is) (Ψ := Ψ)
          (lfpTuple w k Is (composeΦ w k n Is Ψ)) (j' - k) (by omega)
        simp only [Nat.add_sub_cancel' hin'.1] at this; exact this
      · rw [segJoin_out _ _ hin']
        exact inTupleSpace_meetT hLk _ j' (lt_of_not_seg hj' hin')
    refine hmono _ _ hspace1 hspace2 ?_ j hj
    intro j' hj'
    by_cases hin' : k ≤ j' ∧ j' < k + n
    · rw [segJoin_in _ _ hin', segJoin_in _ _ hin']; exact FamLe.refl _ _
    · rw [segJoin_out _ _ hin', segJoin_out _ _ hin']
      exact meetT_eq_of_le (lfpTuple_composeΦ_le hmono hcl) j' (lt_of_not_seg hj' hin')
  · -- a member: the composed operator's closure
    rw [extT, segJoin_out _ _ hin]
    have := lfpTuple_closed hccl hcmono j (by omega)
    rw [composeΦ_apply] at this
    exact this

/-- **Bekić, nested form, the members**: the composed least tuple's
members are the auxiliary least tuple's. -/
theorem lfpTuple_composeΦ {m : Nat} (hm : m < k) :
    lfpTuple w k Is (composeΦ w k n Is Ψ) m = lfpTuple w (k + n) Is Ψ m := by
  have hLmem := lfpTuple_mem w (k + n) Is Ψ
  have hLk := lfpTuple_mem w k Is (composeΦ w k n Is Ψ)
  have h₁ := lfpTuple_composeΦ_le hmono hcl m hm
  have h₂ := lfpTuple_le (isClosedTuple_extT_lfp hmono hcl) m (by omega)
  rw [extT_lt hm] at h₂
  exact famSpace_ext (hLk m hm) (hLmem m (by omega)) fun i hi =>
    Subset.antisymm (h₁ i hi) (h₂ i hi)

/-- **Bekić, nested form, the pins**: the pins' carriers at the composed
least tuple are the auxiliary least tuple's pin components. -/
theorem pinsCar_lfp {q : Nat} (hq : q < n) :
    pinsCar w k n Is Ψ (lfpTuple w k Is (composeΦ w k n Is Ψ)) q = lfpTuple w (k + n) Is Ψ (k + q) := by
  have hLmem := lfpTuple_mem w (k + n) Is Ψ
  have hLk := lfpTuple_mem w k Is (composeΦ w k n Is Ψ)
  have h₁ := pinsCar_le_aux hmono hcl hLk q hq
  rw [segOf_apply] at h₁
  have h₂ := lfpTuple_le (isClosedTuple_extT_lfp hmono hcl) (k + q) (by omega)
  rw [extT_add hq] at h₂
  exact famSpace_ext (pinsCar_mem _ q hq) (hLmem (k + q) (by omega)) fun i hi =>
    Subset.antisymm (h₁ i hi) (h₂ i hi)

/-- **The extended tuple at the composed least tuple IS the auxiliary
least tuple** (on the block's positions). -/
theorem extT_lfp {j : Nat} (hj : j < k + n) :
    extT w k n Is Ψ (lfpTuple w k Is (composeΦ w k n Is Ψ)) j = lfpTuple w (k + n) Is Ψ j := by
  by_cases hjk : j < k
  · rw [extT_lt hjk]; exact lfpTuple_composeΦ hmono hcl hjk
  · have : j = k + (j - k) := by omega
    rw [this, extT_add (by omega)]
    exact pinsCar_lfp hmono hcl (by omega)

end Laws

end Compose

/-! ## The pins' section as a fibre and as an induction (task #315, M7) -/

section PinLaws

variable {w k n : Nat} {Is : Nat → V} {Ψ : (Nat → V) → Nat → V}

/-- The tuple the pins' operator reads at `X` — the members CLAMPED
(`meetT`), the pins at `S` — is in the tuple space. -/
theorem inTupleSpace_pinsJoin {X S : Nat → V} (hX : InTupleSpace w k Is X)
    (hS : InTupleSpace w n (fun q => Is (k + q)) S) :
    InTupleSpace w (k + n) Is (segJoin k n (meetT Is X (lfpTuple w (k + n) Is Ψ)) S) :=
  inTupleSpace_segJoin' (fun j hj hout => inTupleSpace_meetT hX _ j (lt_of_not_seg hj hout)) hS

/-- The honest join — the members at `X`, the pins at `S` — is in the
tuple space. -/
theorem inTupleSpace_join {X S : Nat → V} (hX : InTupleSpace w k Is X)
    (hS : InTupleSpace w n (fun q => Is (k + q)) S) :
    InTupleSpace w (k + n) Is (segJoin k n X S) :=
  inTupleSpace_segJoin' (fun j hj hout => hX j (lt_of_not_seg hj hout)) hS

/-- The clamped join is below the honest one. -/
theorem pinsJoin_le (X S : Nat → V) :
    TupleLe (k + n) Is (segJoin k n (meetT Is X (lfpTuple w (k + n) Is Ψ)) S) (segJoin k n X S) := by
  intro j hj
  by_cases hin : k ≤ j ∧ j < k + n
  · rw [segJoin_in _ _ hin, segJoin_in _ _ hin]; exact FamLe.refl _ _
  · rw [segJoin_out _ _ hin, segJoin_out _ _ hin]
    exact meetT_le_left (k := k) X _ j (lt_of_not_seg hj hin)

section PinLawsFacts

variable (hmono : MonoTuple w (k + n) Is Ψ) (hmaps : MapsTuple w (k + n) Is Ψ)
  (hcl : ∃ L, IsClosedTuple w (k + n) Is Ψ L)

include hmono hmaps hcl

omit hmono hcl in
/-- The pins' operator preserves the pins' tuple space. -/
theorem pinsOp_maps {X : Nat → V} (hX : InTupleSpace w k Is X) :
    MapsTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) :=
  fun Y hY q hq => hmaps _ (inTupleSpace_pinsJoin hX hY) (k + q) (by omega)

omit hmaps hcl in
/-- **The clamp is invisible below the auxiliary carrier**: at `X` below
`L⁺` the fibres of `Ψ` at the clamped join and at the honest join
agree. -/
theorem app_pinsJoin_eq {X S : Nat → V} (hX : InTupleSpace w k Is X)
    (hXL : TupleLe k Is X (lfpTuple w (k + n) Is Ψ))
    (hS : InTupleSpace w n (fun q => Is (k + q)) S) {j : Nat} (hj : j < k + n) {t : V}
    (ht : t ∈ˢ Is j) :
    SetTheory.app (Ψ (segJoin k n (meetT Is X (lfpTuple w (k + n) Is Ψ)) S) j) t
      = SetTheory.app (Ψ (segJoin k n X S) j) t := by
  have hge : TupleLe (k + n) Is (segJoin k n X S)
      (segJoin k n (meetT Is X (lfpTuple w (k + n) Is Ψ)) S) := by
    intro j' hj'
    by_cases hin : k ≤ j' ∧ j' < k + n
    · rw [segJoin_in _ _ hin, segJoin_in _ _ hin]; exact FamLe.refl _ _
    · rw [segJoin_out _ _ hin, segJoin_out _ _ hin]
      exact meetT_eq_of_le hXL j' (lt_of_not_seg hj' hin)
  exact Subset.antisymm
    (hmono _ _ (inTupleSpace_pinsJoin hX hS) (inTupleSpace_join hX hS) (pinsJoin_le X S) j hj t ht)
    (hmono _ _ (inTupleSpace_join hX hS) (inTupleSpace_pinsJoin hX hS) hge j hj t ht)

/-- **The pins' fixed-point law** (DESIGN §U.25 (e) 1): at a members'
tuple below the auxiliary carrier a pin's carrier is `Ψ`'s fibre at
the EXTENDED tuple — the pins' section is closed, and the clamp is
invisible there. -/
theorem app_pinsCar_eq {X : Nat → V} (hX : InTupleSpace w k Is X)
    (hXL : TupleLe k Is X (lfpTuple w (k + n) Is Ψ)) {q : Nat} (hq : q < n) {t : V}
    (ht : t ∈ˢ Is (k + q)) :
    SetTheory.app (pinsCar w k n Is Ψ X q) t
      = SetTheory.app (Ψ (extT w k n Is Ψ X) (k + q)) t := by
  have hfix := app_lfpTuple_eq (pinsOp_closed_exists hmono hcl hX) (pinsOp_mono hmono hX)
    (pinsOp_maps hmaps hX) hq ht
  rw [show pinsCar w k n Is Ψ X = lfpTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) from rfl,
    ← hfix]
  exact app_pinsJoin_eq hmono hX hXL (pinsCar_mem X) (by omega) ht

omit hmaps in
/-- **The pins' induction** (DESIGN §U.25 (e) 1): the pins' carriers at
`X` are the LEAST families closed under `Ψ`'s pin fibres with the
members read at `X` and the pins at the separated carriers — the
clamp only WEAKENS the step, so the honest join may be read. -/
theorem pinsCar_induction {X : Nat → V} (hX : InTupleSpace w k Is X) (P : Nat → V → V → Prop)
    (hP : ∀ q, q < n → ∀ t, t ∈ˢ Is (k + q) → ∀ x,
      x ∈ˢ SetTheory.app
          (Ψ (segJoin k n X (sepTuple w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) P))
            (k + q)) t →
        P q t x) :
    ∀ q, q < n → ∀ t, t ∈ˢ Is (k + q) → ∀ x,
      x ∈ˢ SetTheory.app (pinsCar w k n Is Ψ X q) t → P q t x := by
  refine lfpTuple_induction (pinsOp_closed_exists hmono hcl hX) (pinsOp_mono hmono hX) P ?_
  intro q hq t ht x hx
  refine hP q hq t ht x ?_
  have hS := sepTuple_mem w n (fun q => Is (k + q)) (pinsOp w k n Is Ψ X) P
  exact hmono _ _ (inTupleSpace_pinsJoin hX hS) (inTupleSpace_join hX hS)
    (pinsJoin_le X _) (k + q) (by omega) t ht x hx

omit hmaps in
/-- **The pins' carriers at the block's carrier lie below any tuple of
the pins' space closed under the pins' section at the carrier**
(task #315 L-E, DESIGN §U.36 step (ii)): with `L` the composed least
tuple and `P` a tuple of pin families with `Ψ (segJoin k n L P) (k + q)
≤ P q` at every pin, the auxiliary least tuple's pin components lie
below `P` — `P` closes the pins' operator at `L` (the clamp is the
identity there, `L ≤ L⁺`), so `pinsCar L ≤ P` by leastness, and
`pinsCar L` IS the auxiliary carrier's pin segment (`pinsCar_lfp`). -/
theorem lfp_pins_le_of_section_closed {P : Nat → V}
    (hP : InTupleSpace w n (fun q => Is (k + q)) P)
    (hcl' : ∀ q, q < n →
      FamLe (Is (k + q)) (Ψ (segJoin k n (lfpTuple w k Is (composeΦ w k n Is Ψ)) P) (k + q)) (P q)) :
    ∀ q, q < n → FamLe (Is (k + q)) (lfpTuple w (k + n) Is Ψ (k + q)) (P q) := by
  intro q hq
  rw [← pinsCar_lfp hmono hcl hq]
  refine lfpTuple_le ⟨hP, fun q' hq' => ?_⟩ q hq
  rw [pinsOp, segSec_apply]
  refine FamLe.trans ?_ (hcl' q' hq')
  have hL := lfpTuple_mem w k Is (composeΦ w k n Is Ψ)
  exact hmono _ _ (inTupleSpace_pinsJoin hL hP) (inTupleSpace_join hL hP) (pinsJoin_le _ _)
    (k + q') (by omega)

end PinLawsFacts

end PinLaws

/-! ## The least tuple pulled back along a map of variables (task #315 L-E, DESIGN §U.48 (d)) -/

/-- **The fibre meet**: the base tuple's component `i` cut down to the
elements every component of `Y` above `i` (under `σ`, below `k'`)
carries — `famMeet` over a finite fibre, `sep`-shaped so it stays in
the space. -/
noncomputable def fibreMeet (Is X : Nat → V) (σ : Nat → Nat) (k' : Nat) (Y : Nat → V) (i : Nat) : V :=
  graph (fun t => sep (app (X i) t) fun x => ∀ j, j < k' → σ j = i → x ∈ˢ app (Y j) t) (Is i)

theorem app_fibreMeet {Is X : Nat → V} {σ : Nat → Nat} {k' : Nat} {Y : Nat → V} {i : Nat} {t : V}
    (ht : t ∈ˢ Is i) :
    app (fibreMeet Is X σ k' Y i) t
      = sep (app (X i) t) fun x => ∀ j, j < k' → σ j = i → x ∈ˢ app (Y j) t :=
  app_graph ht

theorem fibreMeet_mem {w : Nat} {Is X : Nat → V} {σ : Nat → Nat} {k' : Nat} {Y : Nat → V} {i : Nat}
    (hX : X i ∈ˢ famSpace w (Is i)) : fibreMeet Is X σ k' Y i ∈ˢ famSpace w (Is i) :=
  graph_mem_famSpace fun _ ht => univ_sep_mem (famSpace_app hX ht)

theorem fibreMeet_le_base (Is X : Nat → V) (σ : Nat → Nat) (k' : Nat) (Y : Nat → V) (i : Nat) :
    FamLe (Is i) (fibreMeet Is X σ k' Y i) (X i) := by
  intro t ht
  rw [app_fibreMeet ht]
  exact sep_subset

theorem fibreMeet_le_fibre {Is X : Nat → V} {σ : Nat → Nat} {k' : Nat} {Y : Nat → V} {i j : Nat}
    (hj : j < k') (hσ : σ j = i) : FamLe (Is i) (fibreMeet Is X σ k' Y i) (Y j) := by
  intro t ht x hx
  rw [app_fibreMeet ht] at hx
  exact (mem_sep.mp hx).2 j hj hσ

theorem famLe_fibreMeet {Is X : Nat → V} {σ : Nat → Nat} {k' : Nat} {Y : Nat → V} {i : Nat} {C : V}
    (h₀ : FamLe (Is i) C (X i)) (h : ∀ j, j < k' → σ j = i → FamLe (Is i) C (Y j)) :
    FamLe (Is i) C (fibreMeet Is X σ k' Y i) := by
  intro t ht x hx
  rw [app_fibreMeet ht]
  exact mem_sep.mpr ⟨h₀ t ht x hx, fun j hj hσ => h j hj hσ t ht x hx⟩

/-- **The least tuple of a system pulled back along a map of variables**
(task #315 L-E, DESIGN §U.48 (d)): a system `Φ'` over `k'` variables
whose operator at a tuple pulled back along `σ : [0,k') → [0,k)` is the
pullback of `Φ`'s (`hpull`, at every tuple in the space BELOW `Φ`'s
least tuple — all the argument visits), with the
index sets pulled back too, has as least tuple the pullback of `Φ`'s —
variables renamed or DUPLICATED along `σ` change nothing.  `(lfp Φ) ∘ σ`
is `Φ'`-closed; conversely `fibreMeet` (the base least tuple cut down
to every fibre's `lfp Φ'` components) is `Φ`-closed, so `lfp Φ` lies
below it and hence below `lfp Φ'` at every variable of the fibre.  No
surjectivity is needed: outside `σ`'s image the fibre meet is the base
least tuple itself. -/
theorem lfpTuple_pullback {w k k' : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}
    {σ : Nat → Nat} (hσ : ∀ j, j < k' → σ j < k)
    (hIs : ∀ j, j < k' → Is' j = Is (σ j))
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ)
    (hcl : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono' : MonoTuple w k' Is' Φ') (hmaps' : MapsTuple w k' Is' Φ')
    (hcl' : ∃ L', IsClosedTuple w k' Is' Φ' L')
    (hpull : ∀ X, InTupleSpace w k Is X → TupleLe k Is X (lfpTuple w k Is Φ) →
      ∀ j, j < k' → Φ' (fun j' => X (σ j')) j = Φ X (σ j)) :
    ∀ j, j < k' → lfpTuple w k' Is' Φ' j = lfpTuple w k Is Φ (σ j) := by
  intro j hj
  -- the pullback of the base least tuple is closed
  have hX'mem : InTupleSpace w k' Is' (fun j' => lfpTuple w k Is Φ (σ j')) := by
    intro j' hj'
    rw [hIs j' hj']
    exact lfpTuple_mem w k Is Φ _ (hσ j' hj')
  have hX'cl : IsClosedTuple w k' Is' Φ' (fun j' => lfpTuple w k Is Φ (σ j')) := by
    refine ⟨hX'mem, fun j' hj' => ?_⟩
    show FamLe (Is' j') (Φ' (fun j'' => lfpTuple w k Is Φ (σ j'')) j') (lfpTuple w k Is Φ (σ j'))
    rw [hpull _ (lfpTuple_mem w k Is Φ) (TupleLe.refl _ _ _) j' hj',
      lfpTuple_eq hcl hmono hmaps (hσ j' hj')]
    exact FamLe.refl _ _
  have h1 := lfpTuple_le hX'cl j hj
  -- the fibre meet is closed under the base operator
  have hTmem : InTupleSpace w k Is (fibreMeet Is (lfpTuple w k Is Φ) σ k' (lfpTuple w k' Is' Φ')) :=
    fun i hi => fibreMeet_mem (lfpTuple_mem w k Is Φ i hi)
  have hTσ : ∀ j', j' < k' →
      FamLe (Is' j') (fibreMeet Is (lfpTuple w k Is Φ) σ k' (lfpTuple w k' Is' Φ') (σ j'))
        (lfpTuple w k' Is' Φ' j') := by
    intro j' hj'
    rw [hIs j' hj']
    exact fibreMeet_le_fibre hj' rfl
  have hTσmem : InTupleSpace w k' Is'
      (fun j' => fibreMeet Is (lfpTuple w k Is Φ) σ k' (lfpTuple w k' Is' Φ') (σ j')) := by
    intro j' hj'
    rw [hIs j' hj']
    exact hTmem _ (hσ j' hj')
  have hTcl : IsClosedTuple w k Is Φ (fibreMeet Is (lfpTuple w k Is Φ) σ k' (lfpTuple w k' Is' Φ')) := by
    refine ⟨hTmem, fun i hi => famLe_fibreMeet ?_ fun j' hj' hσj => ?_⟩
    · have := hmono _ _ hTmem (lfpTuple_mem w k Is Φ)
        (fun i' hi' => fibreMeet_le_base Is _ σ k' _ i') i hi
      rw [lfpTuple_eq hcl hmono hmaps hi] at this
      exact this
    · have e := hpull _ hTmem (fun i' hi' => fibreMeet_le_base Is _ σ k' _ i') j' hj'
      rw [hσj] at e
      rw [← e]
      have := hmono' _ _ hTσmem (lfpTuple_mem w k' Is' Φ') hTσ j' hj'
      rw [lfpTuple_eq hcl' hmono' hmaps' hj', hIs j' hj', hσj] at this
      exact this
  have h2 := lfpTuple_le hTcl (σ j) (hσ j hj)
  have h3 := hTσ j hj
  -- the two least tuples agree at `j`
  refine famSpace_ext (lfpTuple_mem w k' Is' Φ' j hj)
    (by rw [hIs j hj]; exact lfpTuple_mem w k Is Φ _ (hσ j hj)) fun t ht => ?_
  refine Subset.antisymm (h1 t ht) ?_
  have ht' : t ∈ˢ Is (σ j) := by rw [← hIs j hj]; exact ht
  exact (h2 t ht').trans (h3 t ht)

/-! ## Two least tuples agreeing along a RELATION of variables (task #315 L-E, DESIGN §U.48 (h)) -/

/-- **The relational fibre meet**: the base tuple's component `a` cut
down to the elements every component `Y b` with `R a b` (`b < k'`)
carries. -/
noncomputable def relMeet (Is X : Nat → V) (R : Nat → Nat → Prop) (k' : Nat) (Y : Nat → V) (a : Nat) : V :=
  graph (fun t => sep (app (X a) t) fun x => ∀ b, b < k' → R a b → x ∈ˢ app (Y b) t) (Is a)

theorem app_relMeet {Is X : Nat → V} {R : Nat → Nat → Prop} {k' : Nat} {Y : Nat → V} {a : Nat} {t : V}
    (ht : t ∈ˢ Is a) :
    app (relMeet Is X R k' Y a) t = sep (app (X a) t) fun x => ∀ b, b < k' → R a b → x ∈ˢ app (Y b) t :=
  app_graph ht

theorem relMeet_mem {w : Nat} {Is X : Nat → V} {R : Nat → Nat → Prop} {k' : Nat} {Y : Nat → V} {a : Nat}
    (hX : X a ∈ˢ famSpace w (Is a)) : relMeet Is X R k' Y a ∈ˢ famSpace w (Is a) :=
  graph_mem_famSpace fun _ ht => univ_sep_mem (famSpace_app hX ht)

/-- The relational meet lies under the base at EVERY point — off the
index set it is empty (task #315 L-E: `ChainFitT_mono` compares the
tuples at every point, not only inside the index sets). -/
theorem app_relMeet_subset (Is X : Nat → V) (R : Nat → Nat → Prop) (k' : Nat) (Y : Nat → V)
    (a : Nat) (t : V) : app (relMeet Is X R k' Y a) t ⊆ˢ app (X a) t := by
  by_cases ht : t ∈ˢ Is a
  · rw [app_relMeet ht]
    exact sep_subset
  · unfold relMeet
    rw [app_graph_of_not_mem ht]
    exact fun x hx => absurd hx (not_mem_empty x)

theorem relMeet_le_base (Is X : Nat → V) (R : Nat → Nat → Prop) (k' : Nat) (Y : Nat → V) (a : Nat) :
    FamLe (Is a) (relMeet Is X R k' Y a) (X a) := by
  intro t ht
  rw [app_relMeet ht]
  exact sep_subset

theorem relMeet_le_rel {Is X : Nat → V} {R : Nat → Nat → Prop} {k' : Nat} {Y : Nat → V} {a b : Nat}
    (hb : b < k') (hR : R a b) : FamLe (Is a) (relMeet Is X R k' Y a) (Y b) := by
  intro t ht x hx
  rw [app_relMeet ht] at hx
  exact (mem_sep.mp hx).2 b hb hR

theorem famLe_relMeet {Is X : Nat → V} {R : Nat → Nat → Prop} {k' : Nat} {Y : Nat → V} {a : Nat} {C : V}
    (h₀ : FamLe (Is a) C (X a)) (h : ∀ b, b < k' → R a b → FamLe (Is a) C (Y b)) :
    FamLe (Is a) C (relMeet Is X R k' Y a) := by
  intro t ht x hx
  rw [app_relMeet ht]
  exact mem_sep.mpr ⟨h₀ t ht x hx, fun b hb hR => h b hb hR t ht x hx⟩

/-- **One direction of the bisimulation**: if `Φ'` is `R`-monotone over
`Φ` at a FIXED POINT `F'` of `Φ'` — at tuples `X` below `Φ`'s least
tuple, `X ≤_R F'` gives `Φ X a ≤ Φ' F' b` at every related pair — then
`Φ`'s least tuple lies below `F'` at every related pair (`relMeet` is
`Φ`-closed).  Stated at a fixed point rather than the least tuple so a
CARRIER (a fixed point of the whole system) can stand on the right
without its restriction being shown least. -/
theorem lfpTuple_le_of_rel {w k k' : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}
    {R : Nat → Nat → Prop} {F' : Nat → V}
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ)
    (hcl : ∃ L, IsClosedTuple w k Is Φ L)
    (_hF' : InTupleSpace w k' Is' F') (hfix : ∀ b, b < k' → Φ' F' b = F' b)
    (hrel : ∀ X, InTupleSpace w k Is X → TupleLe k Is X (lfpTuple w k Is Φ) →
      (∀ a b, a < k → b < k' → R a b → FamLe (Is a) (X a) (F' b)) →
      ∀ a b, a < k → b < k' → R a b → FamLe (Is a) (Φ X a) (Φ' F' b)) :
    ∀ a b, a < k → b < k' → R a b → FamLe (Is a) (lfpTuple w k Is Φ a) (F' b) := by
  intro a b ha hb hab
  have hTmem : InTupleSpace w k Is (relMeet Is (lfpTuple w k Is Φ) R k' F') :=
    fun a' ha' => relMeet_mem (lfpTuple_mem w k Is Φ a' ha')
  have hTle : TupleLe k Is (relMeet Is (lfpTuple w k Is Φ) R k' F') (lfpTuple w k Is Φ) :=
    fun a' _ => relMeet_le_base Is _ R k' _ a'
  have hTcl : IsClosedTuple w k Is Φ (relMeet Is (lfpTuple w k Is Φ) R k' F') := by
    refine ⟨hTmem, fun a' ha' => famLe_relMeet ?_ fun b' hb' hab' => ?_⟩
    · have := hmono _ _ hTmem (lfpTuple_mem w k Is Φ) hTle a' ha'
      rw [lfpTuple_eq hcl hmono hmaps ha'] at this
      exact this
    · have := hrel _ hTmem hTle (fun a'' b'' _ hb'' hab'' => relMeet_le_rel hb'' hab'') a' b' ha' hb' hab'
      rw [hfix b' hb'] at this
      exact this
  exact (lfpTuple_le hTcl a ha).trans (relMeet_le_rel hb hab)

/-- **Two least tuples agree along a bisimulation of their variables**
(task #315 L-E, DESIGN §U.48 (h)): related variables have related
index sets, and each operator is `R`-monotone over the other at tuples
below the least tuples; then the least tuples agree at every related
pair.  Duplicated variables on EITHER side (several `b` related to one
`a`, or several `a` to one `b`) are absorbed by the relational meets —
no function between the variable sets is needed. -/
theorem lfpTuple_eq_of_rel {w k k' : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}
    {R : Nat → Nat → Prop}
    (hIs : ∀ a b, a < k → b < k' → R a b → Is a = Is' b)
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ)
    (hcl : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono' : MonoTuple w k' Is' Φ') (hmaps' : MapsTuple w k' Is' Φ')
    (hcl' : ∃ L', IsClosedTuple w k' Is' Φ' L')
    (hrel : ∀ X, InTupleSpace w k Is X → TupleLe k Is X (lfpTuple w k Is Φ) →
      ∀ X', InTupleSpace w k' Is' X' → TupleLe k' Is' X' (lfpTuple w k' Is' Φ') →
      (∀ a b, a < k → b < k' → R a b → FamLe (Is a) (X a) (X' b)) →
      ∀ a b, a < k → b < k' → R a b → FamLe (Is a) (Φ X a) (Φ' X' b))
    (hrel' : ∀ X', InTupleSpace w k' Is' X' → TupleLe k' Is' X' (lfpTuple w k' Is' Φ') →
      ∀ X, InTupleSpace w k Is X → TupleLe k Is X (lfpTuple w k Is Φ) →
      (∀ b a, b < k' → a < k → R a b → FamLe (Is' b) (X' b) (X a)) →
      ∀ b a, b < k' → a < k → R a b → FamLe (Is' b) (Φ' X' b) (Φ X a)) :
    ∀ a b, a < k → b < k' → R a b → lfpTuple w k Is Φ a = lfpTuple w k' Is' Φ' b := by
  intro a b ha hb hab
  have h1 := lfpTuple_le_of_rel hmono hmaps hcl (lfpTuple_mem w k' Is' Φ')
    (fun b' hb' => lfpTuple_eq hcl' hmono' hmaps' hb')
    (fun X hX hXle hle => hrel X hX hXle _ (lfpTuple_mem w k' Is' Φ') (TupleLe.refl _ _ _) hle)
    a b ha hb hab
  have h2 := lfpTuple_le_of_rel (R := fun b a => R a b) hmono' hmaps' hcl' (lfpTuple_mem w k Is Φ)
    (fun a' ha' => lfpTuple_eq hcl hmono hmaps ha')
    (fun X' hX' hX'le hle => hrel' X' hX' hX'le _ (lfpTuple_mem w k Is Φ) (TupleLe.refl _ _ _) hle)
    b a hb ha hab
  refine famSpace_ext (lfpTuple_mem w k Is Φ a ha)
    (by rw [hIs a b ha hb hab]; exact lfpTuple_mem w k' Is' Φ' b hb) fun t ht => ?_
  have ht' : t ∈ˢ Is' b := by rw [← hIs a b ha hb hab]; exact ht
  exact Subset.antisymm (h1 t ht) (h2 t ht')

/-- **The relational meet lies under a related family at EVERY point**
(task #315 L-E, DESIGN §U.72): `relMeet_le_rel` off the index set too,
where the meet is empty — the container instance transfer's walk
compares the two tuples at every point, not only inside the index sets
(`app_relMeet_subset`'s twin at a related pair). -/
theorem app_relMeet_le_rel {Is X : Nat → V} {R : Nat → Nat → Prop} {k' : Nat} {Y : Nat → V}
    {a b : Nat} (hb : b < k') (hR : R a b) (t : V) :
    app (relMeet Is X R k' Y a) t ⊆ˢ app (Y b) t := by
  by_cases ht : t ∈ˢ Is a
  · exact relMeet_le_rel hb hR t ht
  · unfold relMeet
    rw [app_graph_of_not_mem ht]
    exact fun x hx => absurd hx (not_mem_empty x)


end ConLeche.SetTheory
