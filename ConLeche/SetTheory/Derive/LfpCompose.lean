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

end ConLeche.SetTheory
