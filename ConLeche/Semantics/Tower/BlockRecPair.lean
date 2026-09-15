module

public import ConLeche.Semantics.Tower.FixRecCoreI
public import ConLeche.SetModel.MutualPair
@[expose] public section

/-!
# The two-member block's recursors as TERMS, ι-specified (task #315, M3's falsifier)

The uniform route's recursors are ONE chosen tuple, pinned by its ι
EQUATIONS rather than by a one-step unfolding:

    Tup  := Σ' (r₀ : RecTy₀) … (r_{k-1} : RecTy_{k-1}), Eqs
    Eqs  := ⋀_J  Π p⃗ M⃗ m⃗ f⃗_J, r_{m_J} p⃗ M⃗ m⃗ e⃗_J(f⃗) (C_J f⃗) = rhs_J p⃗ M⃗ m⃗ f⃗
    Sel  := choice Tup prf
    A mm := fst (snd^mm Sel)

Existence is the block's union recursor (`SetModel/UnionRec.lean`);
typing and every ι rule are read off the Σ' membership of the chosen
element.  No case split, no K-frame body, no squash body.

This file is the falsifying experiment at the two-member MUTUAL block
`A ::= a0 | a1 (b : B)`, `B ::= b0 (a : A)` of `SetModel/MutualPair.lean`
(`PairSig`): the two recursor types at official's shape — motives for
BOTH members, minors for ALL constructors, the major per member —

    T_A := Π (MA : A → Sort ℓ) (MB : B → Sort ℓ) (mA0 : MA a0)
             (mA1 : Π b, MB b → MA (a1 b)) (mB0 : Π a, MA a → MB (b0 a)) (t : A), MA t
    T_B := … (t : B), MB t

the Σ'-chain `sig = Σ' (rA : T_A) (rB : T_B), eqA0 ∧ eqA1 ∧ eqB0`,
`sel = choice sig prf`, `recA = fst sel`, `recB = fst (snd sel)`.  The
carriers and constructors are the five values of a base frame
(`pairFrame`), referenced by de Bruijn index — the closed-term
analogue of the constructors' leaves in the general spelling.

**PASSED** (`pairRecTerms`): at every elimination level `ℓ` (both
regimes) and every ambient frame, `⟦recA⟧ ∈ ⟦T_A⟧`, `⟦recB⟧ ∈ ⟦T_B⟧`,
both graded, and the three ι rules at every official spine.  The
semantic content is exactly `MutualPair`'s: the candidate tuple's
components are the λ-towers over the recursor types' binder data whose
leaf is `unionRec` at the frame's motives and minors (`candA`/`candB`),
typed by `pairRecA_mem`/`pairRecB_mem`, and the three equations hold at
the candidate by `pairRecA_a0`/`pairRecA_a1`/`pairRecB_b0`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

namespace BlockRecPair

/-! ## The terms

The base frame holds, from index `0` up: `b0` (as a function on `A`),
`a1` (as a function on `B`), `a0`, `B`, `A`.  A term at depth `d`
reaches them at `d + i`. -/

/-- The carrier `A` at depth `d`. -/
def tA (d : Nat) : AnnotTerm := .bvar (d + 4)
/-- The carrier `B` at depth `d`. -/
def tB (d : Nat) : AnnotTerm := .bvar (d + 3)
/-- The constructor `a0` at depth `d`. -/
def ca0 (d : Nat) : AnnotTerm := .bvar (d + 2)
/-- The constructor `a1` (a function on `B`) at depth `d`. -/
def ca1 (d : Nat) : AnnotTerm := .bvar (d + 1)
/-- The constructor `b0` (a function on `A`) at depth `d`. -/
def cb0 (d : Nat) : AnnotTerm := .bvar d

/-- `A → Sort ℓ` at depth `d`. -/
def motA (w ℓ d : Nat) : AnnotTerm := .pi w (ℓ + 1) (tA d) (.sort ℓ)
/-- `B → Sort ℓ` at depth `d`. -/
def motB (w ℓ d : Nat) : AnnotTerm := .pi w (ℓ + 1) (tB d) (.sort ℓ)
/-- `MA a0` under `MA MB` (the rec binders start at depth `d`). -/
def minA0 (d : Nat) : AnnotTerm := .app (.bvar 1) (ca0 (d + 2))
/-- `Π (b : B), MB b → MA (a1 b)` under `MA MB mA0`. -/
def minA1 (w ℓ d : Nat) : AnnotTerm :=
  .pi w ℓ (tB (d + 3))
    (.pi ℓ ℓ (.app (.bvar 2) (.bvar 0)) (.app (.bvar 4) (.app (ca1 (d + 5)) (.bvar 1))))
/-- `Π (a : A), MA a → MB (b0 a)` under `MA MB mA0 mA1`. -/
def minB0 (w ℓ d : Nat) : AnnotTerm :=
  .pi w ℓ (tA (d + 4))
    (.pi ℓ ℓ (.app (.bvar 4) (.bvar 0)) (.app (.bvar 4) (.app (cb0 (d + 6)) (.bvar 1))))

/-- The five shared binders `MA MB mA0 mA1 mB0` of both recursor types,
with codomain bit `bit`, starting at depth `d`. -/
def rds5 (w ℓ bit d : Nat) : List (Nat × Nat × AnnotTerm) :=
  [(Nat.max w (ℓ + 1), bit, motA w ℓ d), (Nat.max w (ℓ + 1), bit, motB w ℓ (d + 1)),
   (ℓ, bit, minA0 d), (ℓ, bit, minA1 w ℓ d), (ℓ, bit, minB0 w ℓ d)]

/-- `A.rec`'s binder data: the five, then the major `t : A`. -/
def rdsA (w ℓ : Nat) : List (Nat × Nat × AnnotTerm) := rds5 w ℓ ℓ 0 ++ [(w, ℓ, tA 5)]
/-- `B.rec`'s binder data. -/
def rdsB (w ℓ : Nat) : List (Nat × Nat × AnnotTerm) := rds5 w ℓ ℓ 0 ++ [(w, ℓ, tB 5)]
/-- `MA t`. -/
def concA : AnnotTerm := .app (.bvar 5) (.bvar 0)
/-- `MB t`. -/
def concB : AnnotTerm := .app (.bvar 4) (.bvar 0)
/-- **`A.rec`'s type** at official's shape. -/
def TA (w ℓ : Nat) : AnnotTerm := mkPisAV (rdsA w ℓ) concA
/-- **`B.rec`'s type** at official's shape. -/
def TB (w ℓ : Nat) : AnnotTerm := mkPisAV (rdsB w ℓ) concB

/-- The shared spine `MA MB mA0 mA1 mB0` seen from directly under it. -/
def spine7 : List AnnotTerm := [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
/-- The shared spine seen from under one more binder. -/
def spine8 : List AnnotTerm := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]

/-- `rA MA MB mA0 mA1 mB0 a0` (rec binders under the two tuple binders). -/
def lhsA0 : AnnotTerm := AnnotTerm.mkAppN (.bvar 6) (spine7 ++ [ca0 7])
/-- `mA0`. -/
def rhsA0 : AnnotTerm := .bvar 2
/-- `rA MA MB mA0 mA1 mB0 (a1 b)` under `b`. -/
def lhsA1 : AnnotTerm := AnnotTerm.mkAppN (.bvar 7) (spine8 ++ [.app (ca1 8) (.bvar 0)])
/-- `mA1 b (rB MA MB mA0 mA1 mB0 b)`. -/
def rhsA1 : AnnotTerm :=
  .app (.app (.bvar 2) (.bvar 0)) (AnnotTerm.mkAppN (.bvar 6) (spine8 ++ [.bvar 0]))
/-- `rB MA MB mA0 mA1 mB0 (b0 a)` under `a`. -/
def lhsB0 : AnnotTerm := AnnotTerm.mkAppN (.bvar 6) (spine8 ++ [.app (cb0 8) (.bvar 0)])
/-- `mB0 a (rA MA MB mA0 mA1 mB0 a)`. -/
def rhsB0 : AnnotTerm :=
  .app (.app (.bvar 1) (.bvar 0)) (AnnotTerm.mkAppN (.bvar 7) (spine8 ++ [.bvar 0]))

/-- The ι equation of `a0`, under the two tuple binders `rA rB`. -/
def eqA0 (w ℓ : Nat) : AnnotTerm := mkPisAV (rds5 w ℓ 0 2) (.eqE lhsA0 rhsA0)
/-- The ι equation of `a1`. -/
def eqA1 (w ℓ : Nat) : AnnotTerm :=
  mkPisAV (rds5 w ℓ 0 2 ++ [(w, 0, tB 7)]) (.eqE lhsA1 rhsA1)
/-- The ι equation of `b0`. -/
def eqB0 (w ℓ : Nat) : AnnotTerm :=
  mkPisAV (rds5 w ℓ 0 2 ++ [(w, 0, tA 7)]) (.eqE lhsB0 rhsB0)

/-- Conjunction of propositions: `Σ' (_ : P), Q` at `Prop`. -/
def andAV (P Q : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [0, 0]) [P, .lam 1 P (Q.liftN 1 0)]

/-- The three ι equations. -/
def eqs (w ℓ : Nat) : AnnotTerm := andAV (eqA0 w ℓ) (andAV (eqA1 w ℓ) (eqB0 w ℓ))

/-- The recursor types' sort. -/
def sLev (w ℓ : Nat) : Nat := if ℓ = 0 then 0 else Nat.max w (ℓ + 1)

/-- `Σ' (rB : T_B), eqs`, under `rA`. -/
def inner (w ℓ : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [sLev w ℓ, 0])
    [(TB w ℓ).liftN 1 0, .lam 1 ((TB w ℓ).liftN 1 0) (eqs w ℓ)]

/-- **The Σ'-chain** `Σ' (rA : T_A) (rB : T_B), eqA0 ∧ eqA1 ∧ eqB0`. -/
def sig (w ℓ : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [sLev w ℓ, sLev w ℓ])
    [TA w ℓ, .lam (sLev w ℓ + 1) (TA w ℓ) (inner w ℓ)]

/-- **The chosen tuple** `choice sig prf`. -/
def sel (w ℓ : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .choice [sLev w ℓ]) [sig w ℓ, .prf]

/-- **`A.rec`'s leaf**: the tuple's first component. -/
def recA (w ℓ : Nat) : AnnotTerm := .fst (sel w ℓ)
/-- **`B.rec`'s leaf**: the tuple's second component. -/
def recB (w ℓ : Nat) : AnnotTerm := .fst (.snd (sel w ℓ))

omit [SetTheory V] in
theorem sLev_zero_iff (w ℓ : Nat) : sLev w ℓ = 0 ↔ ℓ = 0 := by
  unfold sLev
  by_cases h : ℓ = 0
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h0 => absurd (Nat.le_zero.mp (h0 ▸ Nat.le_max_right w (ℓ + 1))) (Nat.succ_ne_zero ℓ),
      fun h0 => absurd h0 h⟩

omit [SetTheory V] in
theorem le_sLev (w ℓ : Nat) (hℓ : ℓ ≠ 0) : ℓ ≤ sLev w ℓ := by
  unfold sLev
  rw [if_neg hℓ]
  exact Nat.le_trans (Nat.le_succ ℓ) (Nat.le_max_right w (ℓ + 1))

omit [SetTheory V] in
theorem w_le_sLev (w ℓ : Nat) (hℓ : ℓ ≠ 0) : w ≤ sLev w ℓ := by
  unfold sLev
  rw [if_neg hℓ]
  exact Nat.le_max_left w (ℓ + 1)

omit [SetTheory V] in
theorem succ_le_sLev (w ℓ : Nat) (hℓ : ℓ ≠ 0) : ℓ + 1 ≤ sLev w ℓ := by
  unfold sLev
  rw [if_neg hℓ]
  exact Nat.le_max_right w (ℓ + 1)

/-! ## The frame and the fits -/

/-- **The base frame**: `b0`, `a1` (as functions), `a0`, `B`, `A`. -/
noncomputable def pairFrame (S : PairSig V) (ρ : Nat → V) : Nat → V :=
  cons (lamR 1 (Astar S) S.mkB0) (cons (lamR 1 (Bstar S) S.mkA1)
    (cons S.mkA0 (cons (Bstar S) (cons (Astar S) ρ))))

/-- A frame carrying the five base values at depth `d`. -/
structure FrameAt (S : PairSig V) (d : Nat) (ρ' : Nat → V) : Prop where
  hA : ρ' (d + 4) = Astar S
  hB : ρ' (d + 3) = Bstar S
  hc0 : ρ' (d + 2) = S.mkA0
  hc1 : ρ' (d + 1) = lamR 1 (Bstar S) S.mkA1
  hc2 : ρ' d = lamR 1 (Astar S) S.mkB0

theorem frameAt_zero (S : PairSig V) (ρ : Nat → V) : FrameAt S 0 (pairFrame S ρ) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem frameAt_two (S : PairSig V) (ρ : Nat → V) (a b : V) :
    FrameAt S 2 (cons b (cons a (pairFrame S ρ))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **An official spine's values**: the motives' and minors' typings at
the carriers. -/
structure Fit5 (S : PairSig V) (ℓ : Nat) (MA MB mA0 mA1 mB0 : V) : Prop where
  hMA : MA ∈ˢ piR (ℓ + 1) (Astar S) fun _ => (univ ℓ : V)
  hMB : MB ∈ˢ piR (ℓ + 1) (Bstar S) fun _ => (univ ℓ : V)
  hmA0 : mA0 ∈ˢ app MA S.mkA0
  hmA1 : mA1 ∈ˢ piR ℓ (Bstar S) fun b => piR ℓ (app MB b) fun _ => app MA (S.mkA1 b)
  hmB0 : mB0 ∈ˢ piR ℓ (Astar S) fun a => piR ℓ (app MA a) fun _ => app MB (S.mkB0 a)

theorem cA1_mem (S : PairSig V) : lamR 1 (Bstar S) S.mkA1 ∈ˢ piR 1 (Bstar S) fun _ => Astar S :=
  lamR_mem fun _ hb => mkA1_mem_Astar S hb

theorem cB0_mem (S : PairSig V) : lamR 1 (Astar S) S.mkB0 ∈ˢ piR 1 (Astar S) fun _ => Bstar S :=
  lamR_mem fun _ ha => mkB0_mem_Bstar S ha

section Fits

variable {S : PairSig V} {ℓ d : Nat} {ρ' : Nat → V} {MA MB mA0 mA1 mB0 : V}

/-- The fit, read off the five binders' readings at a frame. -/
theorem fit5_of (hf : FrameAt S d ρ')
    (hMA : MA ∈ˢ interp V ρ' (motA S.w ℓ d))
    (hMB : MB ∈ˢ interp V (cons MA ρ') (motB S.w ℓ (d + 1)))
    (hmA0 : mA0 ∈ˢ interp V (cons MB (cons MA ρ')) (minA0 d))
    (hmA1 : mA1 ∈ˢ interp V (cons mA0 (cons MB (cons MA ρ'))) (minA1 S.w ℓ d))
    (hmB0 : mB0 ∈ˢ interp V (cons mA1 (cons mA0 (cons MB (cons MA ρ')))) (minB0 S.w ℓ d)) :
    Fit5 S ℓ MA MB mA0 mA1 mB0 := by
  change MA ∈ˢ piR (ℓ + 1) (ρ' (d + 4)) (fun _ => (univ ℓ : V)) at hMA
  change MB ∈ˢ piR (ℓ + 1) (ρ' (d + 3)) (fun _ => (univ ℓ : V)) at hMB
  change mA0 ∈ˢ app MA (ρ' (d + 2)) at hmA0
  change mA1 ∈ˢ piR ℓ (ρ' (d + 3))
    (fun b => piR ℓ (app MB b) fun _ => app MA (app (ρ' (d + 1)) b)) at hmA1
  change mB0 ∈ˢ piR ℓ (ρ' (d + 4))
    (fun a => piR ℓ (app MA a) fun _ => app MB (app (ρ' d) a)) at hmB0
  rw [hf.hA] at hMA hmB0
  rw [hf.hB] at hMB hmA1
  rw [hf.hc0] at hmA0
  rw [hf.hc1] at hmA1
  rw [hf.hc2] at hmB0
  refine ⟨hMA, hMB, hmA0, ?_, ?_⟩
  · rwa [piR_congr (fun b hb => by rw [app_lamR_pos Nat.one_ne_zero hb] :
      ∀ b, b ∈ˢ Bstar S →
        (piR ℓ (app MB b) fun _ => app MA (app (lamR 1 (Bstar S) S.mkA1) b))
          = piR ℓ (app MB b) fun _ => app MA (S.mkA1 b))] at hmA1
  · rwa [piR_congr (fun a ha => by rw [app_lamR_pos Nat.one_ne_zero ha] :
      ∀ a, a ∈ˢ Astar S →
        (piR ℓ (app MA a) fun _ => app MB (app (lamR 1 (Astar S) S.mkB0) a))
          = piR ℓ (app MA a) fun _ => app MB (S.mkB0 a))] at hmB0

variable (h : Fit5 S ℓ MA MB mA0 mA1 mB0)
include h

theorem Fit5.mem_motA (hf : FrameAt S d ρ') : MA ∈ˢ interp V ρ' (motA S.w ℓ d) := by
  change MA ∈ˢ piR (ℓ + 1) (ρ' (d + 4)) (fun _ => (univ ℓ : V))
  rw [hf.hA]; exact h.hMA

theorem Fit5.mem_motB (hf : FrameAt S d ρ') :
    MB ∈ˢ interp V (cons MA ρ') (motB S.w ℓ (d + 1)) := by
  change MB ∈ˢ piR (ℓ + 1) (ρ' (d + 3)) (fun _ => (univ ℓ : V))
  rw [hf.hB]; exact h.hMB

theorem Fit5.mem_minA0 (hf : FrameAt S d ρ') :
    mA0 ∈ˢ interp V (cons MB (cons MA ρ')) (minA0 d) := by
  change mA0 ∈ˢ app MA (ρ' (d + 2))
  rw [hf.hc0]; exact h.hmA0

theorem Fit5.mem_minA1 (hf : FrameAt S d ρ') :
    mA1 ∈ˢ interp V (cons mA0 (cons MB (cons MA ρ'))) (minA1 S.w ℓ d) := by
  change mA1 ∈ˢ piR ℓ (ρ' (d + 3))
    (fun b => piR ℓ (app MB b) fun _ => app MA (app (ρ' (d + 1)) b))
  rw [hf.hB, hf.hc1, piR_congr (fun b hb => by rw [app_lamR_pos Nat.one_ne_zero hb] :
      ∀ b, b ∈ˢ Bstar S →
        (piR ℓ (app MB b) fun _ => app MA (app (lamR 1 (Bstar S) S.mkA1) b))
          = piR ℓ (app MB b) fun _ => app MA (S.mkA1 b))]
  exact h.hmA1

theorem Fit5.mem_minB0 (hf : FrameAt S d ρ') :
    mB0 ∈ˢ interp V (cons mA1 (cons mA0 (cons MB (cons MA ρ')))) (minB0 S.w ℓ d) := by
  change mB0 ∈ˢ piR ℓ (ρ' (d + 4))
    (fun a => piR ℓ (app MA a) fun _ => app MB (app (ρ' d) a))
  rw [hf.hA, hf.hc2, piR_congr (fun a ha => by rw [app_lamR_pos Nat.one_ne_zero ha] :
      ∀ a, a ∈ˢ Astar S →
        (piR ℓ (app MA a) fun _ => app MB (app (lamR 1 (Astar S) S.mkB0) a))
          = piR ℓ (app MA a) fun _ => app MB (S.mkB0 a))]
  exact h.hmB0

/-- **The recursion data of a fit** — `MutualPair`'s `PairRecData` at
the spine's values. -/
noncomputable def Fit5.data : PairRecData S where
  ℓ := ℓ
  MA := app MA
  MB := app MB
  mA0 := mA0
  mA1 := fun b ih => app (app mA1 b) ih
  mB0 := fun a ih => app (app mB0 a) ih
  MA_mem := fun a ha => app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMA ha
  MB_mem := fun b hb => app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMB hb
  mA0_typed := h.hmA0
  mA1_typed := fun b ih hb hih => by
    have h1 := app_mem_piR h.hmA1 hb (fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero)
    refine app_mem_piR h1 hih (fun h0 _ _ => ?_)
    have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMA (mkA1_mem_Astar S hb)
    rwa [h0, univ_zero] at this
  mB0_typed := fun a ih ha hih => by
    have h1 := app_mem_piR h.hmB0 ha (fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero)
    refine app_mem_piR h1 hih (fun h0 _ _ => ?_)
    have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMB (mkB0_mem_Bstar S ha)
    rwa [h0, univ_zero] at this

end Fits

/-- A spine fitting six binders has six values. -/
theorem spineFit_six {ρ : Nat → V} {d₁ d₂ d₃ d₄ d₅ d₆ : AnnotTerm} {as : List V}
    (h : SpineFit ρ [d₁, d₂, d₃, d₄, d₅, d₆] as) :
    ∃ a₁ a₂ a₃ a₄ a₅ a₆, as = [a₁, a₂, a₃, a₄, a₅, a₆] := by
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | ⟨a₅, _ | ⟨a₆, _ | ⟨a₇, rest⟩⟩⟩⟩⟩⟩⟩
  · exact h.elim
  · exact h.2.elim
  · exact h.2.2.elim
  · exact h.2.2.2.elim
  · exact h.2.2.2.2.elim
  · exact h.2.2.2.2.2.elim
  · exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl⟩
  · exact h.2.2.2.2.2.2.elim

/-- A spine fitting five binders has five values. -/
theorem spineFit_five {ρ : Nat → V} {d₁ d₂ d₃ d₄ d₅ : AnnotTerm} {as : List V}
    (h : SpineFit ρ [d₁, d₂, d₃, d₄, d₅] as) :
    ∃ a₁ a₂ a₃ a₄ a₅, as = [a₁, a₂, a₃, a₄, a₅] := by
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | ⟨a₅, _ | ⟨a₆, rest⟩⟩⟩⟩⟩⟩
  · exact h.elim
  · exact h.2.elim
  · exact h.2.2.elim
  · exact h.2.2.2.elim
  · exact h.2.2.2.2.elim
  · exact ⟨a₁, a₂, a₃, a₄, a₅, rfl⟩
  · exact h.2.2.2.2.2.elim

section Semantics

variable (S : PairSig V) (ℓ : Nat) (ρ : Nat → V)

/-- The fit of an official spine at the base frame. -/
theorem fit5_of_spine {MA MB mA0 mA1 mB0 : V}
    (hsp : SpineFit (pairFrame S ρ) ((rds5 S.w ℓ ℓ 0).map (·.2.2)) [MA, MB, mA0, mA1, mB0]) :
    Fit5 S ℓ MA MB mA0 mA1 mB0 := by
  obtain ⟨hMA, hMB, hmA0, hmA1, hmB0, -⟩ := hsp
  exact fit5_of (frameAt_zero S ρ) hMA hMB hmA0 hmA1 hmB0

/-- `A.rec`'s spine at a fit and a major. -/
theorem spineFit_rdsA {MA MB mA0 mA1 mB0 t : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0)
    (ht : t ∈ˢ Astar S) :
    SpineFit (pairFrame S ρ) ((rdsA S.w ℓ).map (·.2.2)) [MA, MB, mA0, mA1, mB0, t] :=
  ⟨h.mem_motA (frameAt_zero S ρ), h.mem_motB (frameAt_zero S ρ), h.mem_minA0 (frameAt_zero S ρ),
    h.mem_minA1 (frameAt_zero S ρ), h.mem_minB0 (frameAt_zero S ρ), ht, trivial⟩

/-- `B.rec`'s spine at a fit and a major. -/
theorem spineFit_rdsB {MA MB mA0 mA1 mB0 t : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0)
    (ht : t ∈ˢ Bstar S) :
    SpineFit (pairFrame S ρ) ((rdsB S.w ℓ).map (·.2.2)) [MA, MB, mA0, mA1, mB0, t] :=
  ⟨h.mem_motA (frameAt_zero S ρ), h.mem_motB (frameAt_zero S ρ), h.mem_minA0 (frameAt_zero S ρ),
    h.mem_minA1 (frameAt_zero S ρ), h.mem_minB0 (frameAt_zero S ρ), ht, trivial⟩

/-- The five of an `A.rec` spine fit. -/
theorem fit5_of_spineA {as : List V}
    (hsp : SpineFit (pairFrame S ρ) ((rdsA S.w ℓ).map (·.2.2)) as) :
    ∃ MA MB mA0 mA1 mB0 t, as = [MA, MB, mA0, mA1, mB0, t] ∧
      Fit5 S ℓ MA MB mA0 mA1 mB0 ∧ t ∈ˢ Astar S := by
  obtain ⟨MA, MB, mA0, mA1, mB0, t, rfl⟩ := spineFit_six hsp
  obtain ⟨hMA, hMB, hmA0, hmA1, hmB0, ht, -⟩ := hsp
  exact ⟨MA, MB, mA0, mA1, mB0, t, rfl, fit5_of (frameAt_zero S ρ) hMA hMB hmA0 hmA1 hmB0, ht⟩

/-- The five of a `B.rec` spine fit. -/
theorem fit5_of_spineB {as : List V}
    (hsp : SpineFit (pairFrame S ρ) ((rdsB S.w ℓ).map (·.2.2)) as) :
    ∃ MA MB mA0 mA1 mB0 t, as = [MA, MB, mA0, mA1, mB0, t] ∧
      Fit5 S ℓ MA MB mA0 mA1 mB0 ∧ t ∈ˢ Bstar S := by
  obtain ⟨MA, MB, mA0, mA1, mB0, t, rfl⟩ := spineFit_six hsp
  obtain ⟨hMA, hMB, hmA0, hmA1, hmB0, ht, -⟩ := hsp
  exact ⟨MA, MB, mA0, mA1, mB0, t, rfl, fit5_of (frameAt_zero S ρ) hMA hMB hmA0 hmA1 hmB0, ht⟩

/-! ## The candidate: the union recursor at the frame's data -/

/-- `A.rec`'s value at a leaf frame `(MA, MB, mA0, mA1, mB0, t)`: the
union recursor at class `0`. -/
noncomputable def gA (σ : Nat → V) : V :=
  unionRec ℓ S.w 2 pairIs (pairPhi S) (pairPred S) (pairB (app (σ 5)) (app (σ 4)))
    (pairSt S (σ 3) (fun b ih => app (app (σ 2) b) ih) (fun a ih => app (app (σ 1) a) ih)) 0 pt (σ 0)

/-- `B.rec`'s value at a leaf frame: class `1`. -/
noncomputable def gB (σ : Nat → V) : V :=
  unionRec ℓ S.w 2 pairIs (pairPhi S) (pairPred S) (pairB (app (σ 5)) (app (σ 4)))
    (pairSt S (σ 3) (fun b ih => app (app (σ 2) b) ih) (fun a ih => app (app (σ 1) a) ih)) 1 pt (σ 0)

/-- The candidate `A.rec`: the λ-tower over `A.rec`'s binder data. -/
noncomputable def candA : V := lamTower ℓ (pairFrame S ρ) (rdsA S.w ℓ) (gA S ℓ)
/-- The candidate `B.rec`. -/
noncomputable def candB : V := lamTower ℓ (pairFrame S ρ) (rdsB S.w ℓ) (gB S ℓ)

variable {S ℓ}

theorem gA_eq {MA MB mA0 mA1 mB0 : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0) (ρ' : Nat → V) (t : V) :
    gA S ℓ (cons t (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ'))))))
      = pairRecA h.data t := rfl

theorem gB_eq {MA MB mA0 mA1 mB0 : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0) (ρ' : Nat → V) (t : V) :
    gB S ℓ (cons t (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ'))))))
      = pairRecB h.data t := rfl

theorem rdsA_bits : ∀ d ∈ rdsA S.w ℓ, (ℓ = 0 ↔ d.2.1 = 0) := by
  intro d hd
  simp only [rdsA, rds5, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | rfl | rfl | rfl | rfl) | rfl <;> exact Iff.rfl

theorem rdsB_bits : ∀ d ∈ rdsB S.w ℓ, (ℓ = 0 ↔ d.2.1 = 0) := by
  intro d hd
  simp only [rdsB, rds5, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | rfl | rfl | rfl | rfl) | rfl <;> exact Iff.rfl

variable (S ℓ)

/-- The conclusion `MA t` at a fitting `A.rec` spine is a truth value
at `ℓ = 0`. -/
theorem concA_zero (h0 : ℓ = 0) {as : List V}
    (hsp : SpineFit (pairFrame S ρ) ((rdsA S.w ℓ).map (·.2.2)) as) :
    interp V (consList as (pairFrame S ρ)) concA ∈ˢ (univZero : V) := by
  obtain ⟨MA, MB, mA0, mA1, mB0, t, rfl, h, ht⟩ := fit5_of_spineA S ℓ ρ hsp
  change app MA t ∈ˢ (univZero : V)
  have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMA ht
  rwa [h0, univ_zero] at this

theorem concB_zero (h0 : ℓ = 0) {as : List V}
    (hsp : SpineFit (pairFrame S ρ) ((rdsB S.w ℓ).map (·.2.2)) as) :
    interp V (consList as (pairFrame S ρ)) concB ∈ˢ (univZero : V) := by
  obtain ⟨MA, MB, mA0, mA1, mB0, t, rfl, h, ht⟩ := fit5_of_spineB S ℓ ρ hsp
  change app MB t ∈ˢ (univZero : V)
  have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMB ht
  rwa [h0, univ_zero] at this

/-- **The candidate `A.rec` is typed at official's shape.** -/
theorem candA_mem : candA S ℓ ρ ∈ˢ interp V (pairFrame S ρ) (TA S.w ℓ) := by
  unfold candA TA
  refine lamTower_mem rdsA_bits ?_
  simp only [rdsA, rds5, List.cons_append, List.nil_append, TowerWalk]
  intro MA hMA MB hMB mA0 hmA0 mA1 hmA1 mB0 hmB0 t ht
  have h := fit5_of (frameAt_zero S ρ) hMA hMB hmA0 hmA1 hmB0
  change t ∈ˢ Astar S at ht
  change pairRecA h.data t ∈ˢ app MA t ∧ (ℓ = 0 → app MA t ∈ˢ (univZero : V))
  refine ⟨pairRecA_mem h.data ht, fun h0 => ?_⟩
  have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMA ht
  rwa [h0, univ_zero] at this

/-- **The candidate `B.rec` is typed at official's shape.** -/
theorem candB_mem : candB S ℓ ρ ∈ˢ interp V (pairFrame S ρ) (TB S.w ℓ) := by
  unfold candB TB
  refine lamTower_mem rdsB_bits ?_
  simp only [rdsB, rds5, List.cons_append, List.nil_append, TowerWalk]
  intro MA hMA MB hMB mA0 hmA0 mA1 hmA1 mB0 hmB0 t ht
  have h := fit5_of (frameAt_zero S ρ) hMA hMB hmA0 hmA1 hmB0
  change t ∈ˢ Bstar S at ht
  change pairRecB h.data t ∈ˢ app MB t ∧ (ℓ = 0 → app MB t ∈ˢ (univZero : V))
  refine ⟨pairRecB_mem h.data ht, fun h0 => ?_⟩
  have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMB ht
  rwa [h0, univ_zero] at this

theorem candA_zero (h0 : ℓ = 0) : candA S ℓ ρ = pt := by
  subst h0
  unfold candA rdsA rds5
  simp only [List.cons_append]
  show lamR 0 _ _ = _
  exact lamR_zero

theorem candB_zero (h0 : ℓ = 0) : candB S ℓ ρ = pt := by
  subst h0
  unfold candB rdsB rds5
  simp only [List.cons_append]
  show lamR 0 _ _ = _
  exact lamR_zero

/-- `pt`-headed application chains are `pt`. -/
theorem foldl_app_pt : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt ts

/-! ## The equations' readings -/

variable {S ℓ}

theorem interp_lhsA0 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 : V) :
    interp V (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂))))) lhsA0
      = [MA, MB, mA0, mA1, mB0, ρ₂ 4].foldl SetTheory.app (ρ₂ 1) := rfl

theorem interp_rhsA0 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 : V) :
    interp V (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂))))) rhsA0 = mA0 := rfl

theorem interp_lhsA1 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 b : V) :
    interp V (cons b (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂)))))) lhsA1
      = [MA, MB, mA0, mA1, mB0, app (ρ₂ 3) b].foldl SetTheory.app (ρ₂ 1) := rfl

theorem interp_rhsA1 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 b : V) :
    interp V (cons b (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂)))))) rhsA1
      = app (app mA1 b) ([MA, MB, mA0, mA1, mB0, b].foldl SetTheory.app (ρ₂ 0)) := rfl

theorem interp_lhsB0 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 a : V) :
    interp V (cons a (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂)))))) lhsB0
      = [MA, MB, mA0, mA1, mB0, app (ρ₂ 2) a].foldl SetTheory.app (ρ₂ 0) := rfl

theorem interp_rhsB0 (ρ₂ : Nat → V) (MA MB mA0 mA1 mB0 a : V) :
    interp V (cons a (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ₂)))))) rhsB0
      = app (app mB0 a) ([MA, MB, mA0, mA1, mB0, a].foldl SetTheory.app (ρ₂ 1)) := rfl

/-- Elimination at a `Prop`-valued product. -/
theorem piR_zero_elim {A f x : V} {B : V → V} (hf : f ∈ˢ piR 0 A B) (hx : x ∈ˢ A) :
    ∃ y, y ∈ˢ B x := by
  rw [piR_zero] at hf
  exact of_mem_truthVal hf x hx

variable (S ℓ)

/-! ## The equations hold at the candidate -/

/-- The frame under the tuple binders at the candidate. -/
noncomputable def candFrame : Nat → V := cons (candB S ℓ ρ) (cons (candA S ℓ ρ) (pairFrame S ρ))

theorem eqA0_cand : (pt : V) ∈ˢ interp V (candFrame S ℓ ρ) (eqA0 S.w ℓ) := by
  simp only [eqA0, rds5, mkPisAV, interp_pi]
  refine pt_mem_piR_zero_of fun MA hMA => pt_mem_piR_zero_of fun MB hMB =>
    pt_mem_piR_zero_of fun mA0 hmA0 => pt_mem_piR_zero_of fun mA1 hmA1 =>
    pt_mem_piR_zero_of fun mB0 hmB0 => ?_
  have h := fit5_of (frameAt_two S ρ _ _) hMA hMB hmA0 hmA1 hmB0
  rw [interp_eqE, interp_lhsA0, interp_rhsA0]
  show (pt : V) ∈ˢ eqv ([MA, MB, mA0, mA1, mB0, S.mkA0].foldl SetTheory.app (candA S ℓ ρ)) mA0
  by_cases h0 : ℓ = 0
  · rw [candA_zero S ℓ ρ h0, foldl_app_pt]
    have : mA0 = pt := by
      have hM := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hMA (mkA0_mem_Astar S)
      rw [h0, univ_zero] at hM
      exact eq_pt_of_mem_univZero hM h.hmA0
    rw [this]; exact pt_mem_eqv_self _
  · unfold candA
    rw [lamTower_fold h0 (spineFit_rdsA S ℓ ρ h (mkA0_mem_Astar S))]
    show (pt : V) ∈ˢ eqv (pairRecA h.data S.mkA0) mA0
    rw [pairRecA_a0 h.data]
    exact pt_mem_eqv_self _

theorem eqA1_cand : (pt : V) ∈ˢ interp V (candFrame S ℓ ρ) (eqA1 S.w ℓ) := by
  simp only [eqA1, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi]
  refine pt_mem_piR_zero_of fun MA hMA => pt_mem_piR_zero_of fun MB hMB =>
    pt_mem_piR_zero_of fun mA0 hmA0 => pt_mem_piR_zero_of fun mA1 hmA1 =>
    pt_mem_piR_zero_of fun mB0 hmB0 => pt_mem_piR_zero_of fun b hb => ?_
  have h := fit5_of (frameAt_two S ρ _ _) hMA hMB hmA0 hmA1 hmB0
  change b ∈ˢ Bstar S at hb
  rw [interp_eqE, interp_lhsA1, interp_rhsA1]
  show (pt : V) ∈ˢ eqv
    ([MA, MB, mA0, mA1, mB0, app (lamR 1 (Bstar S) S.mkA1) b].foldl SetTheory.app (candA S ℓ ρ))
    (app (app mA1 b) ([MA, MB, mA0, mA1, mB0, b].foldl SetTheory.app (candB S ℓ ρ)))
  rw [app_lamR_pos Nat.one_ne_zero hb]
  by_cases h0 : ℓ = 0
  · rw [candA_zero S ℓ ρ h0, candB_zero S ℓ ρ h0, foldl_app_pt, foldl_app_pt]
    have : mA1 = pt := eq_pt_of_mem_piR_zero (h0 ▸ h.hmA1)
    rw [this, app_pt, app_pt]
    exact pt_mem_eqv_self _
  · unfold candA candB
    rw [lamTower_fold h0 (spineFit_rdsA S ℓ ρ h (mkA1_mem_Astar S hb)),
      lamTower_fold h0 (spineFit_rdsB S ℓ ρ h hb)]
    show (pt : V) ∈ˢ eqv (pairRecA h.data (S.mkA1 b)) (app (app mA1 b) (pairRecB h.data b))
    rw [pairRecA_a1 h.data hb]
    exact pt_mem_eqv_self _

theorem eqB0_cand : (pt : V) ∈ˢ interp V (candFrame S ℓ ρ) (eqB0 S.w ℓ) := by
  simp only [eqB0, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi]
  refine pt_mem_piR_zero_of fun MA hMA => pt_mem_piR_zero_of fun MB hMB =>
    pt_mem_piR_zero_of fun mA0 hmA0 => pt_mem_piR_zero_of fun mA1 hmA1 =>
    pt_mem_piR_zero_of fun mB0 hmB0 => pt_mem_piR_zero_of fun a ha => ?_
  have h := fit5_of (frameAt_two S ρ _ _) hMA hMB hmA0 hmA1 hmB0
  change a ∈ˢ Astar S at ha
  rw [interp_eqE, interp_lhsB0, interp_rhsB0]
  show (pt : V) ∈ˢ eqv
    ([MA, MB, mA0, mA1, mB0, app (lamR 1 (Astar S) S.mkB0) a].foldl SetTheory.app (candB S ℓ ρ))
    (app (app mB0 a) ([MA, MB, mA0, mA1, mB0, a].foldl SetTheory.app (candA S ℓ ρ)))
  rw [app_lamR_pos Nat.one_ne_zero ha]
  by_cases h0 : ℓ = 0
  · rw [candA_zero S ℓ ρ h0, candB_zero S ℓ ρ h0, foldl_app_pt, foldl_app_pt]
    have : mB0 = pt := eq_pt_of_mem_piR_zero (h0 ▸ h.hmB0)
    rw [this, app_pt, app_pt]
    exact pt_mem_eqv_self _
  · unfold candA candB
    rw [lamTower_fold h0 (spineFit_rdsB S ℓ ρ h (mkB0_mem_Bstar S ha)),
      lamTower_fold h0 (spineFit_rdsA S ℓ ρ h ha)]
    show (pt : V) ∈ˢ eqv (pairRecB h.data (S.mkB0 a)) (app (app mB0 a) (pairRecA h.data a))
    rw [pairRecB_b0 h.data ha]
    exact pt_mem_eqv_self _

/-! ## The conjunction of equations -/

variable {S ℓ}

/-- The equations are truth values, at any frame. -/
theorem eqA0_univZero (ρ' : Nat → V) : interp V ρ' (eqA0 S.w ℓ) ∈ˢ (univZero : V) := by
  show piR 0 _ _ ∈ˢ _
  exact piR_zero_mem_univZero

theorem eqA1_univZero (ρ' : Nat → V) : interp V ρ' (eqA1 S.w ℓ) ∈ˢ (univZero : V) := by
  show piR 0 _ _ ∈ˢ _
  exact piR_zero_mem_univZero

theorem eqB0_univZero (ρ' : Nat → V) : interp V ρ' (eqB0 S.w ℓ) ∈ˢ (univZero : V) := by
  show piR 0 _ _ ∈ˢ _
  exact piR_zero_mem_univZero

/-- `PSigma'.{0,0}` is a graph on `Prop`. -/
theorem psigmaV_00_mem :
    psigmaV V 0 0 ∈ˢ piR 1 (univ 0 : V)
      (fun A => piR 1 (psigmaFibreSpace V 0 A) fun _ => (univ 0 : V)) :=
  lamR_mem fun _ hA => lamR_mem fun _ hB =>
    sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx)

/-- `PSigma'.{u,v}` is a graph. -/
theorem psigmaV_mem (u v : Nat) :
    psigmaV V u v ∈ˢ piR (Nat.max u v + 1) (univ u : V)
      (fun A => piR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun _ => (univ (Nat.max u v) : V)) :=
  lamR_mem fun _ hA => lamR_mem fun _ hB =>
    sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx)

/-- The conjunction reads as the `Prop`-level pair set. -/
theorem interp_andAV {P Q : AnnotTerm} {ρ' : Nat → V}
    (hP : interp V ρ' P ∈ˢ (univZero : V)) (hQ : interp V ρ' Q ∈ˢ (univZero : V)) :
    interp V ρ' (andAV P Q) = sigmaSet 0 (interp V ρ' P) fun _ => interp V ρ' Q := by
  have hP' : interp V ρ' P ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hP
  have hlam : interp V ρ' (.lam 1 P (Q.liftN 1 0)) = lamR 1 (interp V ρ' P) fun _ => interp V ρ' Q := by
    rw [interp_lam]
    exact lamR_congr fun x _ => by rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
  have hfib : (lamR 1 (interp V ρ' P) fun _ => interp V ρ' Q) ∈ˢ psigmaFibreSpace V 0 (interp V ρ' P) :=
    lamR_mem fun _ _ => by rw [univ_zero]; exact hQ
  show SetTheory.app (SetTheory.app (psigmaV V 0 0) (interp V ρ' P)) (interp V ρ' (.lam 1 P (Q.liftN 1 0))) = _
  rw [hlam, psigmaV_app V hP' hfib]
  exact sigma_congr fun x hx => app_lamR_pos Nat.one_ne_zero hx

theorem andAV_univZero {P Q : AnnotTerm} {ρ' : Nat → V}
    (hP : interp V ρ' P ∈ˢ (univZero : V)) (hQ : interp V ρ' Q ∈ˢ (univZero : V)) :
    interp V ρ' (andAV P Q) ∈ˢ (univZero : V) := by
  rw [interp_andAV hP hQ, sigmaSet_zero]
  exact truthVal_mem_univZero _

theorem pt_mem_andAV {P Q : AnnotTerm} {ρ' : Nat → V}
    (hP : interp V ρ' P ∈ˢ (univZero : V)) (hQ : interp V ρ' Q ∈ˢ (univZero : V))
    (hp : (pt : V) ∈ˢ interp V ρ' P) (hq : (pt : V) ∈ˢ interp V ρ' Q) :
    (pt : V) ∈ˢ interp V ρ' (andAV P Q) := by
  rw [interp_andAV hP hQ]
  exact pt_mem_sigma hp hq

theorem of_mem_andAV {P Q : AnnotTerm} {ρ' : Nat → V}
    (hP : interp V ρ' P ∈ˢ (univZero : V)) (hQ : interp V ρ' Q ∈ˢ (univZero : V)) {z : V}
    (hz : z ∈ˢ interp V ρ' (andAV P Q)) :
    (pt : V) ∈ˢ interp V ρ' P ∧ (pt : V) ∈ˢ interp V ρ' Q := by
  rw [interp_andAV hP hQ] at hz
  obtain ⟨a, b, ha, hb, -, -⟩ := mem_sigma_elim hz
  exact ⟨eq_pt_of_mem_univZero hP ha ▸ ha, eq_pt_of_mem_univZero hQ hb ▸ hb⟩

theorem eqs_univZero (ρ' : Nat → V) : interp V ρ' (eqs S.w ℓ) ∈ˢ (univZero : V) :=
  andAV_univZero (eqA0_univZero ρ') (andAV_univZero (eqA1_univZero ρ') (eqB0_univZero ρ'))

theorem pt_mem_eqs_iff (ρ' : Nat → V) :
    (pt : V) ∈ˢ interp V ρ' (eqs S.w ℓ) ↔
      (pt : V) ∈ˢ interp V ρ' (eqA0 S.w ℓ) ∧ (pt : V) ∈ˢ interp V ρ' (eqA1 S.w ℓ) ∧
        (pt : V) ∈ˢ interp V ρ' (eqB0 S.w ℓ) := by
  constructor
  · intro h
    obtain ⟨h0, h12⟩ := of_mem_andAV (eqA0_univZero ρ')
      (andAV_univZero (eqA1_univZero ρ') (eqB0_univZero ρ')) h
    obtain ⟨h1, h2⟩ := of_mem_andAV (eqA1_univZero ρ') (eqB0_univZero ρ') h12
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact pt_mem_andAV (eqA0_univZero ρ') (andAV_univZero (eqA1_univZero ρ') (eqB0_univZero ρ'))
      h0 (pt_mem_andAV (eqA1_univZero ρ') (eqB0_univZero ρ') h1 h2)

/-! ## The recursor types are graded and formed -/

theorem wd_motA (w d : Nat) (ρ' : Nat → V) : WellDenoted V ρ' (motA w ℓ d) := by
  rw [motA, WellDenoted_pi]
  exact ⟨trivial, fun _ _ => trivial⟩

theorem wd_motB (w d : Nat) (ρ' : Nat → V) : WellDenoted V ρ' (motB w ℓ d) := by
  rw [motB, WellDenoted_pi]
  exact ⟨trivial, fun _ _ => trivial⟩

/-- The motive's typing, read off its binder's reading. -/
theorem motA_mem_of {d : Nat} {ρ' : Nat → V} {MA : V} (hf : FrameAt S d ρ')
    (hMA : MA ∈ˢ interp V ρ' (motA S.w ℓ d)) :
    MA ∈ˢ piR (ℓ + 1) (Astar S) fun _ => (univ ℓ : V) := by
  change MA ∈ˢ piR (ℓ + 1) (ρ' (d + 4)) (fun _ => (univ ℓ : V)) at hMA
  rw [hf.hA] at hMA; exact hMA

theorem motB_mem_of {d : Nat} {ρ' : Nat → V} {MA MB : V} (hf : FrameAt S d ρ')
    (hMB : MB ∈ˢ interp V (cons MA ρ') (motB S.w ℓ (d + 1))) :
    MB ∈ˢ piR (ℓ + 1) (Bstar S) fun _ => (univ ℓ : V) := by
  change MB ∈ˢ piR (ℓ + 1) (ρ' (d + 3)) (fun _ => (univ ℓ : V)) at hMB
  rw [hf.hB] at hMB; exact hMB

section WD

variable {d : Nat} {ρ' : Nat → V} {MA MB : V} (hf : FrameAt S d ρ')
  (hMA : MA ∈ˢ piR (ℓ + 1) (Astar S) fun _ => (univ ℓ : V))
include hf hMA

theorem wd_minA0 : WellDenoted V (cons MB (cons MA ρ')) (minA0 d) := by
  rw [minA0, WellDenoted_app]
  refine ⟨trivial, trivial, ℓ + 1, Astar S, fun _ => (univ ℓ : V), hMA, ?_,
    fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
  change ρ' (d + 2) ∈ˢ Astar S
  rw [hf.hc0]; exact mkA0_mem_Astar S

variable (hMB : MB ∈ˢ piR (ℓ + 1) (Bstar S) fun _ => (univ ℓ : V))
include hMB

theorem wd_minA1 {mA0 : V} :
    WellDenoted V (cons mA0 (cons MB (cons MA ρ'))) (minA1 S.w ℓ d) := by
  rw [minA1, WellDenoted_pi]
  refine ⟨trivial, fun b hb => ?_⟩
  change b ∈ˢ ρ' (d + 3) at hb
  rw [hf.hB] at hb
  rw [WellDenoted_pi]
  refine ⟨?_, fun ih _ => ?_⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, trivial, ℓ + 1, Bstar S, fun _ => (univ ℓ : V), hMB, hb,
      fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
  · rw [WellDenoted_app]
    refine ⟨trivial, ?_, ℓ + 1, Astar S, fun _ => (univ ℓ : V), hMA, ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, trivial, 1, Bstar S, fun _ => Astar S, ?_, hb,
        fun h0 => absurd h0 Nat.one_ne_zero⟩
      change ρ' (d + 1) ∈ˢ _
      rw [hf.hc1]; exact cA1_mem S
    · change app (ρ' (d + 1)) b ∈ˢ Astar S
      rw [hf.hc1, app_lamR_pos Nat.one_ne_zero hb]
      exact mkA1_mem_Astar S hb

theorem wd_minB0 {mA0 mA1 : V} :
    WellDenoted V (cons mA1 (cons mA0 (cons MB (cons MA ρ')))) (minB0 S.w ℓ d) := by
  rw [minB0, WellDenoted_pi]
  refine ⟨trivial, fun a ha => ?_⟩
  change a ∈ˢ ρ' (d + 4) at ha
  rw [hf.hA] at ha
  rw [WellDenoted_pi]
  refine ⟨?_, fun ih _ => ?_⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, trivial, ℓ + 1, Astar S, fun _ => (univ ℓ : V), hMA, ha,
      fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
  · rw [WellDenoted_app]
    refine ⟨trivial, ?_, ℓ + 1, Bstar S, fun _ => (univ ℓ : V), hMB, ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, trivial, 1, Astar S, fun _ => Bstar S, ?_, ha,
        fun h0 => absurd h0 Nat.one_ne_zero⟩
      change ρ' d ∈ˢ _
      rw [hf.hc2]; exact cB0_mem S
    · change app (ρ' d) a ∈ˢ Bstar S
      rw [hf.hc2, app_lamR_pos Nat.one_ne_zero ha]
      exact mkB0_mem_Bstar S ha

end WD

theorem wd_concA {ρ' : Nat → V} {MA MB mA0 mA1 mB0 t : V}
    (hMA : MA ∈ˢ piR (ℓ + 1) (Astar S) fun _ => (univ ℓ : V)) (ht : t ∈ˢ Astar S) :
    WellDenoted V (cons t (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ')))))) concA := by
  rw [concA, WellDenoted_app]
  exact ⟨trivial, trivial, ℓ + 1, Astar S, fun _ => (univ ℓ : V), hMA, ht,
    fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩

theorem wd_concB {ρ' : Nat → V} {MA MB mA0 mA1 mB0 t : V}
    (hMB : MB ∈ˢ piR (ℓ + 1) (Bstar S) fun _ => (univ ℓ : V)) (ht : t ∈ˢ Bstar S) :
    WellDenoted V (cons t (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA ρ')))))) concB := by
  rw [concB, WellDenoted_app]
  exact ⟨trivial, trivial, ℓ + 1, Bstar S, fun _ => (univ ℓ : V), hMB, ht,
    fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩

variable (S ℓ)

/-- **`A.rec`'s type is graded.** -/
theorem wd_TA : WellDenoted V (pairFrame S ρ) (TA S.w ℓ) := by
  simp only [TA, rdsA, rds5, List.cons_append, List.nil_append, mkPisAV, WellDenoted_pi]
  refine ⟨wd_motA _ _ _, fun MA hMA => ⟨wd_motB _ _ _, fun MB hMB => ?_⟩⟩
  have hMA' := motA_mem_of (frameAt_zero S ρ) hMA
  have hMB' := motB_mem_of (frameAt_zero S ρ) hMB
  exact ⟨wd_minA0 (frameAt_zero S ρ) hMA', fun mA0 _ =>
    ⟨wd_minA1 (frameAt_zero S ρ) hMA' hMB', fun mA1 _ =>
      ⟨wd_minB0 (frameAt_zero S ρ) hMA' hMB', fun mB0 _ =>
        ⟨trivial, fun t ht => wd_concA hMA' ht⟩⟩⟩⟩

/-- **`B.rec`'s type is graded.** -/
theorem wd_TB : WellDenoted V (pairFrame S ρ) (TB S.w ℓ) := by
  simp only [TB, rdsB, rds5, List.cons_append, List.nil_append, mkPisAV, WellDenoted_pi]
  refine ⟨wd_motA _ _ _, fun MA hMA => ⟨wd_motB _ _ _, fun MB hMB => ?_⟩⟩
  have hMA' := motA_mem_of (frameAt_zero S ρ) hMA
  have hMB' := motB_mem_of (frameAt_zero S ρ) hMB
  exact ⟨wd_minA0 (frameAt_zero S ρ) hMA', fun mA0 _ =>
    ⟨wd_minA1 (frameAt_zero S ρ) hMA' hMB', fun mA1 _ =>
      ⟨wd_minB0 (frameAt_zero S ρ) hMA' hMB', fun mB0 _ =>
        ⟨trivial, fun t ht => wd_concB hMB' ht⟩⟩⟩⟩

/-! ## Formation: the recursor types live in `univ sLev` -/

omit [SetTheory V] in
theorem natMax_self (n : Nat) : Nat.max n n = n := Nat.max_self n

omit [SetTheory V] in
theorem natMax_zero (n : Nat) : Nat.max n 0 = n := Nat.max_zero n

/-- A product at a bit `v ≤ s` (both nonzero) over domains in `univ s`
lives in `univ s`. -/
theorem piR_mem_univ_of {s v : Nat} (hv : v ≠ 0) (hvs : v ≤ s) {A : V} {B : V → V}
    (hA : A ∈ˢ (univ s : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ s : V)) :
    piR v A B ∈ˢ (univ s : V) := by
  have hs : s ≠ 0 := fun h => hv (Nat.le_zero.mp (h ▸ hvs))
  rw [piR_zero_agree (v := v) (v' := s) ⟨fun h => absurd h hv, fun h => absurd h hs⟩
    (fun _ _ => rfl)]
  have := piR_mem_univ hA hB
  rwa [if_neg hs, natMax_self] at this

theorem Astar_mem_univ : Astar S ∈ˢ (univ S.w : V) :=
  famSpace_app (lfpTuple_mem S.w 2 pairIs (pairPhi S) 0 (by omega)) (pt_mem_pairIs 0)

theorem Bstar_mem_univ : Bstar S ∈ˢ (univ S.w : V) :=
  famSpace_app (lfpTuple_mem S.w 2 pairIs (pairPhi S) 1 (by omega)) (pt_mem_pairIs 1)

variable {S ℓ}

theorem app_mot_univ (hℓ : ℓ ≠ 0) {M a A : V} (hM : M ∈ˢ piR (ℓ + 1) A fun _ => (univ ℓ : V))
    (ha : a ∈ˢ A) : app M a ∈ˢ (univ (sLev S.w ℓ) : V) :=
  univ_mono (le_sLev S.w ℓ hℓ) _ (app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM ha)

section Univ

variable (hℓ : ℓ ≠ 0) {d : Nat} {ρ' : Nat → V} (hf : FrameAt S d ρ')
include hℓ hf

theorem motA_univ : interp V ρ' (motA S.w ℓ d) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  change (piR (ℓ + 1) (ρ' (d + 4)) fun _ => (univ ℓ : V)) ∈ˢ _
  rw [hf.hA]
  exact piR_mem_univ_of (Nat.succ_ne_zero ℓ) (succ_le_sLev S.w ℓ hℓ)
    (univ_mono (w_le_sLev S.w ℓ hℓ) _ (Astar_mem_univ S))
    (fun _ _ => univ_mono (succ_le_sLev S.w ℓ hℓ) _ (univ_mem_univ ℓ))

theorem motB_univ {MA : V} :
    interp V (cons MA ρ') (motB S.w ℓ (d + 1)) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  change (piR (ℓ + 1) (ρ' (d + 3)) fun _ => (univ ℓ : V)) ∈ˢ _
  rw [hf.hB]
  exact piR_mem_univ_of (Nat.succ_ne_zero ℓ) (succ_le_sLev S.w ℓ hℓ)
    (univ_mono (w_le_sLev S.w ℓ hℓ) _ (Bstar_mem_univ S))
    (fun _ _ => univ_mono (succ_le_sLev S.w ℓ hℓ) _ (univ_mem_univ ℓ))

variable {MA MB : V} (hMA : MA ∈ˢ piR (ℓ + 1) (Astar S) fun _ => (univ ℓ : V))
  (hMB : MB ∈ˢ piR (ℓ + 1) (Bstar S) fun _ => (univ ℓ : V))
include hMA

theorem minA0_univ : interp V (cons MB (cons MA ρ')) (minA0 d) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  change app MA (ρ' (d + 2)) ∈ˢ _
  rw [hf.hc0]
  exact app_mot_univ hℓ hMA (mkA0_mem_Astar S)

include hMB

theorem minA1_univ {mA0 : V} :
    interp V (cons mA0 (cons MB (cons MA ρ'))) (minA1 S.w ℓ d) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  change (piR ℓ (ρ' (d + 3)) fun b => piR ℓ (app MB b) fun _ => app MA (app (ρ' (d + 1)) b)) ∈ˢ _
  rw [hf.hB, hf.hc1]
  refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ)
    (univ_mono (w_le_sLev S.w ℓ hℓ) _ (Bstar_mem_univ S)) fun b hb => ?_
  refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (app_mot_univ hℓ hMB hb) fun _ _ => ?_
  rw [app_lamR_pos Nat.one_ne_zero hb]
  exact app_mot_univ hℓ hMA (mkA1_mem_Astar S hb)

theorem minB0_univ {mA0 mA1 : V} :
    interp V (cons mA1 (cons mA0 (cons MB (cons MA ρ')))) (minB0 S.w ℓ d)
      ∈ˢ (univ (sLev S.w ℓ) : V) := by
  change (piR ℓ (ρ' (d + 4)) fun a => piR ℓ (app MA a) fun _ => app MB (app (ρ' d) a)) ∈ˢ _
  rw [hf.hA, hf.hc2]
  refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ)
    (univ_mono (w_le_sLev S.w ℓ hℓ) _ (Astar_mem_univ S)) fun a ha => ?_
  refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (app_mot_univ hℓ hMA ha) fun _ _ => ?_
  rw [app_lamR_pos Nat.one_ne_zero ha]
  exact app_mot_univ hℓ hMB (mkB0_mem_Bstar S ha)

end Univ

variable (S ℓ)

/-- **`A.rec`'s type is formed** at the recursor types' sort. -/
theorem TA_univ : interp V (pairFrame S ρ) (TA S.w ℓ) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    rw [(sLev_zero_iff S.w 0).mpr rfl, univ_zero]
    show piR 0 _ _ ∈ˢ _
    exact piR_zero_mem_univZero
  · simp only [TA, rdsA, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi]
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (motA_univ hℓ (frameAt_zero S ρ)) fun MA hMA => ?_
    have hMA' := motA_mem_of (frameAt_zero S ρ) hMA
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (motB_univ hℓ (frameAt_zero S ρ)) fun MB hMB => ?_
    have hMB' := motB_mem_of (frameAt_zero S ρ) hMB
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minA0_univ hℓ (frameAt_zero S ρ) hMA')
      fun mA0 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minA1_univ hℓ (frameAt_zero S ρ) hMA' hMB')
      fun mA1 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minB0_univ hℓ (frameAt_zero S ρ) hMA' hMB')
      fun mB0 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) ?_ fun t ht => ?_
    · change Astar S ∈ˢ _
      exact univ_mono (w_le_sLev S.w ℓ hℓ) _ (Astar_mem_univ S)
    · change t ∈ˢ Astar S at ht
      change app MA t ∈ˢ _
      exact app_mot_univ hℓ hMA' ht

/-- **`B.rec`'s type is formed.** -/
theorem TB_univ : interp V (pairFrame S ρ) (TB S.w ℓ) ∈ˢ (univ (sLev S.w ℓ) : V) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    rw [(sLev_zero_iff S.w 0).mpr rfl, univ_zero]
    show piR 0 _ _ ∈ˢ _
    exact piR_zero_mem_univZero
  · simp only [TB, rdsB, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi]
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (motA_univ hℓ (frameAt_zero S ρ)) fun MA hMA => ?_
    have hMA' := motA_mem_of (frameAt_zero S ρ) hMA
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (motB_univ hℓ (frameAt_zero S ρ)) fun MB hMB => ?_
    have hMB' := motB_mem_of (frameAt_zero S ρ) hMB
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minA0_univ hℓ (frameAt_zero S ρ) hMA')
      fun mA0 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minA1_univ hℓ (frameAt_zero S ρ) hMA' hMB')
      fun mA1 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) (minB0_univ hℓ (frameAt_zero S ρ) hMA' hMB')
      fun mB0 _ => ?_
    refine piR_mem_univ_of hℓ (le_sLev S.w ℓ hℓ) ?_ fun t ht => ?_
    · change Bstar S ∈ˢ _
      exact univ_mono (w_le_sLev S.w ℓ hℓ) _ (Bstar_mem_univ S)
    · change t ∈ˢ Bstar S at ht
      change app MB t ∈ˢ _
      exact app_mot_univ hℓ hMB' ht

/-! ## The Σ'-chain, the choice, the leaves -/

/-- `⟦T_A⟧`. -/
noncomputable def TAv : V := interp V (pairFrame S ρ) (TA S.w ℓ)
/-- `⟦T_B⟧`. -/
noncomputable def TBv : V := interp V (pairFrame S ρ) (TB S.w ℓ)
/-- `⟦eqs⟧` under the tuple `(a, b)`. -/
noncomputable def eqsV (a b : V) : V := interp V (cons b (cons a (pairFrame S ρ))) (eqs S.w ℓ)
/-- `⟦Σ' (rB : T_B), eqs⟧` under `rA := a`. -/
noncomputable def innerV (a : V) : V :=
  sigmaSet (sLev S.w ℓ) (TBv S ℓ ρ) fun b => eqsV S ℓ ρ a b
/-- `⟦sig⟧`. -/
noncomputable def sigV : V := sigmaSet (sLev S.w ℓ) (TAv S ℓ ρ) fun a => innerV S ℓ ρ a

theorem TAv_univ : TAv S ℓ ρ ∈ˢ (univ (sLev S.w ℓ) : V) := TA_univ S ℓ ρ
theorem TBv_univ : TBv S ℓ ρ ∈ˢ (univ (sLev S.w ℓ) : V) := TB_univ S ℓ ρ

theorem interp_TB_lift (a : V) :
    interp V (cons a (pairFrame S ρ)) ((TB S.w ℓ).liftN 1 0) = TBv S ℓ ρ := by
  rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]; rfl

theorem wd_TB_lift (a : V) : WellDenoted V (cons a (pairFrame S ρ)) ((TB S.w ℓ).liftN 1 0) := by
  rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact wd_TB S ℓ ρ

theorem interp_innerLam (a : V) :
    interp V (cons a (pairFrame S ρ)) (.lam 1 ((TB S.w ℓ).liftN 1 0) (eqs S.w ℓ))
      = lamR 1 (TBv S ℓ ρ) fun b => eqsV S ℓ ρ a b := by
  rw [interp_lam, interp_TB_lift]; rfl

theorem innerLam_mem (a : V) :
    (lamR 1 (TBv S ℓ ρ) fun b => eqsV S ℓ ρ a b) ∈ˢ psigmaFibreSpace V 0 (TBv S ℓ ρ) :=
  lamR_mem fun _ _ => by rw [univ_zero]; exact eqs_univZero _

theorem interp_inner (a : V) :
    interp V (cons a (pairFrame S ρ)) (inner S.w ℓ) = innerV S ℓ ρ a := by
  show SetTheory.app (SetTheory.app (psigmaV V (sLev S.w ℓ) 0)
    (interp V (cons a (pairFrame S ρ)) ((TB S.w ℓ).liftN 1 0)))
    (interp V (cons a (pairFrame S ρ)) (.lam 1 ((TB S.w ℓ).liftN 1 0) (eqs S.w ℓ))) = _
  rw [interp_TB_lift, interp_innerLam, psigmaV_app V (TBv_univ S ℓ ρ) (innerLam_mem S ℓ ρ a),
    natMax_zero]
  exact sigma_congr fun b hb => app_lamR_pos Nat.one_ne_zero hb

theorem innerV_univ (a : V) : innerV S ℓ ρ a ∈ˢ (univ (sLev S.w ℓ) : V) := by
  unfold innerV
  have := sigma_mem_univ (u := sLev S.w ℓ) (v := 0) (TBv_univ S ℓ ρ)
    (fun b _ => by rw [univ_zero]; exact eqs_univZero (S := S) (ℓ := ℓ) (cons b (cons a (pairFrame S ρ))))
  rwa [natMax_zero] at this

theorem sigV_univ : sigV S ℓ ρ ∈ˢ (univ (sLev S.w ℓ) : V) := by
  unfold sigV
  have := sigma_mem_univ (TAv_univ S ℓ ρ) (fun a _ => innerV_univ S ℓ ρ a)
  rwa [natMax_self] at this

theorem interp_sigLam :
    interp V (pairFrame S ρ) (.lam (sLev S.w ℓ + 1) (TA S.w ℓ) (inner S.w ℓ))
      = lamR (sLev S.w ℓ + 1) (TAv S ℓ ρ) fun a => innerV S ℓ ρ a := by
  rw [interp_lam]
  exact lamR_congr fun a _ => interp_inner S ℓ ρ a

theorem sigLam_mem :
    (lamR (sLev S.w ℓ + 1) (TAv S ℓ ρ) fun a => innerV S ℓ ρ a)
      ∈ˢ psigmaFibreSpace V (sLev S.w ℓ) (TAv S ℓ ρ) :=
  lamR_mem fun a _ => innerV_univ S ℓ ρ a

theorem interp_sig : interp V (pairFrame S ρ) (sig S.w ℓ) = sigV S ℓ ρ := by
  show SetTheory.app (SetTheory.app (psigmaV V (sLev S.w ℓ) (sLev S.w ℓ)) (TAv S ℓ ρ))
    (interp V (pairFrame S ρ) (.lam (sLev S.w ℓ + 1) (TA S.w ℓ) (inner S.w ℓ))) = _
  rw [interp_sigLam, psigmaV_app V (TAv_univ S ℓ ρ) (sigLam_mem S ℓ ρ), natMax_self]
  exact sigma_congr fun a ha => app_lamR_pos (Nat.succ_ne_zero _) ha

/-- The three equations hold at the candidate tuple. -/
theorem pt_mem_eqsV_cand : (pt : V) ∈ˢ eqsV S ℓ ρ (candA S ℓ ρ) (candB S ℓ ρ) :=
  (pt_mem_eqs_iff (candFrame S ℓ ρ)).mpr ⟨eqA0_cand S ℓ ρ, eqA1_cand S ℓ ρ, eqB0_cand S ℓ ρ⟩

/-- **The Σ'-chain is inhabited** — by the candidate tuple. -/
theorem sigV_inhabited : ∃ x, x ∈ˢ sigV S ℓ ρ := by
  unfold sigV innerV
  by_cases hs : sLev S.w ℓ = 0
  · rw [hs]
    exact ⟨pt, pt_mem_sigma (candA_mem S ℓ ρ)
      (pt_mem_sigma (candB_mem S ℓ ρ) (pt_mem_eqsV_cand S ℓ ρ))⟩
  · exact ⟨spair (candA S ℓ ρ) (spair (candB S ℓ ρ) pt), spair_mem hs (candA_mem S ℓ ρ)
      (spair_mem hs (candB_mem S ℓ ρ) (pt_mem_eqsV_cand S ℓ ρ))⟩

/-- `pt` witnesses the double negation of an inhabited set. -/
theorem pt_mem_dnegSpace_of {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace V A := by
  unfold dnegSpace
  have h1 : piR 0 A (fun _ => (empty : V)) = empty := by
    rw [piR_zero]
    exact truthVal_eq_empty fun hf => not_mem_empty _ (hf x hx).choose_spec
  rw [h1, piR_zero_empty]
  exact pt_mem_unitSet

theorem interp_sel : interp V (pairFrame S ρ) (sel S.w ℓ) = schoice (sigV S ℓ ρ) := by
  show SetTheory.app (SetTheory.app (choiceV V (sLev S.w ℓ))
    (interp V (pairFrame S ρ) (sig S.w ℓ))) pt = _
  rw [interp_sig]
  exact choiceV_app V (sigV_univ S ℓ ρ) (pt_mem_dnegSpace_of (sigV_inhabited S ℓ ρ).choose_spec)

theorem sel_mem : schoice (sigV S ℓ ρ) ∈ˢ sigV S ℓ ρ :=
  schoice_mem (sigV_inhabited S ℓ ρ).choose_spec

/-- **The chosen tuple's components**: a member of each recursor type
satisfying the three equations, and the two leaves ARE them. -/
theorem sel_facts :
    ∃ a b : V, a ∈ˢ TAv S ℓ ρ ∧ b ∈ˢ TBv S ℓ ρ ∧ (pt : V) ∈ˢ eqsV S ℓ ρ a b ∧
      interp V (pairFrame S ρ) (recA S.w ℓ) = a ∧ interp V (pairFrame S ρ) (recB S.w ℓ) = b := by
  obtain ⟨a, e, ha, he, hz, hpos⟩ := mem_sigma_elim
    (show schoice (sigV S ℓ ρ) ∈ˢ sigmaSet (sLev S.w ℓ) (TAv S ℓ ρ) (fun a => innerV S ℓ ρ a)
      from sel_mem S ℓ ρ)
  obtain ⟨b, e', hb, he', hz', hpos'⟩ := mem_sigma_elim
    (show e ∈ˢ sigmaSet (sLev S.w ℓ) (TBv S ℓ ρ) (fun b => eqsV S ℓ ρ a b) from he)
  refine ⟨a, b, ha, hb, ?_, ?_, ?_⟩
  · have hpt : e' = pt := eq_pt_of_mem_univZero (eqs_univZero (cons b (cons a (pairFrame S ρ)))) he'
    rw [hpt] at he'; exact he'
  · show sfst (interp V (pairFrame S ρ) (sel S.w ℓ)) = a
    rw [interp_sel]
    by_cases hs : sLev S.w ℓ = 0
    · rw [hz hs, sfst_pt]
      exact (mem_univ_zero (hs ▸ TAv_univ S ℓ ρ) ha).symm
    · rw [hpos hs, sfst_spair]
  · show sfst (ssnd (interp V (pairFrame S ρ) (sel S.w ℓ))) = b
    rw [interp_sel]
    by_cases hs : sLev S.w ℓ = 0
    · rw [hz hs, ssnd_pt, sfst_pt]
      exact (mem_univ_zero (hs ▸ TBv_univ S ℓ ρ) hb).symm
    · rw [hpos hs, ssnd_spair, hpos' hs, sfst_spair]

/-! ## Grading of the equations, the chain, the leaves -/

theorem wd_bvars7 (σ : Nat → V) : ∀ x ∈ spine7 ++ [ca0 7], WellDenoted V σ x := by
  intro x hx
  simp only [spine7, ca0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem wd_spine8_last (σ : Nat → V) : ∀ x ∈ spine8 ++ [AnnotTerm.bvar 0], WellDenoted V σ x := by
  intro x hx
  simp only [spine8, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem wd_spine8_app (σ : Nat → V) {e : AnnotTerm} (he : WellDenoted V σ e) :
    ∀ x ∈ spine8 ++ [e], WellDenoted V σ x := by
  intro x hx
  simp only [spine8, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact he

variable {S ℓ}

theorem wd_eqA0 {a b : V} (ha : a ∈ˢ TAv S ℓ ρ) :
    WellDenoted V (cons b (cons a (pairFrame S ρ))) (eqA0 S.w ℓ) := by
  simp only [eqA0, rds5, mkPisAV, WellDenoted_pi]
  refine ⟨wd_motA _ _ _, fun MA hMA => ⟨wd_motB _ _ _, fun MB hMB => ?_⟩⟩
  have hf := frameAt_two S ρ a b
  have hMA' := motA_mem_of hf hMA
  have hMB' := motB_mem_of hf hMB
  refine ⟨wd_minA0 hf hMA', fun mA0 hmA0 => ⟨wd_minA1 hf hMA' hMB', fun mA1 hmA1 =>
    ⟨wd_minB0 hf hMA' hMB', fun mB0 hmB0 => ?_⟩⟩⟩
  have h := fit5_of hf hMA hMB hmA0 hmA1 hmB0
  rw [WellDenoted_eqE, lhsA0, rhsA0]
  refine ⟨(mkAppN_wellDenoted_of_chain ?_ (wd_bvars7 _) ?_).1, trivial⟩
  · trivial
  change AppChainOk a [MA, MB, mA0, mA1, mB0, S.mkA0]
  exact appChainOk_of_mkPisAV' rdsA_bits (fun h0 as' hsp => concA_zero S ℓ ρ h0 hsp) ha
    (spineFit_rdsA S ℓ ρ h (mkA0_mem_Astar S))

theorem wd_eqA1 {a b : V} (ha : a ∈ˢ TAv S ℓ ρ) (hb : b ∈ˢ TBv S ℓ ρ) :
    WellDenoted V (cons b (cons a (pairFrame S ρ))) (eqA1 S.w ℓ) := by
  simp only [eqA1, rds5, List.cons_append, List.nil_append, mkPisAV, WellDenoted_pi]
  refine ⟨wd_motA _ _ _, fun MA hMA => ⟨wd_motB _ _ _, fun MB hMB => ?_⟩⟩
  have hf := frameAt_two S ρ a b
  have hMA' := motA_mem_of hf hMA
  have hMB' := motB_mem_of hf hMB
  refine ⟨wd_minA0 hf hMA', fun mA0 hmA0 => ⟨wd_minA1 hf hMA' hMB', fun mA1 hmA1 =>
    ⟨wd_minB0 hf hMA' hMB', fun mB0 hmB0 => ⟨trivial, fun b' hb' => ?_⟩⟩⟩⟩
  have h := fit5_of hf hMA hMB hmA0 hmA1 hmB0
  change b' ∈ˢ Bstar S at hb'
  rw [WellDenoted_eqE, lhsA1, rhsA1]
  have hca1 : WellDenoted V
      (cons b' (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA (cons b (cons a (pairFrame S ρ)))))))))
      (.app (ca1 8) (.bvar 0)) := by
    rw [WellDenoted_app]
    exact ⟨trivial, trivial, 1, Bstar S, fun _ => Astar S, cA1_mem S, hb',
      fun h0 => absurd h0 Nat.one_ne_zero⟩
  refine ⟨(mkAppN_wellDenoted_of_chain ?_ (wd_spine8_app _ hca1) ?_).1, ?_⟩
  · trivial
  · change AppChainOk a [MA, MB, mA0, mA1, mB0, app (lamR 1 (Bstar S) S.mkA1) b']
    rw [app_lamR_pos Nat.one_ne_zero hb']
    exact appChainOk_of_mkPisAV' rdsA_bits (fun h0 as' hsp => concA_zero S ℓ ρ h0 hsp) ha
      (spineFit_rdsA S ℓ ρ h (mkA1_mem_Astar S hb'))
  · rw [WellDenoted_app]
    refine ⟨?_, (mkAppN_wellDenoted_of_chain ?_ (wd_spine8_last _) ?_).1, ℓ, app MB b',
      fun _ => app MA (S.mkA1 b'), ?_, ?_, fun h0 _ _ => ?_⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, trivial, ℓ, Bstar S, fun x => piR ℓ (app MB x) fun _ => app MA (S.mkA1 x),
        h.hmA1, hb', fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero⟩
    · trivial
    · change AppChainOk b [MA, MB, mA0, mA1, mB0, b']
      exact appChainOk_of_mkPisAV' rdsB_bits (fun h0 as' hsp => concB_zero S ℓ ρ h0 hsp) hb
        (spineFit_rdsB S ℓ ρ h hb')
    · change app mA1 b' ∈ˢ _
      exact app_mem_piR h.hmA1 hb' (fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero)
    · change [MA, MB, mA0, mA1, mB0, b'].foldl SetTheory.app b ∈ˢ app MB b'
      exact mkPisAV_fold_mem rdsB_bits (fun h0 as' hsp => concB_zero S ℓ ρ h0 hsp) hb
        (spineFit_rdsB S ℓ ρ h hb')
    · have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hMA' (mkA1_mem_Astar S hb')
      rwa [h0, univ_zero] at this

theorem wd_eqB0 {a b : V} (ha : a ∈ˢ TAv S ℓ ρ) (hb : b ∈ˢ TBv S ℓ ρ) :
    WellDenoted V (cons b (cons a (pairFrame S ρ))) (eqB0 S.w ℓ) := by
  simp only [eqB0, rds5, List.cons_append, List.nil_append, mkPisAV, WellDenoted_pi]
  refine ⟨wd_motA _ _ _, fun MA hMA => ⟨wd_motB _ _ _, fun MB hMB => ?_⟩⟩
  have hf := frameAt_two S ρ a b
  have hMA' := motA_mem_of hf hMA
  have hMB' := motB_mem_of hf hMB
  refine ⟨wd_minA0 hf hMA', fun mA0 hmA0 => ⟨wd_minA1 hf hMA' hMB', fun mA1 hmA1 =>
    ⟨wd_minB0 hf hMA' hMB', fun mB0 hmB0 => ⟨trivial, fun a' ha' => ?_⟩⟩⟩⟩
  have h := fit5_of hf hMA hMB hmA0 hmA1 hmB0
  change a' ∈ˢ Astar S at ha'
  rw [WellDenoted_eqE, lhsB0, rhsB0]
  have hcb0 : WellDenoted V
      (cons a' (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA (cons b (cons a (pairFrame S ρ)))))))))
      (.app (cb0 8) (.bvar 0)) := by
    rw [WellDenoted_app]
    exact ⟨trivial, trivial, 1, Astar S, fun _ => Bstar S, cB0_mem S, ha',
      fun h0 => absurd h0 Nat.one_ne_zero⟩
  refine ⟨(mkAppN_wellDenoted_of_chain ?_ (wd_spine8_app _ hcb0) ?_).1, ?_⟩
  · trivial
  · change AppChainOk b [MA, MB, mA0, mA1, mB0, app (lamR 1 (Astar S) S.mkB0) a']
    rw [app_lamR_pos Nat.one_ne_zero ha']
    exact appChainOk_of_mkPisAV' rdsB_bits (fun h0 as' hsp => concB_zero S ℓ ρ h0 hsp) hb
      (spineFit_rdsB S ℓ ρ h (mkB0_mem_Bstar S ha'))
  · rw [WellDenoted_app]
    refine ⟨?_, (mkAppN_wellDenoted_of_chain ?_ (wd_spine8_last _) ?_).1, ℓ, app MA a',
      fun _ => app MB (S.mkB0 a'), ?_, ?_, fun h0 _ _ => ?_⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, trivial, ℓ, Astar S, fun x => piR ℓ (app MA x) fun _ => app MB (S.mkB0 x),
        h.hmB0, ha', fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero⟩
    · trivial
    · change AppChainOk a [MA, MB, mA0, mA1, mB0, a']
      exact appChainOk_of_mkPisAV' rdsA_bits (fun h0 as' hsp => concA_zero S ℓ ρ h0 hsp) ha
        (spineFit_rdsA S ℓ ρ h ha')
    · change app mB0 a' ∈ˢ _
      exact app_mem_piR h.hmB0 ha' (fun h0 _ _ => by rw [h0]; exact piR_zero_mem_univZero)
    · change [MA, MB, mA0, mA1, mB0, a'].foldl SetTheory.app a ∈ˢ app MA a'
      exact mkPisAV_fold_mem rdsA_bits (fun h0 as' hsp => concA_zero S ℓ ρ h0 hsp) ha
        (spineFit_rdsA S ℓ ρ h ha')
    · have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hMB' (mkB0_mem_Bstar S ha')
      rwa [h0, univ_zero] at this

/-- The `Prop`-level pair is graded. -/
theorem wd_andAV {P Q : AnnotTerm} {ρ' : Nat → V} (hP : WellDenoted V ρ' P) (hQ : WellDenoted V ρ' Q)
    (hPu : interp V ρ' P ∈ˢ (univZero : V)) (hQu : interp V ρ' Q ∈ˢ (univZero : V)) :
    WellDenoted V ρ' (andAV P Q) := by
  have hP' : interp V ρ' P ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hPu
  have hQ' : interp V ρ' Q ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hQu
  have hlam : interp V ρ' (.lam 1 P (Q.liftN 1 0)) = lamR 1 (interp V ρ' P) fun _ => interp V ρ' Q := by
    rw [interp_lam]
    exact lamR_congr fun x _ => by rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
  show WellDenoted V ρ' (.app (.app (.const .psigma [0, 0]) P) (.lam 1 P (Q.liftN 1 0)))
  rw [WellDenoted_app]
  refine ⟨?_, ?_, 1, psigmaFibreSpace V 0 (interp V ρ' P), fun _ => (univ 0 : V), ?_, ?_,
    fun h0 => absurd h0 Nat.one_ne_zero⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, hP, 1, univ 0, fun A => piR 1 (psigmaFibreSpace V 0 A) fun _ => (univ 0 : V),
      psigmaV_00_mem, hP', fun h0 => absurd h0 Nat.one_ne_zero⟩
  · rw [WellDenoted_lam]
    refine ⟨hP, fun x _ => ?_, fun _ => (univ 0 : V), fun x _ => ?_,
      fun h0 => absurd h0 Nat.one_ne_zero⟩
    · rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hQ
    · rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hQ'
  · show SetTheory.app (psigmaV V 0 0) (interp V ρ' P) ∈ˢ _
    exact app_mem_piR_pos Nat.one_ne_zero psigmaV_00_mem hP'
  · rw [hlam]
    exact lamR_mem fun _ _ => hQ'

theorem wd_eqs {a b : V} (ha : a ∈ˢ TAv S ℓ ρ) (hb : b ∈ˢ TBv S ℓ ρ) :
    WellDenoted V (cons b (cons a (pairFrame S ρ))) (eqs S.w ℓ) :=
  wd_andAV (wd_eqA0 ρ ha) (wd_andAV (wd_eqA1 ρ ha hb) (wd_eqB0 ρ ha hb) (eqA1_univZero _)
    (eqB0_univZero _)) (eqA0_univZero _) (andAV_univZero (eqA1_univZero _) (eqB0_univZero _))

variable (S ℓ)

theorem wd_inner {a : V} (ha : a ∈ˢ TAv S ℓ ρ) :
    WellDenoted V (cons a (pairFrame S ρ)) (inner S.w ℓ) := by
  have hps0 := psigmaV_mem (V := V) (sLev S.w ℓ) 0
  rw [natMax_zero] at hps0
  show WellDenoted V (cons a (pairFrame S ρ)) (.app (.app (.const .psigma [sLev S.w ℓ, 0])
    ((TB S.w ℓ).liftN 1 0)) (.lam 1 ((TB S.w ℓ).liftN 1 0) (eqs S.w ℓ)))
  rw [WellDenoted_app]
  refine ⟨?_, ?_, sLev S.w ℓ + 1, psigmaFibreSpace V 0 (TBv S ℓ ρ),
    fun _ => (univ (sLev S.w ℓ) : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · rw [WellDenoted_app]
    refine ⟨trivial, wd_TB_lift S ℓ ρ a, sLev S.w ℓ + 1, univ (sLev S.w ℓ),
      fun A => piR (sLev S.w ℓ + 1) (psigmaFibreSpace V 0 A) fun _ => (univ (sLev S.w ℓ) : V),
      hps0, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    rw [interp_TB_lift]; exact TBv_univ S ℓ ρ
  · rw [WellDenoted_lam]
    refine ⟨wd_TB_lift S ℓ ρ a, fun b hb => ?_, fun _ => (univ 0 : V), fun b _ => ?_,
      fun h0 => absurd h0 Nat.one_ne_zero⟩
    · rw [interp_TB_lift] at hb
      exact wd_eqs ρ ha hb
    · rw [univ_zero]; exact eqs_univZero _
  · show SetTheory.app (psigmaV V (sLev S.w ℓ) 0)
      (interp V (cons a (pairFrame S ρ)) ((TB S.w ℓ).liftN 1 0)) ∈ˢ _
    rw [interp_TB_lift]
    exact app_mem_piR_pos (Nat.succ_ne_zero _) hps0 (TBv_univ S ℓ ρ)
  · rw [interp_innerLam]; exact innerLam_mem S ℓ ρ a

theorem wd_sig : WellDenoted V (pairFrame S ρ) (sig S.w ℓ) := by
  have hps := psigmaV_mem (V := V) (sLev S.w ℓ) (sLev S.w ℓ)
  rw [natMax_self] at hps
  show WellDenoted V (pairFrame S ρ) (.app (.app (.const .psigma [sLev S.w ℓ, sLev S.w ℓ])
    (TA S.w ℓ)) (.lam (sLev S.w ℓ + 1) (TA S.w ℓ) (inner S.w ℓ)))
  rw [WellDenoted_app]
  refine ⟨?_, ?_, sLev S.w ℓ + 1, psigmaFibreSpace V (sLev S.w ℓ) (TAv S ℓ ρ),
    fun _ => (univ (sLev S.w ℓ) : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, wd_TA S ℓ ρ, sLev S.w ℓ + 1, univ (sLev S.w ℓ),
      fun A => piR (sLev S.w ℓ + 1) (psigmaFibreSpace V (sLev S.w ℓ) A)
        fun _ => (univ (sLev S.w ℓ) : V),
      hps, TAv_univ S ℓ ρ, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · rw [WellDenoted_lam]
    refine ⟨wd_TA S ℓ ρ, fun a ha => wd_inner S ℓ ρ ha, fun _ => (univ (sLev S.w ℓ) : V),
      fun a _ => ?_, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    rw [interp_inner]; exact innerV_univ S ℓ ρ a
  · show SetTheory.app (psigmaV V (sLev S.w ℓ) (sLev S.w ℓ)) (TAv S ℓ ρ) ∈ˢ _
    exact app_mem_piR_pos (Nat.succ_ne_zero _) hps (TAv_univ S ℓ ρ)
  · rw [interp_sigLam]; exact sigLam_mem S ℓ ρ

theorem choiceV_mem :
    choiceV V (sLev S.w ℓ) ∈ˢ piR (sLev S.w ℓ) (univ (sLev S.w ℓ) : V)
      (fun A => piR (sLev S.w ℓ) (dnegSpace V A) fun _ => A) :=
  lamR_mem fun _ _ => lamR_mem fun _ hh => schoice_mem (exists_mem_of_dneg V hh).choose_spec

theorem wd_sel : WellDenoted V (pairFrame S ρ) (sel S.w ℓ) := by
  show WellDenoted V (pairFrame S ρ) (.app (.app (.const .choice [sLev S.w ℓ]) (sig S.w ℓ)) .prf)
  rw [WellDenoted_app]
  refine ⟨?_, trivial, sLev S.w ℓ, dnegSpace V (sigV S ℓ ρ), fun _ => sigV S ℓ ρ, ?_, ?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨trivial, wd_sig S ℓ ρ, sLev S.w ℓ, univ (sLev S.w ℓ),
      fun A => piR (sLev S.w ℓ) (dnegSpace V A) fun _ => A, choiceV_mem S ℓ, ?_, fun h0 A _ => ?_⟩
    · rw [interp_sig]; exact sigV_univ S ℓ ρ
    · show piR (sLev S.w ℓ) _ _ ∈ˢ _
      rw [h0]; exact piR_zero_mem_univZero
  · show SetTheory.app (choiceV V (sLev S.w ℓ)) (interp V (pairFrame S ρ) (sig S.w ℓ)) ∈ˢ _
    rw [interp_sig]
    refine app_mem_piR (choiceV_mem S ℓ) (sigV_univ S ℓ ρ) (fun h0 A _ => ?_)
    show piR (sLev S.w ℓ) _ _ ∈ˢ _
    rw [h0]; exact piR_zero_mem_univZero
  · exact pt_mem_dnegSpace_of (sigV_inhabited S ℓ ρ).choose_spec
  · intro h0 _ _
    have := sigV_univ S ℓ ρ
    rwa [h0, univ_zero] at this

/-- **`A.rec`'s leaf is graded.** -/
theorem wd_recA : WellDenoted V (pairFrame S ρ) (recA S.w ℓ) := by
  rw [recA, WellDenoted_fst]
  refine ⟨wd_sel S ℓ ρ, sLev S.w ℓ, sLev S.w ℓ, TAv S ℓ ρ, fun a => innerV S ℓ ρ a, ?_,
    TAv_univ S ℓ ρ, fun a _ => innerV_univ S ℓ ρ a⟩
  rw [interp_sel, natMax_self]; exact sel_mem S ℓ ρ

/-- **`B.rec`'s leaf is graded.** -/
theorem wd_recB : WellDenoted V (pairFrame S ρ) (recB S.w ℓ) := by
  obtain ⟨a, e, ha, he, hz, hpos⟩ := mem_sigma_elim
    (show schoice (sigV S ℓ ρ) ∈ˢ sigmaSet (sLev S.w ℓ) (TAv S ℓ ρ) (fun a => innerV S ℓ ρ a)
      from sel_mem S ℓ ρ)
  have hsnd : ssnd (schoice (sigV S ℓ ρ)) ∈ˢ innerV S ℓ ρ a := by
    by_cases hs : sLev S.w ℓ = 0
    · rw [hz hs, ssnd_pt]
      have hpt : e = pt := mem_univ_zero (hs ▸ innerV_univ S ℓ ρ a) he
      rw [hpt] at he; exact he
    · rw [hpos hs, ssnd_spair]; exact he
  rw [recB, WellDenoted_fst]
  refine ⟨?_, sLev S.w ℓ, 0, TBv S ℓ ρ, fun b => eqsV S ℓ ρ a b, ?_, TBv_univ S ℓ ρ,
    fun b _ => by rw [univ_zero]; exact eqs_univZero (cons b (cons a (pairFrame S ρ)))⟩
  · rw [WellDenoted_snd]
    refine ⟨wd_sel S ℓ ρ, sLev S.w ℓ, sLev S.w ℓ, TAv S ℓ ρ, fun a => innerV S ℓ ρ a, ?_,
      TAv_univ S ℓ ρ, fun a _ => innerV_univ S ℓ ρ a⟩
    rw [interp_sel, natMax_self]; exact sel_mem S ℓ ρ
  · show ssnd (interp V (pairFrame S ρ) (sel S.w ℓ)) ∈ˢ _
    rw [interp_sel, natMax_zero]; exact hsnd

/-! ## The ι rules, read off the chosen tuple -/

variable {S ℓ}

theorem iota_a0_of {a b : V}
    (h1 : (pt : V) ∈ˢ interp V (cons b (cons a (pairFrame S ρ))) (eqA0 S.w ℓ))
    {MA MB mA0 mA1 mB0 : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0) :
    [MA, MB, mA0, mA1, mB0, S.mkA0].foldl SetTheory.app a = mA0 := by
  simp only [eqA0, rds5, mkPisAV, interp_pi] at h1
  have hf := frameAt_two S ρ a b
  obtain ⟨y, hy⟩ := piR_zero_elim h1 (h.mem_motA hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_motB hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA0 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA1 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minB0 hf)
  rw [interp_eqE, interp_lhsA0, interp_rhsA0] at hy
  exact eq_of_mem_eqv hy

theorem iota_a1_of {a b : V}
    (h1 : (pt : V) ∈ˢ interp V (cons b (cons a (pairFrame S ρ))) (eqA1 S.w ℓ))
    {MA MB mA0 mA1 mB0 : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0) {b' : V} (hb' : b' ∈ˢ Bstar S) :
    [MA, MB, mA0, mA1, mB0, S.mkA1 b'].foldl SetTheory.app a
      = app (app mA1 b') ([MA, MB, mA0, mA1, mB0, b'].foldl SetTheory.app b) := by
  simp only [eqA1, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi] at h1
  have hf := frameAt_two S ρ a b
  obtain ⟨y, hy⟩ := piR_zero_elim h1 (h.mem_motA hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_motB hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA0 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA1 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minB0 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (show b' ∈ˢ interp V
    (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA (cons b (cons a (pairFrame S ρ)))))))) (tB 7)
    from hb')
  rw [interp_eqE, interp_lhsA1, interp_rhsA1] at hy
  have := eq_of_mem_eqv hy
  change [MA, MB, mA0, mA1, mB0, app (lamR 1 (Bstar S) S.mkA1) b'].foldl SetTheory.app a
    = app (app mA1 b') ([MA, MB, mA0, mA1, mB0, b'].foldl SetTheory.app b) at this
  rwa [app_lamR_pos Nat.one_ne_zero hb'] at this

theorem iota_b0_of {a b : V}
    (h1 : (pt : V) ∈ˢ interp V (cons b (cons a (pairFrame S ρ))) (eqB0 S.w ℓ))
    {MA MB mA0 mA1 mB0 : V} (h : Fit5 S ℓ MA MB mA0 mA1 mB0) {a' : V} (ha' : a' ∈ˢ Astar S) :
    [MA, MB, mA0, mA1, mB0, S.mkB0 a'].foldl SetTheory.app b
      = app (app mB0 a') ([MA, MB, mA0, mA1, mB0, a'].foldl SetTheory.app a) := by
  simp only [eqB0, rds5, List.cons_append, List.nil_append, mkPisAV, interp_pi] at h1
  have hf := frameAt_two S ρ a b
  obtain ⟨y, hy⟩ := piR_zero_elim h1 (h.mem_motA hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_motB hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA0 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minA1 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (h.mem_minB0 hf)
  obtain ⟨y, hy⟩ := piR_zero_elim hy (show a' ∈ˢ interp V
    (cons mB0 (cons mA1 (cons mA0 (cons MB (cons MA (cons b (cons a (pairFrame S ρ)))))))) (tA 7)
    from ha')
  rw [interp_eqE, interp_lhsB0, interp_rhsB0] at hy
  have := eq_of_mem_eqv hy
  change [MA, MB, mA0, mA1, mB0, app (lamR 1 (Astar S) S.mkB0) a'].foldl SetTheory.app b
    = app (app mB0 a') ([MA, MB, mA0, mA1, mB0, a'].foldl SetTheory.app a) at this
  rwa [app_lamR_pos Nat.one_ne_zero ha'] at this

variable (S ℓ)

/-- **THE FALSIFIER'S VERDICT — PASSED.**  The two leaves are typed at
official's shape, graded, and satisfy the three ι rules at every
official spine `(MA, MB, mA0, mA1, mB0)`, in both regimes. -/
theorem pairRecTerms :
    interp V (pairFrame S ρ) (recA S.w ℓ) ∈ˢ interp V (pairFrame S ρ) (TA S.w ℓ) ∧
    interp V (pairFrame S ρ) (recB S.w ℓ) ∈ˢ interp V (pairFrame S ρ) (TB S.w ℓ) ∧
    WellDenoted V (pairFrame S ρ) (recA S.w ℓ) ∧ WellDenoted V (pairFrame S ρ) (recB S.w ℓ) ∧
    ∀ MA MB mA0 mA1 mB0 : V,
      SpineFit (pairFrame S ρ) ((rds5 S.w ℓ ℓ 0).map (·.2.2)) [MA, MB, mA0, mA1, mB0] →
      [MA, MB, mA0, mA1, mB0, S.mkA0].foldl SetTheory.app
          (interp V (pairFrame S ρ) (recA S.w ℓ)) = mA0 ∧
      (∀ b, b ∈ˢ Bstar S →
        [MA, MB, mA0, mA1, mB0, S.mkA1 b].foldl SetTheory.app
            (interp V (pairFrame S ρ) (recA S.w ℓ))
          = app (app mA1 b) ([MA, MB, mA0, mA1, mB0, b].foldl SetTheory.app
              (interp V (pairFrame S ρ) (recB S.w ℓ)))) ∧
      (∀ a, a ∈ˢ Astar S →
        [MA, MB, mA0, mA1, mB0, S.mkB0 a].foldl SetTheory.app
            (interp V (pairFrame S ρ) (recB S.w ℓ))
          = app (app mB0 a) ([MA, MB, mA0, mA1, mB0, a].foldl SetTheory.app
              (interp V (pairFrame S ρ) (recA S.w ℓ)))) := by
  obtain ⟨a, b, ha, hb, hpt, hra, hrb⟩ := sel_facts S ℓ ρ
  obtain ⟨h0, h1, h2⟩ := (pt_mem_eqs_iff (S := S) (ℓ := ℓ) (cons b (cons a (pairFrame S ρ)))).mp hpt
  rw [hra, hrb]
  refine ⟨ha, hb, wd_recA S ℓ ρ, wd_recB S ℓ ρ, fun MA MB mA0 mA1 mB0 hsp => ?_⟩
  have h := fit5_of_spine S ℓ ρ hsp
  exact ⟨iota_a0_of ρ h0 h, fun b' hb' => iota_a1_of ρ h1 h hb', fun a' ha' => iota_b0_of ρ h2 h ha'⟩

end Semantics

end BlockRecPair

end ConLeche.Semantics
