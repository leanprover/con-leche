module

public import ConLeche.Model.Inductives.TargetRecRead
public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Inductives.TargetCallRead
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.PosFieldLeaf
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Subst
import ConLeche.Semantics.Tower.BlockTower

public section

/-!
# The call frame's field move, read

A call's typing runs at the ABSTRACT frame (`targetCallOk`): the rule's
frame (prefix and fields, `D = rP + nF`), the member holes (`D … B - 1`,
`B = D + k`), then the fields again (`B …`), annotated at the holes
(`targetAbsFields`).  `targetMoveF rP L` moves the fields `rP + j` to
their copies `L[j] = fvar (B + j)`.  Read, the move is a parallel
substitution (`moveS`, erasure-equal: `targetMoveF_erasedEq`), and at the
valuation that gives each copy its field's own value it reads as the
unmoved term at the holes' frame (`substE_moveTau`, `move_read`,
`move_interp`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- The move's index map: field `rP + j` (`j < n`) to `B + j`. -/
@[expose] def moveIdx (rP n B i : Nat) : Nat :=
  if rP ≤ i ∧ i < rP + n then B + (i - rP) else i

/-- The move as a parallel substitution of the variables below `B`. -/
@[expose] def moveS (rP n B : Nat) (i : Nat) : Expr := .fvar (moveIdx rP n B i) (.sort .zero)

/-- The substitution the move's reading applies (`denoteMeta_substFvars`). -/
@[expose] def moveTau (rP n B : Nat) : Nat → AnnotTerm :=
  substTau B (B + n) (fun i => .bvar (B + n - 1 - moveIdx rP n B i))

theorem moveS_ok {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {rP n B : Nat} :
    ∀ i, i < B → Expr.WScoped (B + n) (moveS rP n B i) ∧
      (moveS rP n B i).looseBVarsBounded 0 = true ∧
      denoteMeta acval env φ (B + n) (moveS rP n B i)
        = some (.bvar (B + n - 1 - moveIdx rP n B i)) := by
  intro i hi
  refine ⟨?_, rfl, denoteMeta_fvar _ _ _ _⟩
  simp only [moveS, moveIdx, Expr.WScoped]
  refine ⟨?_, trivial⟩
  split <;> omega

/-- **The move is the substitution, up to annotations.** -/
theorem targetMoveF_erasedEq {rP n B : Nat} {L : List Expr} (hn : L.length = n)
    (hL : ∀ j, j < n → ∃ ty, L[j]? = some (.fvar (B + j) ty)) :
    ∀ (X : Expr), X.fvarsBelow B →
      Expr.ErasedEq (ConLeche.targetMoveF rP L X) (Expr.substFvars B (B + n) (moveS rP n B) X) := by
  intro X hX
  refine Expr.replaceFVars_erasedEq_substFvars (fun v _ ty => ?_) X hX
  simp only [moveS, moveIdx]
  by_cases h1 : rP ≤ v
  · rw [if_pos h1]
    by_cases h2 : v - rP < n
    · obtain ⟨ty', hty'⟩ := hL (v - rP) h2
      rw [hty', Option.getD_some, if_pos ⟨h1, by omega⟩]
      rfl
    · rw [List.getElem?_eq_none (by omega), Option.getD_none, if_neg (by omega)]
      rfl
  · rw [if_neg h1, Option.getD_none, if_neg (by omega)]
    rfl

/-- **The substituted valuation is the holes' frame's** when every moved
field's copy carries the field's own value. -/
theorem substE_moveTau {rP nF k n B : Nat} {xs fs hv : List V} {ρ : Nat → V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (hhv : hv.length = k) (hn : n ≤ nF)
    (hB : rP + nF + k = B) :
    substE V (moveTau rP n B) 0 (consList (fs.take n) (consList hv (consList (xs ++ fs) ρ)))
      = consList hv (consList (xs ++ fs) ρ) := by
  subst hB
  funext p
  have hlen : (xs ++ fs).length = rP + nF := by rw [List.length_append, hxs, hfs]
  have htn : (fs.take n).length = n := by rw [List.length_take]; omega
  simp only [substE, Nat.not_lt_zero, if_false, shiftE_zero_zero, Nat.sub_zero, moveTau, substTau]
  by_cases hp : p < rP + nF + k
  · rw [if_pos hp, interp_bvar]
    simp only [moveIdx]
    by_cases hm : rP ≤ rP + nF + k - 1 - p ∧ rP + nF + k - 1 - p < rP + n
    · -- a moved field: its copy
      rw [if_pos hm]
      have hj : rP + nF + k - 1 - p - rP < n := by omega
      obtain ⟨a, ha⟩ : ∃ a, fs[rP + nF + k - 1 - p - rP]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [consList_apply_lt _ _ _ (by omega), htn,
        List.getElem?_take_of_lt (by omega),
        show n - 1 - (rP + nF + k + n - 1 - (rP + nF + k + (rP + nF + k - 1 - p - rP)))
          = rP + nF + k - 1 - p - rP by omega, ha, Option.getD_some]
      rw [show p = (p - k) + hv.length by omega, consList_apply_add,
        consList_apply_lt _ _ _ (by omega), hlen,
        show rP + nF - 1 - (p - k) = rP + (rP + nF + k - 1 - p - rP) by omega,
        List.getElem?_append_right (by omega), hxs, Nat.add_sub_cancel_left, ha, Option.getD_some]
    · rw [if_neg hm]
      rw [show rP + nF + k + n - 1 - (rP + nF + k - 1 - p) = p + (fs.take n).length by omega,
        consList_apply_add]
  · rw [if_neg hp, interp_bvar,
      show p - (rP + nF + k) + (rP + nF + k + n) = p + (fs.take n).length by omega,
      consList_apply_add]

section Read

variable {env : Env} {φ : Name → Nat}

/-- **The moved term reads as the substituted reading**, opened at locals
above each frame. -/
theorem move_read (m : EnvModel V env) {rP n B : Nat} {L : List Expr}
    (hn : L.length = n) (hL : ∀ j, j < n → ∃ ty, L[j]? = some (.fvar (B + j) ty))
    {X : Expr} (hX : X.fvarsBelow B) {t : Nat} {os osA : List Expr}
    (hos : LocList B t os) (hosA : LocList (B + n) t osA) :
    denoteMeta m.acval env φ (B + n + t) ((ConLeche.targetMoveF rP L X).instantiateList osA 0)
      = (denoteMeta m.acval env φ (B + t) (X.instantiateList os 0)).map
          (AnnotTerm.substAV (moveTau rP n B) · t) := by
  have hs := moveS_ok (acval := m.acval) (env := env) (φ := φ) (rP := rP) (n := n) (B := B)
  have hsb : ∀ v, v < B → (moveS rP n B v).looseBVarsBounded 0 = true := fun v hv => (hs v hv).2.1
  have hE0 : Expr.ErasedEq ((ConLeche.targetMoveF rP L X).instantiateList osA 0)
      (Expr.substFvars B (B + n) (moveS rP n B) (X.instantiateList os 0)) :=
    (erasedEq_instantiateList osA 0 (targetMoveF_erasedEq hn hL X hX)).trans
      (Expr.substFvars_instantiateList hsb t os osA hos.1 hosA.1
        (fun j hj => by
          obtain ⟨ty, h1⟩ := hos.2 j hj
          obtain ⟨ty', h2⟩ := hosA.2 j hj
          exact ⟨ty, ty', h1, h2⟩) X 0)
  have hfb : Expr.fvarsBelow (B + t) (X.instantiateList os 0) :=
    fvarsBelow_instantiateList os (by simpa using hos.fvarsBelow) X 0
      (Expr.fvarsBelow_mono (Nat.le_add_right B t) hX)
  rw [denoteMeta_erasedEq hE0]
  exact denoteMeta_substFvars m hs _ t hfb

end Read

/-- **At the copies' own values the substituted reading is the unmoved
one**, below a spine of locals: its value, and its grading both ways. -/
theorem move_interp {rP nF k n B : Nat} {xs fs hv : List V} {ρ : Nat → V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (hhv : hv.length = k) (hn : n ≤ nF)
    (hB : rP + nF + k = B) (R : AnnotTerm) (bs : List V) :
    interp V (consList bs (consList (fs.take n) (consList hv (consList (xs ++ fs) ρ))))
        (AnnotTerm.substAV (moveTau rP n B) R bs.length)
      = interp V (consList bs (consList hv (consList (xs ++ fs) ρ))) R ∧
    (WellDenoted V (consList bs (consList (fs.take n) (consList hv (consList (xs ++ fs) ρ))))
        (AnnotTerm.substAV (moveTau rP n B) R bs.length)
      ↔ WellDenoted V (consList bs (consList hv (consList (xs ++ fs) ρ))) R) := by
  have hE : substE V (moveTau rP n B) bs.length
      (consList bs (consList (fs.take n) (consList hv (consList (xs ++ fs) ρ))))
      = consList bs (consList hv (consList (xs ++ fs) ρ)) := by
    rw [show bs.length = bs.length + 0 from rfl, substE_consList,
      substE_moveTau hxs hfs hhv hn hB]
  refine ⟨by rw [interp_substAV, hE], ?_⟩
  rw [WellDenoted_substAV _ _ _ _ (fun j => ?_), hE]
  simp only [moveTau, substTau]
  split <;> simp

end ConLeche.Model
