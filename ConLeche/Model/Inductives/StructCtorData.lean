module

public import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The constructor's stage data (task #175 W4c, P3 module 6, part 3)

`CtorData`: the constructor type's peeled reading — the binder data
`ds` (parameters then fields), whose codomain bits are zero exactly at
a squash instance, ending in the family applied to the parameter
variables — with its gradings, bounds and level dependence; derived
from the constructor's `checkConstantVal` run at the environment
holding the former (`ctorData_of`), crossed to later stages
(`CtorData.cross`).

`ctorFrames`: the field chain graded at the constructor's parameter
frame (from the field-sort runs), and the two parameter frames
identified (from the binder pins) — the semantic content the former's
real leaf and the constructor's leaf consume.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A spine of position-indexed variables reads to the frame's own
`bvar`s. -/
theorem denoteMetaSpine_indexed {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ (fvs : List Expr) (off : Nat),
      (∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (off + j) ty) →
      DenoteMetaSpine acval env φ d fvs
        ((List.range fvs.length).map fun j => AnnotTerm.bvar (d - 1 - (off + j)))
  | [], _, _ => .nil
  | x :: fvs, off, h => by
    obtain ⟨nm, ty, rfl⟩ := h 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteMeta_fvar]) ?_
    have hmap : (List.range fvs.length).map
          ((fun j => AnnotTerm.bvar (d - 1 - (off + j))) ∘ Nat.succ)
        = (List.range fvs.length).map fun j => AnnotTerm.bvar (d - 1 - (off + 1 + j)) := by
      apply List.map_congr_left
      intro j _
      show AnnotTerm.bvar (d - 1 - (off + (j + 1))) = AnnotTerm.bvar (d - 1 - (off + 1 + j))
      congr 1; omega
    rw [hmap]
    exact denoteMetaSpine_indexed fvs (off + 1) fun j y hy => by
        obtain ⟨ty', hy'⟩ := h (j + 1) y (by simpa using hy)
        exact ⟨ty', by rw [hy']; congr 1; omega⟩

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
@[expose] def paramBvars (nP nF : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP + nF - 1 - k)

omit [SetTheory V] in
theorem consList_range_reverse :
    ∀ (n : Nat) (ρ : Nat → V),
      consList ((List.range n).reverse.map ρ) (fun j => ρ (j + n)) = ρ := by
  intro n
  induction n with
  | zero => intro ρ; funext j; simp
  | succ n ih =>
    intro ρ
    rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have hcons : cons (ρ n) (fun j => ρ (j + (n + 1))) = fun j => ρ (j + n) := by
      funext j
      cases j with
      | zero => rw [cons_zero, Nat.zero_add]
      | succ j => rw [cons_succ]; congr 1; omega
    rw [hcons]
    exact ih ρ

/-- The prefix and suffix of a peeled binder list, as the reversed
context's parts. -/
theorem reverse_map_take_drop (ds : List (Nat × Nat × AnnotTerm)) (nP : Nat) :
    ((ds.map (·.2.2)).reverse)
      = (((ds.drop nP).map (·.2.2)).reverse) ++ (((ds.take nP).map (·.2.2)).reverse) := by
  rw [← List.reverse_append, ← List.map_append, List.take_append_drop]

/-! ## The constructor's data -/


/-! ## Kit: a spine against an equivalent telescope (task #315 M7-3 s7:
moved down from `MutualCore.lean`, where the mutual route proved it —
the native route's `ctor` clause needs it too) -/

/-- A spine fitting one telescope fits another with the same frames
and the same length. -/
theorem spineFit_of_frames {Ds₁ Ds₂ : List AnnotTerm} (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat V Ds₁.reverse ρ ↔ Sat V Ds₂.reverse ρ) {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ Ds₁ as) : SpineFit ρ Ds₂ as := by
  have h1 := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
  rw [List.append_nil] at h1
  have h2 := (hiff _).mp h1
  have h3 := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact h2)
  have hl : as.length = Ds₂.length := by rw [hsp.length_eq, hlen]
  rw [← hl] at h3
  have hfr : (fun j => consList as ρ (j + as.length)) = ρ := by
    funext j; exact consList_apply_add as ρ j
  rw [hfr] at h3
  have hval : (List.range as.length).reverse.map (consList as ρ) = as := by
    have := consList_range_reverse as.length (consList as ρ)
    rw [hfr] at this
    exact consList_inj_of_length (by simp) this
  rw [hval] at h3
  exact h3
where
  consList_inj_of_length {as bs : List V} {ρ : Nat → V} (hl : as.length = bs.length)
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

end ConLeche.Model
