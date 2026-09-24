module

public import ConLeche.Model.Inductives.FixShadow
public section

/-!
# The X-chains, graded at every family (task #188)

The functor's premise (`XChainsOk`): at every family `X` over the index
tuples and every tuple `t`, a constructor's X-chain — its ordinary
domains lifted past `X` and `t`, its recursive slots reading `X ⟨e⃗⟩`,
the index-equation terminator — is graded (`FieldsOkB`) and its
recursive slots fit (`SlotsFitX`).  The walk along the chain keeps a
**shadow spine** beside the X-chain's values: the same values at the
ordinary slots and a truth value at the recursive ones, which fits the
shadow fields (`shadowFs`: the ordinary domains, `Sort 0` at the
recursive positions) and hence satisfies the shadow context of
`FixShadowP.lean`, where every entry is graded; the entries, the index
expressions and the terminator mention no recursive slot, so their
grading and value carry from the shadow frame to the X-frame
(`interp_congr_noBVar`, `WellDenoted_congr_noBVar`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Kit -/

omit [SetTheory V] in
/-- The shadow spine tracks the X-chain's spine off the recursive
slots. -/
@[expose] def ShadowRel (nP : Nat) (ks : List RecFieldKind) (as as' : List V) : Prop :=
  as'.length = as.length ∧
  ∀ l, l < as.length → ¬ recAt nP ks (nP + l) → as'.getD l pt = as.getD l pt

theorem ShadowRel.nil (nP : Nat) (ks : List RecFieldKind) : ShadowRel (V := V) nP ks [] [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ShadowRel.snoc {nP : Nat} {ks : List RecFieldKind} {as as' : List V}
    (h : ShadowRel nP ks as as') {a a' : V}
    (ha : ¬ recAt nP ks (nP + as.length) → a' = a) :
    ShadowRel nP ks (as ++ [a]) (as' ++ [a']) := by
  refine ⟨by simp [h.1], fun l hl hr => ?_⟩
  simp only [List.length_append, List.length_singleton] at hl
  by_cases hla : l < as.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hla,
      List.getElem?_append_left (by rw [h.1]; exact hla), ← List.getD_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact h.2 l hla hr
  · have hl' : l = as.length := by omega
    subst hl'
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _),
      List.getElem?_append_right (by rw [h.1]; exact Nat.le_refl _),
      h.1, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact ha hr

omit [SetTheory V] in
theorem mem_fvarLeaves_of_getAppArgs : ∀ (e a : Expr), a ∈ e.getAppArgs →
    ∀ l ∈ a.fvarLeaves, l ∈ e.fvarLeaves
  | .app f a', a, ha, l, hl => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.fvarLeaves, List.mem_append]
    rcases ha with ha | rfl
    · exact Or.inl (mem_fvarLeaves_of_getAppArgs f a ha l hl)
    · exact Or.inr hl
  | .bvar _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .fvar _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .sort _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .const _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lam _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .forallE _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .letE _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .proj _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lit _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])

/-! ## Carrying a slot's fit off the shadow frame -/

/-! ## The walk -/

/-! ## Kit (the field entries of the reversed context) -/

omit [SetTheory V] in
theorem drop_map_getD {ds : List (Nat × Nat × AnnotTerm)} {nP nF i : Nat}
    (hlen : ds.length = nP + nF) (hi : i < nF) :
    (((ds.drop nP).map (·.2.2)).getD i default) = (ds.getD (nP + i) default).2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
    List.getElem?_eq_getElem (by omega)]
  rfl

end ConLeche.Model
