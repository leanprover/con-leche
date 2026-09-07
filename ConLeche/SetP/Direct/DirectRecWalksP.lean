import ConLeche.SetP.Direct.DirectRecFramesP

/-!
# The recursor leaf's walks (task #175 W4c, P3 module 6, part 14)

`recWalks`: the recursor leaf's two hereditary premises — `RecPre`
along the parameters (ending in `RecBase`) and `UnderTowerValid` along
the whole frame — from the recursor context's gradings and the frames'
`RecBase`; and the frame split `rds = params ++ [motive, minor, major]`
the leaf's laws are spelled over.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-- A list of length three is its three entries. -/
theorem list_eq_of_length_three {α : Type _} [Inhabited α] {l : List α} (h : l.length = 3) :
    l = [l.getD 0 default, l.getD 1 default, l.getD 2 default] := by
  match l, h with
  | [a, b, c], _ => rfl

/-- The recursor's binder data split at the parameters. -/
theorem rec_split {rds : List (Nat × Nat × AVExpr)} {nP : Nat} (hlen : rds.length = nP + 3) :
    rds = rds.take nP ++ [rds.getD nP default, rds.getD (nP + 1) default,
      rds.getD (nP + 2) default] := by
  have h3 : (rds.drop nP).length = 3 := by simp [hlen]
  have := list_eq_of_length_three h3
  rw [getD_drop', getD_drop', getD_drop', Nat.add_zero] at this
  calc rds = rds.take nP ++ rds.drop nP := (List.take_append_drop nP rds).symm
    _ = _ := by rw [this]

/-- **The recursor leaf's hereditary premises.** -/
theorem recWalks {ℓ w : Nat} {Fs : List AVExpr} {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3)
    (okΓ : ∀ i, i < nP + 3 → ∀ ρ : Nat → V,
      Sat2 V (((rds.map (·.2.2)).reverse).drop (nP + 3 - i)) ρ →
      AnnotOkP V ρ (((rds.map (·.2.2)).reverse).getD (nP + 3 - 1 - i) default))
    (hbase : ∀ ρ : Nat → V, Sat2 V ((((rds.take nP).map (·.2.2)).reverse)) ρ →
      RecBase ℓ w ρ Fs (rds.getD nP default) (rds.getD (nP + 1) default)
        (rds.getD (nP + 2) default)) :
    ∀ ρ : Nat → V,
      RecPre ℓ w ρ Fs (rds.getD nP default) (rds.getD (nP + 1) default)
          (rds.getD (nP + 2) default) (rds.take nP) ∧
      UnderTowerValid ρ (recBodyAV Fs.length) rds := by
  intro ρ
  have hΓlen : ((rds.map (·.2.2)).reverse).length = nP + 3 := by simp [hlen]
  have hdrop3 := drop_three_rec hlen
  have hlenT : (rds.take nP).length = nP := by simp [hlen]
  have hΓplen : ((((rds.take nP).map (·.2.2)).reverse)).length = nP := by simp [hlen]
  constructor
  · -- `RecPre` along the parameters
    have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
        Sat2 V (((((rds.take nP).map (·.2.2)).reverse)).drop (nP - i)) ρ →
        AnnotOkP V ρ (((((rds.take nP).map (·.2.2)).reverse)).getD (nP - 1 - i) default) := by
      intro i hi ρ hρ
      have := okΓ i (by omega) ρ (by
        rw [show nP + 3 - i = 3 + (nP - i) from by omega, ← List.drop_drop, hdrop3]
        exact hρ)
      rwa [show nP + 3 - 1 - i = 3 + (nP - 1 - i) from by omega, ← getD_drop', hdrop3] at this
    have hent : ∀ i, i < nP → ∃ q, (rds.take nP)[i]? = some q ∧
        q.2.2 = ((((rds.take nP).map (·.2.2)).reverse)).getD (nP - 1 - i) default := by
      intro i hi
      have hil : i < (rds.take nP).length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlenT hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds => RecPre ℓ w ρ Fs (rds.getD nP default) (rds.getD (nP + 1) default)
        (rds.getD (nP + 2) default) pds)
      hΓplen hlenT hent okΓp (fun ρ hρ => hbase ρ hρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw
  · -- `UnderTowerValid` along the whole frame
    have hent : ∀ i, i < nP + 3 → ∃ q, rds[i]? = some q ∧
        q.2.2 = ((rds.map (·.2.2)).reverse).getD (nP + 3 - 1 - i) default := by
      intro i hi
      have hil : i < rds.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlen hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (recBodyAV Fs.length) ds')
      hΓlen hlen hent okΓ (fun ρ _ => recBodyAV_validV Fs.length ρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw

/-- **The recursor leaf's P currency and membership**, at every frame. -/
theorem recLeafFacts {ℓ w : Nat} {Fs : List AVExpr} {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3)
    (hz : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0))
    (okΓ : ∀ i, i < nP + 3 → ∀ ρ : Nat → V,
      Sat2 V (((rds.map (·.2.2)).reverse).drop (nP + 3 - i)) ρ →
      AnnotOkP V ρ (((rds.map (·.2.2)).reverse).getD (nP + 3 - 1 - i) default))
    (hbase : ∀ ρ : Nat → V, Sat2 V ((((rds.take nP).map (·.2.2)).reverse)) ρ →
      RecBase ℓ w ρ Fs (rds.getD nP default) (rds.getD (nP + 1) default)
        (rds.getD (nP + 2) default)) :
    ∀ ρ : Nat → V,
      AnnotOkP V ρ (directRecAV ℓ rds Fs.length) ∧
      interp2 V ρ (directRecAV ℓ rds Fs.length)
        ∈ˢ interp2 V ρ (mkPisAV rds (.app (.bvar 2) (.bvar 0))) := by
  intro ρ
  obtain ⟨hpre, hval⟩ := recWalks hlen okΓ hbase ρ
  have hsplit := rec_split hlen
  rw [hsplit] at hval hz
  rw [hsplit]
  exact ⟨directRecAV_okP hz hpre hval, directRecAV_mem hz hpre⟩

end ConLeche.SetP
