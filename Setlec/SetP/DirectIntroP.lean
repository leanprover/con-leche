import Setlec.SetP.Claims2P
import Setlec.SetBase.TowerRec

/-!
# The direct-structure leaves' bit validity and P packages (task #175, stage 4a)

`AnnotValidV` for the three synthesized leaves, completing the
`AnnotOkP` currency (`AnnotOk2` landed with the leaves themselves in
`SetBase/Tower{Leaf,Mk,Rec}.lean`).

The leaves contain **no `.pi` node** — λ, application, constants,
bound variables and the uniform `.proj` spelling only — so their bit
validity is pure hereditary plumbing: `AnnotValidV`'s one genuine
clause (the `pi` codomain component) never fires, and every lemma
here is a walk with no semantic content beyond the λ-clause guards.
`UnderTowerValid` is the single hereditary premise shape, shared by
all three leaves (each IS a `mkLamsC` tower).

The `AnnotOkP` packages (`directTyAV_okP`/`directMkAV_okP`/
`directRecAV_okP`) pair the SetBase `_ok2` laws with the validity
walks — the `hAok`/`hAvalid` rows of `declStepPM_of_basis_cons`, per
leaf.
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- Hereditary bit validity of a field chain. -/
def FieldsValid (ρ : Nat → V) : List AVExpr → Prop
  | [] => True
  | F :: Fs => AnnotValidV V ρ F ∧
      ∀ a, a ∈ˢ interp2 V ρ F → FieldsValid (cons a ρ) Fs

/-- The carrier body (graph regime) is bit-valid (no `pi` nodes;
hereditary). -/
theorem towerBodyAVPos_validV {w : Nat} :
    ∀ {Fs : List AVExpr} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValidV V ρ (towerBodyAVPos w Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValidV V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAVPos w Fs)))
    rw [AnnotValidV_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValidV_app]
      exact ⟨trivial, hv.1⟩
    · rw [AnnotValidV_lam]
      exact ⟨hv.1, fun a ha => towerBodyAVPos_validV (hv.2 a ha)⟩

/-- The carrier body (squash regime) is bit-valid: every `pi` node
carries bit `0` over a truth-value codomain (`piR 0`, or `Empty`). -/
theorem sqBodyAV_validV :
    ∀ {Fs : List AVExpr} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValidV V ρ (sqBodyAV Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValidV V ρ (negAV (.pi 0 0 F (negAV (sqBodyAV Fs))))
    unfold negAV
    rw [AnnotValidV_pi]
    refine ⟨?_, fun _ _ => by simp, fun _ _ _ => ?_⟩
    · rw [AnnotValidV_pi]
      refine ⟨hv.1, fun x hx => ?_, fun _ x _ => ?_⟩
      · rw [AnnotValidV_pi]
        exact ⟨sqBodyAV_validV (hv.2 x hx), fun _ _ => by simp,
          fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
      · exact piR_zero_mem_univZero
    · rw [← univ_zero]; exact empty_mem_univ 0

/-- The carrier body is bit-valid, both regimes. -/
theorem towerBodyAV_validV {w : Nat} {Fs : List AVExpr} {ρ : Nat → V}
    (hv : FieldsValid ρ Fs) : AnnotValidV V ρ (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_validV hv
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_validV hv

/-- The uniform projection spelling is bit-valid whenever its subject
is (`.proj`'s validity clause is hereditary). -/
theorem projAV_validV :
    ∀ {i : Nat} {e : AVExpr} {σ : Nat → V},
      AnnotValidV V σ e → AnnotValidV V σ (projAV i e)
  | 0, e, σ, h => by
    show AnnotValidV V σ (.proj 0 e)
    rw [AnnotValidV_proj]
    exact h
  | i + 1, e, σ, h => by
    show AnnotValidV V σ (projAV i (.proj 1 e))
    exact projAV_validV (by rw [AnnotValidV_proj]; exact h)

/-- Application spines are bit-valid from their parts. -/
theorem mkAppN_validV :
    ∀ {args : List AVExpr} {f : AVExpr} {σ : Nat → V},
      AnnotValidV V σ f → (∀ a ∈ args, AnnotValidV V σ a) →
      AnnotValidV V σ (AVExpr.mkAppN f args)
  | [], _, _, hf, _ => hf
  | a :: args, f, σ, hf, hargs => by
    rw [AVExpr.mkAppN_cons]
    refine mkAppN_validV ?_ fun a' ha' => hargs a' (.tail _ ha')
    rw [AnnotValidV_app]
    exact ⟨hf, hargs a (.head _)⟩

/-- The recursor body is bit-valid unconditionally. -/
theorem recBodyAV_validV (n : Nat) (σ : Nat → V) :
    AnnotValidV V σ (recBodyAV n) := by
  refine mkAppN_validV (by rw [AnnotValidV_bvar]; trivial) ?_
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  exact projAV_validV (by rw [AnnotValidV_bvar]; trivial)

/-- The constructor tupler is bit-valid at a fitting frame — the one
walk that crosses the λ-frame lifts (`AnnotValidV_liftN` +
`shiftE_consList`). -/
theorem mkTowerGoPos_validV {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AVExpr} {ρp : Nat → V} {bs : List V},
      FieldsValid ρp Fs → FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      AnnotValidV V (consList bs ρp) (mkTowerGoPos w Fs)
  | [], _, [], _, _, _ => trivial
  | [], _, _ :: _, _, _, hsp => hsp.elim
  | _ :: _, _, [], _, _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hv, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp2 V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp2 V ρp F := by
      rw [interp2_liftN, hshift]
    show AnnotValidV V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoPos w Fs))
    rw [AnnotValidV_app]
    refine ⟨?_, mkTowerGoPos_validV hw (hv.2 b hsp.1) (hb.2 b hsp.1) hsp.2⟩
    rw [AnnotValidV_app]
    refine ⟨?_, by rw [AnnotValidV_bvar]; trivial⟩
    rw [AnnotValidV_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValidV_app]
      refine ⟨by rw [AnnotValidV_const]; trivial, ?_⟩
      rw [AnnotValidV_liftN, hshift]
      exact hv.1
    · rw [AnnotValidV_lam]
      refine ⟨by rw [AnnotValidV_liftN, hshift]; exact hv.1, ?_⟩
      intro x hx
      rw [hA] at hx
      rw [AnnotValidV_liftN, ← cons_shiftE, hshift]
      exact towerBodyAV_validV (hv.2 x hx)

/-- The constructor tupler is bit-valid at a fitting frame, both
regimes. -/
theorem mkTowerGo_validV {w : Nat} {Fs : List AVExpr} {ρp : Nat → V}
    {bs : List V} (hv : FieldsValid ρp Fs)
    (hb : w ≠ 0 → FieldsBound w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValidV V (consList bs ρp) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_validV hw hv (hb hw) hsp

/-- The single hereditary validity premise of a `mkLamsC` leaf. -/
def UnderTowerValid (ρ : Nat → V) (b : AVExpr) :
    List (Nat × Nat × AVExpr) → Prop
  | [] => AnnotValidV V ρ b
  | d :: ds => AnnotValidV V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp2 V ρ d.2.2 → UnderTowerValid (cons a ρ) b ds

/-- A constant-bit λ-tower is bit-valid from the hereditary premise
(the λ clause of `AnnotValidV` carries no bit component). -/
theorem mkLamsC_validV {m : Nat} {b : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      UnderTowerValid ρ b ds → AnnotValidV V ρ (mkLamsC m ds b)
  | [], _, h => h
  | d :: ds, ρ, h => by
    show AnnotValidV V ρ (.lam m d.2.2 (mkLamsC m ds b))
    rw [AnnotValidV_lam]
    exact ⟨h.1, fun a ha => mkLamsC_validV (h.2 a ha)⟩

/-! ## The `AnnotOkP` packages -/

/-- The type-former leaf's P currency (`hAok`+`hAvalid`, packaged). -/
theorem directTyAV_okP {w : Nat} {Fs : List AVExpr}
    {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hok : ParamsOkT w ρ Fs pps)
    (hval : UnderTowerValid ρ (towerBodyAV w Fs) pps) :
    AnnotOkP V ρ (directTyAV w pps Fs) :=
  ⟨directTyAV_ok2 hok, mkLamsC_validV hval⟩

/-- The constructor leaf's P currency. -/
theorem directMkAV_okP {w : Nat} {bodyC : AVExpr} {ρ : Nat → V}
    {pds fds : List (Nat × Nat × AVExpr)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPre w ρ (fds.map (·.2.2)) bodyC pds)
    (hval : UnderTowerValid ρ (mkTowerGo w (fds.map (·.2.2)))
      (pds ++ fds)) :
    AnnotOkP V ρ (directMkAV w (pds ++ fds) (fds.map (·.2.2))) :=
  ⟨directMkAV_ok2 hz hpre, mkLamsC_validV hval⟩

/-- The recursor leaf's P currency. -/
theorem directRecAV_okP {ℓ w : Nat} {Fs : List AVExpr} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM dm dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM, dm, dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPre ℓ w ρ Fs dM dm dt pds)
    (hval : UnderTowerValid ρ (recBodyAV Fs.length)
      (pds ++ [dM, dm, dt])) :
    AnnotOkP V ρ (directRecAV ℓ (pds ++ [dM, dm, dt]) Fs.length) :=
  ⟨directRecAV_ok2 hz hpre, mkLamsC_validV hval⟩

end Setlec.SetR.Interp2
