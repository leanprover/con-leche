import Lech.SetP.DirectFix.FixRecPreP
import Lech.SetP.DirectFix.FixIntroP

/-!
# The rule right-hand side's gradedness: the kit (task #188)

The sum route certifies a rule's right-hand side by the kernel's own
inference run at the pre-recursor environment; a recursive rule
mentions the recursor, so its gradedness is proved semantically from
the model instead (`FixRuleOkP.lean`).  This module holds the kit: the
minor space's application chain, the ih-moved index expressions'
grading and validity, domain walks over prefixes, appends and lifted
fields, and the validity walk over binder data.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The minor space's application chain -/

/-- A minor-space member applied along a fitting spine is a graded
application chain. -/
theorem minorSpI_appChainOk {ℓ : Nat} {c : List V → V}
    (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs : List AVExpr} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI ℓ c Fs ρf acc → SpineFit ρf Fs as → AppChainOk m as
  | [], _, _, _, [], _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp2 V ρf F →
        minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app m a ∈ˢ minorSpI ℓ c Fs (cons a ρf) (acc ++ [a]) :=
      app_mem_piR hm hsp.1 hB0
    intro l hl
    cases l with
    | zero =>
      exact ⟨ℓ, interp2 V ρf F, fun x => minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]), hm,
        by simpa using hsp.1, hB0⟩
    | succ l =>
      obtain ⟨v, A, B, h1, h2, h3⟩ := minorSpI_appChainOk hc0 (Fs := Fs) (as := as) happ hsp.2 l
        (by simpa using hl)
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2

/-! ## The ih-moved index expressions -/

/-- The ih-moved index expression is graded exactly when the expression
is at the field's own frame. -/
theorem AnnotOk2_ihIdxAt {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (E : AVExpr) :
    AnnotOk2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihIdxAt nF o i l E) ↔
      AnnotOk2 V (consList (fs.take i) ρp) E := by
  unfold ihIdxAt
  rw [AnnotOk2_liftN, show nF + l = fs.length + ihs.length from by omega, shiftE_fieldFrame hms,
    AnnotOk2_liftN, ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The ih-moved index expression is valid exactly when the expression
is at the field's own frame. -/
theorem AnnotValidV_ihIdxAt {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (E : AVExpr) :
    AnnotValidV V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihIdxAt nF o i l E) ↔
      AnnotValidV V (consList (fs.take i) ρp) E := by
  unfold ihIdxAt
  rw [AnnotValidV_liftN, show nF + l = fs.length + ihs.length from by omega, shiftE_fieldFrame hms,
    AnnotValidV_liftN, ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-! ## Domain walks -/

/-- A walk over a prefix. -/
theorem domsWalk_take :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} (k : Nat),
      DomsWalk ρ ds → DomsWalk ρ (ds.take k)
  | [], _, _, _ => by simp [DomsWalk]
  | _ :: _, _, 0, _ => trivial
  | d :: ds, ρ, k + 1, h => ⟨h.1, fun a ha => domsWalk_take k (h.2 a ha)⟩

/-- A walk over an append: the prefix's walk and the suffix's at every
fitting spine of the prefix. -/
theorem domsWalk_append :
    ∀ {xs ys : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      DomsWalk ρ xs →
      (∀ as : List V, SpineFit ρ (xs.map (·.2.2)) as → DomsWalk (consList as ρ) ys) →
      DomsWalk ρ (xs ++ ys)
  | [], ys, ρ, _, hys => by simpa using hys [] trivial
  | x :: xs, ys, ρ, hx, hys => by
    refine ⟨hx.1, fun a ha => domsWalk_append (hx.2 a ha) fun as hsp => ?_⟩
    have := hys (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A walk is insensitive to the bits. -/
theorem domsWalk_rebit (b : Nat) :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}, DomsWalk ρ ds → DomsWalk ρ (rebit b ds)
  | [], _, _ => trivial
  | _ :: ds, _, h => ⟨h.1, fun a ha => domsWalk_rebit b (ds := ds) (h.2 a ha)⟩

/-- Lifted fields walk at a frame shifting to a frame where they are
graded. -/
theorem domsWalk_liftDoms {w n : Nat} :
    ∀ (ds : List (Nat × Nat × AVExpr)) (k : Nat) (σ : Nat → V),
      FieldsOkB w (shiftE n k σ) (ds.map (·.2.2)) → DomsWalk σ (liftDoms n k ds)
  | [], _, _, _ => trivial
  | d :: ds, k, σ, h => by
    refine ⟨?_, fun a ha => ?_⟩
    · show AnnotOk2 V σ (d.2.2.liftN n k)
      rw [AnnotOk2_liftN]; exact h.1
    · have ha' : a ∈ˢ interp2 V (shiftE n k σ) d.2.2 := by
        rwa [show interp2 V σ (d.2.2.liftN n k) = interp2 V (shiftE n k σ) d.2.2 from
          interp2_liftN V n d.2.2 k σ] at ha
      refine domsWalk_liftDoms (w := w) ds (k + 1) (cons a σ) ?_
      rw [shiftE_succ_cons']
      exact h.2.2 a ha'

/-! ## Validity walks -/

/-- A tower is valid under binder data from the validity of every
domain at its prefix's fitting spines and of the body at the leaves. -/
theorem underTowerValid_of :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {b : AVExpr},
      (∀ k d, ds[k]? = some d → ∀ as : List V, SpineFit ρ ((ds.take k).map (·.2.2)) as →
        AnnotValidV V (consList as ρ) d.2.2) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as → AnnotValidV V (consList as ρ) b) →
      UnderTowerValid ρ b ds
  | [], ρ, b, _, hb => by
    have := hb [] trivial
    rwa [consList_nil] at this
  | d :: ds, ρ, b, hd, hb => by
    refine ⟨by have := hd 0 d rfl [] trivial; rwa [consList_nil] at this,
      fun a ha => underTowerValid_of ?_ ?_⟩
    · intro k d' hk as hsp
      have := hd (k + 1) d' (by simpa using hk) (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this
    · intro as hsp
      have := hb (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this

end Lech.SetP
