import Setlec.SetBase.TowerIntro
import Setlec.SetBase.Value

/-!
# The carrier body and the uniform projection spelling (task #175, stage 2)

The value-introduction half of the direct-structure bridge: the tier's
semantic values must be *stored*, and the P dialect stores constant
denotations as closed `AVExpr` leaves over the `BConst` alphabet
(`EnvS2Core.acval`).  This module supplies the two body spellings and
their interpretation equations:

* `towerBodyAV w Fs` — the carrier, spelled through `.psigma` at level
  instantiation `[w, w]` with a `unitSet` terminator (`.punit`).  Two
  interface facts make this land exactly on the tier's `towerSet w`:
  `sigmaSet` reads its level only through the zero test
  (`sigmaSet_pos`/`sigmaSet_zero`), so `max w w = w` closes the level
  bookkeeping; and the fibre λ's annotation is the *codomain type's*
  sort `w + 1 ≠ 0`, so the fibre computes by `app_lamR_pos` in **both**
  regimes and `sigma_congr` rewrites it to the tier's fibre.  The
  premises of `psigmaV2_app` are exactly `FieldsBound w` — O5 plus
  cumulativity, nothing else.

* `projAV i` — the tier's structure-independent `projS i = sfst ∘
  ssnd^i`, spelled by the iterated proj node `.proj 0 ∘ (.proj 1)^i`.
  No type arguments, no entry consultation; `projAV_interp` is the
  definitional commutation.

`towerBodyAV_ok2` grades the body (`AnnotOk2`) from the hereditary
`FieldsOkB` premise (the domains' own `AnnotOk2` + `FieldsBound`);
the app slots are discharged by `psigmaV2_ww_mem`, the `[w, w]`
instance of the pinned pair former's product membership.  Bit validity
(`AnnotValidV`) is a lane predicate and lands with the SetP battery
(stage 4).
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The carrier body: the right-nested `.psigma [w, w]` application
tower over the field domains, `.punit`-terminated.  The fibre λ is
annotated `w + 1` (its body is a type of sort `w`), so it is a graph
at every regime. -/
def towerBodyAV (w : Nat) : List AVExpr → AVExpr
  | [] => .const .punit [w + 1]
  | F :: Fs => .app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAV w Fs))

/-- The uniform projection spelling: `.proj 0 ∘ (.proj 1)^i` — the
`AVExpr` form of the tier's `projS i = sfst ∘ ssnd^i`.  Depends only
on the index. -/
def projAV : Nat → AVExpr → AVExpr
  | 0, e => .proj 0 e
  | i + 1, e => projAV i (.proj 1 e)

/-- `FieldsOkB w ρ Fs`: the hereditary grading the body's `AnnotOk2`
consumes — each domain is itself graded and its interpretation is
bounded, at every fitting prefix. -/
def FieldsOkB (w : Nat) (ρ : Nat → V) : List AVExpr → Prop
  | [] => True
  | F :: Fs => AnnotOk2 V ρ F ∧ interp2 V ρ F ∈ˢ (univ w : V) ∧
      ∀ a, a ∈ˢ interp2 V ρ F → FieldsOkB w (cons a ρ) Fs

theorem FieldsOkB.toBound :
    ∀ {w : Nat} {Fs : List AVExpr} {ρ : Nat → V},
      FieldsOkB w ρ Fs → FieldsBound w ρ Fs
  | _, [], _, _ => trivial
  | _, _ :: Fs, _, h =>
    ⟨h.2.1, fun a ha => FieldsOkB.toBound (Fs := Fs) (h.2.2 a ha)⟩

/-- The `[w, w]` instance of the pair former's product membership: the
`.psigma [w, w]` value inhabits the two-step product landing in
`univ w`.  (`sigma_mem_univ` at the joint level `max w w = w`.) -/
theorem psigmaV2_ww_mem (w : Nat) :
    psigmaV2 V w w ∈ˢ piR (w + 1) (univ w : V)
      (fun A => piR (w + 1) (psigmaFibreSpace V w A)
        fun _ => (univ w : V)) := by
  rw [psigmaV2, show Nat.max w w = w from Nat.max_self w]
  exact lamR_mem fun A hA => lamR_mem fun B hB => by
    have h := sigma_mem_univ (u := w) (v := w) hA
      (fun x hx => psigmaFibre_apply V hB hx)
    rwa [show Nat.max w w = w from Nat.max_self w] at h

/-- **The carrier body reads back as the tier's carrier**: under the
hereditary bound (O5's semantic form), the `.psigma` spelling
interprets to `towerSet w` of the interpreted telescope — at every
level, both regimes. -/
theorem towerBodyAV_interp {w : Nat} :
    ∀ {Fs : List AVExpr} {ρ : Nat → V}, FieldsBound w ρ Fs →
      interp2 V ρ (towerBodyAV w Fs)
        = towerSet w (teleOfFields ρ Fs)
  | [], _, _ => rfl
  | F :: Fs, ρ, hb => by
    have hA : interp2 V ρ F ∈ˢ (univ w : V) := hb.1
    have hG : ∀ x, x ∈ˢ interp2 V ρ F →
        interp2 V (cons x ρ) (towerBodyAV w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAV_interp (hb.2 x hx)
    have hB : (lamR (w + 1) (interp2 V ρ F)
          fun x => interp2 V (cons x ρ) (towerBodyAV w Fs))
        ∈ˢ piR (w + 1) (interp2 V ρ F) (fun _ => (univ w : V)) :=
      lamR_mem fun x hx => by
        rw [hG x hx]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hbv : bval2 V .psigma [w, w] = psigmaV2 V w w := rfl
    show SetTheory.app (SetTheory.app (bval2 V .psigma [w, w])
        (interp2 V ρ F))
        (lamR (w + 1) (interp2 V ρ F)
          fun x => interp2 V (cons x ρ) (towerBodyAV w Fs))
      = towerSet w (teleOfFields ρ (F :: Fs))
    rw [hbv, psigmaV2_app V hA hB,
      show Nat.max w w = w from Nat.max_self w, teleOfFields_cons]
    show sigmaSet w _ _ = sigmaSet w _ _
    exact sigma_congr fun x hx => by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hx, hG x hx]

/-- **The uniform projection spelling reads back as `projS`** — the
definitional commutation, no premises at all (matching the tier's
unconditional iota discipline). -/
theorem projAV_interp :
    ∀ (i : Nat) (e : AVExpr) (ρ : Nat → V),
      interp2 V ρ (projAV i e) = projS i (interp2 V ρ e)
  | 0, e, ρ => by
    show (if 0 = 0 then sfst (interp2 V ρ e) else ssnd (interp2 V ρ e))
      = sfst (interp2 V ρ e)
    rw [if_pos rfl]
  | i + 1, e, ρ => by
    show interp2 V ρ (projAV i (.proj 1 e))
      = projS i (ssnd (interp2 V ρ e))
    rw [projAV_interp i (.proj 1 e) ρ]
    show projS i (if 1 = 0 then sfst (interp2 V ρ e)
      else ssnd (interp2 V ρ e)) = _
    rw [if_neg Nat.one_ne_zero]

/-- `projAV` commutes with lifting (it introduces no binders). -/
theorem projAV_liftN :
    ∀ (i : Nat) (e : AVExpr) (n k : Nat),
      (projAV i e).liftN n k = projAV i (e.liftN n k)
  | 0, _, _, _ => rfl
  | i + 1, e, n, k => projAV_liftN i (.proj 1 e) n k

/-- `projAV` commutes with instantiation. -/
theorem projAV_inst :
    ∀ (i : Nat) (e a : AVExpr) (k : Nat),
      (projAV i e).inst a k = projAV i (e.inst a k)
  | 0, _, _, _ => rfl
  | i + 1, e, a, k => projAV_inst i (.proj 1 e) a k

/-- **The carrier body is graded** (`AnnotOk2`): every app slot is
supplied by `psigmaV2_ww_mem` and the fibre package by the tier's
formation laws; the hereditary premise carries the domains' own
grading. -/
theorem towerBodyAV_ok2 {w : Nat} :
    ∀ {Fs : List AVExpr} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      AnnotOk2 V ρ (towerBodyAV w Fs)
  | [], ρ, _ => by simp [towerBodyAV]
  | F :: Fs, ρ, hok => by
    have hb : FieldsBound w ρ (F :: Fs) := hok.toBound
    have hA : interp2 V ρ F ∈ˢ (univ w : V) := hok.2.1
    have hG : ∀ x, x ∈ˢ interp2 V ρ F →
        interp2 V (cons x ρ) (towerBodyAV w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAV_interp (hb.2 x hx)
    have hbv : interp2 V ρ (.const .psigma [w, w]) = psigmaV2 V w w := rfl
    have hvac : ¬ w + 1 = 0 := Nat.succ_ne_zero w
    show AnnotOk2 V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAV w Fs)))
    rw [AnnotOk2_app]
    refine ⟨?_, ?_, ?_⟩
    · -- the inner application `.psigma [w,w] F`
      rw [AnnotOk2_app]
      exact ⟨trivial, hok.1,
        ⟨w + 1, univ w,
          fun A => piR (w + 1) (psigmaFibreSpace V w A)
            fun _ => (univ w : V),
          hbv ▸ psigmaV2_ww_mem w, hA, fun h => absurd h hvac⟩⟩
    · -- the fibre λ
      rw [AnnotOk2_lam]
      refine ⟨hok.1, fun x hx => towerBodyAV_ok2 (hok.2.2 x hx),
        ⟨fun _ => (univ w : V), fun x hx => ?_, fun h => absurd h hvac⟩⟩
      rw [hG x hx]
      exact towerSet_univ_teleOfFields (hb.2 x hx)
    · -- the outer application's kind slot
      refine ⟨w + 1, psigmaFibreSpace V w (interp2 V ρ F),
        fun _ => (univ w : V), ?_, ?_, fun h => absurd h hvac⟩
      · show SetTheory.app (interp2 V ρ (.const .psigma [w, w]))
            (interp2 V ρ F) ∈ˢ _
        rw [hbv]
        exact app_mem_piR_pos hvac (psigmaV2_ww_mem w) hA
      · exact lamR_mem fun x hx => by
          rw [hG x hx]
          exact towerSet_univ_teleOfFields (hb.2 x hx)

end Setlec.SetR.Interp2
