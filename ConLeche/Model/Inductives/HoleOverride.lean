module

public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Inductives.ContSubst
public import ConLeche.Semantics.NoBVar

public section

/-!
# Filling the holes back in, read

The walk's crest abstracts every whole member application `T_m.{lps} p⃗`
to the member's hole `nP + m`; the concrete crest is the walk's with
one parallel substitution putting the applications back
(`Expr.substFvars_replaceApps_erasedEq`).  Read, that substitution
(`AnnotTerm.substAV` at `substTau`, the parameter variables to
themselves, each hole to its application's reading) is, at the
parameter frame, the hole frame whose hole slots hold the members'
values APPLIED TO THE PARAMETERS (`substE_holeBack`); on a term that
reads no hole slot it only moves the variables above the holes down
(`substAV_holeBack_liftN`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

/-- **A hole-free reading, holes filled back, lifted over the holes, is
itself**: the substitution keeps the variables below the cut, sends the
parameter slots (above the `k` hole slots) to the parameter variables
`k` places lower, and never meets a hole slot. -/
theorem substAV_holeBack_liftN {nP k : Nat} {x : Nat → AnnotTerm}
    (hx : ∀ i, i < nP → x i = .bvar (nP - 1 - i)) :
    ∀ (e : AnnotTerm) (c : Nat), NoBVar (fun i => c ≤ i ∧ i < c + k) e →
      (e.substAV (substTau (nP + k) nP x) c).liftN k c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c h
    have h' : ¬ (c ≤ i ∧ i < c + k) := h
    by_cases hic : i < c
    · rw [AnnotTerm.substAV_bvar_lt _ hic, AnnotTerm.liftN_bvar, ite_eq_left hic]
    · rw [AnnotTerm.substAV_bvar_ge _ (by omega)]
      have hik : c + k ≤ i := by omega
      unfold substTau
      by_cases hb : i - c < nP + k
      · rw [ite_eq_left hb, show nP + k - 1 - (i - c) = nP - 1 - (i - c - k) by omega,
          hx _ (by omega)]
        simp only [AnnotTerm.liftN_bvar]
        split <;> split <;> first | omega | (congr 1; omega)
      · rw [ite_eq_right hb]
        simp only [AnnotTerm.liftN_bvar]
        split <;> split <;> first | omega | (congr 1; omega)
  | sort u => intro c _; rfl
  | const k' us => intro c _; rfl
  | prf => intro c _; rfl
  | app f a ihf iha =>
    intro c h
    rw [AnnotTerm.substAV_app, AnnotTerm.liftN_app, ihf c h.1, iha c h.2]
  | eqE a b iha ihb =>
    intro c h
    show AnnotTerm.liftN k (.eqE (a.substAV _ c) (b.substAV _ c)) c = _
    simp only [AnnotTerm.liftN, iha c h.1, ihb c h.2]
  | fst e ih => intro c h; rw [AnnotTerm.substAV_fst, AnnotTerm.liftN_fst, ih c h]
  | snd e ih => intro c h; rw [AnnotTerm.substAV_snd, AnnotTerm.liftN_snd, ih c h]
  | lam u A b ihA ihb =>
    intro c h
    rw [AnnotTerm.substAV_lam, AnnotTerm.liftN_lam, ihA c h.1, ihb (c + 1) (NoBVar.mono ?_ h.2)]
    intro i hi
    cases i with
    | zero => omega
    | succ i => show c ≤ i ∧ i < c + k; omega
  | pi u v A B ihA ihB =>
    intro c h
    rw [AnnotTerm.substAV_pi, AnnotTerm.liftN_pi, ihA c h.1, ihB (c + 1) (NoBVar.mono ?_ h.2)]
    intro i hi
    cases i with
    | zero => omega
    | succ i => show c ≤ i ∧ i < c + k; omega

section Frame

variable {V : Type w} [SetTheory V]

/-- **The filled-back reading's frame** at the parameter frame `ρ`: the
parameter slots are `ρ`'s own, the hole slots hold the holes' images'
values. -/
theorem substE_holeBack {nP k : Nat} {x : Nat → AnnotTerm}
    (hx : ∀ i, i < nP → x i = .bvar (nP - 1 - i)) (ρ : Nat → V) :
    substE V (substTau (nP + k) nP x) 0 ρ
      = consList ((List.range k).map fun mm => interp V ρ (x (nP + mm))) ρ := by
  rw [substE_substTau]
  congr 1
  funext q
  by_cases hq : q < nP
  · rw [ite_eq_left hq, hx _ (by omega), interp_bvar, show nP - 1 - (nP - 1 - q) = q by omega]
  · rw [ite_eq_right hq, show q - nP + nP = q by omega]

end Frame

end ConLeche.Model
