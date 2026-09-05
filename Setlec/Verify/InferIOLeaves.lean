import Setlec.Verify.InferLeaves
import Setlec.Verify.InferIOLemmas

/-!
# Leaf-closure and loose-bvar preservation for the io lane

`Setlec/Verify/InferLeaves.lean`'s three `inferTypeCore` preservation
inductions, at the io lane (task #161 stage 2, the io-license batch).
The reduction legs are the full lane's (`whnf_*` — the io knot is a
leaf lane), and the io app inversion's certificate **disjunct is
discarded** in all three proofs, exactly as the full proofs discard
the certificate conjunct: preservation never consumed the argument's
run, so the gate costs these lemmas nothing.  That is the structural
reason the io lane's scoping metatheory is the full lane's, clause
for clause.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr

theorem inferTypeCoreIO_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      WScoped d t
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [WScoped]
    | fvar idx n ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        simp only [WScoped] at hw
        exact hw.2.mono (by omega)
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          exact WScoped.of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [WScoped]
      case natCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [WScoped]
    | forallE n ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCoreIO_forall_inv h
      simp [WScoped]
    | lam n ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCoreIO_WScoped henv fuel hbt hwo
      simp only [WScoped]
      exact ⟨hw.1, WScoped.abstract1 0 hwbt⟩
    | app f a =>
      obtain ⟨tf, n', ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      have hwtf := inferTypeCoreIO_WScoped henv fuel htf hw.1
      have hwPi := whnf_WScoped henv fuel hwh hwtf
      simp only [WScoped] at hwPi
      exact WScoped.instantiate1_gen hw.2 0 hwPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hnat, hlen,
        hus, -, hpair, htow, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      have hwte := inferTypeCoreIO_WScoped henv fuel hte hw
      have hwPi := whnf_WScoped henv fuel hwt hwte
      cases htw : entry.tower with
      | false =>
        obtain ⟨A, B, hargs, hres⟩ := hpair htw
        have hwA : WScoped d A := hwPi.getAppArgs A (by rw [hargs]; simp)
        have hwB : WScoped d B := hwPi.getAppArgs B (by rw [hargs]; simp)
        rcases hres with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hwA
        · simp only [WScoped]
          exact ⟨hwB, hw⟩
      | true =>
        obtain ⟨ds, hpi⟩ := htow htw
        refine (instPisAt_WScoped _ _ hpi
          (projEntry_ty_WScoped henv hfp us) ?_).2
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hwPi.getAppArgs a ha
        · rcases List.mem_singleton.mp ha with rfl
          exact hw
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      obtain ⟨-, -, -, -, -, -, -, h'⟩ := inferTypeCoreIO_letE_inv h
      simp only [WScoped] at hw
      exact inferTypeCoreIO_WScoped henv fuel h'
        (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)

theorem inferTypeCoreIO_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; simp [fvarLeaves] at hl
    | fvar idx n ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        intro l hl
        simp [fvarLeaves, hl]
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          intro l hl
          rw [fvarLeaves_eq_nil_of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)] at hl
          cases hl
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; intro l hl; simp [fvarLeaves] at hl
      case natCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; intro l hl; simp [fvarLeaves] at hl
    | forallE n ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCoreIO_forall_inv h
      intro l hl
      simp [fvarLeaves] at hl
    | lam n ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCoreIO_WScoped henv fuel hbt hwo
      intro l hl
      simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact Or.inl hl
      · obtain ⟨hlbt, hlne⟩ := fvarLeaves_abstract1_ne bt 0 hwbt l hl
        have hlo := inferTypeCoreIO_fvarLeaves henv fuel hbt hwo l hlbt
        rcases fvarLeaves_instantiate1 body 0 hlo with hb | hb
        · exact Or.inr hb
        · simp only [fvarLeaves, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd rfl hlne
          · exact Or.inl hb
    | app f a =>
      obtain ⟨tf, n', ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 body' 0 hl with hb | hb
      · refine Or.inl (inferTypeCoreIO_fvarLeaves henv fuel htf hw.1 l ?_)
        refine whnf_fvarLeaves henv fuel hwh l ?_
        simp [fvarLeaves, hb]
      · exact Or.inr hb
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hnat, hlen,
        hus, -, hpair, htow, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves]
      have hsub : ∀ l', l' ∈ te.fvarLeaves → l' ∈ pe.fvarLeaves :=
        fun l' hl' =>
        inferTypeCoreIO_fvarLeaves henv fuel hte hw l'
          (whnf_fvarLeaves henv fuel hwt l' hl')
      cases htw : entry.tower with
      | false =>
        obtain ⟨A, B, hargs, hres⟩ := hpair htw
        rcases hres with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hsub l (fvarLeaves_getAppArgs (by rw [hargs]; simp) l hl)
        · simp only [fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hsub l (fvarLeaves_getAppArgs (by rw [hargs]; simp) l hl)
          · simpa only [fvarLeaves] using hl
      | true =>
        obtain ⟨ds, hpi⟩ := htow htw
        rcases instPisAt_fvarLeaves _ _ hpi l hl with hty | ⟨a, ha, hla⟩
        · rw [fvarLeaves_eq_nil_of_not_hasFvar
            (projEntry_ty_hasFvar henv hfp us)] at hty
          exact nomatch hty
        · rcases List.mem_append.mp ha with ha | ha
          · exact hsub l (fvarLeaves_getAppArgs ha l hla)
          · rcases List.mem_singleton.mp ha with rfl
            exact hla
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      obtain ⟨-, -, -, -, -, -, -, h'⟩ := inferTypeCoreIO_letE_inv h
      simp only [WScoped] at hw
      intro l hl
      have hl' := inferTypeCoreIO_fvarLeaves henv fuel h'
        (WScoped.instantiate1_gen hw.2.1 0 hw.2.2) l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 b' 0 hl' with h2 | h2
      · exact Or.inr h2
      · exact Or.inl (Or.inr h2)

theorem inferTypeCoreIO_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCoreIO mode env fuel d e = .ok t → WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      t.looseBVarsBounded 0 = true
  | 0, d, e, t, h, _, _, _ => nomatch h
  | fuel + 1, d, e, t, h, hw, hb, hLb => by
    cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [looseBVarsBounded]
    | fvar idx n ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        exact hLb (idx, n, ty) (by simp [fvarLeaves])
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨-, -, -, htb, -⟩ := henv _ (find?_mem hf)
          rw [looseBVarsBounded_instantiateLevelParams]
          exact htb
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [looseBVarsBounded]
      case natCase =>
        dsimp only [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [looseBVarsBounded]
    | forallE n ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ :=
        inferTypeCoreIO_forall_inv h
      simp [looseBVarsBounded]
    | lam n ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ :=
        inferTypeCoreIO_lam_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hbo : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0
          = true := looseBVarsBounded_instantiate1 body 0 hb.2
      have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
        · exact hLb l (by simp [fvarLeaves, hb'])
        · simp only [fvarLeaves, List.mem_cons] at hb'
          rcases hb' with rfl | hb'
          · exact hb.1
          · exact hLb l (by simp [fvarLeaves, hb'])
      have hbbt := inferTypeCoreIO_looseBVars henv fuel hbt hwo hbo hLbo
      simp only [looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 bt 0 hbbt⟩
    | app f a =>
      obtain ⟨tf, n', ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCoreIO_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hLbf : Expr.LeavesBounded f := fun l hl =>
        hLb l (by simp [fvarLeaves, hl])
      have hbtf := inferTypeCoreIO_looseBVars henv fuel htf hw.1 hb.1 hLbf
      have hbPi := whnf_looseBVars henv fuel hwh hbtf
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      exact looseBVarsBounded_instantiate1_gen hb.2 hbPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hnat, hlen,
        hus, -, hpair, htow, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded] at hb
      have hLbe : Expr.LeavesBounded pe := fun l hl => hLb l (by
        simp only [fvarLeaves]; exact hl)
      have hbte := inferTypeCoreIO_looseBVars henv fuel hte hw hb hLbe
      have hbPi := whnf_looseBVars henv fuel hwt hbte
      cases htw : entry.tower with
      | false =>
        obtain ⟨A, B, hargs, hres⟩ := hpair htw
        have hbA : A.looseBVarsBounded 0 = true :=
          looseBVarsBounded_getAppArgs hbPi _ (by rw [hargs]; simp)
        have hbB : B.looseBVarsBounded 0 = true :=
          looseBVarsBounded_getAppArgs hbPi _ (by rw [hargs]; simp)
        rcases hres with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hbA
        · simp only [looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hbB, hb⟩
      | true =>
        obtain ⟨ds, hpi⟩ := htow htw
        refine instPisAt_looseBVars _ _ hpi
          (projEntry_ty_looseBVars henv hfp us) ?_
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact looseBVarsBounded_getAppArgs hbPi _ ha
        · rcases List.mem_singleton.mp ha with rfl
          exact hb
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, viewM, Expr.view, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      obtain ⟨-, -, -, -, -, -, -, h'⟩ := inferTypeCoreIO_letE_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      refine inferTypeCoreIO_looseBVars henv fuel h'
        (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
        (looseBVarsBounded_instantiate1_gen hb.1.2 hb.2) ?_
      intro l hl
      rcases fvarLeaves_instantiate1 b' 0 hl with h2 | h2
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inr h2)
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]
          exact Or.inl (Or.inr h2))



/-! ## The slot shims (task #172 B4)

The knot's io slot (`inferTypeIO`) inherits each scoping preservation
from whichever lane the mode selects — `inferTypeIO_off`/`_on` plus
the full- and io-lane inductions above.  Stated once here so every
walk that meets a converted call site consumes one name. -/

theorem inferTypeIO_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e) :
    WScoped d t := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_WScoped henv fuel h hw
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_WScoped henv fuel h hw

theorem inferTypeIO_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e) :
    ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_fvarLeaves henv fuel h hw
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_fvarLeaves henv fuel h hw

theorem inferTypeIO_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded e) :
    t.looseBVarsBounded 0 = true := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h
             exact inferTypeCore_looseBVars henv fuel h hw hb hLb
  | true => rw [inferTypeIO_on hg] at h
            exact inferTypeCoreIO_looseBVars henv fuel h hw hb hLb

end Setlec
