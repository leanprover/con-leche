import Setlec.TTVerify.Denote
import Setlec.TTVerify.VClosed
import Setlec.Verify.Shift

/-!
# Depth shifting

The transpose of `interp_lift` (`Setlec/Model/Subst.lean`), and **the
one place where the mirror deviates in the statement rather than only
in the proof**.  The deviation is deliberate and this is its record.

## The model gets an equation; we get a lift

`interp_lift` reads

```
WScoped p e → p ≤ D → (∀ i < p, ρ' i = ρ i) →
  interpExpr V cval env φ D ρ' e = interpExpr V cval env φ p ρ e
```

— *literal equality* of the two interpretations.  It can, because
`interpExpr` uses the depth only to open binders and reads a free
variable through `ρ`, never through `d`.  The valuation absorbs the
depth.

`denote` has no valuation to absorb it (`Setlec/TTVerify/Denote.lean`):
a free variable at level `i` read at depth `d` is `.bvar (d - 1 - i)`,
which is depth-*relative*.  So the transpose cannot be an equation, and
is instead

```
WScoped p e → p ≤ D →
  denote cval env φ D e = (denote cval env φ p e).map (·.liftN (D - p))
```

This is the second half of the same trade as
`Setlec/TTVerify/VClosed.lean`'s: we saved a valuation parameter on
every clause of `denote`, and we pay for it here and in `cval_closed`.
Recorded rather than smoothed over, because a reader checking the
transposition line by line against `Setlec/Model/Subst.lean` will
otherwise stop at this file and wonder what went wrong.

## The generalization: a shift, not a lift

`interp_lift`'s induction is on `D`, stepping down by one with
`interp_weaken_top`.  That step will not transpose directly, because
its binder clause compares

```
denote (D+2) (body.instantiate1 (.fvar (D+1) n ty))
denote (D+1) (body.instantiate1 (.fvar  D    n ty))
```

— two **genuinely different expressions**, related by
`Expr.shiftFrom D` (`Setlec/Verify/Shift.lean`).  So `denote.induct` on
a single expression cannot see them, and the statement has to be
generalized over the *cut*: `denote_shiftFrom` below relates `e` and
`e.shiftFrom p` with the lift cut `d - p`, which the binder clause
increments to `(d - p) + 1` exactly as `VExpr.liftN` increments its
own cut.  That is why the generalization closes.

The fact that makes the cut behave: **the freshly opened variable
denotes `.bvar 0` at every level.**  `fvar d` at depth `d + 1` and
`fvar (d+1)` at depth `d + 2` both come out `.bvar 0`, so only the
*outer* variables move, and they move by exactly one.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

open Setlec.TT

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- Lifts at cut `0` compose by addition. -/
theorem liftN_liftN : ∀ (v : VExpr) (m n k : Nat),
    VExpr.liftN n (VExpr.liftN m v k) k = VExpr.liftN (m + n) v k := by
  intro v
  induction v with
  | bvar i =>
    intro m n k
    simp only [VExpr.liftN_bvar]
    by_cases h : i < k
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (show ¬ i + m < k by omega)]
      congr 1; omega
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha => intro m n k; simp only [VExpr.liftN_app, ihf, iha]
  | lam A b ihA ihb => intro m n k; simp only [VExpr.liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro m n k; simp only [VExpr.liftN_pi, ihA, ihB]
  | letE T v b ihT ihv ihb =>
    intro m n k; simp only [VExpr.liftN_letE, ihT, ihv, ihb]
  | eqE T a b ihT iha ihb =>
    intro m n k; simp only [VExpr.liftN_eqE, ihT, iha, ihb]
  | proj i e ihe => intro m n k; simp only [VExpr.liftN_proj, ihe]

/-- Lifting by zero is the identity. -/
theorem liftN_zero : ∀ (v : VExpr) (k : Nat), VExpr.liftN 0 v k = v := by
  intro v
  induction v with
  | bvar i => intro k; simp only [VExpr.liftN_bvar]; split <;> rfl
  | sort u => intro _; rfl
  | const c us => intro _; rfl
  | prf => intro _; rfl
  | app f a ihf iha => intro k; simp only [VExpr.liftN_app, ihf, iha]
  | lam A b ihA ihb => intro k; simp only [VExpr.liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro k; simp only [VExpr.liftN_pi, ihA, ihB]
  | letE T v b ihT ihv ihb => intro k; simp only [VExpr.liftN_letE, ihT, ihv, ihb]
  | eqE T a b ihT iha ihb => intro k; simp only [VExpr.liftN_eqE, ihT, iha, ihb]
  | proj i e ihe => intro k; simp only [VExpr.liftN_proj, ihe]

/-- A `Nat` literal's term is closed when the two constructor
valuations are. -/
theorem natLitT_closed {zv sv : VExpr} (hz : VExpr.Closed zv)
    (hs : VExpr.Closed sv) : ∀ n, VExpr.Closed (natLitT zv sv n)
  | 0 => hz
  | n + 1 => ⟨hs, natLitT_closed hz hs n⟩

/-- A character list's term is closed when its constituents are. -/
theorem charListT_closed {nilV consV ofNatV zv sv : VExpr}
    (hn : VExpr.Closed nilV) (hc : VExpr.Closed consV)
    (ho : VExpr.Closed ofNatV) (hz : VExpr.Closed zv)
    (hs : VExpr.Closed sv) :
    ∀ cs : List Char, VExpr.Closed (charListT nilV consV ofNatV zv sv cs)
  | [] => hn
  | c :: cs =>
    ⟨⟨hc, ⟨ho, natLitT_closed hz hs c.toNat⟩⟩,
      charListT_closed hn hc ho hz hs cs⟩

/-- A `String` literal's term is closed when the valuation is. -/
theorem strLitT_closed (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (s : String) : VExpr.Closed (strLitT cval env φ s) := by
  refine ⟨hcl _ _, charListT_closed ?_ ?_ (hcl _ _) (hcl _ _) (hcl _ _) s.toList⟩
  · exact ⟨hcl _ _, hcl _ _⟩
  · exact ⟨hcl _ _, hcl _ _⟩

/-- **Depth shifting.**  Denoting `e.shiftFrom p` one level deeper is
denoting `e` and lifting at cut `d - p`.

The `cval` closedness hypothesis is what lets the `.const` and literal
clauses go through: a constant's term must not move when the context
around it grows (`Setlec/TTVerify/VClosed.lean`). -/
theorem denote_shiftFrom (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.fvarsBelow d e →
      denote cval env φ (d + 1) (e.shiftFrom p) =
        (denote cval env φ d e).map (VExpr.liftN 1 · (d - p))
  | .bvar i, d, hpd, hfb => by simp [Expr.shiftFrom]
  | .sort u, d, hpd, hfb => by simp [Expr.shiftFrom]
  | .const n us, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_const]
    split
    · next ci hf =>
      split
      · next hlen =>
        simp only [Option.map_some]
        rw [VExpr.liftN_eq_self_of_closed (hcl _ _)]
      · rfl
    · rfl
  | .fvar idx n ty, d, hpd, hfb => by
    have hlt : idx < d := hfb
    simp only [Expr.shiftFrom]
    split
    · next hge =>
      -- at or above the shift point: the index does not move, because
      -- `d + 1 - 1 - (idx + 1) = d - 1 - idx`
      rw [denote_fvar, denote_fvar, Option.map_some, VExpr.liftN_bvar,
        if_pos (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      -- below the shift point: the index moves up by one
      rw [denote_fvar, denote_fvar, Option.map_some, VExpr.liftN_bvar,
        if_neg (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app f a, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_app]
    rw [denote_shiftFrom hcl f d hpd hfb.1, denote_shiftFrom hcl a d hpd hfb.2]
    cases denote cval env φ d f <;> cases denote cval env φ d a <;> rfl
  | .forallE n ty body m, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_forallE]
    rw [denote_shiftFrom hcl ty d hpd hfb.1]
    cases hty : denote cval env φ d ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.shiftFrom_instantiate1 hpd body 0,
        denote_shiftFrom hcl (body.instantiate1 (.fvar d n ty)) (d + 1)
          (by omega) (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show d + 1 - p = d - p + 1 from by omega]
      cases denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, VExpr.liftN_pi]
  | .lam n ty body m, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_lam]
    rw [denote_shiftFrom hcl ty d hpd hfb.1]
    cases hty : denote cval env φ d ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.shiftFrom_instantiate1 hpd body 0,
        denote_shiftFrom hcl (body.instantiate1 (.fvar d n ty)) (d + 1)
          (by omega) (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show d + 1 - p = d - p + 1 from by omega]
      cases denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, VExpr.liftN_lam]
  | .letE n ty val body, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_letE]
    rw [denote_shiftFrom hcl ty d hpd hfb.1,
      denote_shiftFrom hcl val d hpd hfb.2.1]
    cases hty : denote cval env φ d ty with
    | none => simp
    | some A =>
      cases hval : denote cval env φ d val with
      | none => simp
      | some xv =>
        simp only [Option.map_some]
        rw [← Expr.shiftFrom_instantiate1 hpd body 0,
          denote_shiftFrom hcl (body.instantiate1 (.fvar d n ty)) (d + 1)
            (by omega) (Expr.fvarsBelow_instantiate1 0 hfb.2.2),
          show d + 1 - p = d - p + 1 from by omega]
        cases denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | none => rfl
        | some B => simp only [Option.map_some, VExpr.liftN_letE]
  | .proj s i e, d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_proj]
    rw [denote_shiftFrom hcl e d hpd hfb]
    cases denote cval env φ d e with
    | none => rfl
    | some ve =>
      simp only [Option.map_some]
      split
      · simp only [Option.map_some, VExpr.liftN_proj]
      · rfl
  | .lit (.natVal k), d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_natLit]
    split
    · simp only [Option.map_some]
      rw [VExpr.liftN_eq_self_of_closed
        (natLitT_closed (hcl _ _) (hcl _ _) k)]
    · rfl
  | .lit (.strVal s), d, hpd, hfb => by
    simp only [Expr.shiftFrom, denote_strLit]
    split
    · simp only [Option.map_some]
      rw [VExpr.liftN_eq_self_of_closed (strLitT_closed hcl s)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- One level of weakening: denoting a `d`-scoped term at `d + 1` lifts
it by one.  The transpose of `interp_weaken_top`, and the step
`denote_lift`'s induction takes. -/
theorem denote_weaken_top (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {e : Expr} (hfb : Expr.fvarsBelow d e) :
    denote cval env φ (d + 1) e =
      (denote cval env φ d e).map (VExpr.liftN 1 · 0) := by
  have h := denote_shiftFrom (env := env) (φ := φ) hcl e d (Nat.le_refl d) hfb
  rw [Expr.shiftFrom_eq_self hfb, Nat.sub_self] at h
  exact h

/-- **Depth lifting** — the transpose of `interp_lift`.  Where the model
gets a literal equation (its valuation absorbs the depth), the bridge
gets a lift; see the module docstring for why that deviation is forced
rather than chosen. -/
theorem denote_lift (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {p : Nat} {e : Expr} (hfb : Expr.fvarsBelow p e) :
    ∀ D : Nat, p ≤ D →
      denote cval env φ D e =
        (denote cval env φ p e).map (VExpr.liftN (D - p) · 0) := by
  intro D
  induction D with
  | zero =>
    intro hpD
    have hp : p = 0 := by omega
    subst hp
    simp only [Nat.sub_self]
    cases denote cval env φ 0 e with
    | none => rfl
    | some v => simp only [Option.map_some, liftN_zero]
  | succ D ih =>
    intro hpD
    by_cases hpD' : p = D + 1
    · subst hpD'
      simp only [Nat.sub_self]
      cases denote cval env φ (D + 1) e with
      | none => rfl
      | some v => simp only [Option.map_some, liftN_zero]
    · have hpD2 : p ≤ D := by omega
      rw [denote_weaken_top hcl (Expr.fvarsBelow_mono hpD2 hfb), ih hpD2]
      cases denote cval env φ p e with
      | none => rfl
      | some v =>
        simp only [Option.map_some, liftN_liftN]
        congr 2
        omega

end Setlec.TTVerify
