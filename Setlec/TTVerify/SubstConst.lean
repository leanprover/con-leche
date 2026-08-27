import Setlec.TTVerify.OfReduceKey

/-!
# Substituting the operation for its own constant

`certifyNatEqs` certifies the structural-`Nat` recurrences in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value (`Expr.substConst0`).  The reason is in
`Setlec/Kernel/Checker.lean`: certifying *after* insertion would let the
operation's own literal fast path discharge its all-literal equations
vacuously.

So the bridge has to move a `Deq` across that substitution — from
"`⟦substConst0 c v e⟧` in `env` under `cval`" to "`⟦e⟧` in `c₀ :: env`
under `cvalAt cval env c v`".  The two sides denote to the *same* term,
and the reason is exactly the install's choice of valuation: `cvalAt`
sends `c` to `v`'s denotation, which is what `substConst0` writes in
its place.

**`substConst0` is shallow** — it recurses through `.app` and stops —
so the lemma below is restricted to the fragment the equations live in
(`sort`, `const`, `fvar`, `app`).  That is not a limitation dodged but
the shape of the thing: `natOpEquations` are spines over constants and
two free variables, with no binder anywhere, and a deep substitution
would have to commute with `instantiate1` and with `fvar` annotations
for no gain.

**Why this module did not move with the rest of the denote stack**
(task #148, T1).  `Setlec/Verify/Denote/*` is the lane-neutral home for
everything the denotation needs; `denote_substConst0` would belong there
too, except that it takes an `EnvTT env` -- for `m.cval` and
`m.cval_closed` alone -- and `EnvTT` is the TT lane's own environment
invariant.  Relocating it would mean generalising the argument to a bare
valuation plus a closedness hypothesis, which is a statement change and
so out of a pure-relocation task's scope.  Same for `cvalAt`, which it
reads from `Setlec/TTVerify/Extend.lean`.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- The fragment `Expr.substConst0` is faithful on: application spines
over constants, sorts and free variables. -/
def shallowE : Expr → Bool
  | .sort _ => true
  | .const _ _ => true
  | .fvar _ _ _ => true
  | .app f a => shallowE f && shallowE a
  | _ => false

/-- **The substitution lemma for the install's own constant.**  On the
shallow fragment, denoting in the *extended* environment under the
extended valuation is denoting the *substituted* expression in the old
one. -/
theorem denote_substConst0 {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {c : Name} {v : Expr} {V : VExpr} (φ : Name → Nat)
    (hname : c₀.name = c) (hfresh : env.find? c = none)
    (hlp : c₀.toConstantVal.levelParams = [])
    (hv : denoteClosed m.cval env φ v = some V)
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true) :
    ∀ (d : Nat) (e : Expr), shallowE e = true →
      denote (cvalAt m.cval env c v) ⟨c₀ :: env.consts⟩ φ d e
        = denote m.cval env φ d (Expr.substConst0 c v e) := by
  intro d e
  induction e with
  | sort u =>
    intro _
    show denote (cvalAt m.cval env c v) ⟨c₀ :: env.consts⟩ φ d (.sort u)
      = denote m.cval env φ d (.sort u)
    rw [denote_sort, denote_sort]
  | fvar idx n ty =>
    intro _
    show denote (cvalAt m.cval env c v) ⟨c₀ :: env.consts⟩ φ d
        (.fvar idx n ty) = denote m.cval env φ d (.fvar idx n ty)
    rw [denote_fvar, denote_fvar]
  | const n us =>
    intro _
    by_cases hn : n = c
    · subst hn
      by_cases hus : us = []
      · subst hus
        rw [show Expr.substConst0 n v (.const n []) = v from by
          rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
        rw [denote_const, Env.find?_cons, if_pos hname]
        dsimp only
        rw [if_pos (by rw [hlp]; rfl), hlp, substFn_nil, cvalAt_self hv,
          denote_depth_closed m.cval_closed hvf hvb d]
        exact hv.symm
      · show denote (cvalAt m.cval env n v) ⟨c₀ :: env.consts⟩ φ d
            (.const n us) = denote m.cval env φ d
            (Expr.substConst0 n v (.const n us))
        rw [show Expr.substConst0 n v (.const n us) = .const n us from by
          rw [Expr.substConst0, if_neg (fun h => hus h.2)]]
        rw [denote_const, denote_const, Env.find?_cons, if_pos hname,
          hfresh]
        dsimp only
        rw [if_neg (by rw [hlp]; simpa using hus)]
    · rw [show Expr.substConst0 c v (.const n us) = .const n us from by
        rw [Expr.substConst0, if_neg (fun h => hn h.1)]]
      rw [denote_const, denote_const,
        Env.find?_cons, if_neg (fun hh => hn (by rw [← hname]; exact hh.symm))]
      cases hf : env.find? n with
      | none => rfl
      | some ci =>
        dsimp only
        rw [cvalAt_ne hn]
  | app f a ihf iha =>
    intro hfr
    simp only [shallowE, Bool.and_eq_true] at hfr
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from rfl]
    rw [denote_app, denote_app, ihf hfr.1, iha hfr.2]
  | bvar _ => intro hfr; simp [shallowE] at hfr
  | lam _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | forallE _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | letE _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | proj _ _ _ => intro hfr; simp [shallowE] at hfr
  | lit _ => intro hfr; simp [shallowE] at hfr

end Setlec.TTVerify
