module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.Denote.VClosed
public import ConLeche.Verify.Shift
import ConLeche.Verify.Abstract

public section

/-!
# Closed denotations

A closed expression denotes to a closed term: the literal spines are
closed when their constructor valuations are (`natLitT_closed`,
`charListT_closed`, `strLitT_closed`), and `denote` keeps every bound
variable below the depth it reads at (`denote_bvarsBelow`), hence
`denote_closed`.  This is the half of `ConLeche/Verify/Denote/VClosed.lean`'s
trade that `denote` pays in `cval_closed`: it saves a valuation
parameter on every clause.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- A `Nat` literal's term is closed when the two constructor
valuations are. -/
theorem natLitT_closed {zv sv : Term} (hz : Term.Closed zv)
    (hs : Term.Closed sv) : ∀ n, Term.Closed (natLitT zv sv n)
  | 0 => hz
  | n + 1 => ⟨hs, natLitT_closed hz hs n⟩

/-- A character list's term is closed when its constituents are. -/
theorem charListT_closed {nilV consV ofNatV zv sv : Term}
    (hn : Term.Closed nilV) (hc : Term.Closed consV)
    (ho : Term.Closed ofNatV) (hz : Term.Closed zv)
    (hs : Term.Closed sv) :
    ∀ cs : List Char, Term.Closed (charListT nilV consV ofNatV zv sv cs)
  | [] => hn
  | c :: cs =>
    ⟨⟨hc, ⟨ho, natLitT_closed hz hs c.toNat⟩⟩,
      charListT_closed hn hc ho hz hs cs⟩

/-- A `String` literal's term is closed when the valuation is. -/
theorem strLitT_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    (s : String) : Term.Closed (strLitT cval env φ s) := by
  refine ⟨hcl _ _, charListT_closed ?_ ?_ (hcl _ _) (hcl _ _) (hcl _ _)
    s.toList⟩
  · exact ⟨hcl _ _, hcl _ _⟩
  · exact ⟨hcl _ _, hcl _ _⟩

/-- `projNV` preserves bvar bounds (hereditary proj clauses). -/
theorem projNV_bvarsBelow {d : Nat} :
    ∀ (i : Nat) {v : Term}, Term.bvarsBelow d v →
      Term.bvarsBelow d (projNV i v)
  | 0, _, h => h
  | i + 1, v, h => projNV_bvarsBelow i (v := .snd v) h

/-! ## Scoping transfers to the denotation

The one place the `Expr`/`Term` separation of §12.6 is crossed
*deliberately*: a term scoped below depth `d` denotes to a `Term`
whose bound variables are below `d`.  That is not a leak — it is the
direction that *does* hold, because `denote` maps an `fvar` at index
`idx < d` to `.bvar (d - 1 - idx) < d` and opens each binder one level
deeper.  The converse (typing telling you about syntax) is what does
not hold.

Consumed at the `.const` clause of `inferBody`, where the stored type
is a closed `Expr` and its denotation has to be a closed `Term` for
the environment invariant's typing to survive lifting. -/

theorem denote_bvarsBelow (hcl : ∀ n ψ, Term.Closed (cval n ψ)) :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      e.looseBVarsBounded 0 = true →
      ∀ {v : Term}, denote cval env φ d e = some v →
        Term.bvarsBelow d v := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env) (φ := φ) with
  | case1 d u =>
    intro _ _ v h
    rw [denote_sort] at h
    obtain rfl : v = .sort (u.eval φ) := (Option.some.inj h).symm
    trivial
  | case2 d idx ty =>
    intro hws _ v h
    rw [denote_fvar] at h
    obtain rfl : v = .bvar (d - 1 - idx) := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_refl d)
  | case3 d n us ci h1 h2 =>
    intro _ _ v h
    simp only [denote_const, h1, ite_eq_left h2] at h
    obtain rfl : v = cval n (Level.substFn φ ci.toConstantVal.levelParams us) :=
      (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d) (hcl _ _)
  | case4 d n us ci h1 h2 =>
    intro _ _ v h; simp only [denote_const, h1, ite_eq_right h2] at h; exact nomatch h
  | case5 d n us h1 =>
    intro _ _ v h; rw [denote_const, h1] at h; exact nomatch h
  | case6 d ty body mb h1 ihty =>
    intro _ _ v h; rw [denote_forallE, h1] at h; exact nomatch h
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    intro _ _ v h; rw [denote_forallE, h1, h2] at h; exact nomatch h
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hws hb v h
    rw [denote_forallE, h1, h2] at h
    obtain rfl : v = .pi B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case9 d ty body mb h1 ihty =>
    intro _ _ v h; rw [denote_lam, h1] at h; exact nomatch h
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    intro _ _ v h; rw [denote_lam, h1, h2] at h; exact nomatch h
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hws hb v h
    rw [denote_lam, h1, h2] at h
    obtain rfl : v = .lam B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case12 d f a vf va h1 h2 ihf iha =>
    intro hws hb v h
    rw [denote_app, h1, h2] at h
    obtain rfl : v = .app vf va := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf hws.1 hb.1 h2, iha hws.2 hb.2 h1⟩
  | case13 d f a hbad ihf iha =>
    intro _ _ v h
    rw [denote_app] at h
    split at h
    · next vf va k1 k2 => exact (hbad vf va k1 k2).elim
    · exact nomatch h
  | case14 d ty val body =>
    intro _ _ v h; rw [denote_letE] at h; exact nomatch h
  | case15 d sn i e h1 ihe =>
    intro _ _ v h; rw [denote_proj, h1] at h; exact nomatch h
  | case16 d sn i e B h1 entry h2 ihe =>
    intro hws hb v h
    rw [denote_proj, h1, h2] at h
    simp only [Option.some.injEq] at h
    simp only [Expr.WScoped] at hws
    obtain rfl : v = projNV (i + entry.off) B := h.symm
    exact projNV_bvarsBelow _ (ihe hws hb h1)
  | case17 d sn i e B h1 h2 ihe =>
    intro hws hb v h
    rw [denote_proj, h1, h2] at h
    simp only [Expr.WScoped] at hws
    have hB : Term.bvarsBelow d B := ihe hws hb h1
    rcases i with _ | _ | i
    · simp only [Term.projPair?, Option.some.injEq] at h
      exact h ▸ hB
    · simp only [Term.projPair?, Option.some.injEq] at h
      exact h ▸ hB
    · exact nomatch h
  | case18 d n hg =>
    intro _ _ v h
    rw [denote_natLit, ite_eq_left hg] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d)
      (natLitT_closed (hcl _ _) (hcl _ _) n)
  | case19 d n hg =>
    intro _ _ v h; rw [denote_natLit, ite_eq_right hg] at h; exact nomatch h
  | case20 d t hg =>
    intro _ _ v h
    rw [denote_strLit, ite_eq_left hg] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d) (strLitT_closed hcl t)
  | case21 d t hg =>
    intro _ _ v h; rw [denote_strLit, ite_eq_right hg] at h; exact nomatch h
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _ _ v h
    match x with
    | .bvar i => rw [denote_bvar] at h; exact nomatch h
    | .sort u => exact (k1 u rfl).elim
    | .fvar a c => exact (k2 a c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE b c dd => exact (k4 b c dd rfl).elim
    | .lam b c dd => exact (k5 b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE b c dd => exact (k7 b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-- A closed expression denotes to a closed term. -/
theorem denote_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} {v : Term} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denoteClosed cval env φ e = some v) : Term.Closed v :=
  denote_bvarsBelow hcl 0 e (Expr.WScoped.of_not_hasFvar hnf) hb h

end ConLeche.Verify
