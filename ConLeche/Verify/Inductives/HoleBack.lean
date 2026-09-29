module

public import ConLeche.Verify.SubstFvars
import ConLeche.Verify.InferLemmas

public section

/-!
# The holes filled back in

A member constructor's walked term abstracts the WHOLE applications
`T_m.{lps} p⃗` of the concrete opening to the canonical holes (`holeAbs`,
`replaceApps` with `nestCanonSub`).  Putting the applications back — one
parallel substitution (`Expr.substFvars`) of the parameter variables by
themselves and each canonical hole `nP + m` by `T_m.{lps}` applied to the
parameters — gives the concrete term back, up to erasure
(`substFvars_replaceApps_erasedEq`).
-/

namespace ConLeche.Expr

/-- A placeholder spine, as a spine. -/
theorem phApp?_spine {b : Nat} :
    ∀ (n : Nat) {e : Expr} {c : Name} {v : List Level}, e.phApp? b n = some (c, v) →
      ∃ args, e = Expr.mkAppN (.const c v) args ∧ args.length = n ∧
        ∀ q x, args[q]? = some x → ∃ ty, x = Expr.fvar (b + q) ty
  | 0, e, c, v, h => ⟨[], phApp?_zero h, rfl, fun _ _ h => nomatch h⟩
  | n + 1, e, c, v, h => by
    obtain ⟨f, ty, rfl, hf⟩ := phApp?_succ h
    obtain ⟨args, rfl, hl, hv⟩ := phApp?_spine n hf
    refine ⟨args ++ [.fvar (b + n) ty], by rw [mkAppN_append_one], by simp [hl],
      fun q x hx => ?_⟩
    by_cases hq : q < args.length
    · rw [List.getElem?_append_left hq] at hx
      exact hv q x hx
    · rw [List.getElem?_append_right (by omega)] at hx
      have : q - args.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
      rw [this] at hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      exact ⟨ty, by rw [← hx]; congr 1; omega⟩

/-- **Filling the whole applications back** (see the module docstring):
on a term whose variables lie below `n`, the substitution that keeps the
variables below `n` (up to annotation) and sends each canonical hole
`n + m` to a spine erasure-equal to `names[m]` at the levels `us`
applied to the parameter variables, undoes the abstraction. -/
theorem substFvars_replaceApps_erasedEq {names : List Name} {us : List Level} {n b D : Nat}
    {s : Nat → Expr} (hnb : n + names.length ≤ b)
    (hpar : ∀ i, i < n → ∃ ty, s i = .fvar i ty)
    (hhole : ∀ m, m < names.length → ∀ args : List Expr, args.length = n →
      (∀ p x, args[p]? = some x → ∃ ty, x = Expr.fvar p ty) →
      ErasedEq (s (n + m)) (Expr.mkAppN (.const (names.getD m .anonymous) us) args)) :
    ∀ e : Expr, e.fvarsBelow n →
      ErasedEq (substFvars b D s (e.replaceApps (ConLeche.nestCanonSub names us n) 0 n)) e := by
  -- a hit: the whole application goes to its hole and back
  have hhit : ∀ e h, e.appHole? (ConLeche.nestCanonSub names us n) 0 n = some h →
      ErasedEq (substFvars b D s h) e := by
    intro e h hh
    unfold appHole? at hh
    cases hp : e.phApp? 0 n with
    | none => rw [hp] at hh; exact nomatch hh
    | some p =>
      rw [hp, Option.bind_some] at hh
      obtain ⟨m, hm, hmc, hv, rfl⟩ := ConLeche.nestCanonSub_some hh
      rw [substFvars_fvar_lt (by omega)]
      obtain ⟨c, v⟩ := p
      simp only at hmc hv
      subst hv
      obtain ⟨args, rfl, hlen, hvar⟩ := phApp?_spine n hp
      have hc : names.getD m .anonymous = c := by
        rw [List.getD_eq_getElem?_getD, hmc, Option.getD_some]
      rw [← hc]
      exact hhole m hm args hlen fun q x hx => by simpa using hvar q x hx
  intro e
  induction e with
  | const c v =>
    intro _
    rw [replaceApps_const]
    split
    · rename_i h hh; exact hhit _ _ hh
    · exact ErasedEq.rfl _
  | app a x iha ihx =>
    intro hb
    simp only [fvarsBelow] at hb
    rw [replaceApps_app]
    split
    · rename_i h hh; exact hhit _ _ hh
    · exact ⟨iha hb.1, ihx hb.2⟩
  | lam t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    exact ⟨rfl, iht hb.1, ihb hb.2⟩
  | forallE t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    exact ⟨rfl, iht hb.1, ihb hb.2⟩
  | letE t v body iht ihv ihb =>
    intro hb; simp only [fvarsBelow] at hb
    exact ⟨iht hb.1, ihv hb.2.1, ihb hb.2.2⟩
  | proj s' i x ih =>
    intro hb; simp only [fvarsBelow] at hb
    exact ⟨rfl, rfl, ih hb⟩
  | fvar i ty _ =>
    intro hb
    simp only [fvarsBelow] at hb
    simp only [replaceApps]
    rw [substFvars_fvar_lt (by omega)]
    obtain ⟨ty', h⟩ := hpar i hb
    rw [h]; rfl
  | bvar => intro _; exact ErasedEq.rfl _
  | sort => intro _; exact ErasedEq.rfl _
  | lit => intro _; exact ErasedEq.rfl _

end ConLeche.Expr
