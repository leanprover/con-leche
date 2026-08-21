import Setlec.Verify.BridgeDecl

/-!
# `wfOpsM` runs to pure runs, per declaration-checker function

With the memo operations unguarded, part B's entry-point bridges carry
the arguments' well-scopedness, so `wfOpsM`'s condition is per call
(`EnvWF env ∧ wscopedB`) and can no longer be discharged wholesale per
function.  This module proves the run-level implications instead: a
successful `wfOpsM` run of each declaration-checker function over a
well-formed environment is the pure `fueledOps` run at the same fuel.
At each operation call site the argument's well-scopedness comes from

* the checker's own input validation (`looseBVarsBounded`/`hasFvar`
  guards precede every `annotate` of raw input — at depth 0
  fvar-freedom *is* well-scopedness),
* the scoping-preservation lemmas for the operations' outputs
  (`annotateCore_WScoped`, `inferTypeCore_WScoped`), and
* closedness of checker-constructed terms (`buildIotaStmt`'s statement
  is assembled from closed pieces — proven below).

`Setlec/Model/BridgeWF.lean` composes these with the intermediate
`EnvWF` facts into `checkDecl_bridge`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

/-! ## Small syntactic toolkit -/

theorem wscopedB_of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} : e.wscopedB d = true :=
  (WScoped.of_not_hasFvar h).to_wscopedB

theorem WScoped.to_wscopedB' {e : Expr} {d : Nat} (h : WScoped d e) :
    e.wscopedB d = true := h.to_wscopedB

theorem hasFvar_liftLooseBVars (n : Nat) :
    ∀ (c : Nat) (e : Expr), (e.liftLooseBVars n c).hasFvar = e.hasFvar := by
  intro c e
  induction e generalizing c <;>
    simp_all [Expr.liftLooseBVars, Expr.hasFvar]
  case bvar i => split <;> simp [Expr.hasFvar]

theorem hasFvar_renameConsts (f : Name → Name) :
    ∀ (e : Expr), (e.renameConsts f).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.hasFvar]

theorem hasFvar_mkAppN :
    ∀ (args : List Expr) (g : Expr), g.hasFvar = false →
      (∀ x ∈ args, x.hasFvar = false) → (Expr.mkAppN g args).hasFvar = false
  | [], g, hg, _ => hg
  | a :: as, g, hg, hargs => by
    simp only [Expr.mkAppN]
    refine hasFvar_mkAppN as _ ?_
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
    simp only [Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨hg, hargs a (List.mem_cons_self ..)⟩

theorem stripLams_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, Expr.stripLams k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.2.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripLams, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .lam n ty b m, h =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripLams_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

theorem stripPis_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, Expr.stripPis k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.2.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripPis, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripPis_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

/-- The iota statement is assembled from closed pieces (rule rhs
components, constructor-type components lifted and renamed, `bvar`
spines), so it is closed. -/
theorem buildIotaStmt_not_hasFvar {f : Name → Name}
    {recName ctorName : Name} {recLPs ctorLPs : List Name}
    {nP nM nm ni nF : Nat} {recTy ctorTy ruleRhs stmt : Expr}
    (h : buildIotaStmt f recName ctorName recLPs ctorLPs nP nM nm ni nF
      recTy ctorTy ruleRhs = some stmt)
    (hrhs : ruleRhs.hasFvar = false) (hctor : ctorTy.hasFvar = false) :
    stmt.hasFvar = false := by
  unfold buildIotaStmt at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Option.guard_eq_some_iff] at h
  obtain ⟨⟨binders₀, body⟩, hstrip, bisR, hbisR, bisC, hbisC,
    ⟨cbinders, cbody⟩, hstripC, mB, hnth, ℓ, hsort, htail⟩ := h
  obtain ⟨-, -, hstmt⟩ := htail
  obtain ⟨hbdoms, hbody⟩ := stripLams_not_hasFvar _ hstrip hrhs
  obtain ⟨-, hcbody⟩ := stripPis_not_hasFvar _ hstripC hctor
  subst hstmt
  -- the domains of the final telescope come from the rule's λ-domains
  have hdoms : ∀ b ∈ (binders₀.zip (bisR ++ bisC.drop nP)).mapIdx
      (fun i (b : (Name × Expr × BinderMeta) × BinderInfo) =>
        ((if i < nP + nM + nm then b.1.1
          else (cbinders.getD (i - (nM + nm)) b.1).1),
         b.1.2.1, b.2)),
      (b.2.1).hasFvar = false := by
    intro b hb
    rw [List.mem_mapIdx] at hb
    obtain ⟨i, hi, hbe⟩ := hb
    have hilt : i < binders₀.length := by
      have := hi
      rw [List.length_zip] at this
      omega
    have hfst : ((binders₀.zip (bisR ++ bisC.drop nP))[i]'hi).1 ∈
        binders₀ := by
      rw [List.getElem_zip]
      exact List.getElem_mem _
    have : b.2.1 = ((binders₀.zip (bisR ++ bisC.drop nP))[i]'hi).1.2.1 := by
      rw [← hbe]
    rw [this]
    exact hbdoms _ hfst
  -- the equation body is closed
  have hiargs : ∀ x ∈ (cbody.getAppArgs.drop nP).map
      (fun e => (e.liftLooseBVars (nM + nm) nF).renameConsts f),
      x.hasFvar = false := by
    intro x hx
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hx
    rw [hasFvar_renameConsts, hasFvar_liftLooseBVars]
    exact hasFvar_getAppArgs hcbody _ (List.mem_of_mem_drop he₀)
  have hbvars : ∀ (l : List Nat) (g : Nat → Expr),
      (∀ k, (g k).hasFvar = false) → ∀ x ∈ l.map g, x.hasFvar = false := by
    intro l g hg x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact hg k
  have hctorApp : (Expr.mkAppN (.const (f ctorName) (ctorLPs.map .param))
      (((List.range nP).map fun k =>
          Expr.bvar (nP + nM + nm + nF - 1 - k)) ++
        ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))).hasFvar
      = false := by
    refine hasFvar_mkAppN _ _ rfl ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        rfl
  have heqApp : ∀ {g : Expr}, g.hasFvar = false →
      ∀ {args : List Expr}, (∀ x ∈ args, x.hasFvar = false) →
      (Expr.mkAppN g args).hasFvar = false :=
    fun hg _ hargs => hasFvar_mkAppN _ _ hg hargs
  -- fold the telescope
  generalize hglist : (binders₀.zip (bisR ++ bisC.drop nP)).mapIdx _ =
    bs at hdoms ⊢
  clear hglist
  induction bs with
  | nil =>
    simp only [List.foldr_nil]
    refine heqApp rfl ?_
    intro x hx
    simp only [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | hx
    · -- α: motive bvar applied to iArgs and the ctor app
      refine heqApp rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hiargs y hy
      · rcases List.mem_singleton.mp hy with rfl
        exact hctorApp
    · -- lhs
      refine heqApp rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · rcases List.mem_append.mp hy with hy | hy
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
            rfl
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
            rfl
        · exact hiargs y hy
      · rcases List.mem_singleton.mp hy with rfl
        exact hctorApp
    · -- rhs
      rw [hasFvar_renameConsts]
      exact hbody
    · exact nomatch hx
  | cons b bs ih =>
    simp only [List.foldr_cons, Expr.hasFvar, Bool.or_eq_false_iff]
    refine ⟨?_, ih (fun x hx => hdoms x (List.mem_cons_of_mem _ hx))⟩
    rw [hasFvar_renameConsts]
    exact hdoms b (List.mem_cons_self ..)

end Setlec
