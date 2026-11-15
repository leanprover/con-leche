module

public import ConLeche.Kernel.CoreDefs
import ConLeche.Verify.InstSpine
public import ConLeche.Verify.Subst

public section

/-!
# Syntactic kit for the ι reduct (task #585)

The ι step reads a stored rule's right-hand side through `Expr.lamBody`, the
body under its `rP + nfields` λs, and substitutes the recursor's leading
arguments and the constructor's fields there at once (`RecRule.iotaReduct`,
lean4 PR #10565's shape).  The install checks that the rule has those λs
(`RuleWF`), so the peel is `stripLams`'s body (`lamBody_of_stripLams`).  The
reduct is the values' `instSpine` of the body (`iotaReduct_eq_instSpine`), so
the `instSpine` kit gives its scoping, closedness and leaves.
-/

namespace ConLeche

open Expr

/-- At a term with `k` manifest λs, the peel is `stripLams`'s body. -/
theorem Expr.lamBody_of_stripLams :
    ∀ {k : Nat} {e : Expr} {bs : List Expr} {b : Expr},
      e.stripLams k = some (bs, b) → e.lamBody k = b
  | 0, e, bs, b, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases e <;> rfl
  | k + 1, e, bs, b, h => by
    match e, h with
    | .lam ty body, h =>
      simp only [Expr.stripLams] at h
      cases hs : body.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        show body.lamBody k = p.2
        exact Expr.lamBody_of_stripLams (bs := p.1) (by rw [hs])

/-- Level instantiation keeps a λ-telescope and instantiates its body. -/
theorem stripLams_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (k : Nat) (e : Expr), (e.instantiateLevelParams ks us).stripLams k =
      (e.stripLams k).map fun p =>
        (p.1.map (·.instantiateLevelParams ks us), p.2.instantiateLevelParams ks us) := by
  intro k
  induction k with
  | zero => intro e; simp [Expr.stripLams]
  | succ k ih =>
    intro e
    cases e <;> simp [Expr.instantiateLevelParams, Expr.stripLams, ih, Option.map_map,
      Function.comp_def]

/-- Substituting below a λ-telescope keeps its length; the body is substituted past it. -/
theorem Expr.stripLams_instantiate1 (v : Expr) :
    ∀ {k : Nat} {e : Expr} {bs : List Expr} {b : Expr} (j : Nat),
      e.stripLams k = some (bs, b) →
      ∃ bs', (e.instantiate1 v j).stripLams k = some (bs', b.instantiate1 v (j + k))
  | 0, e, bs, b, j, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripLams]⟩
  | k + 1, e, bs, b, j, h => by
    match e, h with
    | .lam ty body, h =>
      simp only [Expr.stripLams] at h
      cases hs : body.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', hbs'⟩ := Expr.stripLams_instantiate1 v (j + 1) (bs := p.1) (by rw [hs])
        refine ⟨ty.instantiate1 v j :: bs', ?_⟩
        rw [show j + (k + 1) = j + 1 + k from by omega]
        simp only [Expr.instantiate1, Expr.stripLams, hbs', Option.map_some]

/-- The peel of a free-variable-free term is free-variable-free. -/
theorem Expr.hasFvar_lamBody :
    ∀ (k : Nat) {e : Expr}, e.hasFvar = false → (e.lamBody k).hasFvar = false
  | 0, e, h => by cases e <;> exact h
  | k + 1, e, h => by
    match e with
    | .lam ty body =>
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
      exact Expr.hasFvar_lamBody k h.2
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .forallE _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact h

/-- The peel of a term bounded by `n` binders is bounded by `n + k`. -/
theorem Expr.looseBVarsBounded_lamBody :
    ∀ (k : Nat) {e : Expr} {n : Nat}, e.looseBVarsBounded n = true →
      (e.lamBody k).looseBVarsBounded (n + k) = true
  | 0, e, n, h => by cases e <;> exact h
  | k + 1, e, n, h => by
    match e with
    | .lam ty body =>
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
      have := Expr.looseBVarsBounded_lamBody k h.2
      rwa [show n + 1 + k = n + (k + 1) from by omega] at this
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .forallE _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ =>
      exact Expr.looseBVarsBounded_mono (by omega) h

/-- The peel of a resolving term resolves. -/
theorem Expr.constsResolve_lamBody {env : Env} :
    ∀ (k : Nat) {e : Expr}, e.constsResolve env = true → (e.lamBody k).constsResolve env = true
  | 0, e, h => by cases e <;> exact h
  | k + 1, e, h => by
    match e with
    | .lam ty body =>
      simp only [Expr.constsResolve, Bool.and_eq_true] at h
      exact Expr.constsResolve_lamBody k h.2
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .forallE _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact h

/-- The values an ι step substitutes: the rule prefix of the recursor's spine and the
constructor's fields, `rP + nfields` of them. -/
theorem iotaVals_length {args margs : List Expr} {rP cnP nf : Nat} (hle : rP ≤ args.length)
    (hm : margs.length = cnP + nf) : (args.take rP ++ margs.drop cnP).length = rP + nf := by
  simp only [List.length_append, List.length_take, List.length_drop, hm]
  omega

/-- **The ι reduct is the values' `instSpine` of the peeled body.** -/
theorem RecRule.iotaReduct_eq_instSpine (rl : RecRule) (lps : List Name) (us : List Level)
    (rP : Nat) (vals : List Expr) :
    rl.iotaReduct lps us rP vals = Expr.instSpine vals (vals.length - 1)
      ((rl.rhs.lamBody (rP + rl.nfields)).instantiateLevelParams lps us) :=
  instantiateList_reverse_eq_instSpine vals _

/-- The ι reduct of a free-variable-free rule at well-scoped values is well-scoped. -/
theorem RecRule.iotaReduct_WScoped {d : Nat} {rl : RecRule} {lps : List Name}
    {us : List Level} {rP : Nat} {vals : List Expr} (hf : rl.rhs.hasFvar = false)
    (hv : ∀ a ∈ vals, WScoped d a) : WScoped d (rl.iotaReduct lps us rP vals) := by
  rw [RecRule.iotaReduct_eq_instSpine]
  refine instSpine_WScoped _ (WScoped.of_not_hasFvar ?_) hv
  rw [hasFvar_instantiateLevelParams]; exact Expr.hasFvar_lamBody _ hf

/-- The ι reduct of a closed rule at its full count of bvar-closed values is bvar-closed. -/
theorem RecRule.iotaReduct_closed {rl : RecRule} {lps : List Name} {us : List Level}
    {rP : Nat} {vals : List Expr} (hb : rl.rhs.looseBVarsBounded 0 = true)
    (hlen : vals.length = rP + rl.nfields)
    (hv : ∀ a ∈ vals, a.looseBVarsBounded 0 = true) :
    (rl.iotaReduct lps us rP vals).looseBVarsBounded 0 = true := by
  rw [RecRule.iotaReduct_eq_instSpine]
  refine instSpine_closed hv ?_
  rw [looseBVarsBounded_instantiateLevelParams, hlen]
  simpa using Expr.looseBVarsBounded_lamBody (rP + rl.nfields) hb

/-- The leaves of the ι reduct of a free-variable-free rule are the values'. -/
theorem RecRule.fvarLeaves_iotaReduct {rl : RecRule} {lps : List Name} {us : List Level}
    {rP : Nat} {vals : List Expr} (hf : rl.rhs.hasFvar = false) {l}
    (hl : l ∈ (rl.iotaReduct lps us rP vals).fvarLeaves) :
    ∃ a ∈ vals, l ∈ a.fvarLeaves := by
  rw [RecRule.iotaReduct_eq_instSpine] at hl
  rcases fvarLeaves_instSpine _ hl with hl' | h
  · have hnf : ((rl.rhs.lamBody (rP + rl.nfields)).instantiateLevelParams lps us).hasFvar
        = false := by
      rw [hasFvar_instantiateLevelParams]; exact Expr.hasFvar_lamBody _ hf
    rw [fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl'
    exact absurd hl' List.not_mem_nil
  · exact h

end ConLeche
