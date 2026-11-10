module

public import ConLeche.Verify.Ground.Erased
import ConLeche.Verify.Shift

public section

/-!
# Environments as substitutions: the machine's binding steps (task #423 soundness, layer (c))

The ground machine binds arguments into environments instead of
substituting.  Read back, a node `s` under the environment's origins `vs`
(innermost first) is `s.instantiateList vs`.  This file proves the term
algebra its transitions need, for closed origins:

* `lookup`: a variable under an environment is the environment's cell origin;
* `bounded`: a node bounded by the environment's length reads back closed;
* `beta_env` / `betaN_env`: applying a λ (telescope) under an environment
  to arguments is erased β-reduction to its body under the extended
  environment, all arguments at once;
* `zeta_env`: a `let` under an environment is ζ to its body under the
  environment extended by the value.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Rules

/-- All terms of a list are closed. -/
@[expose] def AllClosed (vs : List Expr) : Prop := ∀ v ∈ vs, v.looseBVarsBounded 0 = true

theorem AllClosed.cons {v : Expr} {vs : List Expr} (hv : v.looseBVarsBounded 0 = true)
    (h : AllClosed vs) : AllClosed (v :: vs) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hv
  · exact h w hw

/-- **Read-back under closed origins is closed.** -/
theorem bounded : ∀ (vs : List Expr) (e : Expr) (d : Nat), AllClosed vs →
    e.looseBVarsBounded (d + vs.length) = true → (e.instantiateList vs d).looseBVarsBounded d = true
  | [], e, d, _, h => by rw [Expr.instantiateList_nil]; simpa using h
  | v :: vs, e, d, hc, h => by
    rw [Expr.instantiateList_cons]
    have ih := bounded vs e (d + 1) (fun w hw => hc w (List.mem_cons_of_mem _ hw))
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    exact Expr.looseBVarsBounded_instantiate1_gen (hc v List.mem_cons_self) ih

/-- **A variable** under an environment of closed origins is its origin. -/
theorem lookup {vs : List Expr} (hc : AllClosed vs) {i : Nat} (hi : i < vs.length) :
    (Expr.bvar i).instantiateList vs = vs[i] := by
  simp only [Expr.instantiateList, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, hi, ↓reduceDIte]
  exact Expr.instantiateList_eq_self (hc _ (List.getElem_mem hi))

/-- A variable past the environment reads back as a variable. -/
theorem lookup_past {vs : List Expr} {i : Nat} (hi : vs.length ≤ i) :
    (Expr.bvar i).instantiateList vs = .bvar (i - vs.length) := by
  have h : ¬ (i < vs.length) := by omega
  simp only [Expr.instantiateList, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, h, ↓reduceDIte]

/-- **β under an environment**. -/
theorem beta_env (env : Env) (ty b : Expr) (vs : List Expr) (a : Expr) :
    ERed env (.app ((Expr.lam ty b).instantiateList vs) a) (b.instantiateList (a :: vs)) := by
  rw [Expr.instantiateList_cons]
  simp only [Expr.instantiateList]
  exact .beta

/-- `k` nested λs over a body. -/
@[expose] def lams : Nat → Expr → Expr
  | 0, b => b
  | k + 1, b => .lam bot (lams k b)

/-- **β, `k` arguments at once** (the first argument the outermost λ's): the
body under the environment extended by the arguments, the last innermost. -/
theorem betaN_env (env : Env) : ∀ (as : List Expr) (b : Expr) (vs : List Expr),
    ERed env (Expr.mkAppN ((lams as.length b).instantiateList vs) as)
      (b.instantiateList (as.reverse ++ vs))
  | [], b, vs => by simp [lams, Expr.mkAppN]; exact .refl
  | a :: as, b, vs => by
    simp only [List.length_cons, lams, Expr.mkAppN, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    have h₁ := beta_env env bot (lams as.length b) vs a
    have h₂ := betaN_env env as b (a :: vs)
    exact (mkAppN_appFn env as h₁).trans h₂
where
  /-- Reduction in head position under a spine. -/
  mkAppN_appFn (env : Env) : ∀ (as : List Expr) {f f' : Expr}, ERed env f f' →
      ERed env (Expr.mkAppN f as) (Expr.mkAppN f' as)
    | [], _, _, h => h
    | _ :: as, _, _, h => mkAppN_appFn env as (.appFn h)

/-- **ζ under an environment**. -/
theorem zeta_env (env : Env) (ty v b : Expr) (vs : List Expr) :
    ERed env ((Expr.letE ty v b).instantiateList vs)
      (b.instantiateList (v.instantiateList vs :: vs)) := by
  rw [Expr.instantiateList_cons vs b _ 0]
  simp only [Expr.instantiateList]
  exact .zeta

end ConLeche.Verify.Ground
