import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level

/-!
# Environment well-formedness

`EnvWF` collects the syntactic facts the checker establishes for every
accepted constant — closed, level parameters within the declared list,
referenced constants resolving — as an invariant of the environment.  The
delta-unfolding and monotonicity lemmas need it.
-/

namespace Setlec

/-- Syntactic well-formedness of one stored constant w.r.t. `env`. -/
def ConstWF (env : Env) (c : ConstantInfo) : Prop :=
  c.toConstantVal.type.hasFvar = false ∧
  c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
  c.toConstantVal.type.constsResolve env = true ∧
  c.toConstantVal.type.looseBVarsBounded 0 = true ∧
  (∀ cv value, c = .defnInfo cv value →
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true ∧
    value.looseBVarsBounded 0 = true) ∧
  (∀ cv nP nM nm ni rules, c = .recInfo cv nP nM nm ni rules →
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true)

/-- Every stored constant is syntactically well-formed. -/
def EnvWF (env : Env) : Prop := ∀ c ∈ env.consts, ConstWF env c

/-- `find?` on a cons. -/
theorem Env.find?_cons {c : ConstantInfo} {env : Env} {n : Name} :
    Env.find? ⟨c :: env.consts⟩ n = if c.name = n then some c else env.find? n := by
  simp only [Env.find?, List.find?]
  split
  · next h => simp_all
  · next h => simp_all

/-- Extending the environment with a fresh constant does not change
successful lookups. -/
theorem Env.find?_cons_of_isSome {c : ConstantInfo} {env : Env} {n : Name}
    (hfresh : env.find? c.name = none) (h : (env.find? n).isSome = true) :
    Env.find? ⟨c :: env.consts⟩ n = env.find? n := by
  rw [Env.find?_cons]
  split
  · next heq => rw [← heq] at h; rw [hfresh] at h; simp at h
  · rfl

/-- Resolution is monotone under environment extension. -/
theorem Expr.constsResolve_mono {c : ConstantInfo} {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨c :: env.consts⟩ = true := by
  intro e
  induction e <;> simp_all [Expr.constsResolve]
  case const n us =>
    rw [Env.find?_cons]
    split <;> simp_all

/-- Resolution survives binder opening. -/
theorem Expr.constsResolve_instantiate1 {env : Env} {d : Nat} {n : Name} {ty : Expr}
    (hty : ty.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 (.fvar d n ty) k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · simpa [Expr.constsResolve] using hty
    · split <;> simp [Expr.constsResolve]

/-- Level instantiation does not change which constants occur. -/
theorem Expr.constsResolve_instantiateLevelParams {env : Env} (ks : List Name)
    (us : List Level) :
    ∀ {e : Expr}, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- No name equals its own string extension. -/
theorem Name.str_ne (n : Name) (s : String) : n.str s ≠ n := by
  intro h
  have h1 : sizeOf (Name.str n s) = sizeOf n := congrArg sizeOf h
  simp at h1
  omega

/-- Resolution only reads whether names are stored. -/
theorem Expr.constsResolve_congr {env₁ env₂ : Env}
    (henv : ∀ n, (env₁.find? n).isSome = (env₂.find? n).isSome) :
    ∀ (e : Expr), e.constsResolve env₁ = e.constsResolve env₂ := by
  intro e
  induction e <;> simp_all [Expr.constsResolve]

/-- Extending with a fresh, well-formed constant preserves `EnvWF`. -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env}
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts⟩ c) : EnvWF ⟨c :: env.consts⟩ := by
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hmem
  · exact hc
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := henv c' hmem
    refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value heq =>
      let ⟨g1, g2, g3, g4⟩ := h5 cv value heq
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_⟩
    intro cv nP nM nm ni rules heq r hr
    obtain ⟨g1, g2, g3, g4⟩ := h6 cv nP nM nm ni rules heq r hr
    exact ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩

end Setlec
