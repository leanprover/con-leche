import Setlec.Kernel.Core
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
  (∀ cv value hint, c = .defnInfo cv value hint →
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
  have hf : ∀ n, (env.find? n).isSome = true →
      (Env.find? ⟨c :: env.consts⟩ n).isSome = true := by
    intro n h
    rw [Env.find?_cons]
    split <;> simp_all
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx nm ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam nm ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE nm ty body mb ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE nm ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

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
  induction e with
  | lit l => cases l <;> simp_all [Expr.constsResolve]
  | _ => simp_all [Expr.constsResolve]

/-- Telescope domains of a resolving type resolve. -/
theorem Expr.constsResolve_stripPis {env : Env} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) → e.constsResolve env = true →
      (∀ b ∈ bs, (b.2.1).constsResolve env = true) ∧
      body.constsResolve env = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h hres
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun b hb => absurd hb (List.not_mem_nil), hres⟩
  | succ k ih =>
    intro e bs body h hres
    match e, h with
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs', body'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.constsResolve, Bool.and_eq_true] at hres
        obtain ⟨hd, hrest⟩ := ih hs hres.2
        refine ⟨?_, hrest⟩
        intro bnd hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hres.1
        · exact hd bnd hb

/-- `stripPis` commutes with constant renaming. -/
theorem Expr.stripPis_renameConsts {f : Name → Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) →
      (e.renameConsts f).stripPis k =
        some (bs.map (fun b => (b.1, (b.2.1).renameConsts f, b.2.2)),
          body.renameConsts f) := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expr.stripPis]
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs', body'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show ((Expr.forallE n ty b m).renameConsts f).stripPis (k + 1) = _
        rw [show (Expr.forallE n ty b m).renameConsts f =
          .forallE n (ty.renameConsts f) (b.renameConsts f) m from rfl]
        simp only [Expr.stripPis, ih hs, Option.map_some, List.map_cons]

/-- Invert `stripPis` across constant renaming: a strip of the renamed
telescope comes from a strip of the original. -/
theorem Expr.stripPis_renameConsts_inv {f : Name → Name} :
    ∀ (k : Nat) {e : Expr} {bs' : List (Name × Expr × BinderMeta)}
      {body' : Expr},
      (e.renameConsts f).stripPis k = some (bs', body') →
      ∃ bs body, e.stripPis k = some (bs, body) ∧
        bs' = bs.map (fun b => (b.1, (b.2.1).renameConsts f, b.2.2)) ∧
        body' = body.renameConsts f := by
  intro k
  induction k with
  | zero =>
    intro e bs' body' h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, by simp [Expr.stripPis]⟩
  | succ k ih =>
    intro e bs' body' h
    match e, h with
    | .forallE n ty b m, h =>
      rw [show (Expr.forallE n ty b m).renameConsts f =
        .forallE n (ty.renameConsts f) (b.renameConsts f) m from rfl] at h
      simp only [Expr.stripPis] at h
      cases hs : (b.renameConsts f).stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs₀, body₀⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨bs, body, hstrip, rfl, rfl⟩ := ih hs
        refine ⟨(n, ty, m) :: bs, body, ?_, by simp, rfl⟩
        simp only [Expr.stripPis, hstrip, Option.map_some]
    | .bvar _, h => exact nomatch h
    | .fvar _ _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _ _ _, h => exact nomatch h
    | .letE _ _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h

/-- Renaming maps that agree on every stored name rename a resolving
expression identically. -/
theorem Expr.renameConsts_congr_resolve {env : Env} {f g : Name → Name}
    (hfg : ∀ n, (env.find? n).isSome = true → f n = g n) :
    ∀ (e : Expr), e.constsResolve env = true →
      e.renameConsts f = e.renameConsts g := by
  intro e
  induction e <;> intro h <;>
    simp_all [Expr.constsResolve, Expr.renameConsts]
  all_goals first
  | (rename_i n _; exact hfg n h)
  | (rename_i s _ _ h'; exact hfg s h'.1)
  | (rename_i s _ _; exact hfg s h.1)

/-- Extending with a fresh, well-formed constant preserves `EnvWF`. -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env}
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts⟩ c) : EnvWF ⟨c :: env.consts⟩ := by
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hmem
  · exact hc
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := henv c' hmem
    refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value hint heq =>
      let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_⟩
    intro cv nP nM nm ni rules heq r hr
    obtain ⟨g1, g2, g3, g4⟩ := h6 cv nP nM nm ni rules heq r hr
    exact ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩

end Setlec
