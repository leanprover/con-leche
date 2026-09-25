module

public import Fragment.Decl
public import Fragment.Hygiene

@[expose] public section

/-!
# Scope of inferred and generated terms

Two groups of syntactic facts the environment section reads when it
moves a declaration's scope (`Expr.Scoped`, `Decl.lean`) from the
checks to the stored constants.

**Inferred terms are in scope.**  An inferred term is closed at its
context's depth and mentions only stored constants: the checker's
`looseBVarsBounded` and `constsResolve` checks are consequences of
inference, not extra premises (`Infer.closedAt`, `Infer.consts`).
Level parameters are not: inference never reads a level, so
`lparamsIn` stays a separate check (`allLevelParamsDefined`).

**Generated telescopes are in scope.**  The generators of `Decl.lean`
build the former's, the constructors' and the recursor's types out of
`mkPis`/`mkLams` over contexts, `varsAt` spines, `liftCtx` and the one
lifting `atCtx`; the lemmas below push the three scope predicates of
`Scope.lean` through each of them.  A context is innermost first:
entry `Γ[i]` sits under `Γ.length - 1 - i` earlier entries, which is
what `CtxClosedAt` says.
-/

namespace Fragment

/-! ## Scope of inferred terms -/

/-- An inferred term is closed at its context's depth: every bound
variable has a context entry, and the binder rules extend the context
with the domain. -/
theorem Infer.closedAt [LevelOracle] {env : Env} :
    ∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → e.closedAt Γ.length = true
  | _, _, _, .bvar h => by
    rw [Expr.closedAt_bvar, decide_eq_true_eq]
    exact (List.getElem?_eq_some_iff.mp h).1
  | _, _, _, .sort => rfl
  | _, _, _, .const _ _ => rfl
  | _, _, _, .pi hA _ hB _ _ => by
    rw [Expr.closedAt_pi, Bool.and_eq_true]
    exact ⟨Infer.closedAt hA, Infer.closedAt hB⟩
  | _, _, _, .lam hA _ hb _ _ _ => by
    rw [Expr.closedAt_lam, Bool.and_eq_true]
    exact ⟨Infer.closedAt hA, Infer.closedAt hb⟩
  | _, _, _, .app hf _ ha _ => by
    rw [Expr.closedAt_app, Bool.and_eq_true]
    exact ⟨Infer.closedAt hf, Infer.closedAt ha⟩

/-- An inferred term mentions only stored constants: the constant rule
looks each one up. -/
theorem Infer.consts [LevelOracle] {env : Env} :
    ∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → ∀ c ∈ e.consts, (env.find? c).isSome
  | _, _, _, .bvar _, _, hc => by simp at hc
  | _, _, _, .sort, _, hc => by simp at hc
  | _, _, _, .const hfind _, _, hc => by
    rw [Expr.consts_const, List.mem_singleton] at hc
    subst hc
    rw [hfind]
    rfl
  | _, _, _, .pi hA _ hB _ _, c, hc => by
    rw [Expr.consts_pi, List.mem_append] at hc
    exact hc.elim (Infer.consts hA c) (Infer.consts hB c)
  | _, _, _, .lam hA _ hb _ _ _, c, hc => by
    rw [Expr.consts_lam, List.mem_append] at hc
    exact hc.elim (Infer.consts hA c) (Infer.consts hb c)
  | _, _, _, .app hf _ ha _, c, hc => by
    rw [Expr.consts_app, List.mem_append] at hc
    exact hc.elim (Infer.consts hf c) (Infer.consts ha c)

/-! ## Generated telescopes -/

namespace Expr

/-- A context is closed at `k`: entry `i` is closed under `k` plus its
earlier entries (the context is innermost first, so entry `i` has
`Γ.length - 1 - i` of them). -/
def CtxClosedAt (k : Nat) (Γ : List Expr) : Prop :=
  ∀ i A, Γ[i]? = some A → closedAt (k + (Γ.length - 1 - i)) A = true

@[simp] theorem CtxClosedAt_nil (k : Nat) : CtxClosedAt k [] := by
  intro i A h
  simp at h

/-- A context's head is closed under `k` and all the other entries;
the tail is closed at `k`. -/
theorem CtxClosedAt_cons {k : Nat} {A : Expr} {Γ : List Expr} :
    CtxClosedAt k (A :: Γ) ↔ closedAt (k + Γ.length) A = true ∧ CtxClosedAt k Γ := by
  constructor
  · intro h
    refine ⟨?_, fun i B hB => ?_⟩
    · simpa using h 0 A rfl
    · have := h (i + 1) B (by simpa using hB)
      have e : (A :: Γ).length - 1 - (i + 1) = Γ.length - 1 - i := by simp; omega
      rw [e] at this
      exact this
  · rintro ⟨hA, hΓ⟩ i B hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB
      subst hB
      simpa using hA
    | succ i =>
      simp only [List.getElem?_cons_succ] at hB
      have e : (A :: Γ).length - 1 - (i + 1) = Γ.length - 1 - i := by simp; omega
      rw [e]
      exact hΓ i B hB

/-- A `∀`-telescope over a context is closed at `k` exactly when the
context is and the body is closed under all of it. -/
theorem closedAt_mkPis_iff {pw : PropWhen} {k : Nat} :
    ∀ {Γ : List Expr} {b : Expr},
      closedAt k (mkPis pw Γ b) = true ↔ CtxClosedAt k Γ ∧ closedAt (k + Γ.length) b = true
  | [], b => by simp
  | A :: Γ, b => by
    rw [mkPis_cons, closedAt_mkPis_iff, closedAt_pi, Bool.and_eq_true, CtxClosedAt_cons]
    simp only [List.length_cons, ← Nat.add_assoc]
    exact ⟨fun ⟨h, hA, hb⟩ => ⟨⟨hA, h⟩, hb⟩, fun ⟨⟨hA, h⟩, hb⟩ => ⟨h, hA, hb⟩⟩

/-- A `λ`-telescope over a context is closed at `k` exactly when the
context is and the body is closed under all of it. -/
theorem closedAt_mkLams_iff {pw : PropWhen} {k : Nat} :
    ∀ {Γ : List Expr} {b : Expr},
      closedAt k (mkLams pw Γ b) = true ↔ CtxClosedAt k Γ ∧ closedAt (k + Γ.length) b = true
  | [], b => by simp
  | A :: Γ, b => by
    rw [mkLams_cons, closedAt_mkLams_iff, closedAt_lam, Bool.and_eq_true, CtxClosedAt_cons]
    simp only [List.length_cons, ← Nat.add_assoc]
    exact ⟨fun ⟨h, hA, hb⟩ => ⟨⟨hA, h⟩, hb⟩, fun ⟨⟨hA, h⟩, hb⟩ => ⟨h, hA, hb⟩⟩

/-- A `∀`-telescope over a closed context and a body closed under it
is closed. -/
theorem closedAt_mkPis {pw : PropWhen} {k : Nat} {Γ : List Expr} {b : Expr}
    (hΓ : CtxClosedAt k Γ) (hb : closedAt (k + Γ.length) b = true) :
    closedAt k (mkPis pw Γ b) = true :=
  closedAt_mkPis_iff.mpr ⟨hΓ, hb⟩

/-- A `λ`-telescope over a closed context and a body closed under it
is closed. -/
theorem closedAt_mkLams {pw : PropWhen} {k : Nat} {Γ : List Expr} {b : Expr}
    (hΓ : CtxClosedAt k Γ) (hb : closedAt (k + Γ.length) b = true) :
    closedAt k (mkLams pw Γ b) = true :=
  closedAt_mkLams_iff.mpr ⟨hΓ, hb⟩

/-- The variables of `n` binders sitting `o` up are closed at any
depth holding all of them. -/
theorem closedAt_varsAt {k o n : Nat} (h : o + n ≤ k) :
    ∀ e ∈ varsAt o n, closedAt k e = true := by
  intro e he
  simp only [varsAt, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, rfl⟩ := he
  rw [closedAt_bvar, decide_eq_true_eq]
  omega

/-- The lifting into a minor premise or a rule keeps an expression
closed: an expression closed under `j` binders and `d` of its own is
closed under `j`, the `nF - k + l` fields and hypotheses inserted
above its own `k` fields, the `o` binders inserted above the
parameters, and its `d`. -/
theorem closedAt_atCtx {nF k l o d j : Nat} {e : Expr} (h : closedAt (j + d) e = true) :
    closedAt (j + (nF - k + l) + o + d) (atCtx nF k l o d e) = true := by
  have eq : j + (nF - k + l) + o + d = j + d + (nF - k + l) + o := by omega
  rw [atCtx, eq]
  exact closedAt_liftN (closedAt_liftN h)

/-- A `∀`-telescope mentions only the constants of its body and of its
context's entries. -/
theorem consts_mkPis (pw : PropWhen) :
    ∀ (Γ : List Expr) (b : Expr) (c : Name), c ∈ consts (mkPis pw Γ b) →
      c ∈ consts b ∨ ∃ A ∈ Γ, c ∈ consts A
  | [], _, _, hc => Or.inl hc
  | A :: Γ, b, c, hc => by
    rw [mkPis_cons] at hc
    rcases consts_mkPis pw Γ (pi A pw b) c hc with h | ⟨B, hB, hc⟩
    · rw [consts_pi, List.mem_append] at h
      rcases h with h | h
      · exact Or.inr ⟨A, List.mem_cons_self, h⟩
      · exact Or.inl h
    · exact Or.inr ⟨B, List.mem_cons_of_mem A hB, hc⟩

/-- A `λ`-telescope mentions only the constants of its body and of its
context's entries. -/
theorem consts_mkLams (pw : PropWhen) :
    ∀ (Γ : List Expr) (b : Expr) (c : Name), c ∈ consts (mkLams pw Γ b) →
      c ∈ consts b ∨ ∃ A ∈ Γ, c ∈ consts A
  | [], _, _, hc => Or.inl hc
  | A :: Γ, b, c, hc => by
    rw [mkLams_cons] at hc
    rcases consts_mkLams pw Γ (lam A pw b) c hc with h | ⟨B, hB, hc⟩
    · rw [consts_lam, List.mem_append] at h
      rcases h with h | h
      · exact Or.inr ⟨A, List.mem_cons_self, h⟩
      · exact Or.inl h
    · exact Or.inr ⟨B, List.mem_cons_of_mem A hB, hc⟩

/-- The lifting into a minor premise or a rule mentions the same
constants. -/
theorem consts_atCtx (nF k l o d : Nat) (e : Expr) : consts (atCtx nF k l o d e) = consts e := by
  rw [atCtx, consts_liftN, consts_liftN]

/-- A variable spine mentions no constant. -/
theorem consts_varsAt (o n : Nat) : ∀ e ∈ varsAt o n, consts e = [] := by
  intro e he
  simp only [varsAt, List.mem_map, List.mem_range] at he
  obtain ⟨j, _, rfl⟩ := he
  rfl

/-- A `∀`-telescope uses the level parameters of its annotation, its
context's entries and its body. -/
theorem lparamsIn_mkPis {ps : List Name} {pw : PropWhen} (hpw : pw.paramsIn ps = true) :
    ∀ {Γ : List Expr} {b : Expr}, (∀ A ∈ Γ, lparamsIn ps A = true) →
      lparamsIn ps b = true → lparamsIn ps (mkPis pw Γ b) = true
  | [], _, _, hb => hb
  | A :: Γ, b, hΓ, hb => by
    rw [mkPis_cons]
    refine lparamsIn_mkPis hpw (fun B hB => hΓ B (List.mem_cons_of_mem A hB)) ?_
    rw [lparamsIn_pi, hΓ A List.mem_cons_self, hpw, hb]
    rfl

/-- A `λ`-telescope uses the level parameters of its annotation, its
context's entries and its body. -/
theorem lparamsIn_mkLams {ps : List Name} {pw : PropWhen} (hpw : pw.paramsIn ps = true) :
    ∀ {Γ : List Expr} {b : Expr}, (∀ A ∈ Γ, lparamsIn ps A = true) →
      lparamsIn ps b = true → lparamsIn ps (mkLams pw Γ b) = true
  | [], _, _, hb => hb
  | A :: Γ, b, hΓ, hb => by
    rw [mkLams_cons]
    refine lparamsIn_mkLams hpw (fun B hB => hΓ B (List.mem_cons_of_mem A hB)) ?_
    rw [lparamsIn_lam, hΓ A List.mem_cons_self, hpw, hb]
    rfl

/-- The lifting into a minor premise or a rule uses the same level
parameters. -/
theorem lparamsIn_atCtx {ps : List Name} {nF k l o d : Nat} {e : Expr} :
    lparamsIn ps (atCtx nF k l o d e) = lparamsIn ps e := by
  rw [atCtx, lparamsIn_liftN, lparamsIn_liftN]

/-- A variable spine uses no level parameter. -/
theorem lparamsIn_varsAt (ps : List Name) (o n : Nat) :
    ∀ e ∈ varsAt o n, lparamsIn ps e = true := by
  intro e he
  simp only [varsAt, List.mem_map, List.mem_range] at he
  obtain ⟨j, _, rfl⟩ := he
  rfl

/-- Entry `i` of a lifted context is entry `i` of the context, lifted
by how many entries sit below it. -/
theorem liftCtx_getElem? {f : Nat → Expr → Expr} :
    ∀ {Γ : List Expr} {i : Nat}, (liftCtx f Γ)[i]? = (Γ[i]?).map (f (Γ.length - 1 - i))
  | [], _ => by simp
  | A :: Γ, 0 => by simp
  | A :: Γ, i + 1 => by
    rw [liftCtx_cons, List.getElem?_cons_succ, List.getElem?_cons_succ, liftCtx_getElem?]
    have e : (A :: Γ).length - 1 - (i + 1) = Γ.length - 1 - i := by simp; omega
    rw [e]

/-- An entry of a lifted context is an entry of the context, lifted by
how many entries sit below it. -/
theorem mem_liftCtx {f : Nat → Expr → Expr} {Γ : List Expr} {A' : Expr}
    (h : A' ∈ liftCtx f Γ) : ∃ i A, Γ[i]? = some A ∧ A' = f (Γ.length - 1 - i) A := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [liftCtx_getElem?, Option.map_eq_some_iff] at hi
  obtain ⟨A, hA, rfl⟩ := hi
  exact ⟨i, A, hA, rfl⟩

end Expr

end Fragment
