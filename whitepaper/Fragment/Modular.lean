module

public import Fragment.Consistency

@[expose] public section

/-!
# Modules: declarations and what they store

The syntactic half of modular checking (`ModularModel.lean` has the
theorem): a module's **declarations** — definitions, theorems,
inductive blocks — checked one after another against an environment
(`Checks`), what they store (`applyAll`, `Decl.stores`), and
**refinement** of constants (`ConstInfo.Le`): a constant refines
another when it is the other, or an assumption with the other's level
parameters and type (`ConstKind.assumed`).
-/

namespace Fragment

/-! ## Refinement of constants -/

/-- **One constant refines another**: it is the other, or an
assumption with the other's level parameters and type. -/
def ConstInfo.Le (ci ci' : ConstInfo) : Prop :=
  ci = ci' ∨ (ci.kind = .assumed ∧ ∃ k, ci' = { ci with kind := k })

theorem ConstInfo.Le.trans {a b c : ConstInfo} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c := by
  rcases h₁ with rfl | ⟨ha, k, rfl⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨-, k', rfl⟩
    · exact .inr ⟨ha, k, rfl⟩
    · exact .inr ⟨ha, k', rfl⟩

theorem ConstInfo.Le.lparams_eq {a b : ConstInfo} (h : a.Le b) : b.lparams = a.lparams := by
  rcases h with rfl | ⟨-, k, rfl⟩ <;> rfl

theorem ConstInfo.Le.type_eq {a b : ConstInfo} (h : a.Le b) : b.type = a.type := by
  rcases h with rfl | ⟨-, k, rfl⟩ <;> rfl

theorem ConstInfo.Le.eq_of_ne {a b : ConstInfo} (h : a.Le b) (hk : a.kind ≠ .assumed) : b = a := by
  rcases h with rfl | ⟨ha, -, -⟩
  · rfl
  · exact absurd ha hk

/-! ## Lookups in front of an environment -/

theorem lookup_append_of_none {Δ cs : List (Name × ConstInfo)} {n : Name} (h : Δ.lookup n = none) :
    (Δ ++ cs).lookup n = cs.lookup n := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm; simp [List.lookup] at h
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb] at h
      simp only [List.cons_append, List.lookup, hb]
      exact ih h

theorem lookup_append_of_some {Δ cs : List (Name × ConstInfo)} {n : Name} {e : ConstInfo}
    (h : Δ.lookup n = some e) : (Δ ++ cs).lookup n = some e := by
  induction Δ with
  | nil => simp at h
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm
      simp only [List.lookup, beq_self_eq_true, List.cons_append] at h ⊢; exact h
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb, List.cons_append] at h ⊢
      exact ih h

theorem key_of_lookup {Δ : List (Name × ConstInfo)} {n : Name} {e : ConstInfo}
    (h : Δ.lookup n = some e) : (n, e) ∈ Δ := by
  induction Δ with
  | nil => simp at h
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h; exact List.mem_cons_self ..
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_ne_none_of_mem {Δ : List (Name × ConstInfo)} {n : Name} {e : ConstInfo}
    (h : (n, e) ∈ Δ) : Δ.lookup n ≠ none := by
  induction Δ with
  | nil => cases h
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm; simp [List.lookup]
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb]
      rcases List.mem_cons.mp h with h | h
      · cases h; exact absurd rfl hnm
      · exact ih h

/-! ## What a block stores -/

namespace IndSpec

/-- The constructors' entries, stored in order in front of `pre`. -/
theorem foldl_add_consts (S : IndSpec) : ∀ (cs : List CtorSpec) (pre rest : List (Name × ConstInfo)),
    (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre ++ rest⟩ : Env)).consts =
      (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre⟩ : Env)).consts ++ rest
  | [], _, _ => rfl
  | c :: cs, pre, rest => foldl_add_consts S cs ((c.name, S.ctorInfo c) :: pre) rest

theorem foldl_add_empty (S : IndSpec) : ∀ (cs : List CtorSpec) (pre : List (Name × ConstInfo)),
    (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre⟩ : Env)).consts =
      (cs.map fun c => (c.name, S.ctorInfo c)).reverse ++ pre
  | [], _ => rfl
  | c :: cs, pre => by
    rw [List.foldl_cons]
    exact (foldl_add_empty S cs ((c.name, S.ctorInfo c) :: pre)).trans (by simp)

/-- **A block stores the same constants in front of any environment.** -/
theorem install_consts (S : IndSpec) (E : Env) :
    (S.install E).consts = (S.install Env.empty).consts ++ E.consts := by
  have hC : (S.envCtors E).consts = (S.envCtors Env.empty).consts ++ E.consts :=
    foldl_add_consts S S.ctors [(S.name, S.indInfo)] E.consts
  unfold install installN
  split <;> simp [Env.add, hC]

/-- The names a block stores: the type former, the recursor, the
auxiliary recursor of a nested block, the constructors. -/
def names (S : IndSpec) : List Name :=
  match S.nest with
  | none => S.name :: S.recName :: S.ctors.map (·.name)
  | some N => S.name :: S.recName :: N.aux :: S.ctors.map (·.name)

end IndSpec

/-! ## Declarations -/

section Checking

variable [LevelOracle]

/-- **A declaration** of a module: a definition, a theorem (its
statement `ci`, an assumption, and its proof) or an inductive block. -/
inductive Decl where
  | defn (c : Name) (ci : ConstInfo)
  | thm (c : Name) (ci : ConstInfo) (proof : Expr)
  | ind (S : IndSpec)
  deriving DecidableEq

namespace Decl

/-- What the declaration stores. -/
def apply : Decl → Env → Env
  | defn c ci, E => E.add c ci
  | thm c ci _, E => E.add c ci
  | ind S, E => S.install E

/-- The check the declaration passes (`Decl.lean`). -/
def Ok (E : Env) : Decl → Prop
  | defn c ci => DefOk E c ci
  | thm c ci v => ThmOk E c ci v
  | ind S => IndOk E S

/-- The names the declaration stores. -/
def names : Decl → List Name
  | defn c _ => [c]
  | thm c _ _ => [c]
  | ind S => S.names

/-- The entries the declaration stores, whatever the environment. -/
def stores (d : Decl) : List (Name × ConstInfo) := (d.apply Env.empty).consts

omit [LevelOracle] in
theorem apply_eq (d : Decl) (E : Env) : d.apply E = ⟨d.stores ++ E.consts⟩ := by
  cases d with
  | defn c ci => rfl
  | thm c ci v => rfl
  | ind S =>
    show S.install E = ⟨(S.install Env.empty).consts ++ E.consts⟩
    rw [← IndSpec.install_consts]

omit [LevelOracle] in
/-- **The names a declaration stores are the keys of its entries.** -/
theorem mem_names_iff (d : Decl) (n : Name) : n ∈ d.names ↔ ∃ e, (n, e) ∈ d.stores := by
  cases d with
  | defn c ci => simp [Decl.names, Decl.stores, Decl.apply, Env.add, Env.empty, eq_comm]
  | thm c ci v => simp [Decl.names, Decl.stores, Decl.apply, Env.add, Env.empty, eq_comm]
  | ind S =>
    have hC : (S.envCtors Env.empty).consts =
        (S.ctors.map fun c => (c.name, S.ctorInfo c)).reverse ++ [(S.name, S.indInfo)] :=
      IndSpec.foldl_add_empty S S.ctors [(S.name, S.indInfo)]
    simp only [Decl.names, Decl.stores, Decl.apply, IndSpec.names, IndSpec.install,
      IndSpec.installN]
    cases hn : S.nest <;> simp [Env.add, hC] <;> grind

end Decl

/-- **A list of declarations checks** against an environment: each
declaration accepted on top of it and the declarations before it. -/
inductive Checks : Env → List Decl → Prop
  | nil {E : Env} : Checks E []
  | cons {E : Env} {d : Decl} {ds : List Decl} : d.Ok E → Checks (d.apply E) ds → Checks E (d :: ds)

/-- The environment with a list of declarations stored. -/
def applyAll : List Decl → Env → Env
  | [], E => E
  | d :: ds, E => applyAll ds (d.apply E)

/-- The entries a list of declarations stores, latest first. -/
def storesAll : List Decl → List (Name × ConstInfo)
  | [] => []
  | d :: ds => storesAll ds ++ d.stores

omit [LevelOracle] in
theorem applyAll_eq : ∀ (ds : List Decl) (E : Env), applyAll ds E = ⟨storesAll ds ++ E.consts⟩
  | [], _ => rfl
  | d :: ds, E => by
    rw [applyAll, applyAll_eq ds, Decl.apply_eq]
    simp [storesAll, List.append_assoc]

omit [LevelOracle] in
theorem storesAll_lookup_some {ds : List Decl} {n : Name} {e : ConstInfo}
    (h : (storesAll ds).lookup n = some e) : ∃ d ∈ ds, d.stores.lookup n = some e := by
  induction ds with
  | nil => simp [storesAll] at h
  | cons d ds ih =>
    simp only [storesAll] at h
    cases hl : (storesAll ds).lookup n with
    | some e' =>
      rw [lookup_append_of_some hl] at h
      cases h
      obtain ⟨d', hd', h'⟩ := ih hl
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩
    | none =>
      rw [lookup_append_of_none hl] at h
      exact ⟨d, List.mem_cons_self .., h⟩

omit [LevelOracle] in
/-- **What a list of declarations stores in front of an environment**:
a found constant is one a declaration stores, or one of the
environment. -/
theorem find?_applyAll {ds : List Decl} {E : Env} {n : Name} {e : ConstInfo}
    (h : (applyAll ds E).find? n = some e) :
    (∃ d ∈ ds, d.stores.lookup n = some e) ∨ E.find? n = some e := by
  rw [applyAll_eq] at h
  cases hl : (storesAll ds).lookup n with
  | some e' =>
    have h' : (storesAll ds ++ E.consts).lookup n = some e' := lookup_append_of_some hl
    rw [show (storesAll ds ++ E.consts).lookup n = some e from h] at h'
    cases h'
    exact .inl (storesAll_lookup_some hl)
  | none =>
    have h' := lookup_append_of_none (cs := E.consts) hl
    rw [show (storesAll ds ++ E.consts).lookup n = some e from h] at h'
    exact .inr h'.symm

end Checking

end Fragment
