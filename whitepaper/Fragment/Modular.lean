module

public import Fragment.Consistency

@[expose] public section

/-!
# Modular checking

A development is a graph of **modules**.  Each module has its own
declarations, a **base** (the environment its declarations are checked
against; with its declarations, its **own environment**) and a
**summary** (the declarations of everything it rests on).  Three abstract notions carry
the argument:

* **refinement** `E₁ ≼ E₂` (`Env.Le`): `E₁` is `E₂` with constants left
  out or turned into assumptions of the same level parameters and type
  (`ConstKind.assumed`);
* **compatibility** of lists of declarations (`Compatible`): where two
  declarations store a common name, they store the same entries;
* the **join** of compatible lists (`join`).

**Checking is monotone** (`Red.mono` … `Infer.mono`, `Checks.mono`):
against a refinement the checker accepts no more.  No hypothesis on
the smaller environment is needed, not even that it is well formed.
The checks that read an absence — a declaration's names must be fresh
— take freshness in the larger environment as a hypothesis; the
inductive checks (positivity, the universe conditions) are monotone
(`IndSpec.IndOk.mono`).

**The local checks** at a module (`LocalOk`) read the module and its
direct imports only: its declarations accepted against its base; every
constant of its base a refinement of a constant of an import's own
environment; its declarations and its imports' summaries compatible;
its summary their join.  They give (`local_checks`): every module's
summary is a checked list of declarations, and its own environment
refines the environment the summary builds (`Module.world`) — an accepted
environment (`local_accepted`) with a model (`local_model`), in which
no closed term inhabits an empty proposition
(`local_no_empty_prop_inhabitant`).  The statement is per module: two
modules that never meet in one summary may store a name differently.

**Theorems** are stored as their statements, assumptions (`ThmOk`), so
two proofs of one statement store the same entries and are
compatible.
-/

namespace Fragment

/-! ## Refinement -/

/-- **Refinement**: `E₁` is `E₂` with constants left out or turned
into assumptions — each constant of `E₁` is stored in `E₂` as it is,
or, where `E₁` has an assumption, with its level parameters and type. -/
def Env.Le (E₁ E₂ : Env) : Prop :=
  ∀ n ci, E₁.find? n = some ci →
    E₂.find? n = some ci ∨ (ci.kind = .assumed ∧ ∃ k, E₂.find? n = some { ci with kind := k })

namespace Env.Le

variable {E₁ E₂ E₃ : Env}

theorem refl (E : Env) : E.Le E := fun _ _ h => .inl h

/-- The lookup in the larger environment: the same level parameters
and type, at some kind — the same kind unless the interface's is an
assumption. -/
theorem find' (h : E₁.Le E₂) {n : Name} {ci : ConstInfo} (hf : E₁.find? n = some ci) :
    ∃ k, E₂.find? n = some { ci with kind := k } ∧ (ci.kind ≠ .assumed → k = ci.kind) := by
  rcases h n ci hf with h' | ⟨ha, k, h'⟩
  · exact ⟨ci.kind, h', fun _ => rfl⟩
  · exact ⟨k, h', fun hn => absurd ha hn⟩

/-- A constant the interface does not assume is stored as it is. -/
theorem find_of_ne (h : E₁.Le E₂) {n : Name} {ci : ConstInfo} (hf : E₁.find? n = some ci)
    (hk : ci.kind ≠ .assumed) : E₂.find? n = some ci := by
  rcases h n ci hf with h' | ⟨ha, _, _⟩
  · exact h'
  · exact absurd ha hk

theorem isSome (h : E₁.Le E₂) {n : Name} (hn : (E₁.find? n).isSome) : (E₂.find? n).isSome := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨k, hk, -⟩ := h.find' hci
  simp [hk]

theorem trans (h₁ : E₁.Le E₂) (h₂ : E₂.Le E₃) : E₁.Le E₃ := by
  intro n ci hf
  rcases h₁ n ci hf with h' | ⟨ha, k, h'⟩
  · exact h₂ n ci h'
  · obtain ⟨k', hk', -⟩ := h₂.find' h'
    exact .inr ⟨ha, k', hk'⟩

/-- Storing the same constant on both sides. -/
theorem add (h : E₁.Le E₂) (c : Name) (ci : ConstInfo) : (E₁.add c ci).Le (E₂.add c ci) := by
  intro n ci' hf
  by_cases hn : n = c
  · subst hn
    simp only [Env.find?_add, ite_true] at hf ⊢
    exact .inl hf
  · simp only [Env.find?_add, hn, ite_false] at hf ⊢
    exact h n ci' hf

end Env.Le

namespace Env.Le

/-- An environment with values hidden refines it. -/
theorem hide (H : Name → Bool) (E : Env) : (E.hide H).Le E := by
  intro n ci hf
  obtain ⟨cm, hcm, rfl⟩ := Env.find?_hide_eq_some hf
  rcases ConstInfo.hideIf_cases (H n) cm with h | h
  · rw [h]; exact .inl hcm
  · rw [h]; exact .inr ⟨rfl, cm.kind, hcm⟩

/-- Leaving constants out refines: every lookup of `E₁` is one of `E₂`. -/
theorem of_sub {E₁ E₂ : Env} (h : ∀ n ci, E₁.find? n = some ci → E₂.find? n = some ci) : E₁.Le E₂ :=
  fun n ci hf => .inl (h n ci hf)

theorem empty (E : Env) : Env.empty.Le E := fun _ _ h => by simp at h

end Env.Le

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

/-- Refinement of environments, constant by constant. -/
theorem Env.Le.iff {E₁ E₂ : Env} :
    E₁.Le E₂ ↔ ∀ n ci, E₁.find? n = some ci → ∃ ci', E₂.find? n = some ci' ∧ ci.Le ci' := by
  constructor
  · intro h n ci hf
    rcases h n ci hf with h' | ⟨ha, k, h'⟩
    · exact ⟨ci, h', .inl rfl⟩
    · exact ⟨_, h', .inr ⟨ha, k, rfl⟩⟩
  · intro h n ci hf
    obtain ⟨ci', h', hle⟩ := h n ci hf
    rcases hle with rfl | ⟨ha, k, rfl⟩
    · exact .inl h'
    · exact .inr ⟨ha, k, h'⟩

/-! ## Monotonicity of the relations -/

variable {E₁ E₂ : Env}

theorem kind_ne_assumed_of_recursor {ci : ConstInfo} {a b c d : Nat} {rs : List RecRule}
    (h : ci.kind = .recursor a b c d rs) : ci.kind ≠ .assumed := by
  rw [h]; exact nofun

theorem kind_ne_assumed_of_ctor {ci : ConstInfo} {I : Name} {a b : Nat}
    (h : ci.kind = .ctor I a b) : ci.kind ≠ .assumed := by
  rw [h]; exact nofun

theorem kind_ne_assumed_of_induct {ci : ConstInfo} {a b : Nat} {cs : List Name} {S : IndSpec}
    (h : ci.kind = .induct a b cs S) : ci.kind ≠ .assumed := by
  rw [h]; exact nofun

theorem kind_ne_assumed_of_value {ci : ConstInfo} {v : Expr}
    (h : ci.value? = some v) : ci.kind ≠ .assumed := by
  intro hk
  simp [ConstInfo.value?, hk, ConstKind.value?] at h

section Mono

variable [LevelOracle]

mutual

/-- **Reduction is monotone** in the environment. -/
theorem Red.mono (h : E₁.Le E₂) : ∀ {Γ : List Expr} {e e' : Expr}, Red E₁ Γ e e' → Red E₂ Γ e e'
  | _, _, _, .refl => .refl
  | _, _, _, .trans h₁ h₂ => .trans (Red.mono h h₁) (Red.mono h h₂)
  | _, _, _, .appFn h₁ => .appFn (Red.mono h h₁)
  | _, _, _, .beta => .beta
  | _, _, _, .zeta => .zeta
  | _, _, _, .delta hfind hv hls =>
    .delta (h.find_of_ne hfind (kind_ne_assumed_of_value hv)) hv hls
  | _, _, _, .iota hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis' hresM
      hIM hDM hdoms' htys' hI' hD' hlv hP hres hshape hrps hX => by
    obtain ⟨k, hcij₂, -⟩ := h.find' hcij
    exact .iota (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst hcij₂ husj hmlen hpis' hresM (Infer.mono h hIM)
      (DefEq.mono h hDM) hdoms' htys' (fun p hp => Infer.mono h (hI' p hp))
      (fun p hp => DefEq.mono h (hD' p hp)) hlv (fun p hp => DefEq.mono h (hP p hp)) hres hshape
      hrps (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaProp hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis'
      hresM hdoms' htys' hI' hD' hlv hP hres hshape hrps hX hI hlsI hpisI hsort hu => by
    obtain ⟨k, hcij₂, -⟩ := h.find' hcij
    obtain ⟨k', hI₂, -⟩ := h.find' hI
    exact .iotaProp (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst hcij₂ husj hmlen hpis' hresM hdoms' htys'
      (fun p hp => Infer.mono h (hI' p hp)) (fun p hp => DefEq.mono h (hD' p hp)) hlv
      (fun p hp => DefEq.mono h (hP p hp)) hres hshape hrps (fun p hp => DefEq.mono h (hX p hp))
      hI₂ hlsI hpisI hsort hu
  | _, _, _, .iotaNested hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj hmlen
      hpis' hresM hIM hDM hdoms' htys' hI' hD' hlv hpl hP hres hshape hrps hX =>
    .iotaNested (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst (h.find_of_ne hcij (kind_ne_assumed_of_ctor hcijk))
      hcijk husj hmlen hpis' hresM (Infer.mono h hIM) (DefEq.mono h hDM) hdoms' htys'
      (fun p hp => Infer.mono h (hI' p hp)) (fun p hp => DefEq.mono h (hD' p hp)) hlv hpl
      (fun p hp => DefEq.mono h (hP p hp)) hres hshape hrps (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaSlot hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis'
      hresM hdoms' htys' hI' hD' hlv hP hres hshape hrps hX => by
    obtain ⟨k, hcij₂, -⟩ := h.find' hcij
    exact .iotaSlot (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst hcij₂ husj hmlen hpis' hresM hdoms' htys'
      (fun p hp => Infer.mono h (hI' p hp)) (fun p hp => DefEq.mono h (hD' p hp)) hlv
      (fun p hp => DefEq.mono h (hP p hp)) hres hshape hrps (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaNestedSlot hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj
      hmlen hpis' hresM hdoms' htys' hI' hD' hlv hpl hP hres hshape hrps hX =>
    .iotaNestedSlot (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst (h.find_of_ne hcij (kind_ne_assumed_of_ctor hcijk))
      hcijk husj hmlen hpis' hresM hdoms' htys' (fun p hp => Infer.mono h (hI' p hp))
      (fun p hp => DefEq.mono h (hD' p hp)) hlv hpl (fun p hp => DefEq.mono h (hP p hp)) hres
      hshape hrps (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaStrict hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis'
      hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl hlv hP hres hshape hrps hX => by
    obtain ⟨k, hcij₂, -⟩ := h.find' hcij
    exact .iotaStrict (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst hcij₂ husj hmlen hpis' hresM hdM
      (h.find_of_ne hI₀ (kind_ne_assumed_of_induct hk₀)) hk₀ hls₀ hd₀ hpis₀ hlvl hlv
      (fun p hp => DefEq.mono h (hP p hp)) hres hshape hrps (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaNestedStrict hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj
      hmlen hpis' hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl hlv hpl hP hres hshape hrps hX =>
    .iotaNestedStrict (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis
      (Red.mono h hmaj) hmeq hrl hctor hinst (h.find_of_ne hcij (kind_ne_assumed_of_ctor hcijk))
      hcijk husj hmlen hpis' hresM hdM (h.find_of_ne hI₀ (kind_ne_assumed_of_induct hk₀)) hk₀
      hls₀ hd₀ hpis₀ hlvl hlv hpl (fun p hp => DefEq.mono h (hP p hp)) hres hshape hrps
      (fun p hp => DefEq.mono h (hX p hp))
  | _, _, _, .iotaK hfind hkind hus hlen hpis hrl hk hI hr hF hD =>
    .iotaK (h.find_of_ne hfind (kind_ne_assumed_of_recursor hkind)) hkind hus hlen hpis hrl hk
      (Infer.mono h hI) (Red.mono h hr) (Infer.mono h hF) (DefEq.mono h hD)

/-- **Definitional equality is monotone** in the environment. -/
theorem DefEq.mono (h : E₁.Le E₂) : ∀ {Γ : List Expr} {a b : Expr}, DefEq E₁ Γ a b → DefEq E₂ Γ a b
  | _, _, _, .refl => .refl
  | _, _, _, .symm h₁ => .symm (DefEq.mono h h₁)
  | _, _, _, .redL hr h₁ => .redL (Red.mono h hr) (DefEq.mono h h₁)
  | _, _, _, .sort h₁ => .sort h₁
  | _, _, _, .const h₁ => .const h₁
  | _, _, _, .pi hA hB => .pi (DefEq.mono h hA) (DefEq.mono h hB)
  | _, _, _, .lam hA hb ht₁ ht₂ ht =>
    .lam (DefEq.mono h hA) (DefEq.mono h hb) (Infer.mono h ht₁) (Infer.mono h ht₂) (DefEq.mono h ht)
  | _, _, _, .lamProp hA hb hs hu hu0 =>
    .lamProp (DefEq.mono h hA) (DefEq.mono h hb) (Infer.mono h hs) (Red.mono h hu) hu0
  | _, _, _, .etaProp htb hr hA hbody hs hu hu0 =>
    .etaProp (Infer.mono h htb) (Red.mono h hr) (DefEq.mono h hA) (DefEq.mono h hbody)
      (Infer.mono h hs) (Red.mono h hu) hu0
  | _, _, _, .lamConst hA hb hc₁ hc₂ => .lamConst (DefEq.mono h hA) (DefEq.mono h hb) hc₁ hc₂
  | _, _, _, .appIn hf hI hr ha =>
    .appIn (DefEq.mono h hf) (Infer.mono h hI) (Red.mono h hr) (DefEqIn.mono h ha)
  | _, _, _, .app hf ha => .app (DefEq.mono h hf) (DefEq.mono h ha)
  | _, _, _, .eta htb hr hA hbody ht₁ htB =>
    .eta (Infer.mono h htb) (Red.mono h hr) (DefEq.mono h hA) (DefEq.mono h hbody)
      (Infer.mono h ht₁) (DefEq.mono h htB)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    .proofIrrel (Infer.mono h hta) (Infer.mono h htta) (Red.mono h hu) hu0 (Infer.mono h htb)
      (Infer.mono h httb) (Red.mono h hv) hv0
  | _, _, _, .lams h₁ => .lams (DefEqLams.mono h h₁)

theorem DefEqLams.mono (h : E₁.Le E₂) :
    ∀ {Γ : List Expr} {a b : Expr}, DefEqLams E₁ Γ a b → DefEqLams E₂ Γ a b
  | _, _, _, .refl => .refl
  | _, _, _, .inner hA hb ht₁ ht₂ ht =>
    .inner (DefEq.mono h hA) (DefEq.mono h hb) (Infer.mono h ht₁) (Infer.mono h ht₂)
      (DefEq.mono h ht)
  | _, _, _, .outer hA hb => .outer (DefEq.mono h hA) (DefEqLams.mono h hb)

theorem DefEqIn.mono (h : E₁.Le E₂) :
    ∀ {Γ : List Expr} {T a b : Expr}, DefEqIn E₁ Γ T a b → DefEqIn E₂ Γ T a b
  | _, _, _, _, .of h₁ => .of (DefEq.mono h h₁)
  | _, _, _, _, .symm h₁ => .symm (DefEqIn.mono h h₁)
  | _, _, _, _, .lam hr hb => .lam (Red.mono h hr) (DefEqIn.mono h hb)
  | _, _, _, _, .eta hr hb => .eta (Red.mono h hr) (DefEqIn.mono h hb)

/-- **Inference is monotone** in the environment: an assumption is
read through its type alone, which the larger environment stores
unchanged. -/
theorem Infer.mono (h : E₁.Le E₂) : ∀ {Γ : List Expr} {e T : Expr}, Infer E₁ Γ e T → Infer E₂ Γ e T
  | _, _, _, .bvar h₁ => .bvar h₁
  | _, _, _, .sort => .sort
  | _, _, _, .const (ci := ci) hfind hls => by
    obtain ⟨k, hf₂, -⟩ := h.find' hfind
    exact Infer.const (ci := { ci with kind := k }) hf₂ hls
  | _, _, _, .pi hA hu hB hv => .pi (Infer.mono h hA) (Red.mono h hu) (Infer.mono h hB) (Red.mono h hv)
  | _, _, _, .lam hA hu hb => .lam (Infer.mono h hA) (Red.mono h hu) (Infer.mono h hb)
  | _, _, _, .app hf hr ha hd => .app (Infer.mono h hf) (Red.mono h hr) (Infer.mono h ha) (DefEq.mono h hd)
  | _, _, _, .letE hT hu hv hd hb =>
    .letE (Infer.mono h hT) (Red.mono h hu) (Infer.mono h hv) (DefEq.mono h hd) (Infer.mono h hb)

end

end Mono

/-! ## What a declaration stores -/

/-- A lookup in front of an environment that misses the front. -/
theorem Env.find?_append_of_lookup {Δ cs : List (Name × ConstInfo)} {n : Name}
    (h : Δ.lookup n = none) : (⟨Δ ++ cs⟩ : Env).find? n = (⟨cs⟩ : Env).find? n := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm; simp [List.lookup] at h
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb] at h
      simp only [Env.find?, List.cons_append, List.lookup, hb]
      exact ih h

/-- A name missing from an environment with a front is missing from
the front and from the rest. -/
theorem Env.find?_append_none {Δ cs : List (Name × ConstInfo)} {n : Name}
    (h : (⟨Δ ++ cs⟩ : Env).find? n = none) :
    Δ.lookup n = none ∧ (⟨cs⟩ : Env).find? n = none := by
  induction Δ with
  | nil => exact ⟨rfl, h⟩
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm; simp [Env.find?] at h
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [Env.find?, List.cons_append, List.lookup, hb] at h
      simp only [List.lookup, hb]
      exact ih h

namespace Env.Le

/-- Storing the same constants in front on both sides. -/
theorem prepend (h : E₁.Le E₂) : ∀ Δ : List (Name × ConstInfo),
    (⟨Δ ++ E₁.consts⟩ : Env).Le ⟨Δ ++ E₂.consts⟩
  | [] => h
  | (c, ci) :: Δ => (prepend h Δ).add c ci

end Env.Le

namespace IndSpec

/-- The constructors' entries, stored in order in front of `pre`. -/
theorem foldl_add_consts (S : IndSpec) : ∀ (cs : List CtorSpec) (pre rest : List (Name × ConstInfo)),
    (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre ++ rest⟩ : Env)).consts =
      (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre⟩ : Env)).consts ++ rest
  | [], _, _ => rfl
  | c :: cs, pre, rest => foldl_add_consts S cs ((c.name, S.ctorInfo c) :: pre) rest

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

/-! ## Declarations and modules -/

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

/-- An accepted declaration's names are fresh. -/
theorem Ok.fresh {E : Env} {d : Decl} (h : d.Ok E) : ∀ n ∈ d.names, E.find? n = none := by
  cases d with
  | defn c ci => intro n hn; simp only [names, List.mem_singleton] at hn; subst hn; exact h.1
  | thm c ci v => intro n hn; simp only [names, List.mem_singleton] at hn; subst hn; exact h.2.1.1
  | ind S =>
    simp only [Ok, IndOk] at h
    simp only [names, IndSpec.names]
    split at h <;> rename_i hn <;> rw [hn]
    · exact h.2.1
    · exact h.2.2.1

end Decl

/-- **A definition's check is monotone** in the environment, at a
name that is fresh in the larger one. -/
theorem DefOk.mono (h : E₁.Le E₂) {c : Name} {ci : ConstInfo} (hf : E₂.find? c = none)
    (hok : DefOk E₁ c ci) : DefOk E₂ c ci :=
  have ⟨_, ⟨s, u, hT, hs⟩, ⟨v, T, hk, hv, hd, hl⟩, hps⟩ := hok
  ⟨hf, ⟨s, u, Infer.mono h hT, Red.mono h hs⟩, ⟨v, T, hk, Infer.mono h hv, DefEq.mono h hd, hl⟩, hps⟩

namespace IndSpec

omit [LevelOracle] in
theorem envCtors_le (S : IndSpec) (h : E₁.Le E₂) : (S.envCtors E₁).Le (S.envCtors E₂) := by
  have hC (E : Env) : S.envCtors E = ⟨(S.envCtors Env.empty).consts ++ E.consts⟩ :=
    congrArg Env.mk (foldl_add_consts S S.ctors [(S.name, S.indInfo)] E.consts)
  rw [hC E₁, hC E₂]
  exact h.prepend _

/-- **A block's check is monotone** in the environment, at names that
are fresh in the larger one. -/
theorem IndOk.mono (S : IndSpec) (h : E₁.Le E₂) (hf : ∀ n ∈ S.names, E₂.find? n = none)
    (hok : IndOk E₁ S) : IndOk E₂ S := by
  have hI : (S.envInd E₁).Le (S.envInd E₂) := h.add _ _
  have hC := S.envCtors_le h
  have hsc : ∀ n, (E₁.find? n).isSome → (E₂.find? n).isSome := fun _ hn => h.isSome hn
  simp only [IndOk] at hok ⊢
  simp only [names] at hf
  split at hok <;> rename_i hn <;> simp only [hn] at hf ⊢
  · obtain ⟨h1, -, h3, ⟨T, hT⟩, h5, h6, ⟨T', hT'⟩⟩ := hok
    refine ⟨h1, hf, h3.mono hsc, ⟨T, Infer.mono h hT⟩, fun c hc => ?_, h6, ⟨T', Infer.mono hC hT'⟩⟩
    obtain ⟨⟨T, u, ha, hb⟩, f2, f3, ⟨T2, hr⟩⟩ := h5 c hc
    refine ⟨⟨T, u, Infer.mono hI ha, Red.mono hI hb⟩, fun i A hA => ?_, fun i tele es he t T ht => ?_,
      ⟨T2, Infer.mono hC hr⟩⟩
    · obtain ⟨s, v, x, y, z, w⟩ := f2 i A hA
      exact ⟨s, v, Infer.mono hI x, Red.mono hI y, z, w⟩
    · obtain ⟨s, w, x, y, z⟩ := f3 i tele es he t T ht
      exact ⟨s, w, Infer.mono hI x, Red.mono hI y, z⟩
  · rename_i N
    obtain ⟨h0, h1, -, h3, ⟨T, hT⟩, h5, ⟨ci, hK, hk⟩, h7, h8, ⟨T₁, u₁, hc₁, hr₁⟩, h10, h11,
      ⟨T₂, hT₂⟩, ⟨T₃, hT₃⟩⟩ := hok
    refine ⟨h0, h1, hf, h3.mono hsc, ⟨T, Infer.mono h hT⟩, fun c hc => ?_,
      ⟨ci, h.find_of_ne hK (kind_ne_assumed_of_induct hk), hk⟩, h7, h8,
      ⟨T₁, u₁, Infer.mono hI hc₁, Red.mono hI hr₁⟩, h10,
      fun c hc => (h11 c hc).elim fun T hT => ⟨T, Infer.mono hC hT⟩,
      ⟨T₂, Infer.mono hC hT₂⟩, ⟨T₃, Infer.mono hC hT₃⟩⟩
    obtain ⟨⟨T, u, ha, hb⟩, f2, f3, ⟨T2, hr⟩⟩ := h5 c hc
    refine ⟨⟨T, u, Infer.mono hI ha, Red.mono hI hb⟩, fun i A hA => ?_, fun i tele es he t T ht => ?_,
      ⟨T2, Infer.mono hC hr⟩⟩
    · obtain ⟨s, v, x, y, z⟩ := f2 i A hA
      exact ⟨s, v, Infer.mono hI x, Red.mono hI y, z⟩
    · obtain ⟨s, w, x, y, z⟩ := f3 i tele es he t T ht
      exact ⟨s, w, Infer.mono hI x, Red.mono hI y, z⟩

end IndSpec

/-- **A declaration's check is monotone** in the environment, at
names fresh in the larger one. -/
theorem Decl.Ok.mono {d : Decl} (h : E₁.Le E₂) (hf : ∀ n ∈ d.names, E₂.find? n = none)
    (hok : d.Ok E₁) : d.Ok E₂ := by
  cases d with
  | defn c ci => exact DefOk.mono h (hf c (by simp [Decl.names])) hok
  | thm c ci v =>
    obtain ⟨hk, hd, s, u, hT, hs, hu⟩ := hok
    exact ⟨hk, DefOk.mono h (hf c (by simp [Decl.names])) hd, s, u, Infer.mono h hT, Red.mono h hs, hu⟩
  | ind S => exact IndSpec.IndOk.mono S h hf hok

/-- **A module checks**: its declarations, each accepted on top of the
environment it is checked against and the declarations before it. -/
inductive Checks : Env → List Decl → Prop
  | nil {E : Env} : Checks E []
  | cons {E : Env} {d : Decl} {ds : List Decl} : d.Ok E → Checks (d.apply E) ds → Checks E (d :: ds)

/-- The environment with a module's declarations stored. -/
def applyAll : List Decl → Env → Env
  | [], E => E
  | d :: ds, E => applyAll ds (d.apply E)

/-- A checked module's names are fresh in the environment it was
checked against. -/
theorem Checks.fresh {E : Env} {ds : List Decl} (h : Checks E ds) :
    ∀ d ∈ ds, ∀ n ∈ d.names, E.find? n = none := by
  induction h with
  | nil => intro _ hd; cases hd
  | @cons E d ds hd _ ih =>
    intro d' hd' n hn
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hd.fresh n hn
    · have := ih d' hd' n hn
      rw [Decl.apply_eq] at this
      exact (Env.find?_append_none this).2

/-- **A module's check is monotone** in the environment it is checked
against, at names fresh in the larger one. -/
theorem Checks.mono {E₁ : Env} {ds : List Decl} (hc : Checks E₁ ds) :
    ∀ {E₂ : Env}, E₁.Le E₂ → (∀ d ∈ ds, ∀ n ∈ d.names, E₂.find? n = none) → Checks E₂ ds := by
  induction hc with
  | nil => intro _ _ _; exact .nil
  | @cons E d ds hd hrest ih =>
    intro E₂ h hf
    refine .cons (hd.mono h (hf d (List.mem_cons_self ..))) (ih ?_ ?_)
    · rw [Decl.apply_eq, Decl.apply_eq]
      exact h.prepend _
    · intro d' hd' n hn
      have h₁ := hrest.fresh d' hd' n hn
      rw [Decl.apply_eq] at h₁
      rw [Decl.apply_eq, Env.find?_append_of_lookup (Env.find?_append_none h₁).1]
      exact hf d' (List.mem_cons_of_mem _ hd') n hn

/-- A module checked against an accepted environment extends it to an
accepted one. -/
theorem Checks.accepted {E : Env} {ds : List Decl} (hc : Checks E ds) (hE : Accepted E) :
    Accepted (applyAll ds E) := by
  induction hc with
  | nil => exact hE
  | @cons E d ds hd _ ih =>
    apply ih
    cases d with
    | defn c ci => exact .defn hE hd
    | thm c ci v => exact .thm hE hd
    | ind S => exact .ind S hE hd

/-! ## The entries of a checked list of declarations -/

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
theorem applyAll_append : ∀ (ds ds' : List Decl) (E : Env),
    applyAll (ds ++ ds') E = applyAll ds' (applyAll ds E)
  | [], _, _ => rfl
  | d :: ds, ds', E => applyAll_append ds ds' (d.apply E)

omit [LevelOracle] in
theorem IndSpec.foldl_add_empty (S : IndSpec) : ∀ (cs : List CtorSpec) (pre : List (Name × ConstInfo)),
    (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) (⟨pre⟩ : Env)).consts =
      (cs.map fun c => (c.name, S.ctorInfo c)).reverse ++ pre
  | [], _ => rfl
  | c :: cs, pre => by
    rw [List.foldl_cons]
    exact (IndSpec.foldl_add_empty S cs ((c.name, S.ctorInfo c) :: pre)).trans (by simp)

omit [LevelOracle] in
/-- **The names a declaration stores are the keys of its entries.** -/
theorem Decl.mem_names_iff (d : Decl) (n : Name) : n ∈ d.names ↔ ∃ e, (n, e) ∈ d.stores := by
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

omit [LevelOracle] in
theorem lookup_eq_none_of_not_key {Δ : List (Name × ConstInfo)} {n : Name}
    (h : ∀ e, (n, e) ∉ Δ) : Δ.lookup n = none := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨m, cm⟩ := p
    by_cases hnm : n = m
    · subst hnm; exact absurd (List.mem_cons_self ..) (h cm)
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb]
      exact ih fun e he => h e (List.mem_cons_of_mem _ he)

omit [LevelOracle] in
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

omit [LevelOracle] in
theorem lookup_append_of_none {Δ cs : List (Name × ConstInfo)} {n : Name} (h : Δ.lookup n = none) :
    (Δ ++ cs).lookup n = cs.lookup n :=
  Env.find?_append_of_lookup (cs := cs) h

omit [LevelOracle] in
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

omit [LevelOracle] in
/-- A name no declaration of a list stores is looked up past them. -/
theorem storesAll_lookup_none {ds : List Decl} {n : Name} (h : ∀ d ∈ ds, n ∉ d.names) :
    (storesAll ds).lookup n = none := by
  apply lookup_eq_none_of_not_key
  intro e he
  induction ds with
  | nil => simp [storesAll] at he
  | cons d ds ih =>
    simp only [storesAll, List.mem_append] at he
    rcases he with he | he
    · exact ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) he
    · exact h d (List.mem_cons_self ..) ((d.mem_names_iff n).mpr ⟨e, he⟩)

omit [LevelOracle] in
/-- A name found among a list's entries is found in one declaration. -/
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

/-- In a checked list, a later declaration's names are not stored by
an earlier one. -/
theorem Checks.disjoint {E : Env} {d : Decl} {ds : List Decl} (h : Checks E (d :: ds)) :
    ∀ d' ∈ ds, ∀ n ∈ d'.names, d.stores.lookup n = none := by
  cases h with
  | cons _ hrest =>
    intro d' hd' n hn
    have := hrest.fresh d' hd' n hn
    rw [Decl.apply_eq] at this
    exact (Env.find?_append_none this).1

/-- **Where a checked list stores a name, the lookup finds it**: the
entry of the one declaration that stores it. -/
theorem Checks.find?_of_lookup {E : Env} {ds : List Decl} (h : Checks E ds) {d : Decl} (hd : d ∈ ds)
    {n : Name} {e : ConstInfo} (hl : d.stores.lookup n = some e) : (applyAll ds E).find? n = some e := by
  induction h with
  | nil => cases hd
  | @cons E d₀ ds hd₀ hrest ih =>
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hdis := (Checks.cons hd₀ hrest).disjoint
      have hn : n ∈ d.names := (d.mem_names_iff n).mpr ⟨e, key_of_lookup hl⟩
      have hnone : (storesAll ds).lookup n = none :=
        storesAll_lookup_none fun d' hd' hn' => by rw [hdis d' hd' n hn'] at hl; cases hl
      show (applyAll ds (d.apply E)).find? n = some e
      rw [applyAll_eq, Decl.apply_eq]
      show (storesAll ds ++ (d.stores ++ E.consts)).lookup n = some e
      rw [lookup_append_of_none hnone, lookup_append_of_some hl]
    · exact ih hd'

omit [LevelOracle] in
/-- What a list of declarations stores in front of an environment. -/
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

/-- **A checked list refines another** that stores, for each of its
declarations, one storing the same entries. -/
theorem Checks.le_of_stores {K L : List Decl} (hL : Checks Env.empty L)
    (h : ∀ d ∈ K, ∃ d' ∈ L, d'.stores = d.stores) :
    (applyAll K Env.empty).Le (applyAll L Env.empty) := by
  refine Env.Le.of_sub fun n e hf => ?_
  rcases find?_applyAll hf with ⟨d, hd, hl⟩ | hl
  · obtain ⟨d', hd', hs⟩ := h d hd
    exact hL.find?_of_lookup hd' (by rw [hs]; exact hl)
  · simp at hl

/-! ## Joining compatible lists -/

/-- Two declarations store a common name. -/
def Decl.overlaps (d d' : Decl) : Bool := d.names.any (d'.names.contains ·)

omit [LevelOracle] in
theorem Decl.overlaps_iff {d d' : Decl} : d.overlaps d' = true ↔ ∃ n ∈ d.names, n ∈ d'.names := by
  simp [Decl.overlaps]

/-- **Compatible lists of declarations**: where a declaration of the
one and a declaration of the other store a common name, they store the
same entries. -/
def Compatible (K L : List Decl) : Prop :=
  ∀ k ∈ K, ∀ d ∈ L, k.overlaps d = true → k.stores = d.stores

/-- **The join** of two lists of declarations: the first, then the
declarations of the second that store no name the first stores. -/
def join (K L : List Decl) : List Decl := K ++ L.filter fun d => !K.any (·.overlaps d)

omit [LevelOracle] in
theorem mem_join {K L : List Decl} {d : Decl} (h : d ∈ join K L) : d ∈ K ∨ d ∈ L := by
  rcases List.mem_append.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_filter.mp h).1

omit [LevelOracle] in
/-- A declaration of the second list is in the join, or one of the
first stores the same entries. -/
theorem stores_of_join {K L : List Decl} (hc : Compatible K L) {d : Decl} (hd : d ∈ L) :
    ∃ d' ∈ join K L, d'.stores = d.stores := by
  by_cases ho : K.any (·.overlaps d) = true
  · obtain ⟨k, hk, hkd⟩ := List.any_eq_true.mp ho
    exact ⟨k, List.mem_append_left _ hk, hc k hk d hd hkd⟩
  · exact ⟨d, List.mem_append_right _ (List.mem_filter.mpr ⟨hd, by simpa using ho⟩), rfl⟩

omit [LevelOracle] in
/-- Entries in front of an environment that a larger one stores, with
the environment refining it, refine it. -/
theorem Env.Le.front {Δ : List (Name × ConstInfo)} {E₀ E₂ : Env}
    (h₁ : ∀ n e, Δ.lookup n = some e → E₂.find? n = some e) (h₂ : E₀.Le E₂) :
    (⟨Δ ++ E₀.consts⟩ : Env).Le E₂ := by
  intro n e hf
  cases hl : Δ.lookup n with
  | some e' =>
    have h' : (Δ ++ E₀.consts).lookup n = some e' := lookup_append_of_some hl
    rw [show (Δ ++ E₀.consts).lookup n = some e from hf] at h'
    cases h'
    exact .inl (h₁ n e hl)
  | none =>
    have h' := lookup_append_of_none (cs := E₀.consts) hl
    rw [show (Δ ++ E₀.consts).lookup n = some e from hf] at h'
    exact h₂ n e h'.symm

theorem Checks.snoc {E : Env} {K : List Decl} {d : Decl} (hK : Checks E K) (hd : d.Ok (applyAll K E)) :
    Checks E (K ++ [d]) := by
  induction hK with
  | nil => exact .cons hd .nil
  | cons h₁ _ ih => exact .cons h₁ (ih hd)

/-- **Joining a checked list onto another**: a list checked against
an environment that the first list's environment refines, and
compatible with the first list, joins it into a checked list. -/
theorem Checks.joined {E₀ : Env} {L : List Decl} (hL : Checks E₀ L) :
    ∀ {K : List Decl}, Checks Env.empty K → E₀.Le (applyAll K Env.empty) → Compatible K L →
      Checks Env.empty (join K L) := by
  induction hL with
  | nil => intro K hK _ _; simpa [join] using hK
  | @cons E d ds hd hrest ih =>
    intro K hK hle hc
    have hdis := (Checks.cons hd hrest).disjoint
    have hcr : Compatible K ds := fun k hk d' hd' => hc k hk d' (List.mem_cons_of_mem _ hd')
    by_cases ho : K.any (·.overlaps d) = true
    · -- `d` stores what a declaration of `K` stores: skipped
      have hj : join K (d :: ds) = join K ds := by simp [join, ho]
      rw [hj]
      obtain ⟨k, hk, hkd⟩ := List.any_eq_true.mp ho
      have hs := hc k hk d (List.mem_cons_self ..) hkd
      refine ih hK ?_ hcr
      rw [Decl.apply_eq]
      exact Env.Le.front (fun n e hl => hK.find?_of_lookup hk (by rw [hs]; exact hl)) hle
    · -- `d` stores nothing `K` stores: kept
      have hno : ∀ d' ∈ ds, d.overlaps d' = false := by
        intro d' hd'
        cases h : d.overlaps d' with
        | false => rfl
        | true =>
          obtain ⟨n, hn, hn'⟩ := Decl.overlaps_iff.mp h
          obtain ⟨e, he⟩ := (d.mem_names_iff n).mp hn
          exact absurd (hdis d' hd' n hn') (lookup_ne_none_of_mem he)
      have hj : join K (d :: ds) = join (K ++ [d]) ds := by
        simp only [join, List.filter_cons, ho, Bool.not_false, ite_true, List.append_assoc,
          List.singleton_append]
        congr 2
        apply List.filter_congr
        intro d' hd'
        simp [List.any_append, hno d' hd']
      rw [hj]
      have hfresh : ∀ n ∈ d.names, (applyAll K Env.empty).find? n = none := by
        intro n hn
        rw [applyAll_eq]
        show (storesAll K ++ []).lookup n = none
        rw [List.append_nil]
        apply storesAll_lookup_none
        intro k hk hnk
        exact ho (List.any_eq_true.mpr ⟨k, hk, Decl.overlaps_iff.mpr ⟨n, hnk, hn⟩⟩)
      refine ih (hK.snoc (hd.mono hle hfresh)) ?_ ?_
      · rw [applyAll_append, applyAll, applyAll, Decl.apply_eq, Decl.apply_eq]
        exact hle.prepend _
      · intro k hk d' hd' hkd
        rcases List.mem_append.mp hk with hk | hk
        · exact hcr k hk d' hd' hkd
        · simp only [List.mem_singleton] at hk
          subst hk
          rw [hno d' hd'] at hkd
          cases hkd

/-! ## A development, checked module by module -/

/-- **A module** of a development: the modules it imports, its
declarations, the environment its declarations are checked against
(its **base**), and its **summary**: the declarations of everything it
rests on, itself included. -/
structure Module where
  imports : List Nat
  decls : List Decl
  base : Env
  summary : List Decl

/-- **A module's own environment**: its base with its declarations,
what its declarations were checked in. -/
def Module.own (m : Module) : Env := applyAll m.decls m.base

/-- The joined summaries of some imported modules, in order. -/
def importsJoin (dev : Nat → Module) (bs : List Nat) : List Decl :=
  bs.foldl (fun K b => join K (dev b).summary) []

/-- The partial environments a module's check compares: its own
declarations and its imports' summaries. -/
def family (dev : Nat → Module) (i : Nat) : List (List Decl) :=
  (dev i).decls :: (dev i).imports.map fun b => (dev b).summary

/-- **The local checks at module `i`.**  They read the module and its
direct imports — their own environments and their summaries — and
nothing else:

* the imports come earlier (the import graph has no cycle);
* the declarations are accepted against the base;
* every constant of the base refines a constant of some import's own
  environment;
* its declarations and its imports' summaries are compatible;
* its summary is their join. -/
structure LocalOk (dev : Nat → Module) (i : Nat) : Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  checks : Checks (dev i).base (dev i).decls
  base_le : ∀ n ci, (dev i).base.find? n = some ci →
    ∃ b ∈ (dev i).imports, ∃ ci', (dev b).own.find? n = some ci' ∧ ci.Le ci'
  compatible : ∀ X ∈ family dev i, ∀ Y ∈ family dev i, Compatible X Y
  summary_eq : (dev i).summary = join (importsJoin dev (dev i).imports) (dev i).decls

/-- **The environment a module rests on**: its summary, stored in
order. -/
def Module.world (m : Module) : Env := applyAll m.summary Env.empty

/-- The fold over the imports: checked, made of the imports'
declarations, and storing, for each of them, the same entries. -/
theorem importsJoin_inv (dev : Nat → Module) (i : Nat) (h : LocalOk dev i)
    (ih : ∀ b ∈ (dev i).imports, Checks Env.empty (dev b).summary) :
    ∀ (bs : List Nat) (K : List Decl), (∀ b ∈ bs, b ∈ (dev i).imports) →
      Checks Env.empty K → (∀ k ∈ K, ∃ b ∈ (dev i).imports, k ∈ (dev b).summary) →
      Checks Env.empty (bs.foldl (fun K b => join K (dev b).summary) K) ∧
      (∀ k ∈ bs.foldl (fun K b => join K (dev b).summary) K, ∃ b ∈ (dev i).imports, k ∈ (dev b).summary) ∧
      (∀ d ∈ K, d ∈ bs.foldl (fun K b => join K (dev b).summary) K) ∧
      (∀ b ∈ bs, ∀ d ∈ (dev b).summary,
        ∃ d' ∈ bs.foldl (fun K b => join K (dev b).summary) K, d'.stores = d.stores)
  | [], K, _, hK, hm => ⟨hK, hm, fun _ hd => hd, fun _ hb => by cases hb⟩
  | b :: bs, K, hbs, hK, hm => by
    have hb : b ∈ (dev i).imports := hbs b (List.mem_cons_self ..)
    have hfam : ∀ b ∈ (dev i).imports, (dev b).summary ∈ family dev i :=
      fun b hb => List.mem_cons_of_mem _ (List.mem_map_of_mem hb)
    have hc : Compatible K (dev b).summary := by
      intro k hk d hd hkd
      obtain ⟨b', hb', hk'⟩ := hm k hk
      exact h.compatible _ (hfam b' hb') _ (hfam b hb) k hk' d hd hkd
    have hK' : Checks Env.empty (join K (dev b).summary) :=
      (ih b hb).joined hK (Env.Le.empty _) hc
    have hm' : ∀ k ∈ join K (dev b).summary, ∃ b ∈ (dev i).imports, k ∈ (dev b).summary := by
      intro k hk
      rcases mem_join hk with hk | hk
      · exact hm k hk
      · exact ⟨b, hb, hk⟩
    obtain ⟨r1, r2, r3, r4⟩ := importsJoin_inv dev i h ih bs (join K (dev b).summary)
      (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) hK' hm'
    refine ⟨r1, r2, fun d hd => r3 d (List.mem_append_left _ hd), ?_⟩
    intro b' hb' d hd
    rcases List.mem_cons.mp hb' with rfl | hb'
    · obtain ⟨d', hd', hs⟩ := stores_of_join hc hd
      exact ⟨d', r3 d' hd', hs⟩
    · exact r4 b' hb' d hd

/-- **The local checks suffice** (the theorem of modular checking):
if every module up to `i` passes its local checks, then module `i`'s
summary is a checked list of declarations, and the module's own
environment refines the environment the summary builds. -/
theorem local_checks (dev : Nat → Module) :
    ∀ i, (∀ j ≤ i, LocalOk dev j) →
      Checks Env.empty (dev i).summary ∧ (dev i).own.Le (dev i).world := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ihi =>
  intro hall
  have h := hall i (Nat.le_refl i)
  have ihb : ∀ b ∈ (dev i).imports, Checks Env.empty (dev b).summary ∧
      (dev b).own.Le (dev b).world := fun b hb =>
    ihi b (h.below b hb) fun j hj => hall j (Nat.le_trans hj (Nat.le_of_lt (h.below b hb)))
  obtain ⟨hK, hKm, -, hKs⟩ := importsJoin_inv dev i h (fun b hb => (ihb b hb).1)
    (dev i).imports [] (fun _ hb => hb) .nil (fun _ hk => by cases hk)
  have hK' : Checks Env.empty (importsJoin dev (dev i).imports) := hK
  -- every import's own environment refines the joined imports
  have hoff : ∀ b ∈ (dev i).imports,
      (dev b).own.Le (applyAll (importsJoin dev (dev i).imports) Env.empty) := fun b hb =>
    (ihb b hb).2.trans (hK'.le_of_stores fun d hd => hKs b hb d hd)
  -- the base refines the joined imports
  have hbase : (dev i).base.Le (applyAll (importsJoin dev (dev i).imports) Env.empty) := by
    rw [Env.Le.iff]
    intro n ci hf
    obtain ⟨b, hb, ci', hci', hle⟩ := h.base_le n ci hf
    obtain ⟨ci'', h'', hle'⟩ := Env.Le.iff.mp (hoff b hb) n ci' hci'
    exact ⟨ci'', h'', hle.trans hle'⟩
  have hc : Compatible (importsJoin dev (dev i).imports) (dev i).decls := by
    intro k hk d hd hkd
    obtain ⟨b, hb, hk'⟩ := hKm k hk
    exact h.compatible _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hb)) _ (List.mem_cons_self ..)
      k hk' d hd hkd
  have hS : Checks Env.empty (dev i).summary := by
    rw [h.summary_eq]; exact h.checks.joined hK' hbase hc
  have hsub : (applyAll (importsJoin dev (dev i).imports) Env.empty).Le (dev i).world := by
    rw [Module.world]
    exact hS.le_of_stores fun d hd => ⟨d, by rw [h.summary_eq]; exact List.mem_append_left _ hd, rfl⟩
  have hown : (dev i).own.Le (dev i).world := by
    intro n e hf
    rcases find?_applyAll hf with ⟨d, hd, hl⟩ | hl
    · obtain ⟨d', hd', hs⟩ := stores_of_join hc hd
      left
      rw [Module.world]
      rw [h.summary_eq] at hS ⊢
      exact hS.find?_of_lookup hd' (by rw [hs]; exact hl)
    · exact (hbase.trans hsub) n e hl
  exact ⟨hS, hown⟩

/-- **The environment a module rests on is accepted**, declaration
by declaration. -/
theorem local_accepted (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, LocalOk dev j) :
    Accepted (dev i).world :=
  (local_checks dev i h).1.accepted .empty

end Checking

section Corollaries

variable [LevelOracle]

open SetLib IndLib

universe u

variable (V : Type u) [IndLib V]

include V in
/-- **The environment a module rests on has a model.** -/
theorem local_model (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, LocalOk dev j) :
    Nonempty (BlockModel V (dev i).world) :=
  accepted_model V (local_accepted dev i h)

include V in
/-- **No closed term of a module inhabits an empty proposition**: in
the environment the module's declarations were checked in — its base
with its declarations — no closed term has the type of an empty
proposition it stores. -/
theorem local_no_empty_prop_inhabitant (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, LocalOk dev j)
    {name recName elim : Name}
    (hrec : (dev i).own.find? recName = some (IndSpec.falseSpec name recName elim).recInfo)
    (e : Expr) : ¬ Infer (dev i).own [] e (.const name []) := by
  intro he
  have hle := (local_checks dev i h).2
  have hrec' := hle.find_of_ne hrec (by simp [IndSpec.recInfo])
  exact no_empty_prop_inhabitant V (local_accepted dev i h) hrec' e (Infer.mono hle he)

end Corollaries

end Fragment
