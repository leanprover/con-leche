module

public import Fragment.Consistency

@[expose] public section

/-!
# Modular checking

A development is a collection of **modules**, each a list of
declarations checked against what its imports export rather than
against everything before it.  What a module exports may hide
definitions' values: an importing module sees such a definition as an
**assumption**, a constant with its type and no value
(`ConstKind.assumed`).  So a module is checked against an
**interface**: an environment each of whose constants is stored in the
union of the modules before it, as it is there or with its value
hidden (`Env.Le`).

The soundness argument is **monotonicity**: checking against more
constants, or against a definition where the interface had an
assumption, accepts everything checking against the interface accepts
(`Red.mono` … `Infer.mono`, `Checks.mono`).  An assumption is used
only through its type, and the definition has the same type; a
definition adds the δ step, never removes one.  So a module accepted
against its interface is accepted against the union before it, the
union of all modules is an environment the checker accepts declaration
by declaration (`Modular.accepted`), and the consistency corollary of
`Consistency.lean` applies to it (`modular_model`,
`modular_no_empty_prop_inhabitant`).

Each module's check reads its interface and nothing else, so modules
none of which imports another are checked independently: the
hypotheses of `Modular.step` for two modules mention only their own
interfaces.

What is assumed of the bookkeeping that assembles the union: every name
is declared by one module (`Modular.step`'s freshness premise); and
each interface is related to the union before its module by `Env.Le`.
-/

namespace Fragment

/-! ## Hiding a value -/

/-- A definition seen without its value: an assumption of the same
type; every other constant as it is. -/
def ConstInfo.hide (ci : ConstInfo) : ConstInfo :=
  match ci.kind with
  | .defn _ => { ci with kind := .assumed }
  | _ => ci

/-- **The exported view** of an environment: the definitions `H`
selects seen as assumptions. -/
def Env.hide (H : Name → Bool) (env : Env) : Env :=
  ⟨env.consts.map fun p => if H p.1 then (p.1, p.2.hide) else p⟩

/-- **An interface of an environment**: each of its constants is
stored there, as it is, or — where the interface has an assumption —
with the same level parameters and type and some kind. -/
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

/-- The lookup in the exported view: the stored constant, hidden where
`H` selects it. -/
theorem Env.find?_hide (H : Name → Bool) (E : Env) (n : Name) :
    (E.hide H).find? n = (E.find? n).map fun ci => if H n then ci.hide else ci := by
  obtain ⟨cs⟩ := E
  induction cs with
  | nil => rfl
  | cons p cs ih =>
    obtain ⟨m, cm⟩ := p
    have ih' : List.lookup n (cs.map fun p => if H p.1 then (p.1, p.2.hide) else p) =
        (List.lookup n cs).map fun ci => if H n then ci.hide else ci := ih
    show List.lookup n ((if H m then (m, cm.hide) else (m, cm)) ::
        cs.map fun p => if H p.1 then (p.1, p.2.hide) else p) =
      (List.lookup n ((m, cm) :: cs)).map fun ci => if H n then ci.hide else ci
    by_cases hnm : n = m
    · subst hnm
      have hb : (n == n) = true := beq_self_eq_true n
      by_cases hH : H n
      · simp only [hH, ite_true, List.lookup, hb, Option.map_some]
      · simp only [hH, Bool.false_eq_true, ite_false, List.lookup, hb, Option.map_some]
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      by_cases hH : H m
      · simp only [hH, ite_true, List.lookup, hb]
        exact ih'
      · simp only [hH, Bool.false_eq_true, ite_false, List.lookup, hb]
        exact ih'


namespace Env.Le

/-- An environment is an interface of itself with any values hidden. -/
theorem hide (H : Name → Bool) (E : Env) : (E.hide H).Le E := by
  intro n ci hf
  rw [Env.find?_hide] at hf
  obtain ⟨cm, hcm, rfl⟩ := Option.map_eq_some_iff.mp hf
  by_cases hH : H n
  · simp only [hH, ite_true]
    unfold ConstInfo.hide
    split
    · exact .inr ⟨rfl, cm.kind, hcm⟩
    · exact .inl hcm
  · simp only [hH]
    exact .inl hcm

end Env.Le

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

/-- **A declaration** of a module: a definition or an inductive block. -/
inductive Decl where
  | defn (c : Name) (ci : ConstInfo)
  | ind (S : IndSpec)

namespace Decl

/-- What the declaration stores. -/
def apply : Decl → Env → Env
  | defn c ci, E => E.add c ci
  | ind S, E => S.install E

/-- The check the declaration passes (`Decl.lean`). -/
def Ok (E : Env) : Decl → Prop
  | defn c ci => DefOk E c ci
  | ind S => IndOk E S

/-- The names the declaration stores. -/
def names : Decl → List Name
  | defn c _ => [c]
  | ind S => S.names

/-- The entries the declaration stores, whatever the environment. -/
def stores (d : Decl) : List (Name × ConstInfo) := (d.apply Env.empty).consts

omit [LevelOracle] in
theorem apply_eq (d : Decl) (E : Env) : d.apply E = ⟨d.stores ++ E.consts⟩ := by
  cases d with
  | defn c ci => rfl
  | ind S =>
    show S.install E = ⟨(S.install Env.empty).consts ++ E.consts⟩
    rw [← IndSpec.install_consts]

/-- An accepted declaration's names are fresh. -/
theorem Ok.fresh {E : Env} {d : Decl} (h : d.Ok E) : ∀ n ∈ d.names, E.find? n = none := by
  cases d with
  | defn c ci => intro n hn; simp only [names, List.mem_singleton] at hn; subst hn; exact h.1
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
    | ind S => exact .ind S hE hd

/-- **The union of modules checked against their interfaces**: each
module's declarations check against an interface of the union of the
modules before it (`Env.Le`: its constants stored in the union, as
they are there or as assumptions of the same type), and its names are
fresh in that union. -/
inductive Modular : Env → Prop
  | empty : Modular Env.empty
  | step {U I : Env} {ds : List Decl} : Modular U → I.Le U → Checks I ds →
      (∀ d ∈ ds, ∀ n ∈ d.names, U.find? n = none) → Modular (applyAll ds U)

/-- **The union is an accepted environment**: every module's check
against its interface is a check against the union before it. -/
theorem Modular.accepted {U : Env} (h : Modular U) : Accepted U := by
  induction h with
  | empty => exact .empty
  | step _ hI hc hf ih => exact (hc.mono hI hf).accepted ih

end Checking

section Corollaries

variable [LevelOracle]

open SetLib IndLib

universe u

variable (V : Type u) [IndLib V]

include V in
/-- **The union of the modules has a model.** -/
theorem modular_model {U : Env} (h : Modular U) : Nonempty (BlockModel V U) :=
  accepted_model V h.accepted

include V in
/-- **No closed term in the union inhabits an empty proposition.** -/
theorem modular_no_empty_prop_inhabitant {U : Env} (h : Modular U) {name recName elim : Name}
    (hrec : U.find? recName = some (IndSpec.falseSpec name recName elim).recInfo) (e : Expr) :
    ¬ Infer U [] e (.const name []) :=
  no_empty_prop_inhabitant V h.accepted hrec e

end Corollaries

end Fragment
