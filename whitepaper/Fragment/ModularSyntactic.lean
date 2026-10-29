module

public import Fragment.ModularSemantics

@[expose] public section

/-!
# A syntactic instance of the modular interface

The interface of `ModularSemantics.lean` asks nothing of models but
what the modular argument needs.  This file instantiates it with
realisations in a type system with constants (`SubstSystem`) in which
closed terms of a fixed ground theory realise environments.  It
illustrates the interface; it does not show that a syntactic
consistency proof of Lean fits it.  The interface gives every proof one
shared value (`proofVal`), which suits set models but not a syntactic
proof, where proofs of different propositions are different terms; and
this instance handles definitions only (see the end of this comment).
Whether the interface suits another real consistency proof is open
until there is such a proof to connect it to.

* **a model** of an environment (`Real`) is a **realisation**: a
  ground term for every constant, of the realised type, equal to the
  realised value of a definition; a name's value is its term;
* **the step** realises a new definition by its realised value, which
  has the realised type by the system's **substitution lemma**
  (`SubstSystem.der_subst`): a derivation over an environment stays a
  derivation when a realisation of the environment is substituted in;
* **amalgamation** is the union of realisations that agree on every
  name of the assembled environment that two of them store.

Declarations are definitions only: no axioms, no inductive types, and
none is flagged a proof.  An axiom has no realised value, and the step
must extend every realisation, so axioms are not conservative here
either.
-/

namespace Fragment.Syntactic

universe u

/-- **A type system with constants**, over names `N`: terms, constants
among them, simultaneous substitution of terms for constants, what a
term mentions, typing of ground terms (`HasTy`, the ground theory) and
typing over an environment of typed constants (`Der`), with the
substitution lemma relating the two. -/
structure SubstSystem (N : Type u) where
  Tm : Type u
  const : N → Tm
  subst : (N → Tm) → Tm → Tm
  Mentions : Tm → N → Prop
  subst_congr : ∀ {σ τ t}, (∀ c, Mentions t c → σ c = τ c) → subst σ t = subst τ t
  /-- ground typing: the ground theory -/
  HasTy : Tm → Tm → Prop
  /-- typing over an environment: each constant's type and, for a
  definition, its value -/
  Der : (N → Option (Tm × Option Tm)) → Tm → Tm → Prop
  der_scoped : ∀ {Γ t A}, Der Γ t A →
    (∀ c, Mentions t c → (Γ c).isSome) ∧ ∀ c, Mentions A c → (Γ c).isSome
  /-- **the substitution lemma** -/
  der_subst : ∀ {Γ t A} {σ : N → Tm}, Der Γ t A →
    (∀ c B v, Γ c = some (B, v) → HasTy (σ c) (subst σ B) ∧ ∀ s, v = some s → σ c = subst σ s) →
    HasTy (subst σ t) (subst σ A)

variable {N : Type u} {T : SubstSystem N}

open Classical

/-! ## Environments and realisations -/

/-- An entry: a type and, for a definition, a value. -/
abbrev Entry (T : SubstSystem N) := T.Tm × Option T.Tm

/-- **A scoped environment** of typed constants: what an entry
mentions is stored. -/
def Scoped (E : N → Option (Entry T)) : Prop :=
  ∀ c A v, E c = some (A, v) →
    (∀ d, T.Mentions A d → (E d).isSome) ∧ ∀ t, v = some t → ∀ d, T.Mentions t d → (E d).isSome

/-- Environments: scoped maps from names to entries. -/
abbrev SEnv (T : SubstSystem N) := { E : N → Option (Entry T) // Scoped E }

/-- **σ realises `E`**: every constant's realisation has the realised
type, and a definition's is its realised value. -/
def Realises (σ : N → T.Tm) (E : N → Option (Entry T)) : Prop :=
  ∀ c A v, E c = some (A, v) → T.HasTy (σ c) (T.subst σ A) ∧ ∀ t, v = some t → σ c = T.subst σ t

/-- **A model of an environment**: a realisation. -/
structure Real (T : SubstSystem N) (E : SEnv T) where
  σ : N → T.Tm
  real : Realises σ E.1

/-- Two realisations agreeing on what a term mentions substitute it
alike. -/
theorem realises_congr {E : N → Option (Entry T)} (hE : Scoped E) {σ τ : N → T.Tm}
    (he : ∀ c, (E c).isSome → σ c = τ c) (h : Realises σ E) : Realises τ E := by
  intro c A v hc
  obtain ⟨h1, h2⟩ := h c A v hc
  have hA : T.subst σ A = T.subst τ A :=
    T.subst_congr fun d hd => he d ((hE c A v hc).1 d hd)
  refine ⟨by rw [← he c (by rw [hc]; rfl), ← hA]; exact h1, fun t ht => ?_⟩
  rw [← he c (by rw [hc]; rfl), h2 t ht]
  exact T.subst_congr fun d hd => he d ((hE c A v hc).2 t ht d hd)

/-! ## Acceptance and the step -/

/-- The environment with a definition added. -/
noncomputable def addDef (Γ : SEnv T) (c : N) (A t : T.Tm) (hd : T.Der Γ.1 t A) : SEnv T :=
  ⟨fun d => if d = c then some (A, some t) else Γ.1 d, by
    intro d B v hd'
    have hsub : ∀ e, (Γ.1 e).isSome → ((if e = c then some (A, some t) else Γ.1 e).isSome) :=
      fun e he => by by_cases h : e = c <;> simp [h, he]
    by_cases h : d = c
    · simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨rfl, rfl⟩ := hd'
      exact ⟨fun e he => hsub e ((T.der_scoped hd).2 e he),
        fun s hs e he => by cases hs; exact hsub e ((T.der_scoped hd).1 e he)⟩
    · simp only [h, ↓reduceIte] at hd'
      exact ⟨fun e he => hsub e ((Γ.2 d B v hd').1 e he),
        fun s hs e he => hsub e ((Γ.2 d B v hd').2 s hs e he)⟩⟩

/-- **Acceptance**: definitions, each of a fresh name, its value of its
type over the environment so far. -/
inductive Accepts : SEnv T → List (N × T.Tm × T.Tm) → SEnv T → Prop
  | nil {Γ : SEnv T} : Accepts Γ [] Γ
  | cons {Γ Γ' : SEnv T} {c : N} {A t : T.Tm} {D : List (N × T.Tm × T.Tm)}
      (hc : Γ.1 c = none) (hd : T.Der Γ.1 t A) :
      Accepts (addDef Γ c A t hd) D Γ' → Accepts Γ ((c, A, t) :: D) Γ'

/-- **The step for one definition**: realised by its realised value,
by the substitution lemma. -/
theorem addDef_step {Γ : SEnv T} {c : N} {A t : T.Tm} {hd : T.Der Γ.1 t A} (hc : Γ.1 c = none)
    (m : Real T Γ) : ∃ m' : Real T (addDef Γ c A t hd), ∀ d, (Γ.1 d).isSome → m'.σ d = m.σ d := by
  have hval := T.der_subst hd m.real
  let σ' : N → T.Tm := fun d => if d = c then T.subst m.σ t else m.σ d
  have hold : ∀ d, (Γ.1 d).isSome → σ' d = m.σ d := fun d hd' => by
    have : d ≠ c := fun h => by rw [h, hc] at hd'; cases hd'
    simp [σ', this]
  have hA : T.subst σ' A = T.subst m.σ A :=
    T.subst_congr fun d h => hold d ((T.der_scoped hd).2 d h)
  have ht : T.subst σ' t = T.subst m.σ t :=
    T.subst_congr fun d h => hold d ((T.der_scoped hd).1 d h)
  refine ⟨{ σ := σ', real := ?_ }, hold⟩
  intro d B v hd'
  by_cases h : d = c
  · subst h
    simp only [addDef, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl⟩ := hd'
    refine ⟨by simp only [σ', ↓reduceIte, hA]; exact hval, fun s hs => ?_⟩
    cases hs
    simp only [σ', ↓reduceIte, ht]
  · have hΓ : Γ.1 d = some (B, v) := by simpa [addDef, h] using hd'
    exact realises_congr Γ.2 (fun e he => (hold e he).symm) m.real d B v hΓ

theorem Accepts.step {Γ Γ' : SEnv T} {D : List (N × T.Tm × T.Tm)} (h : Accepts Γ D Γ')
    (m : Real T Γ) : ∃ m' : Real T Γ', ∀ d, (Γ.1 d).isSome → m'.σ d = m.σ d := by
  induction h with
  | nil => exact ⟨m, fun _ _ => rfl⟩
  | @cons Γ Γ' c A t D hc hd _ ih =>
    obtain ⟨m₁, hm₁⟩ := addDef_step (hd := hd) hc m
    obtain ⟨m', hm'⟩ := ih m₁
    refine ⟨m', fun d hd' => ?_⟩
    have hs : ((addDef Γ c A t hd).1 d).isSome := by
      have : d ≠ c := fun h => by rw [h, hc] at hd'; cases hd'
      simpa [addDef, this] using hd'
    rw [hm' d hs, hm₁ d hd']

/-! ## Assembly and amalgamation -/

/-- **`C` is assembled from the family `E`**: every entry of `C` is, at
the same name, the entry of a member, its value kept or left out. -/
def Assembled (C : SEnv T) {ι : Type u} (E : ι → SEnv T) : Prop :=
  ∀ c A v, C.1 c = some (A, v) → ∃ i,
    ∃ v', (E i).1 c = some (A, v') ∧ ∀ t, v = some t → v' = some t

/-- **Amalgamation**: the union of realisations that agree on every name
of `C` two members store. -/
theorem amalgamate {C : SEnv T} {ι : Type u} {E : ι → SEnv T}
    (h : Assembled C E) (m : (i : ι) → Real T (E i))
    (hcomp : ∀ c i i', (C.1 c).isSome → ((E i).1 c).isSome →
      ((E i').1 c).isSome → some ((m i).σ c) = some ((m i').σ c)) :
    ∃ mC : Real T C, ∀ c i, (C.1 c).isSome → ((E i).1 c).isSome →
      some (mC.σ c) = some ((m i).σ c) := by
  let σ : N → T.Tm := fun c =>
    if hx : ∃ i, ((E i).1 c).isSome then (m (Classical.choose hx)).σ c else T.const c
  have hag : ∀ c i, (C.1 c).isSome → ((E i).1 c).isSome → σ c = (m i).σ c := by
    intro c i hC hE
    have hx : ∃ i, ((E i).1 c).isSome := ⟨i, hE⟩
    simp only [σ, dite_eq_left hx]
    exact Option.some.inj (hcomp c _ i hC (Classical.choose_spec hx) hE)
  have hreal : Realises σ C.1 := by
    intro c A v hc
    obtain ⟨i, v', hE, hv⟩ := h c A v hc
    have hCs : (C.1 c).isSome := by rw [hc]; rfl
    have hEs : ((E i).1 c).isSome := by rw [hE]; rfl
    obtain ⟨r1, r2⟩ := (m i).real c A v' hE
    have hsub : ∀ t, (∀ d, T.Mentions t d → (C.1 d).isSome ∧ ((E i).1 d).isSome) →
        T.subst σ t = T.subst (m i).σ t := fun t ht =>
      T.subst_congr fun d hd => hag d i (ht d hd).1 (ht d hd).2
    refine ⟨?_, fun t ht => ?_⟩
    · rw [hag c i hCs hEs, hsub A fun d hd =>
        ⟨(C.2 c A v hc).1 d hd, ((E i).2 c A v' hE).1 d hd⟩]
      exact r1
    · rw [hag c i hCs hEs, hsub t fun d hd =>
        ⟨(C.2 c A v hc).2 t ht d hd, ((E i).2 c A v' hE).2 t (hv t ht) d hd⟩]
      exact r2 t (hv t ht)
  exact ⟨{ σ := σ, real := hreal }, fun c i hC hE => congrArg some (hag c i hC hE)⟩

/-! ## The instance -/

variable (T) in
/-- **A syntactic consistency proof as a modular semantics.** -/
noncomputable def syntacticSemantics : ModularSemantics.{u, u} where
  Env := SEnv T
  Name := N
  Stores E c := (E.1 c).isSome = true
  Mod := Real T
  Val := Option T.Tm
  val m c := some (m.σ c)
  proofVal := none
  Assembled C _ E := Assembled C E
  assembled_src h c hc := by
    obtain ⟨⟨A, v⟩, hA⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨i, v', hE, -⟩ := h c A v hA
    exact ⟨i, by rw [hE]; rfl⟩
  amalgamate h m hc := by
    obtain ⟨mC, hmC⟩ := amalgamate h m fun c i i' => hc i i' c
    exact ⟨mC, fun i c hc _ hs => hmC c i hc hs⟩
  Decls := List (N × T.Tm × T.Tm)
  Flagged _ _ := False
  Accepts := Accepts
  step h m := by
    obtain ⟨m', hm'⟩ := h.step m
    exact ⟨m', fun c hc => by rw [hm' c hc], fun _ h => h.elim⟩

end Fragment.Syntactic
