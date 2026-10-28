module

public import Fragment.ModularSemantics

@[expose] public section

/-!
# A syntactic consistency proof as a modular semantics

The interface of `ModularSemantics.lean` asks nothing of models but
what the gluing needs, so a proof by syntax plugs in as well as the
fragment's set-theoretic one.  This file is such an instance, for any
type system with constants (`SubstSystem`) in which closed terms of a
fixed ground theory realise environments:

* **a model** of an environment (`Real`) is a **realisation**: a
  ground term for every constant, of the realised type, equal to the
  realised value of a definition;
* **restriction** reads the realisation through the renaming;
* **the step** realises a new definition by its realised value, which
  has the realised type by the system's **substitution lemma**
  (`SubstSystem.der_subst`): a derivation over an environment stays a
  derivation when a realisation of the environment is substituted in;
* **amalgamation** is the union of two realisations that agree on the
  context;
* **the base** is the empty environment.

Declarations are definitions only: an axiom has no realised value,
and the step must extend every realisation, so axioms are not
conservative here either.
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
  subst_const : ∀ σ c, subst σ (const c) = σ c
  subst_id : ∀ t, subst const t = t
  subst_subst : ∀ σ τ t, subst σ (subst τ t) = subst (fun c => subst σ (τ c)) t
  Mentions : Tm → N → Prop
  subst_congr : ∀ {σ τ t}, (∀ c, Mentions t c → σ c = τ c) → subst σ t = subst τ t
  mentions_subst : ∀ {σ t d}, Mentions (subst σ t) d → ∃ c, Mentions t c ∧ Mentions (σ c) d
  mentions_const : ∀ {c d}, Mentions (const c) d → d = c
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

namespace SubstSystem

/-- Renaming the constants. -/
def rename (T : SubstSystem N) (ρ : N → N) (t : T.Tm) : T.Tm := T.subst (T.const ∘ ρ) t

theorem subst_rename (σ : N → T.Tm) (ρ : N → N) (t : T.Tm) :
    T.subst σ (T.rename ρ t) = T.subst (σ ∘ ρ) t := by
  unfold rename
  rw [T.subst_subst]
  congr 1
  funext c
  exact T.subst_const σ (ρ c)

theorem rename_id (t : T.Tm) : T.rename id t = t := T.subst_id t

theorem rename_rename (ρ σ : N → N) (t : T.Tm) :
    T.rename σ (T.rename ρ t) = T.rename (σ ∘ ρ) t := by
  show T.subst (T.const ∘ σ) (T.rename ρ t) = _
  rw [subst_rename]
  rfl

theorem mentions_rename {ρ : N → N} {t : T.Tm} {d : N} (h : T.Mentions (T.rename ρ t) d) :
    ∃ c, T.Mentions t c ∧ d = ρ c := by
  obtain ⟨c, hc, hd⟩ := T.mentions_subst h
  exact ⟨c, hc, T.mentions_const hd⟩

end SubstSystem

open SubstSystem Classical

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

/-- **A model of an environment**: a realisation, the constant itself
off the environment. -/
structure Real (T : SubstSystem N) (E : SEnv T) where
  σ : N → T.Tm
  off : ∀ c, E.1 c = none → σ c = T.const c
  real : Realises σ E.1

theorem Real.ext {E : SEnv T} {m m' : Real T E} (h : m.σ = m'.σ) : m = m' := by
  cases m; cases m'; cases h; rfl

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

/-! ## Refinement and restriction -/

/-- **Refinement with renaming**: every entry of `Γ`, renamed, is an
entry of `E`, a definition's value kept or the value left out. -/
def Refines (Γ : SEnv T) (ρ : N → N) (E : SEnv T) : Prop :=
  ∀ c A v, Γ.1 c = some (A, v) → ∃ v', E.1 (ρ c) = some (T.rename ρ A, v') ∧
    ∀ t, v = some t → v' = some (T.rename ρ t)

theorem Refines.isSome {Γ E : SEnv T} {ρ : N → N} (h : Refines Γ ρ E) {c : N}
    (hc : (Γ.1 c).isSome) : (E.1 (ρ c)).isSome := by
  obtain ⟨⟨A, v⟩, hA⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨v', h', -⟩ := h c A v hA
  rw [h']; rfl

theorem refines_id (E : SEnv T) : Refines E id E := fun c A v hc =>
  ⟨v, by rw [rename_id]; exact hc, fun t ht => by rw [rename_id, ht]⟩

theorem refines_comp {Γ E F : SEnv T} {ρ σ : N → N} (h₁ : Refines Γ ρ E) (h₂ : Refines E σ F) :
    Refines Γ (σ ∘ ρ) F := by
  intro c A v hc
  obtain ⟨v₁, h1, e1⟩ := h₁ c A v hc
  obtain ⟨v₂, h2, e2⟩ := h₂ _ _ _ h1
  refine ⟨v₂, by rw [← rename_rename]; exact h2, fun t ht => ?_⟩
  rw [e2 _ (e1 t ht), rename_rename]

open Classical in
/-- **Restriction**: the realisation read through the renaming. -/
noncomputable def restrict {Γ E : SEnv T} {ρ : N → N} (h : Refines Γ ρ E) (m : Real T E) :
    Real T Γ where
  σ c := if (Γ.1 c).isSome then m.σ (ρ c) else T.const c
  off c hc := by simp [hc]
  real := by
    refine realises_congr Γ.2 (σ := m.σ ∘ ρ) (fun c hc => by simp [hc]) ?_
    intro c A v hc
    obtain ⟨v', h', e'⟩ := h c A v hc
    obtain ⟨r1, r2⟩ := m.real _ _ _ h'
    refine ⟨by rw [← subst_rename]; exact r1, fun t ht => ?_⟩
    rw [Function.comp_apply, r2 _ (e' t ht), subst_rename]

theorem restrict_σ {Γ E : SEnv T} {ρ : N → N} (h : Refines Γ ρ E) (m : Real T E) (c : N)
    (hc : (Γ.1 c).isSome) : (restrict h m).σ c = m.σ (ρ c) := by
  simp [restrict, hc]

theorem restrict_id {E : SEnv T} (m : Real T E) : restrict (refines_id E) m = m := by
  refine Real.ext (funext fun c => ?_)
  by_cases hc : (E.1 c).isSome
  · exact restrict_σ _ m c hc
  · simp [restrict, hc, m.off c (Option.not_isSome_iff_eq_none.mp hc)]

theorem restrict_comp {Γ E F : SEnv T} {ρ σ : N → N} (h₁ : Refines Γ ρ E) (h₂ : Refines E σ F)
    (m : Real T F) : restrict (refines_comp h₁ h₂) m = restrict h₁ (restrict h₂ m) := by
  refine Real.ext (funext fun c => ?_)
  by_cases hc : (Γ.1 c).isSome
  · rw [restrict_σ _ _ c hc, restrict_σ _ _ c hc, restrict_σ _ _ _ (h₁.isSome hc)]; rfl
  · simp [restrict, hc]

/-! ## Acceptance and the step -/

open Classical in
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

theorem addDef_refines {Γ : SEnv T} {c : N} {A t : T.Tm} {hd : T.Der Γ.1 t A} (hc : Γ.1 c = none) :
    Refines Γ id (addDef Γ c A t hd) := by
  intro d B v hd'
  have hne : d ≠ c := fun h => by rw [h, hc] at hd'; cases hd'
  refine ⟨v, ?_, fun s hs => by rw [rename_id, hs]⟩
  show (if d = c then _ else Γ.1 d) = _
  rw [ite_eq_right hne, rename_id, hd']

theorem Accepts.refines {Γ Γ' : SEnv T} {D : List (N × T.Tm × T.Tm)} (h : Accepts Γ D Γ') :
    Refines Γ id Γ' := by
  induction h with
  | nil => exact refines_id _
  | cons hc _ _ ih => exact refines_comp (σ := id) (addDef_refines hc) ih

open Classical in
/-- **The step for one definition**: realised by its realised value,
by the substitution lemma. -/
theorem addDef_step {Γ : SEnv T} {c : N} {A t : T.Tm} {hd : T.Der Γ.1 t A} (hc : Γ.1 c = none)
    (m : Real T Γ) : ∃ m' : Real T (addDef Γ c A t hd), restrict (addDef_refines hc) m' = m := by
  have hval := T.der_subst hd m.real
  let σ' : N → T.Tm := fun d => if d = c then T.subst m.σ t else m.σ d
  have hold : ∀ d, (Γ.1 d).isSome → σ' d = m.σ d := fun d hd' => by
    have : d ≠ c := fun h => by rw [h, hc] at hd'; cases hd'
    simp [σ', this]
  have hA : T.subst σ' A = T.subst m.σ A :=
    T.subst_congr fun d h => hold d ((T.der_scoped hd).2 d h)
  have ht : T.subst σ' t = T.subst m.σ t :=
    T.subst_congr fun d h => hold d ((T.der_scoped hd).1 d h)
  refine ⟨{ σ := σ', off := fun d hd' => ?_, real := ?_ }, Real.ext (funext fun d => ?_)⟩
  · have hne : d ≠ c := fun h => by
      subst h; simp [addDef] at hd'
    have : Γ.1 d = none := by simpa [addDef, hne] using hd'
    simp [σ', hne, m.off d this]
  · intro d B v hd'
    by_cases h : d = c
    · subst h
      simp only [addDef, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨rfl, rfl⟩ := hd'
      refine ⟨by simp only [σ', ↓reduceIte, hA]; exact hval, fun s hs => ?_⟩
      cases hs
      simp only [σ', ↓reduceIte, ht]
    · have hΓ : Γ.1 d = some (B, v) := by simpa [addDef, h] using hd'
      have hs : (Γ.1 d).isSome := by rw [hΓ]; rfl
      exact realises_congr Γ.2 (fun e he => (hold e he).symm) m.real d B v hΓ
  · by_cases hd' : (Γ.1 d).isSome
    · rw [restrict_σ _ _ d hd']; exact hold d hd'
    · simp [restrict, hd', m.off d (Option.not_isSome_iff_eq_none.mp hd')]

theorem Accepts.step {Γ Γ' : SEnv T} {D : List (N × T.Tm × T.Tm)} (h : Accepts Γ D Γ')
    (m : Real T Γ) : ∃ m' : Real T Γ', restrict h.refines m' = m := by
  induction h with
  | nil => exact ⟨m, restrict_id m⟩
  | cons hc _ h' ih =>
    obtain ⟨m₁, hm₁⟩ := addDef_step hc m
    obtain ⟨m', hm'⟩ := ih m₁
    exact ⟨m', (restrict_comp (σ := id) (addDef_refines hc) h'.refines m').trans
      (by rw [hm', hm₁])⟩

/-! ## Amalgamation -/

/-- **Freshness**: the renaming names `Γ'`'s constants apart, and a
constant `Γ'` adds to `Γ` is renamed off `W`. -/
def Fresh (W : SEnv T) (ρ : N → N) (Γ Γ' : SEnv T) : Prop :=
  (∀ c c', (Γ'.1 c).isSome → (Γ'.1 c').isSome → ρ c = ρ c' → c = c') ∧
    ∀ c, (Γ'.1 c).isSome → Γ.1 c = none → W.1 (ρ c) = none

open Classical in
/-- `W` with `Γ'`'s entries added, renamed. -/
noncomputable def glueRaw (W : SEnv T) (ρ : N → N) (Γ' : SEnv T) : N → Option (Entry T) :=
  fun d => match W.1 d with
    | some e => some e
    | none =>
      if h : ∃ c, (Γ'.1 c).isSome ∧ ρ c = d then
        (Γ'.1 (Classical.choose h)).map fun e => (T.rename ρ e.1, e.2.map (T.rename ρ))
      else none

open Classical in
/-- **The glued environment** (`W` itself when the union is not scoped,
which acceptance and freshness exclude). -/
noncomputable def glue (W : SEnv T) (ρ : N → N) (Γ' : SEnv T) : SEnv T :=
  if h : Scoped (glueRaw W ρ Γ') then ⟨_, h⟩ else W

theorem glueRaw_left {W Γ' : SEnv T} {ρ : N → N} {d : N} {e : Entry T} (h : W.1 d = some e) :
    glueRaw W ρ Γ' d = some e := by
  simp [glueRaw, h]

theorem glue_left {W Γ' : SEnv T} {ρ : N → N} : Refines W id (glue W ρ Γ') := by
  unfold glue
  split
  · intro c A v hc
    exact ⟨v, by rw [rename_id]; exact glueRaw_left hc, fun t ht => by rw [rename_id, ht]⟩
  · exact refines_id W

theorem Accepts.keep {Γ Γ' : SEnv T} {D : List (N × T.Tm × T.Tm)} (h : Accepts Γ D Γ') :
    ∀ {c e}, Γ.1 c = some e → Γ'.1 c = some e := by
  induction h with
  | nil => exact fun h => h
  | @cons Γ Γ' c A t D hc hd _ ih =>
    intro d e he
    apply ih
    have hne : d ≠ c := fun h => by rw [h, hc] at he; cases he
    show (if d = c then _ else Γ.1 d) = _
    rw [ite_eq_right hne, he]

/-- What the glued environment stores at a renamed constant of `Γ'`. -/
theorem glueRaw_right {Γ Γ' W : SEnv T} {ρ : N → N} (r : Refines Γ ρ W)
    (hkeep : ∀ c e, Γ.1 c = some e → Γ'.1 c = some e)
    (f : Fresh W ρ Γ Γ') {c : N} {A : T.Tm} {v : Option T.Tm} (hc : Γ'.1 c = some (A, v)) :
    ∃ v', glueRaw W ρ Γ' (ρ c) = some (T.rename ρ A, v') ∧
      ∀ t, v = some t → v' = some (T.rename ρ t) := by
  have hs : (Γ'.1 c).isSome := by rw [hc]; rfl
  cases hΓ : Γ.1 c with
  | some e =>
    have he := hkeep c e hΓ
    rw [hc] at he
    obtain rfl := Option.some.inj he
    obtain ⟨v', h', e'⟩ := r c A v hΓ
    exact ⟨v', glueRaw_left h', e'⟩
  | none =>
    have hW := f.2 c hs hΓ
    have hex : ∃ c', (Γ'.1 c').isSome ∧ ρ c' = ρ c := ⟨c, hs, rfl⟩
    have hch : Classical.choose hex = c :=
      f.1 _ _ (Classical.choose_spec hex).1 hs (Classical.choose_spec hex).2
    refine ⟨v.map (T.rename ρ), ?_, fun t ht => by rw [ht]; rfl⟩
    simp only [glueRaw, hW, dite_eq_left hex, hch, hc, Option.map_some]

/-- What the glued environment stores comes from `W` or, renamed, from
`Γ'`. -/
theorem glueRaw_cases {W Γ' : SEnv T} {ρ : N → N} {d : N} {e : Entry T}
    (h : glueRaw W ρ Γ' d = some e) :
    W.1 d = some e ∨ ∃ c A v, Γ'.1 c = some (A, v) ∧ ρ c = d ∧ W.1 d = none ∧
      e = (T.rename ρ A, v.map (T.rename ρ)) := by
  unfold glueRaw at h
  split at h
  · rename_i e' he'; exact .inl (by rw [he']; exact h)
  · rename_i hW
    split at h
    · rename_i hex
      obtain ⟨h1, h2⟩ := Classical.choose_spec hex
      cases hc : Γ'.1 (Classical.choose hex) with
      | none => rw [hc] at h; cases h
      | some e' =>
        rw [hc] at h
        obtain ⟨A, v⟩ := e'
        exact .inr ⟨_, A, v, hc, h2, hW, (Option.some.inj h).symm⟩
    · cases h

/-- **The union is scoped**, under refinement, acceptance and
freshness. -/
theorem glueRaw_scoped {Γ Γ' W : SEnv T} {ρ : N → N} (r : Refines Γ ρ W)
    (hkeep : ∀ c e, Γ.1 c = some e → Γ'.1 c = some e) (f : Fresh W ρ Γ Γ') :
    Scoped (glueRaw W ρ Γ') := by
  have hstore : ∀ c, (Γ'.1 c).isSome → (glueRaw W ρ Γ' (ρ c)).isSome := by
    intro c hc
    obtain ⟨⟨A, v⟩, hA⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨v', h', -⟩ := glueRaw_right r hkeep f hA
    rw [h']; rfl
  have hW : ∀ d, (W.1 d).isSome → (glueRaw W ρ Γ' d).isSome := by
    intro d hd
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
    rw [glueRaw_left he]; rfl
  have hren : ∀ t, (∀ d, T.Mentions t d → (Γ'.1 d).isSome) →
      ∀ d, T.Mentions (T.rename ρ t) d → (glueRaw W ρ Γ' d).isSome := by
    intro t ht d hd
    obtain ⟨d', hd', rfl⟩ := mentions_rename hd
    exact hstore d' (ht d' hd')
  intro d B w hd
  rcases glueRaw_cases hd with hd | ⟨c, A, v, hc, rfl, -, he⟩
  · exact ⟨fun e he => hW e ((W.2 d B w hd).1 e he),
      fun t ht e he => hW e ((W.2 d B w hd).2 t ht e he)⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨hren A (Γ'.2 c A v hc).1, fun t ht => ?_⟩
    cases v with
    | none => cases ht
    | some s =>
      simp only [Option.map_some, Option.some.injEq] at ht
      subst ht
      exact hren s ((Γ'.2 c A (some s) hc).2 s rfl)

theorem glue_eq {Γ Γ' W : SEnv T} {ρ : N → N} (r : Refines Γ ρ W)
    (hkeep : ∀ c e, Γ.1 c = some e → Γ'.1 c = some e) (f : Fresh W ρ Γ Γ') :
    (glue W ρ Γ').1 = glueRaw W ρ Γ' := by
  unfold glue
  rw [dite_eq_left (glueRaw_scoped r hkeep f)]

theorem glue_right {Γ Γ' W : SEnv T} {D : List (N × T.Tm × T.Tm)} {ρ : N → N} (r : Refines Γ ρ W)
    (a : Accepts Γ D Γ') (f : Fresh W ρ Γ Γ') : Refines Γ' ρ (glue W ρ Γ') := by
  intro c A v hc
  rw [glue_eq r (fun _ _ h => a.keep h) f]
  exact glueRaw_right r (fun _ _ h => a.keep h) f hc

open Classical in
/-- **Amalgamation**: the union of the two realisations. -/
theorem amalgamate {Γ Γ' W : SEnv T} {D : List (N × T.Tm × T.Tm)} {ρ : N → N}
    (r : Refines Γ ρ W) (a : Accepts Γ D Γ') (f : Fresh W ρ Γ Γ') (mW : Real T W)
    (m' : Real T Γ') (he : restrict r mW = restrict a.refines m') :
    ∃ m'' : Real T (glue W ρ Γ'), restrict glue_left m'' = mW ∧
      restrict (glue_right r a f) m'' = m' := by
  have hkeep : ∀ c e, Γ.1 c = some e → Γ'.1 c = some e := fun _ _ h => a.keep h
  have hG := glue_eq r hkeep f
  have hctx : ∀ c, (Γ.1 c).isSome → mW.σ (ρ c) = m'.σ c := by
    intro c hc
    have := congrFun (congrArg Real.σ he) c
    rwa [restrict_σ _ _ c hc, restrict_σ _ _ c hc] at this
  let σ'' : N → T.Tm := fun d =>
    if (W.1 d).isSome then mW.σ d
    else if hk : ∃ c, (Γ'.1 c).isSome ∧ ρ c = d then m'.σ (Classical.choose hk) else T.const d
  have hold : ∀ d, (W.1 d).isSome → σ'' d = mW.σ d := fun d hd => by simp [σ'', hd]
  have hat : ∀ c, (Γ'.1 c).isSome → σ'' (ρ c) = m'.σ c := by
    intro c hc
    by_cases hW : (W.1 (ρ c)).isSome
    · rw [hold _ hW]
      cases hΓ : Γ.1 c with
      | some e => exact hctx c (by rw [hΓ]; rfl)
      | none =>
        have := f.2 c hc hΓ
        rw [this] at hW; cases hW
    · have hex : ∃ c', (Γ'.1 c').isSome ∧ ρ c' = ρ c := ⟨c, hc, rfl⟩
      simp only [σ'', hW, Bool.false_eq_true, ↓reduceIte, dite_eq_left hex]
      rw [f.1 _ _ (Classical.choose_spec hex).1 hc (Classical.choose_spec hex).2]
  have hreal : Realises σ'' (glueRaw W ρ Γ') := by
    intro d B w hd
    rcases glueRaw_cases hd with hd | ⟨c, A, v, hc, rfl, -, he⟩
    · exact realises_congr W.2 (σ := mW.σ) (fun e he => (hold e he).symm) mW.real d B w hd
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hs : (Γ'.1 c).isSome := by rw [hc]; rfl
      have hcomp : ∀ t, (∀ e, T.Mentions t e → (Γ'.1 e).isSome) →
          T.subst σ'' (T.rename ρ t) = T.subst m'.σ t := by
        intro t ht
        rw [subst_rename]
        exact T.subst_congr fun e he => hat e (ht e he)
      obtain ⟨r1, r2⟩ := m'.real c A v hc
      refine ⟨by rw [hat c hs, hcomp A (Γ'.2 c A v hc).1]; exact r1, fun t ht => ?_⟩
      cases v with
      | none => cases ht
      | some s =>
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        rw [hat c hs, hcomp s ((Γ'.2 c A (some s) hc).2 s rfl)]
        exact r2 s rfl
  refine ⟨{ σ := σ'', off := fun d hd => ?_, real := by rw [hG]; exact hreal },
    Real.ext (funext fun d => ?_), Real.ext (funext fun c => ?_)⟩
  · rw [hG] at hd
    have hW : W.1 d = none := by
      cases h : W.1 d with
      | none => rfl
      | some e => rw [glueRaw_left h] at hd; cases hd
    have hex : ¬ ∃ c, (Γ'.1 c).isSome ∧ ρ c = d := by
      rintro ⟨c, hc, rfl⟩
      obtain ⟨⟨A, v⟩, hA⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨v', h', -⟩ := glueRaw_right r hkeep f hA
      rw [h'] at hd; cases hd
    simp [σ'', hW, hex]
  · by_cases hd : (W.1 d).isSome
    · rw [restrict_σ _ _ d hd]; exact hold d hd
    · simp [restrict, hd, mW.off d (Option.not_isSome_iff_eq_none.mp hd)]
  · by_cases hc : (Γ'.1 c).isSome
    · rw [restrict_σ _ _ c hc]; exact hat c hc
    · simp [restrict, hc, m'.off c (Option.not_isSome_iff_eq_none.mp hc)]

/-! ## The instance -/

/-- The empty environment. -/
def SEnv.empty : SEnv T := ⟨fun _ => none, fun _ _ _ h => by cases h⟩

variable (T) in
/-- **A syntactic consistency proof as a modular semantics.** -/
noncomputable def syntacticSemantics : ModularSemantics.{u, u} where
  Env := SEnv T
  Name := N
  Refines := Refines
  refines_id := refines_id
  refines_comp := refines_comp
  Mod := Real T
  restrict := restrict
  restrict_id := restrict_id
  restrict_comp := restrict_comp
  Decls := List (N × T.Tm × T.Tm)
  Accepts := Accepts
  accepts_refines h := h.refines
  step h m := h.step m
  Fresh := Fresh
  glue := glue
  glue_left := glue_left
  glue_right := glue_right
  amalgamate := amalgamate
  base := SEnv.empty
  baseModel := { σ := T.const, off := fun _ _ => rfl, real := fun _ _ _ h => by cases h }

end Fragment.Syntactic
