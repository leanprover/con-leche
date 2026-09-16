module

public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Kernel.Inductives.StructParts

public section

/-!
# What a successful `denoteMeta` witnesses about the environment (task #315)

`denoteMeta` (`ConLeche/Model/Annot/Bit.lean`) reads a `.const n us`
node only against `env.find? n`, so a term it reads successfully
cannot name a constant the environment does not have.  That is the
fact the nested route's model tier wants when it has a copy's type in
hand and knows the copy mentions an auxiliary name.

**The walk that carries it is not `Expr.mentionsConst`.**  The kernel's
occurrence walk looks in two places the reading does *not*:

* a `fvar`'s type annotation — `denoteMeta` answers `.bvar (d-1-idx)`
  at every variable and never inspects the annotation;
* a `.proj s i e`'s STRUCTURE NAME — the reading consults
  `env.findProj? s i`, but its `none` branch falls back to the pinned
  pair decoding `AnnotTerm.projPair?`, which succeeds at `i < 2`
  whatever `s` is.  So `denoteMeta acval env φ d (.proj n 0 (.sort u))`
  is `some (.fst (.sort _))` even at an `n` the environment never heard
  of: the `mentionsConst`-shaped statement is FALSE, and the leaf
  hypothesis does not repair it.

`mentionsConstRead` below is the occurrence walk the reading actually
performs, `mentionsConstProj` the one clause that separates it from
`Expr.mentionsConst` once the leaves are excluded, and
`mentionsConstRead_of_mentionsConst` the bridge between them.
-/

namespace ConLeche.Model

open ConLeche.Semantics
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

variable {env : Env} {φ : Name → Nat} {acval : Name → (Name → Nat) → AnnotTerm}
variable {n : Name}

/-! ## The two halves of `Expr.mentionsConst` -/

/-- **The occurrence walk `denoteMeta` performs**: `Expr.mentionsConst`
minus the two nodes the reading does not look at — a `fvar`'s type
annotation and a `.proj`'s structure name. -/
@[expose] def mentionsConstRead (T : Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ | .fvar _ _ => false
  | .const m _ => m == T
  | .app f a => mentionsConstRead T f || mentionsConstRead T a
  | .lam ty b _ | .forallE ty b _ => mentionsConstRead T ty || mentionsConstRead T b
  | .letE ty v b =>
    mentionsConstRead T ty || mentionsConstRead T v || mentionsConstRead T b
  | .proj _ _ e => mentionsConstRead T e

/-- **The clause that separates the two walks**: `T` at a `.proj`'s
structure name.  (The other difference, `T` inside a `fvar`
annotation, is what the leaf hypothesis of
`mentionsConstRead_of_mentionsConst` excludes, so this walk stops at a
variable.) -/
@[expose] def mentionsConstProj (T : Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ | .fvar _ _ | .const _ _ => false
  | .app f a => mentionsConstProj T f || mentionsConstProj T a
  | .lam ty b _ | .forallE ty b _ => mentionsConstProj T ty || mentionsConstProj T b
  | .letE ty v b =>
    mentionsConstProj T ty || mentionsConstProj T v || mentionsConstProj T b
  | .proj s _ e => s == T || mentionsConstProj T e

/-- The reading's walk is a restriction of the kernel's. -/
theorem mentionsConst_of_mentionsConstRead {T : Name} :
    ∀ (e : Expr), mentionsConstRead T e = true → e.mentionsConst T = true := by
  intro e
  induction e with
  | bvar i => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | fvar idx ty _ => intro h; exact nomatch h
  | const m us => intro h; exact h
  | app f a ihf iha =>
    intro h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp ihf iha
  | lam ty b m ihty ihb =>
    intro h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp ihty ihb
  | forallE ty b m ihty ihb =>
    intro h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp ihty ihb
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp (fun h => h.imp ihty ihv) ihb
  | proj s i sub ih =>
    intro h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact Or.inr (ih h)

/-- **The bridge**: away from the `fvar` annotations (the leaf
hypothesis) and away from the `.proj` structure names
(`mentionsConstProj`), the kernel's occurrence walk is the reading's. -/
theorem mentionsConstRead_of_mentionsConst {T : Name} :
    ∀ (e : Expr), e.mentionsConst T = true →
      (∀ l ∈ e.fvarLeaves, l.2.mentionsConst T = false) →
      mentionsConstProj T e = false → mentionsConstRead T e = true := by
  intro e
  induction e with
  | bvar i => intro h _ _; exact nomatch h
  | sort u => intro h _ _; exact nomatch h
  | lit l => intro h _ _; cases l <;> exact nomatch h
  | fvar idx ty _ =>
    intro h hl _
    have := hl (idx, ty) (by rw [Expr.fvarLeaves]; exact List.mem_cons_self)
    simp only [Expr.mentionsConst] at h
    rw [this] at h
    exact nomatch h
  | const m us => intro h _ _; exact h
  | app f a ihf iha =>
    intro h hl hp
    rw [Expr.fvarLeaves] at hl
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [mentionsConstProj, Bool.or_eq_false_iff] at hp
    simp only [mentionsConstRead, Bool.or_eq_true]
    exact h.imp
      (fun h => ihf h (fun l hl' => hl l (List.mem_append_left _ hl')) hp.1)
      (fun h => iha h (fun l hl' => hl l (List.mem_append_right _ hl')) hp.2)
  | lam ty b m ihty ihb =>
    intro h hl hp
    rw [Expr.fvarLeaves] at hl
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [mentionsConstProj, Bool.or_eq_false_iff] at hp
    simp only [mentionsConstRead, Bool.or_eq_true]
    exact h.imp
      (fun h => ihty h (fun l hl' => hl l (List.mem_append_left _ hl')) hp.1)
      (fun h => ihb h (fun l hl' => hl l (List.mem_append_right _ hl')) hp.2)
  | forallE ty b m ihty ihb =>
    intro h hl hp
    rw [Expr.fvarLeaves] at hl
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [mentionsConstProj, Bool.or_eq_false_iff] at hp
    simp only [mentionsConstRead, Bool.or_eq_true]
    exact h.imp
      (fun h => ihty h (fun l hl' => hl l (List.mem_append_left _ hl')) hp.1)
      (fun h => ihb h (fun l hl' => hl l (List.mem_append_right _ hl')) hp.2)
  | letE ty v b ihty ihv ihb =>
    intro h hl hp
    rw [Expr.fvarLeaves] at hl
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [mentionsConstProj, Bool.or_eq_false_iff] at hp
    simp only [mentionsConstRead, Bool.or_eq_true]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (ihty h
        (fun l hl' => hl l (List.mem_append_left _ (List.mem_append_left _ hl'))) hp.1.1))
    · exact Or.inl (Or.inr (ihv h
        (fun l hl' => hl l (List.mem_append_left _ (List.mem_append_right _ hl'))) hp.1.2))
    · exact Or.inr (ihb h (fun l hl' => hl l (List.mem_append_right _ hl')) hp.2)
  | proj s i sub ih =>
    intro h hl hp
    rw [Expr.fvarLeaves] at hl
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [mentionsConstProj, Bool.or_eq_false_iff] at hp
    refine ih (h.resolve_left (fun hs => ?_)) hl hp.2
    rw [hs] at hp
    exact nomatch hp.1

/-- Substitution keeps a read occurrence: `instantiate1` rewrites
`bvar` nodes only, and the walk finds nothing at a `bvar`. -/
theorem mentionsConstRead_instantiate1 {T : Name} {v : Expr} :
    ∀ {e : Expr} {j : Nat}, mentionsConstRead T e = true →
      mentionsConstRead T (e.instantiate1 v j) = true := by
  intro e
  induction e with
  | bvar i => intro j h; exact nomatch h
  | sort u => intro j h; exact nomatch h
  | lit l => intro j h; exact nomatch h
  | fvar idx ty _ => intro j h; exact nomatch h
  | const m us => intro j h; exact h
  | app f a ihf iha =>
    intro j h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, mentionsConstRead, Bool.or_eq_true]
    exact h.imp (fun h => ihf h) (fun h => iha h)
  | lam ty b m ihty ihb =>
    intro j h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, mentionsConstRead, Bool.or_eq_true]
    exact h.imp (fun h => ihty h) (fun h => ihb h)
  | forallE ty b m ihty ihb =>
    intro j h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, mentionsConstRead, Bool.or_eq_true]
    exact h.imp (fun h => ihty h) (fun h => ihb h)
  | letE ty v' b ihty ihv ihb =>
    intro j h
    simp only [mentionsConstRead, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, mentionsConstRead, Bool.or_eq_true]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (ihty h))
    · exact Or.inl (Or.inr (ihv h))
    · exact Or.inr (ihb h)
  | proj s i sub ih =>
    intro j h
    simp only [mentionsConstRead] at h
    simp only [Expr.instantiate1, mentionsConstRead]
    exact ih h

/-! ## The reading's witness -/

/-- The `const` clause consults the environment, in all three of its
arms. -/
private theorem denoteMeta_const_found {d : Nat} {m : Name} {us : List Level}
    {ea : AnnotTerm} (h : denoteMeta acval env φ d (.const m us) = some ea) :
    (env.find? m).isSome = true := by
  rw [denoteMeta] at h
  cases hf : env.find? m with
  | none => rw [hf] at h; exact nomatch h
  | some ci => rfl

/-- **A SUCCESSFUL READING WITNESSES ITS CONSTANTS** (task #315): every
constant `denoteMeta` reads is one it found in the environment, so a
term it reads and that names `n` at a read node puts `n` in the
environment.  The binder clauses read the OPENED body, which names `n`
wherever the body does (`mentionsConstRead_instantiate1`); the `letE`
clause reads nothing (`none` by design) and the literal clauses name no
constant. -/
private theorem denoteMeta_some_found_aux :
    ∀ (d : Nat) (e : Expr) (ea : AnnotTerm),
      denoteMeta acval env φ d e = some ea → mentionsConstRead n e = true →
        (env.find? n).isSome = true := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => intro ea _ h2; exact nomatch h2
  | case2 d idx ty => intro ea _ h2; exact nomatch h2
  | case3 d m us ci hf hlen =>
    intro ea h1 h2
    simp only [mentionsConstRead, beq_iff_eq] at h2
    rw [← h2]
    exact denoteMeta_const_found h1
  | case4 d m us ci hf hlen =>
    intro ea h1 h2
    simp only [mentionsConstRead, beq_iff_eq] at h2
    rw [← h2]
    exact denoteMeta_const_found h1
  | case5 d m us hf =>
    intro ea h1 h2
    simp only [mentionsConstRead, beq_iff_eq] at h2
    rw [← h2]
    exact denoteMeta_const_found h1
  | case6 d ty body m ihty ihbody =>
    intro ea h1 h2
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_forallE_inv h1
    simp only [mentionsConstRead, Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact ihty ta hta h2
    · exact ihbody ba hba (mentionsConstRead_instantiate1 h2)
  | case7 d ty body m ihty ihbody =>
    intro ea h1 h2
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_lam_inv h1
    simp only [mentionsConstRead, Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact ihty ta hta h2
    · exact ihbody ba hba (mentionsConstRead_instantiate1 h2)
  | case8 d f a ihf iha =>
    intro ea h1 h2
    obtain ⟨fa, aa, hfa, haa, -⟩ := denoteMeta_app_inv h1
    simp only [mentionsConstRead, Bool.or_eq_true] at h2
    exact h2.elim (fun h2 => ihf fa hfa h2) (fun h2 => iha aa haa h2)
  | case9 d ty val body =>
    intro ea h1 _
    rw [denoteMeta] at h1
    exact nomatch h1
  | case10 d sn i sub ihsub =>
    intro ea h1 h2
    obtain ⟨ia, hia, -⟩ := denoteMeta_proj_inv h1
    exact ihsub ia hia h2
  | case11 d m hsup => intro ea _ h2; exact nomatch h2
  | case12 d m hsup => intro ea _ h2; exact nomatch h2
  | case13 d s hsup => intro ea _ h2; exact nomatch h2
  | case14 d s hsup => intro ea _ h2; exact nomatch h2
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h1 h2
    cases x with
    | bvar i => exact nomatch h2
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const m us => exact absurd rfl (hc m us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal m => exact absurd rfl (hnat m)
      | strVal s => exact absurd rfl (hstr s)

/-- **A SUCCESSFUL READING WITNESSES ITS CONSTANTS**, with the reading
position implicit — the form consumers take. -/
theorem denoteMeta_some_found :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env φ d e = some ea → mentionsConstRead n e = true →
        (env.find? n).isSome = true := by
  intro d e ea h1 h2
  exact denoteMeta_some_found_aux d e ea h1 h2

/-- The same witness in the kernel's own occurrence walk, under the two
side conditions the reading needs: the annotations do not name `n`
(the leaf hypothesis), and no `.proj`'s structure name is `n` — the
clause the reading genuinely does not check. -/
theorem denoteMeta_some_found_of_mentionsConst :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env φ d e = some ea → e.mentionsConst n = true →
        (∀ l ∈ e.fvarLeaves, l.2.mentionsConst n = false) →
        mentionsConstProj n e = false →
        (env.find? n).isSome = true := by
  intro d e ea h1 h2 h3 h4
  exact denoteMeta_some_found_aux d e ea h1 (mentionsConstRead_of_mentionsConst e h2 h3 h4)

end ConLeche.Model
