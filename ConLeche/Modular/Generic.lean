module

@[expose] public section

/-!
# The modular argument, for any consistency proof

The modular theorem (`ConLeche.modular_model_exists`) has two halves:
a consistency proof for one environment, and the argument that glues
the modules of a development into one world.  This file is the second
half, stated over an interface (`ModularSemantics`) that says what the
first half must provide, so that the consistency proof can be swapped
(for a syntactic one, say) without redoing the gluing.  It imports
nothing.

**The interface.**  Environments, with **refinement with renaming**
`Refines Γ ρ E` (`Γ ≼[ρ] E`: every constant of `Γ` is, renamed by `ρ`,
a constant of `E` or an assumption of its statement; constants of `E`
may be left out), a preorder: identity, composition.  Then:

1. **models as data** (`Mod E`, a type, not a proposition), with a
   **restriction** along every refinement, functorial: restricting
   along the identity changes nothing, along a composite is
   restricting twice;
2. **the conservative step** (`step`): if the checker accepts
   declarations `D` over `Γ`, giving `Γ'`, every model of `Γ` extends
   to one of `Γ'` that restricts back to it;
3. **amalgamation** (`amalgamate`): given `Γ ≼[ρ] W`, the names `Γ'`
   adds to `Γ` new in `W` after renaming (`Fresh`), a model of `W` and
   one of `Γ'` that restrict to the same model of `Γ` combine to a
   model of `W` with what `Γ'` adds, renamed (`glue W ρ Γ'`),
   restricting to both;
4. **a base** environment with a model.

This is the structure known as an institution with amalgamation
(Goguen and Burstall): signatures and their morphisms (here:
environments and refinements), a contravariant functor of models, and
models of a pushout made of compatible models of its parts.

**Why models must be data.**  A predicate "has a model" is too weak for
the gluing: let `Γ` assume `c : Nat`, let `W` define `c := 5`, and let
`D` add the axiom `c = 0`.  Then `Γ + D` and `W` both have models, but
`W + D` has none.  What excludes it is that the step must extend
*every* model of `Γ` — including the one `W`'s model restricts to,
where `c` is `5` — and an axiom `c = 0` does not; amalgamation then
only ever meets models that agree on `Γ`.

**The theorem** (`Development.modular`).  A development is a sequence
of modules, each with a context, declarations, an own environment and
a resolution of its names to qualified names (`ren`).  The world
(`Development.world`) starts at the base and grows by every checked
module's own environment, renamed.  A module is **valid**
(`Development.Valid`) if it is checked — its context refines the world
so far, its declarations are accepted over the context, and what they
add is fresh — or compared — its whole own environment refines the
world so far (a challenge read against its solution).  If every module
is valid, the world has a model, every module's own environment
refines the world, and so (`Development.own_model`) each has a model:
the world's, restricted.
-/

namespace ConLeche.Modular

universe u w

/-- **What a consistency proof provides for modular checking** (see the
module docstring). -/
structure ModularSemantics where
  /-- environments -/
  Env : Type u
  /-- names: a module's own names and the qualified names of the world -/
  Name : Type u
  /-- **refinement with renaming**, `Γ ≼[ρ] E` -/
  Refines : Env → (Name → Name) → Env → Prop
  refines_id : ∀ E, Refines E id E
  refines_comp : ∀ {Γ E F : Env} {ρ σ : Name → Name},
    Refines Γ ρ E → Refines E σ F → Refines Γ (σ ∘ ρ) F
  /-- **the models** of an environment -/
  Mod : Env → Type w
  /-- **restriction** along a refinement -/
  restrict : ∀ {Γ E : Env} {ρ : Name → Name}, Refines Γ ρ E → Mod E → Mod Γ
  restrict_id : ∀ {E : Env} (m : Mod E), restrict (refines_id E) m = m
  restrict_comp : ∀ {Γ E F : Env} {ρ σ : Name → Name} (h₁ : Refines Γ ρ E)
    (h₂ : Refines E σ F) (m : Mod F),
    restrict (refines_comp h₁ h₂) m = restrict h₁ (restrict h₂ m)
  /-- declarations -/
  Decls : Type u
  /-- **acceptance**: the checker accepts `D` over `Γ`, giving `Γ'` -/
  Accepts : Env → Decls → Env → Prop
  accepts_refines : ∀ {Γ Γ' : Env} {D : Decls}, Accepts Γ D Γ' → Refines Γ id Γ'
  /-- **the conservative step** -/
  step : ∀ {Γ Γ' : Env} {D : Decls} (h : Accepts Γ D Γ') (m : Mod Γ),
    ∃ m' : Mod Γ', restrict (accepts_refines h) m' = m
  /-- **freshness**: `Fresh W ρ Γ Γ'`, what `Γ'` adds to `Γ` is, renamed
  by `ρ`, new in `W` -/
  Fresh : Env → (Name → Name) → Env → Env → Prop
  /-- `W` with what `Γ'` adds, renamed by `ρ` -/
  glue : Env → (Name → Name) → Env → Env
  glue_left : ∀ {W Γ' : Env} {ρ : Name → Name}, Refines W id (glue W ρ Γ')
  glue_right : ∀ {Γ Γ' W : Env} {D : Decls} {ρ : Name → Name},
    Refines Γ ρ W → Accepts Γ D Γ' → Fresh W ρ Γ Γ' → Refines Γ' ρ (glue W ρ Γ')
  /-- **amalgamation** -/
  amalgamate : ∀ {Γ Γ' W : Env} {D : Decls} {ρ : Name → Name} (r : Refines Γ ρ W)
    (a : Accepts Γ D Γ') (f : Fresh W ρ Γ Γ') (mW : Mod W) (m' : Mod Γ'),
    restrict r mW = restrict (accepts_refines a) m' →
    ∃ m'' : Mod (glue W ρ Γ'), restrict glue_left m'' = mW ∧ restrict (glue_right r a f) m'' = m'
  /-- **the base** -/
  base : Env
  baseModel : Mod base

variable {S : ModularSemantics.{u, w}}

/-- **A development** over `S`: per module its context, declarations, own
environment and resolution, and whether it is compared rather than
checked. -/
structure Development (S : ModularSemantics.{u, w}) where
  ctx : Nat → S.Env
  decls : Nat → S.Decls
  own : Nat → S.Env
  ren : Nat → S.Name → S.Name
  compared : Nat → Bool

/-- **The world** before module `i`: the base, grown by every checked
module's own environment, renamed. -/
def Development.world (dev : Development S) : Nat → S.Env
  | 0 => S.base
  | i + 1 => if dev.compared i then dev.world i else S.glue (dev.world i) (dev.ren i) (dev.own i)

/-- **A valid module**: checked (its context refines the world so far,
its declarations are accepted over it, what they add is fresh), or
compared (its own environment refines the world so far). -/
def Development.Valid (dev : Development S) (i : Nat) : Prop :=
  if dev.compared i then S.Refines (dev.own i) (dev.ren i) (dev.world i)
  else S.Refines (dev.ctx i) (dev.ren i) (dev.world i) ∧
    S.Accepts (dev.ctx i) (dev.decls i) (dev.own i) ∧
    S.Fresh (dev.world i) (dev.ren i) (dev.ctx i) (dev.own i)

/-- **The modular theorem, for any consistency proof**: if every module
before `k` is valid, the world has a model and every such module's own
environment refines it. -/
theorem Development.modular (dev : Development S) :
    ∀ k, (∀ i < k, dev.Valid i) →
      Nonempty (S.Mod (dev.world k)) ∧ ∀ i < k, S.Refines (dev.own i) (dev.ren i) (dev.world k)
  | 0, _ => ⟨⟨S.baseModel⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hv => by
    obtain ⟨⟨mW⟩, hown⟩ := dev.modular k fun i hi => hv i (Nat.lt_succ_of_lt hi)
    have hk := hv k (Nat.lt_succ_self k)
    unfold Development.Valid at hk
    unfold Development.world
    cases hc : dev.compared k with
    | true =>
      simp only [hc, ↓reduceIte] at hk ⊢
      refine ⟨⟨mW⟩, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hown i hi
      · exact hk
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨r, a, f⟩ := hk
      obtain ⟨m', hm'⟩ := S.step a (S.restrict r mW)
      obtain ⟨m'', -, -⟩ := S.amalgamate r a f mW m' hm'.symm
      refine ⟨⟨m''⟩, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact S.refines_comp (ρ := dev.ren i) (σ := id) (hown i hi) S.glue_left
      · exact S.glue_right r a f

/-- **Every valid module's own environment has a model**: the world's,
restricted. -/
theorem Development.own_model (dev : Development S) (k : Nat) (hv : ∀ i < k, dev.Valid i) :
    ∀ i < k, Nonempty (S.Mod (dev.own i)) := by
  obtain ⟨⟨m⟩, hr⟩ := dev.modular k hv
  exact fun i hi => ⟨S.restrict (hr i hi) m⟩

end ConLeche.Modular
