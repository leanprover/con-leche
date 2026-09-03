import Setlec.SetBase.Ok2
import Setlec.SetBase.Sat2

/-!
# `SetBase/Hoist` — the `AnnotOk2` hoist kit

The generation-four hoist kit, re-based out of
`SetR/Interp2/Step2/Dispatch.lean` at THE SEPARATION's S2 (task #161).

Every lemma here is an implication between `∀ ρ, Sat2 V Δa ρ → …`
shapes: the splitters that take a hoisted node fact apart, the
converses that build one from its parts, the head transfer that moves a
hoisted fact across a domain equality, and the lift.  They mention no
fuel, no `denote2`, no run and no environment — the trap-check section
at the end of this file makes exactly that observation — and both
lanes' quarters consume them at every congruence.

The one thing left behind in `Dispatch` is the `CtxOk2.openCong`
satisfiability example, which is about `CtxOk2` and therefore 2U.

Statements verbatim, namespace (`Setlec.SetR.Interp2`) unchanged.
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- **The positive half: the hoist is self-propagating at a `∀`.**  A
hoisted `AnnotOk2` of the node gives the domain's hoisted form and the
codomain's *in the extended context*, which is exactly the pair the
recursive call needs.  So paying the repair at the congruence costs
nothing beyond restating it. -/
theorem AnnotOk2.hoist_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ B) := by
  refine ⟨fun ρ hρ => ((AnnotOk2_pi V ρ u v A B) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((AnnotOk2_pi V _ u v A B) ▸ h _ (Sat2_tail hρ)).2
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-- The same at a `λ`, where the node's second component has the same
shape.  Together these cover all five congruence sites. -/
theorem AnnotOk2.hoist_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ b) := by
  refine ⟨fun ρ hρ => ((AnnotOk2_lam V ρ v A b) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((AnnotOk2_lam V _ v A b) ▸ h _ (Sat2_tail hρ)).2.1
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-! ## The hoist kit, generation four — the complete list

`hoist_pi`/`hoist_lam` above are the two shapes the congruences named,
and they are stated exactly as a consumer holding
`∀ ρ, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B)` wants them: the
domain's hoisted form over `Δa`, and the codomain's hoisted form over
the **extended** context `A :: Δa`.  That is the pair a recursive call
into the claim family takes.

Audited against that use, three things were missing and are added
here.

1. **The non-binder splitters** (`hoist_app`, `hoist_letE`,
   `hoist_proj`, `hoist_eqE`) and the two contraction forms
   (`hoist_beta_pos`, `hoist_zeta`).  Mechanical, but a quarter that
   re-derives them re-derives them four times.
2. **The converses** (`of_pi`, `of_lam`, `of_app`, `of_letE`,
   `of_proj`, `of_eqE`).  `WhnfCoreClaims2C`/`WhnfClaims2C` and
   `InferClaims2C` now *deliver* a ρ-uniform `AnnotOk2`, so assembling
   the node fact from its parts' hoisted forms is an obligation this
   generation created.  `Sat2_cons` is the whole content of the binder
   ones; the semantic components (the `λ`'s fibre, the app's slot)
   stay per-valuation, because they are memberships and not gradings.
3. **The head transfer** (`Sat2.head_congr`,
   `AnnotOk2.hoist_head_congr`) — *the piece without which the split
   kit does not reach its own motivating site.*  `CtxOk2.openCong`
   extends the context with the **left** domain `ta₁`, while
   `hoist_pi`/`hoist_lam` deliver the right side's codomain fact over
   `ta₂ :: Δa`.  The two lists differ in their head and nothing else
   relates them; the bridge is the domains' own semantic agreement,
   which is `DefEqClaims2C`'s conclusion — already in hand at every
   congruence.

**Two shapes are deliberately absent, and the absence is a finding.**

* There is **no `letE` binder splitter**.  `AnnotOk2`'s `letE` clause
  reads the body at `cons (interp2 V ρ v) ρ` — the *value's* point —
  while `Sat2 (T :: Δa) ρ'` constrains `ρ' 0` only to inhabit `T`.  So
  the body's fact does not hoist into the extended context, and no
  restatement of the hoist repairs that.  `hoist_zeta` is what a
  consumer gets instead, and it is what the checker needs: `letE` is
  reduced by substitution, not by opening.
* There is **no unconditional `of_lam`**.  The `λ` clause's fibre
  component is a genuinely per-valuation semantic fact with no
  hereditary source, so the converse takes it as a premise. -/

/-- The application splits into its two parts, both hoisted.  The slot
component stays per-valuation: it is a membership, not a grading. -/
theorem AnnotOk2.hoist_app {Δa : List AVExpr} {f a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.app f a)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ f) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a) :=
  ⟨fun ρ hρ => ((AnnotOk2_app V ρ f a) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_app V ρ f a) ▸ h ρ hρ).2.1⟩

/-- The `letE`'s two *unopened* parts.  The body is not here — see the
kit's note; `hoist_zeta` is its usable form. -/
theorem AnnotOk2.hoist_letE {Δa : List AVExpr} {T v b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v) :=
  ⟨fun ρ hρ => ((AnnotOk2_letE V ρ T v b) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_letE V ρ T v b) ▸ h ρ hρ).2.1⟩

/-- The projection's subject. -/
theorem AnnotOk2.hoist_proj {Δa : List AVExpr} {i : Nat} {e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.proj i e)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e :=
  fun ρ hρ => ((AnnotOk2_proj V ρ i e) ▸ h ρ hρ).1

/-- The equality node's two sides. -/
theorem AnnotOk2.hoist_eqE {Δa : List AVExpr} {T a b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.eqE T a b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ b) :=
  ⟨fun ρ hρ => ((AnnotOk2_eqE V ρ T a b) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_eqE V ρ T a b) ▸ h ρ hρ).2⟩

/-- The β contractum, hoisted, at a positive codomain kind. -/
theorem AnnotOk2.hoist_beta_pos {Δa : List AVExpr} {v : Nat}
    (hv : v ≠ 0) {A b a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (.app (.lam v A b) a)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (b.inst a) :=
  fun ρ hρ => (AnnotOk2_beta_pos V hv (h ρ hρ)).2

/-- The ζ contractum, hoisted — the `letE` body's usable form. -/
theorem AnnotOk2.hoist_zeta {Δa : List AVExpr} {T v b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (b.inst v) :=
  fun ρ hρ => (AnnotOk2_zeta V (h ρ hρ)).2

/-! ### The converses -/

/-- **The converse at a `Π`.**  `Sat2_cons` is the whole content: an
inhabitant of the domain extends the valuation into `A :: Δa`. -/
theorem AnnotOk2.of_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (hA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A)
    (hB : ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ B) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B) := by
  intro ρ hρ
  rw [AnnotOk2_pi]
  exact ⟨hA ρ hρ, fun x hx => hB _ (Sat2_cons (V := V) hρ hx)⟩

/-- **The converse at a `λ`.**  The fibre component has no hereditary
source and is therefore a premise, stated per-valuation because that
is what it is. -/
theorem AnnotOk2.of_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (hA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A)
    (hb : ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ b)
    (hfib : ∀ ρ : Nat → V, Sat2 V Δa ρ → ∃ B : V → V,
      (∀ x, x ∈ˢ interp2 V ρ A → interp2 V (cons x ρ) b ∈ˢ B x) ∧
      (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A →
        B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.lam v A b) := by
  intro ρ hρ
  rw [AnnotOk2_lam]
  exact ⟨hA ρ hρ, fun x hx => hb _ (Sat2_cons (V := V) hρ hx),
    hfib ρ hρ⟩

/-- **The converse at an application.**  The slot stays
per-valuation; `AnnotOk2_app_of` (`Annot/Ok2.lean`) is the shape that
builds it from an annotated `Π`. -/
theorem AnnotOk2.of_app {Δa : List AVExpr} {f a : AVExpr}
    (hf : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ f)
    (ha : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a)
    (hslot : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      ∃ (v : Nat) (A : V) (B : V → V),
        interp2 V ρ f ∈ˢ piR v A B ∧ interp2 V ρ a ∈ˢ A ∧
        (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.app f a) := by
  intro ρ hρ
  rw [AnnotOk2_app]
  exact ⟨hf ρ hρ, ha ρ hρ, hslot ρ hρ⟩

/-- **The converse at a `letE`**, in the form the extended context can
actually supply: the value inhabits the annotation, so `Sat2_cons`
puts the body's hoisted fact at exactly the point the clause reads. -/
theorem AnnotOk2.of_letE {Δa : List AVExpr} {T v b : AVExpr}
    (hT : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T)
    (hv : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v)
    (hmem : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ v ∈ˢ interp2 V ρ T)
    (hb : ∀ ρ : Nat → V, Sat2 V (T :: Δa) ρ → AnnotOk2 V ρ b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b) := by
  intro ρ hρ
  rw [AnnotOk2_letE]
  exact ⟨hT ρ hρ, hv ρ hρ,
    hb _ (Sat2_cons (V := V) hρ (hmem ρ hρ))⟩

/-- The converse at a `letE` with the body's fact in its raw,
value-indexed form — for a consumer that has no membership to spend. -/
theorem AnnotOk2.of_letE_raw {Δa : List AVExpr} {T v b : AVExpr}
    (hT : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T)
    (hv : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v)
    (hb : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V (cons (interp2 V ρ v) ρ) b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b) := by
  intro ρ hρ
  rw [AnnotOk2_letE]
  exact ⟨hT ρ hρ, hv ρ hρ, hb ρ hρ⟩

/-- The converse at a projection. -/
theorem AnnotOk2.of_proj {Δa : List AVExpr} {i : Nat} {e : AVExpr}
    (he : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e) (hi : i < 2)
    (hsig : ∀ ρ : Nat → V, Sat2 V Δa ρ → ∃ u v A Bf,
      interp2 V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.proj i e) := by
  intro ρ hρ
  rw [AnnotOk2_proj]
  exact ⟨he ρ hρ, hi, hsig ρ hρ⟩

/-- The converse at an equality node. -/
theorem AnnotOk2.of_eqE {Δa : List AVExpr} {T a b : AVExpr}
    (ha : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a)
    (hb : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.eqE T a b) := by
  intro ρ hρ
  rw [AnnotOk2_eqE]
  exact ⟨ha ρ hρ, hb ρ hρ⟩

/-! ### The head transfer — what makes the kit reach `openCong`

Without these two the split kit stops one step short of the sites it
was built for: `hoist_pi`/`hoist_lam` hand the right side's codomain
fact over `ta₂ :: Δa`, and the recursive call runs in `ta₁ :: Δa`. -/

/-- **A satisfying valuation transfers across a head equality.**
`Sat2` reads the head at the *tail* valuation, which is exactly where
the domains' agreement is stated, so the transfer is immediate. -/
theorem Sat2.head_congr {Δa : List AVExpr} {A B : AVExpr}
    {ρ : Nat → V}
    (heq : ∀ ρ' : Nat → V, Sat2 V Δa ρ' →
      interp2 V ρ' A = interp2 V ρ' B)
    (hρ : Sat2 V (A :: Δa) ρ) : Sat2 V (B :: Δa) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : B = Aa := by simpa using hi
    have h0 : ρ 0 ∈ˢ interp2 V (fun j => ρ (j + 1)) A := hρ 0 A rfl
    show ρ 0 ∈ˢ interp2 V (fun j => ρ (j + 1)) B
    rwa [heq _ (Sat2_tail hρ)] at h0
  | succ i => exact hρ (i + 1) Aa (by simpa using hi)

/-- **A hoisted fact transfers with it.**  `heq` is
`DefEqClaims2C`'s conclusion; `h` is `hoist_pi.2`/`hoist_lam.2` on the
right side; the result is what the recursive call in `ta₁ :: Δa`
takes. -/
theorem AnnotOk2.hoist_head_congr {Δa : List AVExpr} {A B e : AVExpr}
    (heq : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ A = interp2 V ρ B)
    (h : ∀ ρ : Nat → V, Sat2 V (B :: Δa) ρ → AnnotOk2 V ρ e) :
    ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ e :=
  fun ρ hρ => h ρ (Sat2.head_congr heq hρ)

/-- **Weakening a hoisted fact under one more binder.**  The
annotation lifts and `Sat2_tail` carries the valuation; the transpose
of `CtxOk2.weakenTop` for the grading. -/
theorem AnnotOk2.hoist_lift {Δa : List AVExpr} {X e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e) :
    ∀ ρ : Nat → V, Sat2 V (X :: Δa) ρ → AnnotOk2 V ρ e.lift := by
  intro ρ hρ
  refine (AnnotOk2_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat2_tail hρ)

/-! ### Trap-check on the kit

Every lemma above is an implication between `∀ ρ, Sat2 → …` shapes and
mentions no fuel, no `denote2` and no run, so the smallest-fuel test
has nothing to bite on — and, per seal 11, that is *not* a clean bill
of health on its own.  The semantic check that matters is inhabitation
in a *non-vacuous* context, which the two examples below give: the
splitters and the converses are exercised at a `Δa` whose `Sat2` is
satisfiable, so neither direction is a vacuous implication. -/

/-- `ρ ≡ ∅` satisfies `[⟪Sort 0⟫]`: the context used below is
genuinely inhabited. -/
private theorem sat2_sort0_empty :
    Sat2 V [AVExpr.sort 0] (fun _ => (empty : V)) := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : AVExpr.sort 0 = Aa := by simpa using hi
    simpa using empty_mem_univ (V := V) 0
  | succ i => simp at hi

/-- The converse builds a `Π` fact over that context and the splitter
takes it back apart, so neither direction of the kit is a vacuous
implication. -/
example :
    AnnotOk2 V (fun _ => (empty : V))
      (.pi 1 2 (.sort 0) (.sort 1)) ∧
    (∀ ρ : Nat → V, Sat2 V [AVExpr.sort 0] ρ →
      AnnotOk2 V ρ (AVExpr.sort 0)) := by
  have hpi : ∀ ρ : Nat → V, Sat2 V [AVExpr.sort 0] ρ →
      AnnotOk2 V ρ (.pi 1 2 (.sort 0) (.sort 1)) :=
    AnnotOk2.of_pi (fun _ _ => by simp) (fun _ _ => by simp)
  exact ⟨hpi _ sat2_sort0_empty, (AnnotOk2.hoist_pi hpi).1⟩

end Setlec.SetR.Interp2
