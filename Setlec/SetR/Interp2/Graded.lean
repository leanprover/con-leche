import Setlec.SetR.Interp2.Ops

/-!
# Option C: the graded soundness judgment — feasibility (task #151, tier B)

The F4/A3 impasse (the λ node cannot carry its codomain sort, and the
checker does not compute it) was ruled to be repaired by **option C**:
move the two-regime split from the λ *value* to the soundness
*judgment*.

* `interp2 (lam …)` becomes **uniformly the graph** — no annotation
  read, so tier B's `lam_cod_sort_needed` refutation no longer applies
  (it targets value-level uniformity landing in `piR` at both regimes,
  a requirement C abandons);
* `pi u v A B` keeps both numerals and dispatches as landed;
* the soundness conclusion becomes **graded by the type's kind**:
  positive kinds keep membership, kind `0` concludes only that the
  type's interpretation is *true* (inhabited), and the subject's value
  is never consulted — classical proof-irrelevant semantics.

`Real k x T` below is that graded conclusion.  This module is the
feasibility check the ruling asked for, on three representative rules,
stated semantically (over the data a rule has, as
`Interp2/TierA.lean`'s refutation is) so that no new interpretation or
judgment has to be built to run it.

## Result

**Two of the three work; the third has a wall, and the wall is not
about λ.**

| rule | status |
|---|---|
| **I7** (λ), both regimes | ✅ `graded_lam` — *one* statement covers both, and it reads **no** codomain annotation.  This is exactly what C buys. |
| **D8** (proof irrelevance) | ✅ `graded_proof_irrel` — free, by construction: the kind-`0` conclusion does not mention the subject. |
| **I8** (app), argument at a **positive** kind | ✅ `graded_app` — both codomain regimes, one proof. |
| **I8** (app), argument at kind **`0`** — a *proof* argument | ❌ `graded_app_zero_dom_refuted`, `graded_app_zero_dom_zero_cod_refuted` |

The wall: applying a function to a **proof** needs the proof's *value*
to inhabit its proposition, and the graded conclusion at kind `0`
supplies only the proposition's truth.  Under C a proof-λ's value is a
graph — concretely `⟦fun (x : False) => x⟧ = graph _ ∅ = ∅` — which is
not `pt` and does not inhabit any true proposition.  So `app ⟦f⟧ ⟦a⟧`
is off-domain junk.

`proof_value_forced` is the reason no re-grading escapes: **equality
reflection and `propext` force propositions to be subsingletons of
`{pt}`** (a `Prop`'s interpretation must be a truth value, or
`propext`'s own graded conclusion `eqv ⟦A⟧ ⟦B⟧` inhabited — i.e.
`⟦A⟧ = ⟦B⟧` — fails for equi-inhabited propositions), so a proof whose
value is *ever consumed* must **be** `pt`.  Knowing which terms are
proofs is the λ codomain sort again.

Proof arguments are not a corner case: `Quot.lift` takes the
invariance proof, `Classical.choice` takes `¬¬A`, `Empty.rec` takes the
subject — every one of them is an `I8` step at `u = 0` in the basis
constants' own application laws.

## The guard the ruling asked for

"Kinds are conversion-invariant so regimes can't mix across `DefEq`" is
true **syntactically** (tier A's unique kinding) and **false
semantically**: `kind_not_semantic` exhibits `unitSet ∈ univ 0` and
`unitSet ∈ univ 1`.  Cumulativity means no value-level fact excludes a
`DefEq` relating a kind-`0` type to a kind-`1` one, so the grading must
be indexed by the *derivation's* kind and every graded lemma must carry
it as data — it cannot be recovered from `V`.
-/

namespace Setlec.SetR.Interp2

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- `Setlec.TT.imax`, restated here to keep this module's imports at
`Interp2/Ops.lean`. -/
def imaxN (u v : Nat) : Nat := if v = 0 then 0 else Nat.max u v

theorem imaxN_ne_zero_iff {u v : Nat} : imaxN u v ≠ 0 ↔ v ≠ 0 := by
  unfold imaxN
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv]
    exact ⟨fun _ => hv, fun _ h =>
      hv (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))⟩

/-! ## The graded conclusion -/

/-- The soundness conclusion at a type of kind `k`: membership above
`0`, **truth** at `0` — where the subject `x` is not mentioned. -/
def Real (k : Nat) (x T : V) : Prop :=
  if k = 0 then (∃ y, y ∈ˢ T) else x ∈ˢ T

theorem Real_zero {x T : V} : Real 0 x T ↔ ∃ y, y ∈ˢ T := by
  unfold Real; rw [if_pos rfl]

theorem Real_pos {k : Nat} (hk : k ≠ 0) {x T : V} : Real k x T ↔ x ∈ˢ T := by
  unfold Real; rw [if_neg hk]

theorem Real_of_mem {k : Nat} {x T : V} (h : x ∈ˢ T) : Real k x T := by
  unfold Real
  split
  · exact ⟨x, h⟩
  · exact h

/-- The grading only reads `k = 0`, like `piR`/`lamR`. -/
theorem Real_zero_agree {k k' : Nat} (hz : k = 0 ↔ k' = 0) {x T : V} :
    Real k x T ↔ Real k' x T := by
  by_cases hk : k = 0
  · rw [hk, hz.mp hk]
  · have hk' : k' ≠ 0 := fun h0 => hk (hz.mpr h0)
    rw [Real_pos hk, Real_pos hk']

/-- **D8 — proof irrelevance, for free.**  At kind `0` the conclusion
does not mention the subject, so any two subjects are interchangeable.
This is C's cleanest win: irrelevance stops being a fact about values
and becomes a property of the judgment's shape. -/
theorem graded_proof_irrel {T x y : V} (h : Real 0 x T) : Real 0 y T := by
  rw [Real_zero] at h ⊢; exact h

/-! ## I7 — the λ rule, **sound at both regimes, annotation-free**

This is what option C buys, and it does buy it: the λ's value is the
graph unconditionally, and *one* statement covers both regimes.  At
`v ≠ 0` the conclusion is `graph_mem_piSet`; at `v = 0` it is
`pt_mem_truthVal`, and the quantification direction matches on the
nose — the body's pointwise truth over the domain **is** the product's
truth. -/

theorem graded_lam {v : Nat} {A : V} {F B : V → V}
    (h : ∀ x, x ∈ˢ A → Real v (F x) (B x)) :
    Real v (graph F A) (piR v A B) := by
  by_cases hv : v = 0
  · subst hv
    rw [Real_zero, piR_zero]
    refine ⟨pt, pt_mem_truthVal fun x hx => ?_⟩
    exact (Real_zero (V := V)).mp (h x hx)
  · rw [Real_pos hv, piR_pos hv]
    exact graph_mem_piSet fun x hx => (Real_pos hv).mp (h x hx)

/-- The λ's own kind is `imax u v`; the grading is insensitive to the
difference. -/
theorem graded_lam_imax {u v : Nat} {A : V} {F B : V → V}
    (h : ∀ x, x ∈ˢ A → Real v (F x) (B x)) :
    Real (imaxN u v) (graph F A) (piR v A B) := by
  refine (Real_zero_agree (k := v) (k' := imaxN u v) ?_).mp (graded_lam h)
  constructor
  · intro h0; unfold imaxN; rw [if_pos h0]
  · intro h0
    unfold imaxN at h0
    by_cases hv : v = 0
    · exact hv
    · rw [if_neg hv] at h0
      exact absurd (Nat.le_zero.mp (h0 ▸ Nat.le_max_right u v)) hv

/-! ## I8 — the app rule -/

/-- **Sound when the argument's kind is positive.**  One proof for both
codomain regimes: at `v = 0` the product's truth *is* the pointwise
fibre truth (the squash-regime modus ponens), at `v ≠ 0` it is
`app_mem_piR_pos`. -/
theorem graded_app {u v : Nat} (hu : u ≠ 0) {A a f : V} {B : V → V}
    (hf : Real (imaxN u v) f (piR v A B)) (ha : Real u a A) :
    Real v (app f a) (B a) := by
  have ha' : a ∈ˢ A := (Real_pos hu).mp ha
  by_cases hv : v = 0
  · subst hv
    have hf0 : Real 0 f (piR 0 A B) := by
      have : imaxN u 0 = 0 := by unfold imaxN; rw [if_pos rfl]
      rwa [this] at hf
    rw [Real_zero, piR_zero] at hf0
    obtain ⟨y, hy⟩ := hf0
    rw [Real_zero]
    exact of_mem_truthVal hy a ha'
  · have hfm : f ∈ˢ piR v A B :=
      (Real_pos (imaxN_ne_zero_iff.mpr hv)).mp hf
    rw [Real_pos hv]
    exact app_mem_piR_pos hv hfm ha'

/-! ## The wall: a **proof** argument

Both refutations use `a := ∅`, which is not an arbitrary junk value:
under option C it is the value of `fun (x : False) => x`, since
`⟦False⟧ = ∅` and a λ is the graph of its body over its domain
(`graph F ∅ = ∅`).  So the counterexample is realized by an ordinary
proof term. -/

/-- The fibre family used below is a legitimate `Sort 1`-valued one:
truth values live in every universe by cumulativity. -/
theorem eqvFamily_mem_univ_one (x y : V) : eqv x y ∈ˢ (univ 1 : V) :=
  univ_mono (Nat.zero_le 1) _ (eqv_mem_univ x y)

/-- **No graded `app` rule is sound at a `Prop` domain, positive
codomain.**  Witness: `A = {•}` (true), fibres `B x = ⟦x = •⟧` (a
`Sort 1`-valued family by `eqvFamily_mem_univ_one`),
`f = graph (fun _ => •) {•}`, and the *proof* argument `a = ∅`.  Then
`app f ∅ = ∅` off-domain, while `B ∅ = ⟦∅ = •⟧` is false — so nothing
inhabits the fibre and the graded conclusion cannot hold. -/
theorem graded_app_zero_dom_refuted :
    ¬ ∀ (v : Nat) (A a f : V) (B : V → V),
        Real (imaxN 0 v) f (piR v A B) → Real 0 a A → Real v (app f a) (B a) := by
  intro hrule
  have hf : Real (imaxN 0 1) (graph (fun _ => (pt : V)) unitSet)
      (piR 1 (unitSet : V) fun x => eqv x pt) := by
    rw [Real_pos (imaxN_ne_zero_iff.mpr Nat.one_ne_zero), piR_pos Nat.one_ne_zero]
    refine graph_mem_piSet fun x hx => ?_
    rw [mem_unitSet_iff.mp hx]
    exact pt_mem_eqv_self pt
  have ha : Real 0 (empty : V) (unitSet : V) :=
    Real_zero.mpr ⟨pt, pt_mem_unitSet⟩
  have hgoal := hrule 1 unitSet empty (graph (fun _ => (pt : V)) unitSet)
    (fun x => eqv x pt) hf ha
  rw [Real_pos Nat.one_ne_zero] at hgoal
  exact pt_ne_empty (mem_eqv hgoal).symm

/-- **…and not at a `Prop` domain with a `Prop` codomain either.**
Same witness, read at kind `0`: the product is true, the domain is
true, and the fibre at the proof's value `∅` is `⟦∅ = •⟧` — false. -/
theorem graded_app_zero_dom_zero_cod_refuted :
    ¬ ∀ (A a f : V) (B : V → V),
        Real 0 f (piR 0 A B) → Real 0 a A → Real 0 (app f a) (B a) := by
  intro hrule
  have hf : Real 0 (pt : V) (piR 0 unitSet fun x => eqv x pt) := by
    rw [Real_zero, piR_zero]
    exact ⟨pt, pt_mem_truthVal fun x hx =>
      ⟨pt, mem_unitSet_iff.mp hx ▸ pt_mem_eqv_self x⟩⟩
  have ha : Real 0 (empty : V) (unitSet : V) :=
    Real_zero.mpr ⟨pt, pt_mem_unitSet⟩
  have hgoal := hrule unitSet empty pt (fun x => eqv x pt) hf ha
  rw [Real_zero] at hgoal
  obtain ⟨y, hy⟩ := hgoal
  exact pt_ne_empty (mem_eqv hy).symm

/-- **The root cause, and why no re-grading escapes it.**  Equality
reflection and `propext` force a proposition's interpretation to be a
subset of the canonical singleton; so if a proof's value is required to
inhabit *every* true proposition it is offered to — which is exactly
what `I8` at a `Prop` domain asks — then that value **is** the
canonical proof.  Recovering "which terms are proofs" is the λ codomain
sort all over again. -/
theorem proof_value_forced {a : V}
    (h : ∀ T : V, T ∈ˢ (univZero : V) → (∃ y, y ∈ˢ T) → a ∈ˢ T) : a = pt :=
  mem_unitSet_iff.mp
    (h unitSet (mem_univZero.mpr (Subset.refl _)) ⟨pt, pt_mem_unitSet⟩)

/-- Under option C a proof-λ's value really is not the canonical proof:
`⟦fun (x : False) => …⟧ = graph _ ∅ = ∅ ≠ •`.  So the refutations above
are reachable, not hypothetical. -/
theorem proof_lam_value_ne_pt (F : V → V) :
    graph F (empty : V) = (empty : V) ∧ (empty : V) ≠ pt := by
  refine ⟨eq_empty fun z hz => ?_, Ne.symm pt_ne_empty⟩
  obtain ⟨x, hx, -⟩ := mem_graph.mp hz
  exact not_mem_empty x hx

/-! ## The guard -/

/-- **Kinds are not semantically determined.**  Cumulativity puts the
same set in `univ 0` and `univ 1`, so no value-level fact excludes a
`DefEq` relating a kind-`0` type to a kind-`1` one: "regimes can't mix
across `DefEq`" is a *syntactic* guarantee (tier A's unique kinding),
and every graded statement must carry its kind as data rather than
recover it from `V`. -/
theorem kind_not_semantic : ∃ T : V, T ∈ˢ (univ 0 : V) ∧ T ∈ˢ (univ 1 : V) :=
  ⟨unitSet, unitSet_mem_univ 0, unitSet_mem_univ 1⟩

end Setlec.SetR.Interp2
