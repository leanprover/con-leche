import Setlec.Model.BasisVal

/-!
# Why raw storage needs an annotation witness (task #100)

Formal witnesses for the *refutation* of the third candidate design for
annotation-free storage — the reason `RawEnvModel`
(`Setlec/Model/RawEnv.lean`) carries an annotated shadow environment
rather than dropping annotation data from the model altogether.  The
refuted design: interpret raw trees with
the binder classifier derived *semantically* (least-`u` variant) or
computed *structurally* alongside the recursion as a tuple component
(structural variant), so that neither the environment nor `EnvModel`
carries any annotation data.

## Checkpoint 1 — positive

`SetTheory.pi`/`lam` read their level argument **only through the
`v = 0` test** (`pi_pos`/`lam_pos`; `pi_level_indifferent` below).  So
the interpretation's value never needs a *level* at binders — only the
one-bit Prop-or-not classifier (full levels enter the model's values
only at `.sort` leaves, which are self-contained).  Any replacement
design must supply exactly this bit, plus the `univ (eval ·)` facts in
the *invariant* clauses.

## Checkpoint 2 / the refutation — negative

The bit cannot be recovered from the semantic values (`least-u`
variant), and it cannot be computed structurally from subterm tuples
(structural variant):

* **Value recovery is unsound** — witnessed below by two exact
  coincidences of the derived construction (they hold in *every*
  interface model, since the operators are derived):
  `⟦Nat.succ Nat.zero⟧ = pt` (the von Neumann `1` *is* the proof
  point, `natSuccVal_zero_eq_pt`) and `⟦PUnit⟧ = truthVal True`
  (a `Type`-level type's value *is* a truth value,
  `punitVal_eq_truthVal_true`).  Consequently `fun (_ : PUnit) =>
  (1 : Nat)` and `fun (_ : PUnit) => True.intro` present *identical*
  data to the λ-clause — same domain value, same body-value function
  (constantly `pt`) — yet require *different* interpretations (a graph
  resp. the proof point: `lam_interp_not_value_determined`).  So no
  function of the λ-clause's semantic inputs can interpret λ, and no
  predicate of a type's *value* decides Prop-ness.

* **Structural composition fails at applications and projections** —
  meta-level (see the spike report): the classifier of `∀ x : Nat,
  P x` is the evaluated result sort of `P`, which no finite per-node
  component of `P`'s tuple can carry (`Nat.imax` preserves the
  *proof*-bit through application — `b(f a) = b(f)` — but destroys the
  *sort* of the codomain, and the ∀-classifier needs the latter);
  static "universe skeletons" die on whnf-dependent classifier sorts
  (large elimination: `∀ y : Nat, F true` with `F : ∀ b, motive b`,
  `motive true ≡ι Prop` — the classifier is computable only by
  *reduction* of the inferred type, i.e. by exactly the inference the
  annotation pass / a `codOf` memo performs); and `b(.proj s i e)`
  needs the parent's level instantiation, which is neither in the node
  nor in `e`'s tuple.  Closing the recursion semantically (components
  as value-indexed universe *families*) is possible in principle but
  is full semantic typing (lean4lean-model territory) — a rewrite of
  the model layer, not a refactor.
-/

namespace Setlec

open SetTheory

variable {V : Type u} [SetTheory V]

/-- Checkpoint 1: the dependent product reads its level only through
the zero test — interpretation values need the Prop-bit, never the
level. -/
theorem pi_level_indifferent {u v : Nat} (hu : u ≠ 0) (hv : v ≠ 0)
    (A : V) (B : V → V) : pi u A B = pi v A B := by
  rw [pi_pos hu, pi_pos hv]

/-- The von Neumann `1` is the proof point: `{∅} = pt`. -/
theorem vsucc_empty_eq_pt : vsucc (empty : V) = pt := by
  apply SetTheory.ext
  intro z
  rw [mem_vsucc, mem_pt]
  constructor
  · rintro (hz | rfl)
    · exact absurd hz (not_mem_empty z)
    · rfl
  · rintro rfl
    exact Or.inr rfl

/-- The basis value of the numeral `1` — `Nat.succ` applied to
`Nat.zero` — **is the proof point**: prop-ness of a value's *type* is
not readable off the value. -/
theorem natSuccVal_zero_eq_pt (ψ : Name → Nat) :
    SetTheory.app (natSuccVal V ψ) natzero = (pt : V) := by
  rw [natSuccVal]
  rw [app_lam' (v := 1) (F := natsucc) (B := fun _ => (omega : V))
    natzero_mem (fun x hx => natsucc_mem hx) (fun h => absurd h (by decide))]
  simp only [natsucc, natzero]
  exact vsucc_empty_eq_pt (V := V)

/-- The pinned value of the `Type`-level `PUnit` **is a truth value**
(the one `True` would get): Prop-ness of a *type* is not readable off
the type's value either. -/
theorem punitVal_eq_truthVal_true :
    pinnedVal V punitName ψ = truthVal True := by
  rw [truthVal_eq_unitSet trivial]
  rfl

/-- The refutation kernel for every "no-data" λ-clause: the λ-terms
`fun (_ : PUnit) => (1 : Nat)` and `fun (_ : PUnit) => True.intro`
present **identical** semantic inputs — the same domain value
(`⟦PUnit⟧ = unitSet`) and the same body-value function (constantly
`pt`, first conjunct) — yet their required interpretations (the graph
resp. the proof point, as forced by `EnvModel.mem_type` against their
`∀`-types) are **distinct** (second conjunct).  Interpretation at λ is
therefore not a function of the λ-clause's semantic data: the
Prop-collapse bit must be supplied from outside the values. -/
theorem lam_interp_not_value_determined :
    ((fun _ : V => vsucc (empty : V)) = (fun _ : V => (pt : V))) ∧
    SetTheory.lam 1 (unitSet : V) (fun _ : V => vsucc empty) ≠
      SetTheory.lam 0 (unitSet : V) (fun _ : V => pt) := by
  refine ⟨funext fun _ => vsucc_empty_eq_pt, ?_⟩
  rw [lam_pos (by decide : (1 : Nat) ≠ 0), lam_zero]
  exact graph_ne_pt

end Setlec
