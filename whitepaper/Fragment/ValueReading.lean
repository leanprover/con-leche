module

public import Fragment.UniformBeta

public section

/-!
# Reading binders off the values: the two prices

A binder of the fragment carries its domain alone (`Syntax.lean`), and
the interpretation reads its regime off the values (`SetLib.piV`,
`SetLib.lamV`): a function space is propositional exactly when every
fibre is a truth value, an abstraction is the point exactly when every
body value is.  Over a nonempty domain that says whether the body is a
proof.  Over an EMPTY domain the values say nothing, and the reading
is fixed: the function space is `{pt}`, the abstraction the point,
whatever the body's sort.  This file shows the two things that choice
costs, each as a witness.

* **`Sort (n+1)` holds the truth values.**  `False → Nat`, a type of
  sort `Type`, denotes `{pt}` (`piV_empty_not_strict`), which is no
  strict set; so the positive sorts admit every type of their universe,
  truth values included (`Lib.lean`, `typeU`).  The point itself is
  still no member of any sort (`UniformBeta.lean`, `badEnv_no_model`).

* **λ-congruence and η compare their bodies' types.**  A body may be a
  proof at some values of its variable and not at others (its type's
  fibres are truth values at some indices, strict sets at others), and
  the claim of a definitional equality says nothing where one side is
  the point.  `lam_congr_untyped_unsound`: in a model of the empty
  environment, the λ-congruence rule WITHOUT its type premises — both
  of whose premises the checker derives (`refl` on the domains, β then
  `refl` on the bodies) — would equate two well-denoted λs that are
  not the point and denote different graphs.  The witness is

      fun (x : Prop) => (fun (h : E x) => h) n   ≡   fun (x : Prop) => n

  with `E` sending `True` to `Prop` and `False` to `False`, and
  `n := True`: at `x := False` the left body is an abstraction over an
  empty domain applied — the point — and the right body is `True`.
  (The left λ is ill-typed: `n` is no member of `E x`.  The invariant
  is semantic, and an untyped β under the binder reaches it.)  The
  typed rule (`Rules.lean`, `DefEq.lam`) infers both bodies' types
  under the binder and compares them; then both bodies lie in one type
  at every value, which holds the point or nothing else.
-/

namespace Fragment

open SetLib Expr Classical

universe w

variable {V : Type w} [SetLib V]

/-! ## The positive sorts hold `{pt}` -/

/-- A function space over an empty domain is `{pt}`, which is no strict set;
so a positive sort, which holds `False → Nat`, holds a set that is not
strict. -/
theorem piV_empty_not_strict {A : V} {B : V → V} (h : ∀ x, ¬ x ∈ˢ A) :
    ¬ Strict (piV A B) := by
  rw [piV_of_empty h]; exact fun hs => hs.2 (mem_one.mpr rfl)

/-! ## Untyped λ-congruence is unsound -/

/-- A truth value is `{pt}` or empty. -/
theorem tv_cases {x : V} (hx : x ∈ˢ univ 0) : x = one ∨ x = truthVal False := by
  by_cases h : pt ∈ˢ x
  · exact Or.inl (eq_one_of_mem_univ_zero hx h)
  · refine Or.inr (ext fun z => ⟨fun hz => ?_, fun hz => absurd (of_mem_truthVal hz) id⟩)
    exact absurd (eq_pt_of_mem_univ_zero hx hz ▸ hz) h

/-- The family constant `E : Prop → Type`. -/
@[expose] def eName : Name := "E"

/-- The constant `n : Prop`. -/
@[expose] def nName : Name := "n"

/-- `(fun (h : E x) => h) n`, under `x : Prop`. -/
@[expose] def mixedBody : Expr :=
  .app (.lam (.app (.const eName []) (.bvar 0)) (.bvar 0)) (.const nName [])

/-- `fun (x : Prop) => (fun (h : E x) => h) n`. -/
@[expose] def lamMixed : Expr := .lam (.sort .zero) mixedBody

/-- `fun (x : Prop) => n`. -/
@[expose] def lamConst : Expr := .lam (.sort .zero) (.const nName [])

/-- The witness model: `E` sends `True` to `Prop`'s set and every other
truth value to the empty set, `n` is `True`. -/
noncomputable def mixedM : Name → List Nat → V := fun c _ =>
  if c = eName then graph (fun x => if x = one then typeU 0 else truthVal False) (typeU 0)
  else if c = nName then one else pt

theorem mixedM_E (ls : List Nat) :
    (mixedM eName ls : V) =
      graph (fun x => if x = one then typeU 0 else truthVal False) (typeU 0) := by
  simp [mixedM]

theorem mixedM_n (ls : List Nat) : (mixedM nName ls : V) = one := by
  simp [mixedM, eName, nName]

theorem one_mem_typeU_zero : (one : V) ∈ˢ typeU 0 :=
  mem_typeU_zero.mpr one_mem_univ_zero

theorem false_mem_typeU_zero : (truthVal False : V) ∈ˢ typeU 0 :=
  mem_typeU_zero.mpr (truthVal_mem_univ_zero False)

theorem one_ne_pt : (one : V) ≠ pt := ne_pt_of_mem_univ_zero one_mem_univ_zero

theorem IsTy_one : IsTy (one : V) := Or.inl one_mem_univ_zero

section
variable (φ : Name → Nat) (ρ : Nat → V)

/-- `E x`'s value. -/
theorem interp_Ex {x : V} (hx : x ∈ˢ typeU 0) :
    interp mixedM φ (cons x ρ) (.app (.const eName []) (.bvar 0)) =
      if x = one then typeU 0 else truthVal False := by
  rw [interp_app, interp_const, interp_bvar, cons_zero, mixedM_E, app_graph hx]

theorem IsTy_interp_Ex {x : V} (hx : x ∈ˢ typeU 0) :
    IsTy (interp mixedM φ (cons x ρ) (.app (.const eName []) (.bvar 0))) := by
  rw [interp_Ex φ ρ hx]
  split
  · exact IsTy_typeU 0
  · exact Or.inl (truthVal_mem_univ_zero False)

/-- The left body: `True` where `x` is `True`, the point elsewhere. -/
theorem interp_mixedBody {x : V} (hx : x ∈ˢ typeU 0) :
    interp mixedM φ (cons x ρ) mixedBody = if x = one then one else pt := by
  have hlam : interp mixedM φ (cons x ρ) (.lam (.app (.const eName []) (.bvar 0)) (.bvar 0)) =
      lamV (if x = one then typeU 0 else truthVal False) fun h => h := by
    rw [interp_lam, interp_Ex φ ρ hx]; rfl
  rw [mixedBody, interp_app, hlam, interp_const, mixedM_n]
  split
  · exact app_lamV one_mem_typeU_zero
  · rw [lamV_of_empty fun z hz => of_mem_truthVal hz, app_pt]

theorem WellDenoted_Ex {x : V} (hx : x ∈ˢ typeU 0) :
    WellDenoted mixedM φ (cons x ρ) (.app (.const eName []) (.bvar 0)) := by
  rw [WellDenoted_app]
  refine ⟨trivial, trivial, appliesTo_of_mem_piR (p := false) (B := fun _ => typeU 1) ?_
    (IsTy_typeU 0) hx⟩
  rw [interp_const, mixedM_E, piR_false]
  refine graph_mem_piSet fun y _ => ?_
  split
  · exact typeU_mem_typeU_succ 0
  · exact (mem_typeU_pos (by omega)).mpr
      ⟨univ_mono (Nat.zero_le 1) (truthVal_mem_univ_zero False),
        Or.inl (truthVal_mem_univ_zero False)⟩

theorem WellDenoted_mixedBody {x : V} (hx : x ∈ˢ typeU 0) :
    WellDenoted mixedM φ (cons x ρ) mixedBody := by
  have hinner : WellDenoted mixedM φ (cons x ρ) (.lam (.app (.const eName []) (.bvar 0)) (.bvar 0)) := by
    rw [WellDenoted_lam]
    exact ⟨WellDenoted_Ex φ ρ hx, IsTy_interp_Ex φ ρ hx, fun _ _ => trivial⟩
  rw [mixedBody, WellDenoted_app]
  refine ⟨hinner, trivial, appliesTo_of_mem_piV (A := typeU 0)
    (B := fun _ => if x = one then typeU 0 else one) ?_
    (IsTy_typeU 0) (by rw [interp_const, mixedM_n]; exact one_mem_typeU_zero)⟩
  show _ ∈ˢ piV _ _
  rw [interp_lam, interp_Ex φ ρ hx]
  by_cases h1 : x = one
  · simp only [h1, ite_true]
    exact lamV_mem (fun y hy => hy) fun _ _ => IsTy_typeU 0
  · simp only [h1, ite_false]
    rw [lamV_of_empty fun z hz => of_mem_truthVal hz,
      ← lamV_eq_pt (A := (typeU 0 : V)) (F := fun _ => pt) fun _ _ => rfl]
    exact lamV_mem (fun _ _ => mem_one.mpr rfl) fun _ _ => IsTy_one

end

/-- **Untyped lambda congruence is unsound** in the value-driven model: the
rule's two premises are checker derivations — the domains by `refl`,
the bodies by β then `refl` — yet in a model of the empty environment
the two lambdas are well-denoted, neither is the point, and they differ. -/
theorem lam_congr_untyped_unsound [LevelOracle] (φ : Name → Nat) (ρ : Nat → V) :
    DefEq Env.empty [] (.sort .zero) (.sort .zero) ∧
    DefEq Env.empty [.sort .zero] mixedBody (.const nName []) ∧
    ¬ DefEqSem (EnvModel.empty (mixedM (V := V))) φ [] lamMixed lamConst := by
  refine ⟨.refl, .redL .beta .refl, fun h => ?_⟩
  have hw₁ : WellDenoted mixedM φ ρ lamMixed := by
    rw [lamMixed, WellDenoted_lam]
    exact ⟨trivial, IsTy_typeU 0, fun x hx => WellDenoted_mixedBody φ ρ hx⟩
  have hw₂ : WellDenoted mixedM φ ρ lamConst := by
    rw [lamConst, WellDenoted_lam]
    exact ⟨trivial, IsTy_typeU 0, fun _ _ => trivial⟩
  have hn₁ : interp mixedM φ ρ lamMixed ≠ pt := by
    rw [lamMixed, interp_lam]
    refine lamV_ne_pt_of (x := one) one_mem_typeU_zero ?_
    rw [interp_mixedBody φ ρ one_mem_typeU_zero, ite_eq_left rfl]; exact one_ne_pt
  have hn₂ : interp mixedM φ ρ lamConst ≠ pt := by
    rw [lamConst, interp_lam]
    refine lamV_ne_pt_of (x := one) one_mem_typeU_zero ?_
    rw [interp_const, mixedM_n]; exact one_ne_pt
  have heq : interp mixedM φ ρ lamMixed = interp mixedM φ ρ lamConst :=
    h ρ trivial hw₁ hw₂ hn₁ hn₂
  have happ := congrArg (fun f => SetLib.app f (truthVal False)) heq
  simp only [lamMixed, lamConst, interp_lam, interp_sort, Level.eval_zero] at happ
  rw [app_lamV false_mem_typeU_zero, app_lamV false_mem_typeU_zero,
    interp_mixedBody φ ρ false_mem_typeU_zero, interp_const, mixedM_n,
    ite_eq_right one_ne_truthVal_false.symm] at happ
  exact one_ne_pt happ.symm

end Fragment
