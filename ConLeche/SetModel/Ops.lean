module

public import ConLeche.SetTheory.Basic

@[expose] public section

/-!
# The two-regime function space and abstraction (task #151, tier B; task #342, L14a)

`piR v`/`lamR v` are the function space and abstraction at an explicit
regime numeral; `piV`/`lamV` (the last section) read the numeral off
the values, and are what the interpretation and `Denotes` use.

* **`v = 0` — the truth-value regime.**  `piR 0 A B h` is `piProp A B`,
  the truth value `[∀ x ∈ A, B x inhabited]`, `lamR 0 A F h` is the
  canonical proof.  Propositions are subsets of the canonical
  one-element set `unitSet = {pt}`, so proof irrelevance and
  impredicativity are both immediate: a Π-type landing in `Prop` is
  small whatever its domain is (`piR_zero_mem_univZero`).
* **`v ≠ 0` — the graph regime.**  `piR v A B h` is `piSet A B h`, the
  set of total single-valued function graphs over `A`; `lamR v A F h` is
  the literal graph `graph F A h`.  A member is a graph, never `pt`, and
  determines its own domain (`graph_dom_unique`).

`piV A B h` is the truth-value regime exactly when every fibre over `A`
is a truth value; `lamV A F h` exactly when every body value over `A` is
the point.  Over a nonempty domain this is the regime the binder's
codomain sort gives; over an empty domain both read "proposition".

All set-forming operators (`piR`, `lamR`, `piV`, `lamV`) are
proof-carrying and zero-junk, taking explicit `HasSigmaPairs A B` or
`HasGraph A F` witnesses, and export full `DefFun` closure lemmas.
-/

namespace ConLeche.SetModel

open SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The truth-value function space `[∀ x ∈ A, B x inhabited]` at `Prop`
codomain. -/
noncomputable def piProp (A : V) (B : V → V) : V :=
  truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x)

theorem mem_piProp {A z : V} {B : V → V} :
    z ∈ˢ piProp A B ↔ (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) ∧ z = pt :=
  mem_truthVal

theorem piProp_mem_univZero {A : V} {B : V → V} :
    piProp A B ∈ˢ (univZero : V) :=
  truthVal_mem_univZero _

theorem piProp_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    piProp A B = piProp A B' :=
  truthVal_congr
    ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩

theorem piProp_ext {A A' : V} {B B' : V → V} (hA : A = A')
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piProp A B = piProp A' B' := by
  subst hA; exact piProp_congr h

theorem DefFun.piProp_apply {k : Nat}
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => piProp (A env) (fun x => B (fcons x env)) := by
  unfold piProp
  have hB' : DefFun (k + 2) fun w => B (fcons (w 1) (ftail (ftail w))) :=
    hB.weaken.congr fun w => congrArg B (fcons_zero_ftail (ftail w)).symm
  exact DefFun.truthVal_apply
    (DefRel.bForall_curry hA
      (DefRel.exists_curry (DefRel.mem_apply (DefFun.proj 0) hB')))

theorem DefFun.piProp_apply_curry {k : Nat}
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => piProp (A env) (fun x => B x env) :=
  DefFun.piProp_apply (B := fun v => B (v 0) (ftail v)) hA hB

theorem hasSigmaPairs_of_empty {A : V} {B : V → V} (h : ∀ x, ¬ x ∈ˢ A) :
    HasSigmaPairs A B := by
  have he : A = empty := eq_empty h
  subst he
  exact hasSigmaPairs_empty B

theorem hasGraph_of_empty {A : V} {F : V → V} (h : ∀ x, ¬ x ∈ˢ A) :
    HasGraph A F := by
  have he : A = empty := eq_empty h
  subst he
  exact hasGraph_empty F

/-- The dependent function space at codomain sort `v`: a truth value at `0`,
the set of function graphs above it. -/
noncomputable def piR (v : Nat) (A : V) (B : V → V) (h : HasSigmaPairs A B) : V :=
  if v = 0 then piProp A B else piSet A B h

/-- Abstraction at codomain sort `v`: the canonical proof at `0`, the
literal function graph above it. -/
noncomputable def lamR (v : Nat) (A : V) (F : V → V) (h : HasGraph A F) : V :=
  if v = 0 then pt else graph F A h

/-! ## The two branches -/

theorem piR_zero_eq_piProp {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    piR 0 A B h = piProp A B := ite_eq_left rfl

theorem piR_zero {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    piR 0 A B h = truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) := ite_eq_left rfl

theorem piR_pos {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    piR v A B h = piSet A B h := ite_eq_right hv

theorem lamR_zero {A : V} {F : V → V} {h : HasGraph A F} :
    lamR 0 A F h = (pt : V) := ite_eq_left rfl

theorem lamR_pos {v : Nat} (hv : v ≠ 0) {A : V} {F : V → V} {h : HasGraph A F} :
    lamR v A F h = graph F A h := ite_eq_right hv

/-! ## Congruence and `DefFun` closure for `piR` / `lamR` -/

theorem piR_congr {v : Nat} {A : V} {B B' : V → V}
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR v A B hB = piR v A B' hB' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [piR_zero_eq_piProp, piR_zero_eq_piProp]
    exact piProp_congr h
  · rw [piR_pos (Nat.pos_iff_ne_zero.mp hv), piR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact piSet_congr hB hB' h

theorem piR_ext {v : Nat} {A A' : V} {B B' : V → V} (hA : A = A')
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A' B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR v A B hB = piR v A' B' hB' := by
  subst hA; exact piR_congr hB hB' h

theorem lamR_congr {v : Nat} {A : V} {F F' : V → V}
    (hF : HasGraph A F) (hF' : HasGraph A F')
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR v A F hF = lamR v A F' hF' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, lamR_zero]
  · rw [lamR_pos (Nat.pos_iff_ne_zero.mp hv), lamR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_congr hF hF' h

theorem lamR_ext {v : Nat} {A A' : V} {F F' : V → V} (hA : A = A')
    (hF : HasGraph A F) (hF' : HasGraph A' F')
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR v A F hF = lamR v A' F' hF' := by
  subst hA; exact lamR_congr hF hF' h

theorem DefFun.piR_apply {k : Nat} (v : Nat)
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B (fcons x env))}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => piR v (A env) (fun x => B (fcons x env)) (h env) := by
  unfold piR
  by_cases hv : v = 0
  · simp only [hv, ↓reduceIte]
    exact DefFun.piProp_apply hA hB
  · simp only [hv, ↓reduceIte]
    exact DefFun.piSet_apply hA hB

theorem DefFun.piR_apply_curry {k : Nat} (v : Nat)
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B x env)}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => piR v (A env) (fun x => B x env) (h env) :=
  DefFun.piR_apply v (B := fun v => B (v 0) (ftail v)) hA hB

theorem DefFun.lamR_apply {k : Nat} (v : Nat)
    {F : (Fin (k + 1) → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F (fcons x env))}
    (hF : DefFun (k + 1) F) (hA : DefFun k A) :
    DefFun k fun env => lamR v (A env) (fun x => F (fcons x env)) (h env) := by
  unfold lamR
  by_cases hv : v = 0
  · simp only [hv, ↓reduceIte]
    exact DefFun.pt
  · simp only [hv, ↓reduceIte]
    exact DefFun.graph_apply hF hA

theorem DefFun.lamR_apply_curry {k : Nat} (v : Nat)
    {F : V → (Fin k → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F x env)}
    (hF : DefFun (k + 1) fun v => F (v 0) (ftail v)) (hA : DefFun k A) :
    DefFun k fun env => lamR v (A env) (fun x => F x env) (h env) :=
  DefFun.lamR_apply v (F := fun v => F (v 0) (ftail v)) hF hA

/-! ## Introduction, elimination, beta, eta -/

/-- Introduction: fibre-wise members abstract into the function space.  At
`v = 0` the premise itself witnesses every fibre inhabited. -/
theorem lamR_mem {v : Nat} {A : V} {F B : V → V}
    {hG : HasGraph A F} {hS : HasSigmaPairs A B}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR v A F hG ∈ˢ piR v A B hS := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, piR_zero]
    exact pt_mem_truthVal fun x hx => ⟨F x, hF x hx⟩
  · rw [lamR_pos (Nat.pos_iff_ne_zero.mp hv), piR_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_mem_piSet hF

/-- **Proof irrelevance at function spaces**: inhabitants of a `Prop`-valued
function space are the canonical proof. -/
theorem eq_pt_of_mem_piR_zero {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piR 0 A B hS) : f = pt := by
  rw [piR_zero] at hf; exact eq_pt_of_mem_truthVal hf

/-- **Squash-regime introduction from inhabitation.**  At `v = 0` the
function space is a truth value, so membership of the canonical proof needs
only that every fibre is *inhabited* — strictly weaker than
`lamR_mem`'s pointwise `F x ∈ˢ B x`, and the form every tower whose
value carries no regime tag has to use at kind `0`
(`Semantics/BasisOk.lean`'s `.psigmaMk` case). -/
theorem pt_mem_piR_zero {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) : (pt : V) ∈ˢ piR 0 A B hS := by
  rw [piR_zero]; exact pt_mem_truthVal h

/-- The pointwise form. -/
theorem pt_mem_piR_zero_of {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x) : (pt : V) ∈ˢ piR 0 A B hS :=
  pt_mem_piR_zero fun x hx => ⟨pt, h x hx⟩

/-- Elimination.  The fibre premise is needed only at `v = 0`, where
the fibres must be truth values. -/
theorem app_mem_piR {v : Nat} {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piR v A B hS) (ha : a ∈ˢ A)
    (hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) : app f a ∈ˢ B a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have hfp : f = pt := eq_pt_of_mem_piR_zero hf
    rw [piR_zero] at hf
    obtain ⟨y, hy⟩ := of_mem_truthVal hf a ha
    rw [hfp, app_pt]
    rwa [eq_pt_of_mem_univZero (hB0 rfl a ha) hy] at hy
  · rw [piR_pos (Nat.pos_iff_ne_zero.mp hv)] at hf
    exact app_mem_of_mem_piSet hf ha

/-- Elimination in the graph regime: no fibre premise at all. -/
theorem app_mem_piR_pos {v : Nat} {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hv : v ≠ 0) (hf : f ∈ˢ piR v A B hS) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  rw [piR_pos hv] at hf; exact app_mem_of_mem_piSet hf ha

/-- **Beta in the graph regime**: application of an abstraction on its
domain computes, with no typing premise whatsoever — it is literally
`app_graph`. -/
theorem app_lamR_pos {v : Nat} {A a : V} {F : V → V} {hG : HasGraph A F}
    (hv : v ≠ 0) (ha : a ∈ˢ A) : app (lamR v A F hG) a = F a := by
  rw [lamR_pos hv]; exact app_graph ha

/-- Graph-regime abstractions are graphs, never the proof point. -/
theorem lamR_ne_pt {v : Nat} {A : V} {F : V → V} {hG : HasGraph A F} (hv : v ≠ 0) :
    lamR v A F hG ≠ pt := by rw [lamR_pos hv]; exact graph_ne_pt

/-- **An abstraction that is not the point is the graph** — the
explicit-numeral form of the value reading's `lamV_eq_graph`
(task #342, L6).  A lemma that needs a spelled abstraction AS a graph
goes through this, with the non-point fact as its premise: under the
value reading the premise is exactly what an empty domain or a point
body fails. -/
theorem lamR_eq_graph_of_ne_pt {v : Nat} {A : V} {F : V → V} {hG : HasGraph A F}
    (h : lamR v A F hG ≠ pt) : lamR v A F hG = graph F A hG := by
  by_cases hv : v = 0
  · subst hv; exact absurd lamR_zero h
  · exact lamR_pos hv

/-- Eta: a member of a function space is the abstraction of its
applications. -/
theorem lamR_eta {v : Nat} {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piR v A B hS) : lamR v A (fun x => app f x) (hasGraph_app f A) = f := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lamR_zero, eq_pt_of_mem_piR_zero hf]
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    rw [piR_pos hv'] at hf
    rw [lamR_pos hv']
    exact eq_graph_app_of_mem_piSet hf

/-! ## The graph regime

The numeral has already decided the regime, so membership in a
positive-regime function space is *by definition* graph-hood: no consumer
dispatches on "graph or proof point". -/

/-! ## The truth-value regime -/

/-- **Impredicativity.**  A function space landing in `Prop` is a truth value
— for an arbitrary domain `A` and arbitrary fibres, with no size
condition.  This is the one place a set-theoretic model of Lean has to
say something, and here it is the `v = 0` branch of a numeral test. -/
theorem piR_zero_mem_univZero {A : V} {B : V → V} {hS : HasSigmaPairs A B} :
    piR 0 A B hS ∈ˢ (univZero : V) := by
  rw [piR_zero]; exact truthVal_mem_univZero _

/-- A function space is in the regime its numeral names: a truth value
at `v = 0`, strict above (task #342). -/
theorem Fib_piR (v : Nat) (A : V) (B : V → V) (hS : HasSigmaPairs A B) :
    Fib (decide (v = 0)) (piR v A B hS) := by
  by_cases hv : v = 0
  · subst hv; simp only [decide_true, Fib_true]; exact piR_zero_mem_univZero
  · simp only [hv, decide_false, Fib_false]; rw [piR_pos hv]; exact strict_piSet

/-- A function space is a type. -/
theorem IsTy_piR (v : Nat) (A : V) (B : V → V) (hS : HasSigmaPairs A B) :
    IsTy (piR v A B hS) :=
  IsTy_of_Fib (Fib_piR v A B hS)

/-! ## What a value may be applied to

The semantic invariant's application clause, on values: the point may be
applied to anything (`app_pt`), a graph whose domain is a type to the
members of its domain, and any other set to nothing.  It is well-defined,
as a graph determines its domain (`graph_dom_unique`). -/

/-- **`f` applies to `a`**: `f` is the point, or a graph whose domain is a
type holding `a`. -/
def AppliesTo (f a : V) : Prop :=
  f = pt ∨ ∃ (F : V → V) (A : V) (h : HasGraph A F), f = graph F A h ∧ IsTy A ∧ a ∈ˢ A

theorem appliesTo_pt (a : V) : AppliesTo (pt : V) a := Or.inl rfl

theorem appliesTo_graph {F : V → V} {A a : V} {h : HasGraph A F} :
    AppliesTo (graph F A h) a ↔ IsTy A ∧ a ∈ˢ A := by
  refine ⟨fun ha => ?_, fun ha => Or.inr ⟨F, A, h, rfl, ha⟩⟩
  rcases ha with he | ⟨F', A', h', he, ha⟩
  · exact absurd he graph_ne_pt
  · exact graph_dom_unique he ▸ ha

/-- A member of a graph-regime function space whose domain is a type
applies to the members of the domain. -/
theorem appliesTo_of_mem_piSet {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piSet A B hS) (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a := by
  rw [← eq_graph_app_of_mem_piSet hf]; exact appliesTo_graph.mpr ⟨hA, ha⟩

/-- The same at either regime: a member of a propositional function space
is the point. -/
theorem appliesTo_of_mem_piR {v : Nat} {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piR v A B hS) (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a := by
  by_cases hv : v = 0
  · subst hv; rw [eq_pt_of_mem_piR_zero hf]; exact appliesTo_pt a
  · rw [piR_pos hv] at hf; exact appliesTo_of_mem_piSet hf hA ha

/-- A member of a function space that applies to `a`: the space's domain
is a type holding `a`. -/
theorem AppliesTo.dom {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : AppliesTo f a) (hf : f ∈ˢ piSet A B hS) : IsTy A ∧ a ∈ˢ A := by
  rw [← eq_graph_app_of_mem_piSet hf] at h; exact appliesTo_graph.mp h

theorem AppliesTo.mem {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : AppliesTo f a) (hf : f ∈ˢ piSet A B hS) : a ∈ˢ A := (h.dom hf).2

/-! ## The value-read regimes (task #342, L14a)

The interpretation's binder clauses (`Semantics/Interp.lean`) and
`Denotes`' (`ConLeche/Denotes.lean`).  The regime is not a datum but a
property of the values: a function space is a truth value exactly when
every fibre over the domain is one (`propN`), an abstraction is the
point exactly when every body value over the domain is (`ptN`).  Over a
nonempty domain this is the regime the binder's codomain sort gives;
over an empty domain both read "proposition": the function space is
`{pt}`, the abstraction the point. -/

open Classical in
/-- The function space's regime numeral: `0` when every fibre over the
domain is a truth value, `1` otherwise. -/
noncomputable def propN (A : V) (B : V → V) : Nat :=
  if ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) then 0 else 1

open Classical in
/-- The abstraction's regime numeral: `0` when every body value over
the domain is the point, `1` otherwise. -/
noncomputable def ptN (A : V) (F : V → V) : Nat :=
  if ∀ x, x ∈ˢ A → F x = pt then 0 else 1

/-- **The dependent function space, its regime read off the fibres.** -/
noncomputable def piV (A : V) (B : V → V) (h : HasSigmaPairs A B) : V :=
  piR (propN A B) A B h

/-- **The abstraction, its regime read off the body values.** -/
noncomputable def lamV (A : V) (F : V → V) (h : HasGraph A F) : V :=
  lamR (ptN A F) A F h

open Classical in
theorem propN_eq_zero {A : V} {B : V → V} :
    propN A B = 0 ↔ ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := by
  unfold propN; split <;> simp_all

open Classical in
theorem ptN_eq_zero {A : V} {F : V → V} :
    ptN A F = 0 ↔ ∀ x, x ∈ˢ A → F x = pt := by
  unfold ptN; split <;> simp_all

theorem propN_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    propN A B = propN A B' := by
  unfold propN
  rw [show (∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) ↔ (∀ x, x ∈ˢ A → B' x ∈ˢ (univZero : V)) from
    ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩]

theorem ptN_congr {A : V} {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    ptN A F = ptN A F' := by
  unfold ptN
  rw [show (∀ x, x ∈ˢ A → F x = pt) ↔ (∀ x, x ∈ˢ A → F' x = pt) from
    ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩]

theorem piV_congr {A : V} {B B' : V → V}
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piV A B hB = piV A B' hB' := by
  unfold piV; rw [propN_congr h]; exact piR_congr hB hB' h

theorem piV_ext {A A' : V} {B B' : V → V} (hA : A = A')
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A' B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piV A B hB = piV A' B' hB' := by
  subst hA; exact piV_congr hB hB' h

theorem lamV_congr {A : V} {F F' : V → V}
    (hF : HasGraph A F) (hF' : HasGraph A F')
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamV A F hF = lamV A F' hF' := by
  unfold lamV; rw [ptN_congr h]; exact lamR_congr hF hF' h

theorem lamV_ext {A A' : V} {F F' : V → V} (hA : A = A')
    (hF : HasGraph A F) (hF' : HasGraph A' F')
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamV A F hF = lamV A' F' hF' := by
  subst hA; exact lamV_congr hF hF' h

theorem DefFun.piV_apply {k : Nat}
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B (fcons x env))}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => piV (A env) (fun x => B (fcons x env)) (h env) := by
  have hcond : DefRel k fun env => ∀ x, x ∈ˢ A env → B (fcons x env) ∈ˢ (univZero : V) :=
    DefRel.bForall_curry hA
      (DefRel.mem_apply (hB.congr fun v => by rw [fcons_zero_ftail]) DefFun.univZero)
  have hite := DefFun.ite hcond (DefFun.piProp_apply hA hB) (DefFun.piSet_apply (h := h) hA hB)
  refine hite.congr fun env => ?_
  by_cases hc : ∀ x, x ∈ˢ A env → B (fcons x env) ∈ˢ (univZero : V)
  · rw [ite_eq_left hc]
    unfold piV
    rw [propN_eq_zero.mpr hc, piR_zero_eq_piProp]
  · rw [ite_eq_right hc]
    have hne : propN (A env) (fun x => B (fcons x env)) ≠ 0 :=
      fun h0 => hc (propN_eq_zero.mp h0)
    unfold piV
    rw [piR_pos hne]

theorem DefFun.piV_apply_curry {k : Nat}
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B x env)}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => piV (A env) (fun x => B x env) (h env) :=
  DefFun.piV_apply (B := fun v => B (v 0) (ftail v)) hA hB

theorem DefFun.lamV_apply {k : Nat}
    {F : (Fin (k + 1) → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F (fcons x env))}
    (hF : DefFun (k + 1) F) (hA : DefFun k A) :
    DefFun k fun env => lamV (A env) (fun x => F (fcons x env)) (h env) := by
  have hcond : DefRel k fun env => ∀ x, x ∈ˢ A env → F (fcons x env) = pt :=
    DefRel.bForall_curry hA
      (DefRel.eq_apply (hF.congr fun v => by rw [fcons_zero_ftail]) DefFun.pt)
  have hite := DefFun.ite hcond (DefFun.pt (k := k)) (DefFun.graph_apply (h := h) hF hA)
  refine hite.congr fun env => ?_
  by_cases hc : ∀ x, x ∈ˢ A env → F (fcons x env) = pt
  · rw [ite_eq_left hc]
    unfold lamV
    rw [ptN_eq_zero.mpr hc, lamR_zero]
  · rw [ite_eq_right hc]
    have hne : ptN (A env) (fun x => F (fcons x env)) ≠ 0 :=
      fun h0 => hc (ptN_eq_zero.mp h0)
    unfold lamV
    rw [lamR_pos hne]

theorem DefFun.lamV_apply_curry {k : Nat}
    {F : V → (Fin k → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F x env)}
    (hF : DefFun (k + 1) fun v => F (v 0) (ftail v)) (hA : DefFun k A) :
    DefFun k fun env => lamV (A env) (fun x => F x env) (h env) :=
  DefFun.lamV_apply (F := fun v => F (v 0) (ftail v)) hF hA

/-- **β, on the domain, with no other premise.** -/
theorem app_lamV {A a : V} {F : V → V} {hG : HasGraph A F} (ha : a ∈ˢ A) :
    app (lamV A F hG) a = F a := by
  unfold lamV
  by_cases h : ptN A F = 0
  · rw [h, lamR_zero, app_pt]; exact ((ptN_eq_zero.mp h) a ha).symm
  · exact app_lamR_pos h ha

/-- An abstraction all of whose body values are the point is the point. -/
theorem lamV_eq_pt {A : V} {F : V → V} {hG : HasGraph A F}
    (h : ∀ x, x ∈ˢ A → F x = pt) : lamV A F hG = pt := by
  unfold lamV; rw [ptN_eq_zero.mpr h, lamR_zero]

/-- An abstraction that is not the point is the graph. -/
theorem lamV_eq_graph {A : V} {F : V → V} {hG : HasGraph A F}
    (h : lamV A F hG ≠ pt) : lamV A F hG = graph F A hG :=
  lamR_eq_graph_of_ne_pt h

/-- An abstraction over a type applies to the members of its domain. -/
theorem appliesTo_lamV {A a : V} {F : V → V} {hG : HasGraph A F}
    (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo (lamV A F hG) a := by
  by_cases h : lamV A F hG = pt
  · rw [h]; exact appliesTo_pt a
  · rw [lamV_eq_graph h]; exact appliesTo_graph.mpr ⟨hA, ha⟩

/-- An abstraction with a body value that is not the point is a graph,
never the point. -/
theorem lamV_ne_pt_of {A : V} {F : V → V} {hG : HasGraph A F} {x : V}
    (hx : x ∈ˢ A) (h : F x ≠ pt) : lamV A F hG ≠ pt := by
  unfold lamV
  by_cases hb : ptN A F = 0
  · exact absurd ((ptN_eq_zero.mp hb) x hx) h
  · exact lamR_ne_pt hb

/-- A function space is a type. -/
theorem IsTy_piV {A : V} {B : V → V} {hS : HasSigmaPairs A B} :
    IsTy (piV A B hS) := IsTy_piR _ _ _ hS

/-- A member of a function space that is not the point is a member of
the graph space. -/
theorem mem_piSet_of_mem_piV {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piV A B hS) (hn : f ≠ pt) : f ∈ˢ piSet A B hS := by
  unfold piV at hf
  by_cases hb : propN A B = 0
  · rw [hb] at hf; exact absurd (eq_pt_of_mem_piR_zero hf) hn
  · rwa [piR_pos hb] at hf

/-- **Elimination**, with no fibre premise: where the fibres are truth
values the function is the point and so is its value, which inhabits
the (inhabited) fibre. -/
theorem app_mem_piV {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piV A B hS) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  unfold piV at hf
  by_cases hb : propN A B = 0
  · rw [hb] at hf
    exact app_mem_piR hf ha fun _ => propN_eq_zero.mp hb
  · exact app_mem_piR_pos hb hf ha

/-- **A typed application meets the application clause**: a member of a
function space applies to an argument of its domain, the domain a type. -/
theorem appliesTo_of_mem_piV {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piV A B hS) (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a :=
  appliesTo_of_mem_piR hf hA ha

/-- **Introduction**: body values in fibres that are types abstract into
the function space.  Where every fibre is a truth value every body value
is the point, and so is the abstraction; where one fibre is not, it is
strict, its body value is not the point, and the abstraction is the
graph. -/
theorem lamV_mem {A : V} {F B : V → V} {hG : HasGraph A F} {hS : HasSigmaPairs A B}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) (hB : ∀ x, x ∈ˢ A → IsTy (B x)) :
    lamV A F hG ∈ˢ piV A B hS := by
  unfold piV
  by_cases hp : propN A B = 0
  · have h0 := propN_eq_zero.mp hp
    rw [hp, lamV_eq_pt fun x hx => eq_pt_of_mem_univZero (h0 x hx) (hF x hx)]
    exact pt_mem_piR_zero fun x hx => ⟨F x, hF x hx⟩
  · have : ¬ ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := fun h => hp (propN_eq_zero.mpr h)
    obtain ⟨x₀, hx₀, hB₀⟩ : ∃ x, x ∈ˢ A ∧ ¬ B x ∈ˢ (univZero : V) :=
      Classical.byContradiction fun hne => this fun x hx =>
        Classical.byContradiction fun h => hne ⟨x, hx, h⟩
    have hs : Strict (B x₀) := (hB x₀ hx₀).resolve_left hB₀
    rw [lamV_eq_graph (lamV_ne_pt_of hx₀ (ne_pt_of_mem_strict hs (hF x₀ hx₀))), piR_pos hp]
    exact graph_mem_piSet hF

/-- **η**: a member of a function space whose fibres are types is the
abstraction of its applications. -/
theorem lamV_eta {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piV A B hS) (hB : ∀ x, x ∈ˢ A → IsTy (B x)) :
    lamV A (fun x => app f x) (hasGraph_app f A) = f := by
  by_cases hn : f = pt
  · subst hn
    exact lamV_eq_pt fun x _ => app_pt x
  · have hf' := mem_piSet_of_mem_piV hf hn
    have hp : propN A B ≠ 0 := fun h => by
      unfold piV at hf; rw [h] at hf; exact hn (eq_pt_of_mem_piR_zero hf)
    have : ¬ ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := fun h => hp (propN_eq_zero.mpr h)
    obtain ⟨x₀, hx₀, hB₀⟩ : ∃ x, x ∈ˢ A ∧ ¬ B x ∈ˢ (univZero : V) :=
      Classical.byContradiction fun hne => this fun x hx =>
        Classical.byContradiction fun h => hne ⟨x, hx, h⟩
    have hs : Strict (B x₀) := (hB x₀ hx₀).resolve_left hB₀
    rw [lamV_eq_graph (lamV_ne_pt_of hx₀
      (ne_pt_of_mem_strict hs (app_mem_of_mem_piSet hf' hx₀)))]
    exact eq_graph_app_of_mem_piSet hf'

/-- A member of a function space whose fibres hold only the point is
the point. -/
theorem eq_pt_of_mem_piV {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) (hf : f ∈ˢ piV A B hS) : f = pt := by
  unfold piV at hf; rw [propN_eq_zero.mpr hB] at hf
  exact eq_pt_of_mem_piR_zero hf

/-- Over an empty domain the function space is `{pt}`. -/
theorem piV_of_empty {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : ∀ x, ¬ x ∈ˢ A) : piV A B hS = unitSet := by
  unfold piV
  rw [propN_eq_zero.mpr fun x hx => absurd hx (h x), piR_zero]
  exact ext fun z => by
    rw [mem_truthVal, mem_unitSet_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨fun x hx => absurd hx (h x), h'⟩⟩

/-- Over an empty domain the abstraction is the point. -/
theorem lamV_of_empty {A : V} {F : V → V} {hG : HasGraph A F}
    (h : ∀ x, ¬ x ∈ˢ A) : lamV A F hG = pt :=
  lamV_eq_pt fun x hx => absurd hx (h x)

/-- **`∀`-formation in the universes**, with no regime premise: over
fibres in `Sort 0` the function space is a truth value; over fibres in
a positive sort it is a truth value or a strict function space, a type
either way. -/
theorem piV_mem_univ {u v : Nat} {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piV A B hS ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  by_cases hv : v = 0
  · subst hv
    have hp : propN A B = 0 :=
      propN_eq_zero.mpr fun x hx => univ_zero (V := V) ▸ hB x hx
    rw [ite_eq_left rfl, univ_zero]
    unfold piV; rw [hp]; exact piR_zero_mem_univZero
  · have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    rw [ite_eq_right hv]
    unfold piV
    by_cases hp : propN A B = 0
    · rw [hp]
      have h0 : piR 0 A B hS ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact piR_zero_mem_univZero
      exact univ_mono (Nat.zero_le _) _ h0
    · rw [piR_pos hp]
      exact mem_univ_of_tg_strict ((tg_isGrothendieck hw).piSet_mem
        (tg_mono (Nat.le_max_left u v) A (mem_tg_of_mem_univ hA))
        (fun x hx => tg_mono (Nat.le_max_right u v) _ (mem_tg_of_mem_univ (hB x hx)))
        hS)
        strict_piSet

/-- Where every fibre is a truth value the function space is the
truth-value regime's. -/
theorem piV_eq_zero {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    piV A B hS = piR 0 A B hS := by
  unfold piV; rw [propN_eq_zero.mpr h]

/-- Where some fibre is not a truth value the function space is the
graph regime's. -/
theorem piV_eq_pos {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    {x : V} (hx : x ∈ˢ A) (h : ¬ B x ∈ˢ (univZero : V)) :
    piV A B hS = piR v A B hS := by
  unfold piV
  have hp : propN A B ≠ 0 := fun h0 => h (propN_eq_zero.mp h0 x hx)
  rw [piR_pos hp, piR_pos hv]

/-- An abstraction with a body value that is not the point is the graph
regime's. -/
theorem lamV_eq_pos {v : Nat} (hv : v ≠ 0) {A : V} {F : V → V} {hG : HasGraph A F}
    {x : V} (hx : x ∈ˢ A) (h : F x ≠ pt) : lamV A F hG = lamR v A F hG := by
  rw [lamV_eq_graph (lamV_ne_pt_of hx h), lamR_pos hv]

/-- **Transport of a member along fibres that are types**: a member of
one function space over `A` whose applications land in the fibres of
another, both families of types, is a member of the other.  The point
member: its applications are the point, so the new fibres hold the
point and are truth values.  A graph member: it has a value that is not
the point (its old fibre there is strict), so the new fibre there is no
truth value and the new space holds graphs. -/
theorem mem_piV_of_app {A f : V} {B₀ B : V → V}
    {hS₀ : HasSigmaPairs A B₀} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piV A B₀ hS₀)
    (hB₀ : ∀ x, x ∈ˢ A → IsTy (B₀ x)) (hB : ∀ x, x ∈ˢ A → IsTy (B x))
    (happ : ∀ x, x ∈ˢ A → app f x ∈ˢ B x) : f ∈ˢ piV A B hS := by
  by_cases hfp : f = pt
  · subst hfp
    have h0 : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := fun x hx =>
      (hB x hx).resolve_right fun hs => hs.2 (by simpa [app_pt] using happ x hx)
    rw [piV_eq_zero h0]
    exact pt_mem_piR_zero fun x hx => ⟨_, happ x hx⟩
  · have hf' := mem_piSet_of_mem_piV hf hfp
    have hp : propN A B₀ ≠ 0 := fun h => hfp (eq_pt_of_mem_piV (propN_eq_zero.mp h) hf)
    obtain ⟨x₀, hx₀, hB₀x⟩ : ∃ x, x ∈ˢ A ∧ ¬ B₀ x ∈ˢ (univZero : V) :=
      Classical.byContradiction fun hne => hp (propN_eq_zero.mpr fun x hx =>
        Classical.byContradiction fun h => hne ⟨x, hx, h⟩)
    have hs : Strict (B₀ x₀) := (hB₀ x₀ hx₀).resolve_left hB₀x
    have hne : app f x₀ ≠ pt := ne_pt_of_mem_strict hs (app_mem_of_mem_piSet hf' hx₀)
    have hBx : ¬ B x₀ ∈ˢ (univZero : V) := fun h => hne (eq_pt_of_mem_univZero h (happ x₀ hx₀))
    rw [piV_eq_pos Nat.one_ne_zero hx₀ hBx, piR_pos Nat.one_ne_zero,
      ← eq_graph_app_of_mem_piSet hf']
    exact graph_mem_piSet happ

/-- **The point inhabits a function space of types** exactly when it
inhabits every fibre. -/
theorem pt_mem_piV_iff {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hB : ∀ x, x ∈ˢ A → IsTy (B x)) :
    (pt : V) ∈ˢ piV A B hS ↔ ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x := by
  refine ⟨fun h x hx => by simpa [app_pt] using app_mem_piV h hx, fun h => ?_⟩
  have h0 : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := fun x hx =>
    (hB x hx).resolve_right fun hs => hs.2 (h x hx)
  rw [piV_eq_zero h0]
  exact pt_mem_piR_zero fun x hx => ⟨_, h x hx⟩

/-- **`piV` is monotone in fibres that are types.** -/
theorem piV_subset_mono {A : V} {B B' : V → V}
    {hS : HasSigmaPairs A B} {hS' : HasSigmaPairs A B'}
    (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x)
    (hB : ∀ x, x ∈ˢ A → IsTy (B x)) (hB' : ∀ x, x ∈ˢ A → IsTy (B' x)) :
    piV A B hS ⊆ˢ piV A B' hS' := fun _ hf =>
  mem_piV_of_app hf hB hB' fun x hx => h x hx _ (app_mem_piV hf hx)

/-- A universe is not a truth value: it holds `∅`, which is not the
point. -/
theorem univ_not_mem_univZero (w : Nat) : ¬ (univ w : V) ∈ˢ (univZero : V) := fun h =>
  pt_ne_empty (eq_pt_of_mem_univZero h (empty_mem_univ w)).symm

/-- A function space into a universe over an inhabited domain is the
graph regime's. -/
theorem piV_univ_eq_pos {v : Nat} (hv : v ≠ 0) {A : V} {x : V} (hx : x ∈ˢ A)
    (B : V → V) {hS : HasSigmaPairs A B}
    (hB : ∀ y, y ∈ˢ A → ∃ w, B y = univ w) : piV A B hS = piR v A B hS :=
  piV_eq_pos hv hx fun h => by
    obtain ⟨w, hw⟩ := hB x hx
    rw [hw] at h
    exact univ_not_mem_univZero w h

end ConLeche.SetModel
