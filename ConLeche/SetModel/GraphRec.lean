module

public import ConLeche.SetTheory.Derive.LfpFam
import ConLeche.SetTheory.Derive.Pt
@[expose] public section

/-!
# Recursion from induction: the recursor family's GRAPH as a least fixed point (lane GRAPH-F)

The maintainer's question (2026-09-23): *can every recursor accepted by
the syntactic primitive-recursion check be implemented by nested
INDUCTION alone — one mechanism for every sort, replacing the three
proof regimes (IND / WF / SQ)?*

This module is the abstract core of the answer.  Over an arbitrary set
`U` of MAJORS (the tagged union of the family's classes), a recursor
family is presented by four data:

* `Dec u d` — the major `u` DECODES as the datum `d`, of any type `R`
  (at a block: the class, the constructor and the fields; the decoding
  carries the fields' fit at the carrier).  The datum is the
  DECODING's spelling, independent of the value's encoding: at a
  `Prop` block every value is `pt`, its decodings are not;
* `pred d` — the majors of the RECURSIVE CALLS the rule matching `d`
  makes (a set, by replacement over the fields' telescopes);
* `B u` — the bound: the recursor's conclusion at the major;
* `st d g` — the STEP: the rule's right-hand side at the decoded
  fields, with every `ih` read off the choice function `g` of
  recursive values over `pred d`.

**The graph** `gGraph` is the least family over `U` closed under
"if `u` decodes as `d` and `g` picks a value of the graph at every
predecessor of `d`, then `st d g` is a value at `u`" — the rules read
as closure conditions on a relation.  The recursor is the graph's
selector, and the ι laws are the closure conditions read backwards
(`GraphRecKit.rec_eq`).

**The theorem** (`GraphRecKit.exu`): the graph has EXACTLY ONE value at
every major.  Its proof is the kit's `ind` — an induction principle
over the majors, the only fact ever asked of the carriers — with the
predicate "the graph's fibre is a singleton".  Existence needs the
step's typing (`hst`); uniqueness needs ONE sort-dependent fact,
`huniq`: at every major, two decodings are EQUAL, or the bound is a
subsingleton.  That disjunction is exactly the three regimes' three
reasons, and it is discharged three ways with NOTHING ELSE changing:

* `ℓ = 0` (regime IND): the bound is a truth value —
  `huniq_of_prop`; decodings need not be unique at all;
* `w ≠ 0` (regime WF): the encoding `inj j (mkTower fs)` is injective
  — `huniq_of_dec`; no regularity, no subterm relation;
* `w = 0, ℓ ≠ 0` (regime SQ): the major is the point, and the
  subsingleton criterion (every field a proof or an index) makes the
  decoding a function of the INDEX — `huniq_of_dec` again.

The negative control — a two-constructor `Prop` with a large motive —
is where `huniq` fails; lane GRAPH-F's `SetModel/GraphRecProp.lean`
(branch `agent/uinds-GRAPHF`, with the other set-level instances)
exhibits the graph with two values there.  The block's instance is
`Semantics/Tower/BlockRecTower.lean` and the run's
`Model/Inductives/BlockRecGraph.lean`.

No choice: existence uses the SELECTOR of a singleton (a description,
`recSel`), and the choice function over the predecessors is the graph
of that selector (replacement).  No regularity: the only induction is
the block's (and its containers') own least-fixed-point induction,
which is what `ind` is instantiated with in every test case.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The graph's selector: the fibre's element (the point off the graph). -/
noncomputable def recSel (G : V) (i : V) : V :=
  open Classical in
  if h : ∃ v, v ∈ˢ app G i then Classical.choose h else pt

theorem recSel_mem {G i : V} (h : ∃ v, v ∈ˢ app G i) : recSel G i ∈ˢ app G i := by
  unfold recSel
  rw [dif_pos h]
  exact Classical.choose_spec h

/-! ## The graph -/

section Graph

variable {R : Type u} (ℓ : Nat) (U : V) (Dec : V → R → Prop) (pred : R → V) (B : V → V)
  (st : R → V → V)

/-- The graph functor's fibre at the major `u` over the family `S`:
the values of some rule at some decoding of `u`, at a choice of
`S`-values over that decoding's predecessors. -/
noncomputable def gFibre (S u : V) : V :=
  sep (B u) fun v => ∃ d, Dec u d ∧ ∃ g, g ∈ˢ piSet (pred d) (fun j => app S j) ∧ v = st d g

/-- The graph functor on families over `U`. -/
noncomputable def gStep : V :=
  graph (fun S => graph (fun u => gFibre Dec pred B st S u) U) (famSpace ℓ U)

/-- **The recursor family's graph**: the least fixed point of the graph
functor. -/
noncomputable def gGraph : V := lfpFamSet ℓ U (gStep ℓ U Dec pred B st)

variable {ℓ U Dec pred B st}

theorem app_gStep {S : V} (hS : S ∈ˢ famSpace ℓ U) :
    app (gStep ℓ U Dec pred B st) S = graph (fun u => gFibre Dec pred B st S u) U :=
  app_graph hS

theorem app_app_gStep {S u : V} (hS : S ∈ˢ famSpace ℓ U) (hu : u ∈ˢ U) :
    app (app (gStep ℓ U Dec pred B st) S) u = gFibre Dec pred B st S u := by
  rw [app_gStep hS, app_graph hu]

theorem mem_gFibre {S u v : V} :
    v ∈ˢ gFibre Dec pred B st S u ↔
      v ∈ˢ B u ∧ ∃ d, Dec u d ∧ ∃ g, g ∈ˢ piSet (pred d) (fun j => app S j) ∧ v = st d g :=
  mem_sep

theorem gStep_maps (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)) :
    MapsFam ℓ U (gStep ℓ U Dec pred B st) := by
  intro S hS
  rw [app_gStep hS]
  exact graph_mem_famSpace fun u hu => univ_sep_mem (hB u hu)

theorem gStep_mono (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) :
    MonoFam ℓ U (gStep ℓ U Dec pred B st) := by
  intro X Y hX hY hle u hu v hv
  rw [app_app_gStep hX hu] at hv
  rw [app_app_gStep hY hu]
  obtain ⟨hvB, d, hd, g, hg, rfl⟩ := mem_gFibre.mp hv
  refine mem_gFibre.mpr ⟨hvB, d, hd, g, ?_, rfl⟩
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hg
  refine mem_piSet.mpr ⟨fun p hp => ?_, htot⟩
  obtain ⟨j, hj, y, hy, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
  exact mem_sigmaPairs.mpr ⟨j, hj, y, hle j (hpred u hu d hd j hj) y hy, rfl⟩

theorem gStep_closed (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)) :
    IsClosedFam ℓ U (gStep ℓ U Dec pred B st) (graph B U) := by
  refine ⟨graph_mem_famSpace hB, fun u hu v hv => ?_⟩
  rw [app_app_gStep (graph_mem_famSpace hB) hu] at hv
  rw [app_graph hu]
  exact (mem_gFibre.mp hv).1

/-- **The fixed-point equation**, fibrewise. -/
theorem app_gGraph_eq (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V))
    (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) {u : V} (hu : u ∈ˢ U) :
    app (gGraph ℓ U Dec pred B st) u = gFibre Dec pred B st (gGraph ℓ U Dec pred B st) u := by
  unfold gGraph
  rw [← app_lfpFamSet_eq ⟨_, gStep_closed hB⟩ (gStep_mono hpred) (gStep_maps hB) hu,
    app_app_gStep (lfpFamSet_mem _ _ _) hu]

/-- Every value of the graph lies in the bound. -/
theorem gGraph_mem_B (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V))
    (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) {u v : V} (hu : u ∈ˢ U)
    (hv : v ∈ˢ app (gGraph ℓ U Dec pred B st) u) : v ∈ˢ B u := by
  rw [app_gGraph_eq hB hpred hu] at hv
  exact (mem_gFibre.mp hv).1

end Graph

/-- A family's fibre at `u` is a singleton. -/
def Single (G u : V) : Prop :=
  (∃ v, v ∈ˢ app G u) ∧ ∀ v v', v ∈ˢ app G u → v' ∈ˢ app G u → v = v'

/-! ## The kit -/

/-- **The recursion data of a family over its majors** — and the ONE
induction principle it asks of them. -/
structure GraphRecKit (ℓ : Nat) (U : V) (R : Type u) where
  /-- `u` decodes as `d`. -/
  Dec : V → R → Prop
  /-- the recursive calls' majors at a decoding -/
  pred : R → V
  /-- the bound: the conclusion at the major -/
  B : V → V
  /-- the step: the rule's right-hand side at a decoding, the `ih`s read off `g` -/
  st : R → V → V
  /-- the predecessors are majors -/
  hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U
  /-- the bound is a set of the eliminating level -/
  hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)
  /-- the step lands in the bound (the rule's certified typing) -/
  hst : ∀ u, u ∈ˢ U → ∀ d, Dec u d → ∀ g,
    g ∈ˢ piSet (pred d) (fun j => app (gGraph ℓ U Dec pred B st) j) → st d g ∈ˢ B u
  /-- **the sort-dependent fact**: decodings are unique, or the bound is a subsingleton -/
  huniq : ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
    d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v'
  /-- **the induction principle of the majors**: a property that holds
  at a major whenever it holds at the predecessors of SOME decoding
  holds everywhere -/
  ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ U → (∃ d, Dec u d ∧ ∀ j, j ∈ˢ pred d → P j) → P u) → ∀ u, u ∈ˢ U → P u

/-- `huniq` from unique decodings (regimes WF and SQ). -/
theorem huniq_of_dec {R : Type u} {U : V} {Dec : V → R → Prop} {B : V → V}
    (h : ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' → d = d') :
    ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' :=
  fun u hu d d' hd hd' => Or.inl (h u hu d d' hd hd')

/-- `huniq` from a propositional bound (regime IND, `ℓ = 0`). -/
theorem huniq_of_prop {R : Type u} {U : V} {Dec : V → R → Prop} {B : V → V}
    (h : ∀ u, u ∈ˢ U → B u ∈ˢ (univ 0 : V)) :
    ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' :=
  fun u hu _ _ _ _ => Or.inr fun _ _ hv hv' =>
    (eq_pt_of_mem_univZero (univ_zero (V := V) ▸ h u hu) hv).trans
      (eq_pt_of_mem_univZero (univ_zero (V := V) ▸ h u hu) hv').symm

namespace GraphRecKit

variable {ℓ : Nat} {U : V} {R : Type u} (K : GraphRecKit ℓ U R)

/-- The kit's graph. -/
noncomputable def G : V := gGraph ℓ U K.Dec K.pred K.B K.st

/-- The kit's recursor: the graph's selector. -/
noncomputable def recAt (u : V) : V := recSel K.G u

theorem app_G_eq {u : V} (hu : u ∈ˢ U) :
    app K.G u = gFibre K.Dec K.pred K.B K.st K.G u :=
  app_gGraph_eq K.hB K.hpred hu

theorem graph_mem_B {u v : V} (hu : u ∈ˢ U) (hv : v ∈ˢ app K.G u) : v ∈ˢ K.B u :=
  gGraph_mem_B K.hB K.hpred hu hv

/-- **The recursion theorem, from induction**: the graph has exactly
one value at every major. -/
theorem exu : ∀ u, u ∈ˢ U → Single K.G u := by
  refine K.ind (fun u => Single K.G u) ?_
  intro u hu ⟨d, hd, hP⟩
  -- the choice function over the decoding's predecessors
  have hg : graph (fun j => recSel K.G j) (K.pred d)
      ∈ˢ piSet (K.pred d) (fun j => app K.G j) :=
    graph_mem_piSet fun j hj => recSel_mem (hP j hj).1
  constructor
  · refine ⟨K.st d (graph (fun j => recSel K.G j) (K.pred d)), ?_⟩
    rw [K.app_G_eq hu]
    exact mem_gFibre.mpr ⟨K.hst u hu d hd _ hg, d, hd, _, hg, rfl⟩
  · intro v v' hv hv'
    rw [K.app_G_eq hu] at hv hv'
    obtain ⟨hvB, d₁, hd₁, g₁, hg₁, rfl⟩ := mem_gFibre.mp hv
    obtain ⟨hvB', d₂, hd₂, g₂, hg₂, rfl⟩ := mem_gFibre.mp hv'
    rcases K.huniq u hu d d₁ hd hd₁ with rfl | hsub
    · rcases K.huniq u hu d d₂ hd hd₂ with rfl | hsub
      · congr 1
        exact eq_of_mem_piSet_app_eq hg₁ hg₂ fun j hj =>
          (hP j hj).2 _ _ (app_mem_of_mem_piSet hg₁ hj) (app_mem_of_mem_piSet hg₂ hj)
      · exact hsub _ _ hvB hvB'
    · exact hsub _ _ hvB hvB'

theorem rec_mem_G {u : V} (hu : u ∈ˢ U) : K.recAt u ∈ˢ app K.G u :=
  recSel_mem (K.exu u hu).1

/-- **Typing**: the recursor's value lies in the bound. -/
theorem rec_mem_B {u : V} (hu : u ∈ˢ U) : K.recAt u ∈ˢ K.B u :=
  K.graph_mem_B hu (K.rec_mem_G hu)

/-- The recursor's graph over a decoding's predecessors is a choice of
graph values. -/
theorem recGraph_mem_piSet {u : V} {d : R} (hu : u ∈ˢ U) (hd : K.Dec u d) :
    graph (fun j => K.recAt j) (K.pred d) ∈ˢ piSet (K.pred d) (fun j => app K.G j) :=
  graph_mem_piSet fun j hj => K.rec_mem_G (K.hpred u hu d hd j hj)

/-- **The ι law, at ANY decoding**: the recursor at a major is the
step at that decoding, the `ih`s being the recursor at the
predecessors. -/
theorem rec_eq {u : V} {d : R} (hu : u ∈ˢ U) (hd : K.Dec u d) :
    K.recAt u = K.st d (graph (fun j => K.recAt j) (K.pred d)) := by
  have hv := K.rec_mem_G hu
  rw [K.app_G_eq hu] at hv
  obtain ⟨hvB, d₁, hd₁, g₁, hg₁, heq⟩ := mem_gFibre.mp hv
  rcases K.huniq u hu d d₁ hd hd₁ with rfl | hsub
  · rw [heq]
    congr 1
    refine eq_of_mem_piSet_app_eq hg₁ (K.recGraph_mem_piSet hu hd) fun j hj => ?_
    rw [app_graph hj]
    exact (K.exu j (K.hpred u hu d hd j hj)).2 _ _ (app_mem_of_mem_piSet hg₁ hj)
      (K.rec_mem_G (K.hpred u hu d hd j hj))
  · exact hsub _ _ hvB (K.hst u hu d hd _ (K.recGraph_mem_piSet hu hd))

end GraphRecKit

end ConLeche.SetTheory
