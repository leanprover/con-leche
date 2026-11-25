module

public import ConLeche.SetTheory.Derive.LfpFam
@[expose] public section

/-!
# Recursion from induction: the recursor family's GRAPH as a least fixed point

Every recursor accepted by the syntactic primitive-recursion check is
implemented by nested INDUCTION alone — one mechanism for every sort,
covering the three proof regimes (IND / WF / SQ).

This module is the abstract core.  Over an arbitrary set
`U` of MAJORS (the tagged union of the family's classes), a recursor
family is presented by four first-order definable data over `V`:

* `Dec u d` — the major `u` DECODES as the set-encoded datum `d : V`
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
choice-free singleton selector `recSel`, and the ι laws are the closure
conditions read backwards (`GraphRecKit.rec_eq`).

**The theorem** (`GraphRecKit.exu`): the graph has EXACTLY ONE value at
every major.  Its proof is the kit's `ind` — an induction principle
over the majors (guarded by `HasSep U P`), the only fact ever asked of
the carriers — with the definable predicate `Single K.G` ("the graph's
fibre is a singleton").  Existence needs the step's typing (`hst`);
uniqueness needs ONE sort-dependent fact, `huniq`: at every major, two
decodings are EQUAL, or the bound is a subsingleton.  That disjunction
is exactly the three regimes' three reasons, and it is discharged three
ways with NOTHING ELSE changing:

* `ℓ = 0` (regime IND): the bound is a truth value —
  `huniq_of_prop`; decodings need not be unique at all;
* `w ≠ 0` (regime WF): the encoding `inj j (mkTower fs)` is injective
  — `huniq_of_dec`; no regularity, no subterm relation;
* `w = 0, ℓ ≠ 0` (regime SQ): the major is the point, and the
  subsingleton criterion (every field a proof or an index) makes the
  decoding a function of the INDEX — `huniq_of_dec` again.

The negative control — a two-constructor `Prop` with a large motive —
is where `huniq` fails: the graph has two values there.  The block's instance is
`Semantics/Tower/BlockRecTower.lean` and the run's
`Model/Inductives/BlockRecGraph.lean`.

No choice: existence uses the choice-free selector `recSel G i :=
if Single G i then ⋃ (app G i) else pt`, and the choice function over
the predecessors is the graph of that selector (replacement).  No
regularity: the only induction is the block's (and its containers')
own least-fixed-point induction, which is what `ind` is instantiated
with in every test case.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Singleton predicate and choice-free selector -/

/-- A family's fibre at `u` is a singleton. -/
def Single (G u : V) : Prop :=
  (∃ v, v ∈ˢ app G u) ∧ ∀ v v', v ∈ˢ app G u → v' ∈ˢ app G u → v = v'

theorem DefRel.single_apply {k : Nat} {G U : (Fin k → V) → V}
    (hG : DefFun k G) (hU : DefFun k U) :
    DefRel k fun env => Single (G env) (U env) := by
  unfold Single
  have hex : DefRel k fun env => ∃ v, v ∈ˢ app (G env) (U env) :=
    DefRel.exists_curry (DefRel.mem_apply (DefFun.proj 0)
      (DefFun.app_apply hG.weaken hU.weaken))
  have hun : DefRel k fun env => ∀ v v', v ∈ˢ app (G env) (U env) →
      v' ∈ˢ app (G env) (U env) → v = v' :=
    DefRel.forall_curry (DefRel.forall_curry
      (DefRel.imp
        (DefRel.mem_apply (DefFun.proj 1) (DefFun.app_apply hG.weaken.weaken hU.weaken.weaken))
        (DefRel.imp
          (DefRel.mem_apply (DefFun.proj 0) (DefFun.app_apply hG.weaken.weaken hU.weaken.weaken))
          (DefRel.eq_apply (DefFun.proj 1) (DefFun.proj 0)))))
  exact hex.and hun

theorem defPred_single (G : V) : DefPred (Single G) :=
  DefRel.single_apply (DefFun.const G) (DefFun.proj 0)

open Classical in
/-- The graph's choice-free selector: `⋃ (app G i)` when `Single G i`,
`pt` otherwise. -/
noncomputable def recSel (G i : V) : V :=
  if Single G i then sUnion (app G i) else pt

theorem recSel_eq_of_single {G i v : V} (h : Single G i) (hv : v ∈ˢ app G i) :
    recSel G i = v := by
  unfold recSel
  rw [ite_eq_left h]
  apply ext fun z => ?_
  rw [mem_sUnion]
  exact ⟨fun ⟨y, hy, hzy⟩ => (h.2 y v hy hv) ▸ hzy, fun hzv => ⟨v, hv, hzv⟩⟩

theorem recSel_mem {G i : V} (h : Single G i) : recSel G i ∈ˢ app G i := by
  obtain ⟨v, hv⟩ := h.1
  rwa [recSel_eq_of_single h hv]

theorem DefFun.recSel_apply {k : Nat} {G I : (Fin k → V) → V}
    (hG : DefFun k G) (hI : DefFun k I) :
    DefFun k fun env => recSel (G env) (I env) := by
  unfold recSel
  exact DefFun.ite (DefRel.single_apply hG hI)
    (DefFun.sUnion_apply (DefFun.app_apply hG hI))
    DefFun.pt

theorem hasGraph_recSel (G A : V) : HasGraph A (fun j => recSel G j) :=
  hasGraph_of_defFun1 (DefFun.recSel_apply (DefFun.const G) (DefFun.proj 0))

/-! ## Private parametric composition helpers -/

private theorem defRel2_comp {k m : Nat} {R : (Fin k → V) → V → V → Prop}
    (hR : DefRel (k + 2) fun v => R (ftail (ftail v)) (v 0) (v 1))
    {Env : (Fin m → V) → Fin k → V} (hEnv : ∀ i, DefFun m fun w => Env w i)
    {X Y : (Fin m → V) → V} (hX : DefFun m X) (hY : DefFun m Y) :
    DefRel m fun w => R (Env w) (X w) (Y w) := by
  let Gs : Fin (k + 2) → (Fin m → V) → V
    | ⟨0, _⟩ => X
    | ⟨1, _⟩ => Y
    | ⟨i + 2, hi⟩ => fun w => Env w ⟨i, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)⟩
  have hGs : ∀ j : Fin (k + 2), DefFun m (Gs j) := by
    rintro ⟨j, hj⟩
    match j with
    | 0 => exact hX
    | 1 => exact hY
    | i + 2 => exact hEnv ⟨i, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)⟩
  refine (DefRel.comp hR hGs).congr fun w => ?_
  have heqv : ftail (ftail (fun i : Fin (k + 2) => Gs i w)) = Env w := by
    funext ⟨i, hi⟩
    rfl
  change R (ftail (ftail (fun i => Gs i w))) (Gs 0 w) (Gs 1 w) ↔ R (Env w) (X w) (Y w)
  rw [heqv]
  rfl

private theorem defFun1_comp {k m : Nat} {F : (Fin k → V) → V → V}
    (hF : DefFun (k + 1) fun v => F (ftail v) (v 0))
    {Env : (Fin m → V) → Fin k → V} (hEnv : ∀ i, DefFun m fun w => Env w i)
    {X : (Fin m → V) → V} (hX : DefFun m X) :
    DefFun m fun w => F (Env w) (X w) := by
  let Gs : Fin (k + 1) → (Fin m → V) → V
    | ⟨0, _⟩ => X
    | ⟨i + 1, hi⟩ => fun w => Env w ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  have hGs : ∀ j : Fin (k + 1), DefFun m (Gs j) := by
    rintro ⟨j, hj⟩
    match j with
    | 0 => exact hX
    | i + 1 => exact hEnv ⟨i, Nat.lt_of_succ_lt_succ hj⟩
  refine (DefFun.comp hF hGs).congr fun w => ?_
  have heqv : ftail (fun i : Fin (k + 1) => Gs i w) = Env w := by
    funext ⟨i, hi⟩
    rfl
  change F (ftail (fun i => Gs i w)) (Gs 0 w) = F (Env w) (X w)
  rw [heqv]
  rfl

private theorem defFun2_comp {k m : Nat} {F : (Fin k → V) → V → V → V}
    (hF : DefFun (k + 2) fun v => F (ftail (ftail v)) (v 0) (v 1))
    {Env : (Fin m → V) → Fin k → V} (hEnv : ∀ i, DefFun m fun w => Env w i)
    {X Y : (Fin m → V) → V} (hX : DefFun m X) (hY : DefFun m Y) :
    DefFun m fun w => F (Env w) (X w) (Y w) := by
  let Gs : Fin (k + 2) → (Fin m → V) → V
    | ⟨0, _⟩ => X
    | ⟨1, _⟩ => Y
    | ⟨i + 2, hi⟩ => fun w => Env w ⟨i, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)⟩
  have hGs : ∀ j : Fin (k + 2), DefFun m (Gs j) := by
    rintro ⟨j, hj⟩
    match j with
    | 0 => exact hX
    | 1 => exact hY
    | i + 2 => exact hEnv ⟨i, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)⟩
  refine (DefFun.comp hF hGs).congr fun w => ?_
  have heqv : ftail (ftail (fun i : Fin (k + 2) => Gs i w)) = Env w := by
    funext ⟨i, hi⟩
    rfl
  change F (ftail (ftail (fun i => Gs i w))) (Gs 0 w) (Gs 1 w) = F (Env w) (X w) (Y w)
  rw [heqv]
  rfl

/-! ## The graph -/

theorem hasSigmaPairs_app (A S : V) : HasSigmaPairs A (fun j => app S j) :=
  hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const S) (DefFun.proj 0))

/-- Separation predicate for the graph functor's fibre at `(S, u)`. -/
def gFibrePred (Dec : V → V → Prop) (pred : V → V) (st : V → V → V) (S u v : V) : Prop :=
  ∃ d, Dec u d ∧
    ∃ g, g ∈ˢ piSet (pred d) (fun j => app S j) (hasSigmaPairs_app (pred d) S) ∧ v = st d g

/-- Proof-carrying, zero-junk fibre of the graph functor at `(S, u)`. -/
noncomputable def gFibre (Dec : V → V → Prop) (pred B : V → V) (st : V → V → V)
    (S u : V) (hSep : HasSep (B u) (gFibrePred Dec pred st S u)) : V :=
  sep (B u) (gFibrePred Dec pred st S u) hSep

/-- Proof-carrying witness package asserting that `gFibre`, `gStep`, and
`famOf B U` exist as sets in `V`. -/
structure HasGraphStep (ℓ : Nat) (U : V) (Dec : V → V → Prop) (pred B : V → V)
    (st : V → V → V) : Prop where
  hSep : ∀ S u, HasSep (B u) (gFibrePred Dec pred st S u)
  hFam : ∀ S, HasGraph U (fun u => gFibre Dec pred B st S u (hSep S u))
  hGraph : HasGraph (famSpaceIn (tg ℓ) U)
    (fun S => famOf (fun u => gFibre Dec pred B st S u (hSep S u)) U (hFam S))
  hBGraph : HasGraph U B

theorem defRel_gFibrePred {k : Nat}
    {Dec : (Fin k → V) → V → V → Prop}
    {pred : (Fin k → V) → V → V}
    {st : (Fin k → V) → V → V → V}
    (hDec : DefRel (k + 2) fun v => Dec (ftail (ftail v)) (v 0) (v 1))
    (hpred : DefFun (k + 1) fun v => pred (ftail v) (v 0))
    (hst : DefFun (k + 2) fun v => st (ftail (ftail v)) (v 0) (v 1)) :
    DefRel (k + 3) fun v =>
      gFibrePred (Dec (ftail (ftail (ftail v))))
        (pred (ftail (ftail (ftail v))))
        (st (ftail (ftail (ftail v))))
        (v 2) (v 1) (v 0) := by
  unfold gFibrePred
  have hDec4 : DefRel (k + 4) fun w =>
      Dec (ftail (ftail (ftail (ftail w)))) (w 2) (w 0) :=
    defRel2_comp hDec (fun i => DefFun.proj i.succ.succ.succ.succ)
      (DefFun.proj 2) (DefFun.proj 0)
  have hpred5 : DefFun (k + 5) fun z =>
      pred (ftail (ftail (ftail (ftail (ftail z))))) (z 1) :=
    defFun1_comp hpred (fun i => DefFun.proj i.succ.succ.succ.succ.succ) (DefFun.proj 1)
  have hpi5 : DefFun (k + 5) fun z =>
      piSet (pred (ftail (ftail (ftail (ftail (ftail z))))) (z 1))
        (fun j => app (z 4) j)
        (hasSigmaPairs_app _ (z 4)) :=
    DefFun.piSet_apply_curry hpred5 (DefFun.app_apply (DefFun.proj 5) (DefFun.proj 0))
  have hst5 : DefFun (k + 5) fun z =>
      st (ftail (ftail (ftail (ftail (ftail z))))) (z 1) (z 0) :=
    defFun2_comp hst (fun i => DefFun.proj i.succ.succ.succ.succ.succ)
      (DefFun.proj 1) (DefFun.proj 0)
  have hinner : DefRel (k + 4) fun w =>
      ∃ g, g ∈ˢ piSet (pred (ftail (ftail (ftail (ftail w)))) (w 0))
        (fun j => app (w 3) j) (hasSigmaPairs_app _ (w 3)) ∧
        w 1 = st (ftail (ftail (ftail (ftail w)))) (w 0) g :=
    DefRel.exists_curry (DefRel.and (DefRel.mem_apply (DefFun.proj 0) hpi5)
      (DefRel.eq_apply (DefFun.proj 2) hst5))
  exact DefRel.exists_curry (hDec4.and hinner)

theorem DefFun.gFibre_apply {k : Nat}
    {Dec : (Fin k → V) → V → V → Prop}
    {pred B : (Fin k → V) → V → V}
    {st : (Fin k → V) → V → V → V}
    {hSep : ∀ env S u, HasSep (B env u) (gFibrePred (Dec env) (pred env) (st env) S u)}
    (hDec : DefRel (k + 2) fun v => Dec (ftail (ftail v)) (v 0) (v 1))
    (hpred : DefFun (k + 1) fun v => pred (ftail v) (v 0))
    (hB : DefFun (k + 1) fun v => B (ftail v) (v 0))
    (hst : DefFun (k + 2) fun v => st (ftail (ftail v)) (v 0) (v 1)) :
    DefFun (k + 2) fun w =>
      gFibre (Dec (ftail (ftail w))) (pred (ftail (ftail w))) (B (ftail (ftail w)))
        (st (ftail (ftail w))) (w 1) (w 0)
        (hSep (ftail (ftail w)) (w 1) (w 0)) := by
  unfold gFibre
  have hBw : DefFun (k + 2) fun w => B (ftail (ftail w)) (w 0) :=
    defFun1_comp hB (fun i => DefFun.proj i.succ.succ) (DefFun.proj 0)
  exact DefFun.sep_apply_curry hBw (defRel_gFibrePred hDec hpred hst)

theorem hasSep_gFibre_of_def {Dec : V → V → Prop} {pred B : V → V} {st : V → V → V}
    (hDec : DefRel 2 fun v => Dec (v 0) (v 1))
    (hpred : DefFun 1 fun v => pred (v 0))
    (hst : DefFun 2 fun v => st (v 0) (v 1)) (S u : V) :
    HasSep (B u) (gFibrePred Dec pred st S u) := by
  have h3 := defRel_gFibrePred (k := 0) (Dec := fun _ => Dec)
    (pred := fun _ => pred) (st := fun _ => st) hDec hpred hst
  let Gs : Fin 3 → (Fin 1 → V) → V
    | ⟨0, _⟩ => fun w => w 0
    | ⟨1, _⟩ => fun _ => u
    | ⟨2, _⟩ => fun _ => S
  have hGs : ∀ i : Fin 3, DefFun 1 (Gs i) := by
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact DefFun.proj 0
    | 1 => exact DefFun.const u
    | 2 => exact DefFun.const S
  exact hasSep_of_defPred ((DefRel.comp h3 hGs).congr fun _ => Iff.rfl)

theorem hasGraphStep_of_def (ℓ : Nat) (U : V)
    {Dec : V → V → Prop} {pred B : V → V} {st : V → V → V}
    (hDec : DefRel 2 fun v => Dec (v 0) (v 1))
    (hpred : DefFun 1 fun v => pred (v 0))
    (hB : DefFun 1 fun v => B (v 0))
    (hst : DefFun 2 fun v => st (v 0) (v 1)) :
    HasGraphStep ℓ U Dec pred B st := by
  have hSep : ∀ S u, HasSep (B u) (gFibrePred Dec pred st S u) :=
    hasSep_gFibre_of_def hDec hpred hst
  have hFib2 : DefFun 2 fun w =>
      gFibre Dec pred B st (w 1) (w 0) (hSep (w 1) (w 0)) :=
    DefFun.gFibre_apply (k := 0) (Dec := fun _ => Dec) (pred := fun _ => pred)
      (B := fun _ => B) (st := fun _ => st)
      (hSep := fun _ => hSep) hDec hpred hB hst
  have hFam : ∀ S, HasGraph U (fun u => gFibre Dec pred B st S u (hSep S u)) := by
    intro S
    let Gs : Fin 2 → (Fin 1 → V) → V
      | ⟨0, _⟩ => fun w => w 0
      | ⟨1, _⟩ => fun _ => S
    have hGs : ∀ i : Fin 2, DefFun 1 (Gs i) := by
      rintro ⟨i, hi⟩
      match i with
      | 0 => exact DefFun.proj 0
      | 1 => exact DefFun.const S
    exact hasGraph_of_defFun1 ((DefFun.comp hFib2 hGs).congr fun _ => rfl)
  have hFamDef : DefFun 1 fun v =>
      famOf (fun u => gFibre Dec pred B st (v 0) u (hSep (v 0) u)) U (hFam (v 0)) :=
    DefFun.famOf_apply_curry (k := 1)
      (G := fun u v => gFibre Dec pred B st (v 0) u (hSep (v 0) u))
      (I := fun _ => U) (h := fun v => hFam (v 0))
      (hFib2.congr fun _ => rfl) (DefFun.const U)
  exact ⟨hSep, hFam, hasGraph_of_defFun1 hFamDef, hasGraph_of_defFun1 hB⟩

section Graph

variable (ℓ : Nat) (U : V) (Dec : V → V → Prop) (pred B : V → V) (st : V → V → V)

/-- The graph functor on families over `U`. -/
noncomputable def gStep (h : HasGraphStep ℓ U Dec pred B st) : V :=
  graph (fun S => famOf (fun u => gFibre Dec pred B st S u (h.hSep S u)) U (h.hFam S))
    (famSpaceIn (tg ℓ) U) h.hGraph

/-- **The recursor family's graph**: the least fixed point of the graph
functor, over families of the axiomatic level `tg ℓ` — a relation,
whose fibres are sets of values, not types (no drop ever fires: the
level is closed under subsets). -/
noncomputable def gGraph (h : HasGraphStep ℓ U Dec pred B st) : V :=
  lfpFamIn (tg ℓ) U (gStep ℓ U Dec pred B st h)

variable {ℓ U Dec pred B st}

theorem DefFun.gStep_apply {k : Nat} (ℓ : Nat)
    {U : (Fin k → V) → V}
    {Dec : (Fin k → V) → V → V → Prop}
    {pred B : (Fin k → V) → V → V}
    {st : (Fin k → V) → V → V → V}
    {h : ∀ env, HasGraphStep ℓ (U env) (Dec env) (pred env) (B env) (st env)}
    (hU : DefFun k U)
    (hDec : DefRel (k + 2) fun v => Dec (ftail (ftail v)) (v 0) (v 1))
    (hpred : DefFun (k + 1) fun v => pred (ftail v) (v 0))
    (hB : DefFun (k + 1) fun v => B (ftail v) (v 0))
    (hst : DefFun (k + 2) fun v => st (ftail (ftail v)) (v 0) (v 1)) :
    DefFun k fun env => gStep ℓ (U env) (Dec env) (pred env) (B env) (st env) (h env) := by
  unfold gStep
  have hFib : DefFun (k + 2) fun w =>
      gFibre (Dec (ftail (ftail w))) (pred (ftail (ftail w))) (B (ftail (ftail w)))
        (st (ftail (ftail w))) (w 1) (w 0) ((h (ftail (ftail w))).hSep (w 1) (w 0)) :=
    DefFun.gFibre_apply (hSep := fun env S u => (h env).hSep S u) hDec hpred hB hst
  have hFam : DefFun (k + 1) fun v =>
      famOf (fun u => gFibre (Dec (ftail v)) (pred (ftail v)) (B (ftail v)) (st (ftail v))
        (v 0) u ((h (ftail v)).hSep (v 0) u)) (U (ftail v)) ((h (ftail v)).hFam (v 0)) :=
    DefFun.famOf_apply_curry
      (G := fun u v => gFibre (Dec (ftail v)) (pred (ftail v)) (B (ftail v)) (st (ftail v))
        (v 0) u ((h (ftail v)).hSep (v 0) u))
      (I := fun v => U (ftail v))
      (h := fun v => (h (ftail v)).hFam (v 0))
      (hFib.congr fun _ => rfl)
      hU.weaken
  exact DefFun.graph_apply_curry
    (F := fun S env => famOf (fun u => gFibre (Dec env) (pred env) (B env) (st env)
      S u ((h env).hSep S u)) (U env) ((h env).hFam S))
    (A := fun env => famSpaceIn (tg ℓ) (U env))
    (h := fun env => (h env).hGraph)
    (hFam.congr fun _ => rfl)
    (DefFun.famSpaceIn_apply (DefFun.tg_const ℓ) hU)

theorem DefFun.gGraph_apply {k : Nat} (ℓ : Nat)
    {U : (Fin k → V) → V}
    {Dec : (Fin k → V) → V → V → Prop}
    {pred B : (Fin k → V) → V → V}
    {st : (Fin k → V) → V → V → V}
    {h : ∀ env, HasGraphStep ℓ (U env) (Dec env) (pred env) (B env) (st env)}
    (hU : DefFun k U)
    (hDec : DefRel (k + 2) fun v => Dec (ftail (ftail v)) (v 0) (v 1))
    (hpred : DefFun (k + 1) fun v => pred (ftail v) (v 0))
    (hB : DefFun (k + 1) fun v => B (ftail v) (v 0))
    (hst : DefFun (k + 2) fun v => st (ftail (ftail v)) (v 0) (v 1)) :
    DefFun k fun env => gGraph ℓ (U env) (Dec env) (pred env) (B env) (st env) (h env) := by
  unfold gGraph
  exact DefFun.lfpFamIn_apply (DefFun.tg_const ℓ) hU
    (DefFun.gStep_apply ℓ hU hDec hpred hB hst)

theorem app_gStep {h : HasGraphStep ℓ U Dec pred B st} {S : V}
    (hS : S ∈ˢ famSpaceIn (tg ℓ) U) :
    app (gStep ℓ U Dec pred B st h) S =
      famOf (fun u => gFibre Dec pred B st S u (h.hSep S u)) U (h.hFam S) :=
  app_graph hS

theorem app_app_gStep {h : HasGraphStep ℓ U Dec pred B st} {S u : V}
    (hS : S ∈ˢ famSpaceIn (tg ℓ) U) (hu : u ∈ˢ U) :
    app (app (gStep ℓ U Dec pred B st h) S) u = gFibre Dec pred B st S u (h.hSep S u) := by
  rw [app_gStep hS, app_famOf hu]

theorem mem_gFibre {S u v : V} {hSep : HasSep (B u) (gFibrePred Dec pred st S u)} :
    v ∈ˢ gFibre Dec pred B st S u hSep ↔
      v ∈ˢ B u ∧ ∃ d, Dec u d ∧
        ∃ g, g ∈ˢ piSet (pred d) (fun j => app S j) (hasSigmaPairs_app (pred d) S) ∧ v = st d g :=
  mem_sep

theorem gStep_maps {h : HasGraphStep ℓ U Dec pred B st}
    (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)) :
    MapsFamIn (tg ℓ) U (gStep ℓ U Dec pred B st h) := by
  intro S hS
  rw [app_gStep hS]
  exact famOf_mem_famSpaceIn fun u hu =>
    subsetClosed_tg ℓ _ _ (mem_tg_of_mem_univ (hB u hu)) sep_subset

theorem gStep_mono {h : HasGraphStep ℓ U Dec pred B st}
    (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) :
    MonoFamIn (tg ℓ) U (gStep ℓ U Dec pred B st h) := by
  intro X Y hX hY hle u hu v hv
  rw [app_app_gStep hX hu] at hv
  rw [app_app_gStep hY hu]
  obtain ⟨hvB, d, hd, g, hg, rfl⟩ := mem_gFibre.mp hv
  refine mem_gFibre.mpr ⟨hvB, d, hd, g, ?_, rfl⟩
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hg
  refine mem_piSet.mpr ⟨fun p hp => ?_, htot⟩
  obtain ⟨j, hj, y, hy, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
  exact mem_sigmaPairs.mpr ⟨j, hj, y, hle j (hpred u hu d hd j hj) y hy, rfl⟩

theorem gStep_closed {h : HasGraphStep ℓ U Dec pred B st}
    (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)) :
    IsClosedFamIn (tg ℓ) U (gStep ℓ U Dec pred B st h) (famOf B U h.hBGraph) := by
  have hB' : ∀ u, u ∈ˢ U → B u ∈ˢ (tg ℓ : V) := fun u hu => mem_tg_of_mem_univ (hB u hu)
  refine ⟨famOf_mem_famSpaceIn hB', fun u hu v hv => ?_⟩
  rw [app_app_gStep (famOf_mem_famSpaceIn hB') hu] at hv
  rw [app_famOf hu]
  exact (mem_gFibre.mp hv).1

/-- **The fixed-point equation**, fibrewise. -/
theorem app_gGraph_eq {h : HasGraphStep ℓ U Dec pred B st}
    (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V))
    (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) {u : V} (hu : u ∈ˢ U) :
    app (gGraph ℓ U Dec pred B st h) u =
      gFibre Dec pred B st (gGraph ℓ U Dec pred B st h) u
        (h.hSep (gGraph ℓ U Dec pred B st h) u) := by
  unfold gGraph
  rw [← app_lfpFamIn_eq (subsetClosed_tg ℓ).dropClosed (empty_mem_tg ℓ) ⟨_, gStep_closed hB⟩
      (gStep_mono hpred) (gStep_maps hB) hu,
    app_app_gStep (lfpFamIn_mem (empty_mem_tg ℓ) _ _) hu]

/-- Every value of the graph lies in the bound. -/
theorem gGraph_mem_B {h : HasGraphStep ℓ U Dec pred B st}
    (hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V))
    (hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U) {u v : V} (hu : u ∈ˢ U)
    (hv : v ∈ˢ app (gGraph ℓ U Dec pred B st h) u) : v ∈ˢ B u := by
  rw [app_gGraph_eq hB hpred hu] at hv
  exact (mem_gFibre.mp hv).1

end Graph

/-! ## The kit -/

/-- **The recursion data of a family over its majors** — first-order
definable over `V`, with `HasSep`-guarded induction on the majors. -/
structure GraphRecKit (ℓ : Nat) (U : V) where
  /-- `u` decodes as `d : V`. -/
  Dec : V → V → Prop
  /-- the recursive calls' majors at a decoding -/
  pred : V → V
  /-- the bound: the conclusion at the major -/
  B : V → V
  /-- the step: the rule's right-hand side at a decoding, the `ih`s read off `g` -/
  st : V → V → V
  /-- `Dec` is first-order definable -/
  hDec_def : DefRel 2 fun v => Dec (v 0) (v 1)
  /-- `pred` is first-order definable -/
  hpred_def : DefFun 1 fun v => pred (v 0)
  /-- `B` is first-order definable -/
  hB_def : DefFun 1 fun v => B (v 0)
  /-- `st` is first-order definable -/
  hst_def : DefFun 2 fun v => st (v 0) (v 1)
  /-- the predecessors are majors -/
  hpred : ∀ u, u ∈ˢ U → ∀ d, Dec u d → pred d ⊆ˢ U
  /-- the bound is a set of the eliminating level -/
  hB : ∀ u, u ∈ˢ U → B u ∈ˢ (univ ℓ : V)
  /-- the step lands in the bound (the rule's certified typing) -/
  hst : ∀ u, u ∈ˢ U → ∀ d, Dec u d → ∀ g,
    g ∈ˢ piSet (pred d)
      (fun j => app (gGraph ℓ U Dec pred B st
        (hasGraphStep_of_def ℓ U hDec_def hpred_def hB_def hst_def)) j)
      (hasSigmaPairs_app (pred d) _) →
    st d g ∈ˢ B u
  /-- **the sort-dependent fact**: decodings are unique, or the bound is a subsingleton -/
  huniq : ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
    d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v'
  /-- **the induction principle of the majors** (guarded by `HasSep U P`):
  a property that holds at a major whenever it holds at the predecessors
  of SOME decoding holds everywhere -/
  ind : ∀ P : V → Prop, HasSep U P →
    (∀ u, u ∈ˢ U → (∃ d, Dec u d ∧ ∀ j, j ∈ˢ pred d → P j) → P u) → ∀ u, u ∈ˢ U → P u

/-- `huniq` from unique decodings (regimes WF and SQ). -/
theorem huniq_of_dec {U : V} {Dec : V → V → Prop} {B : V → V}
    (h : ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' → d = d') :
    ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' :=
  fun u hu d d' hd hd' => Or.inl (h u hu d d' hd hd')

/-- `huniq` from a propositional bound (regime IND, `ℓ = 0`). -/
theorem huniq_of_prop {U : V} {Dec : V → V → Prop} {B : V → V}
    (h : ∀ u, u ∈ˢ U → B u ∈ˢ (univ 0 : V)) :
    ∀ u, u ∈ˢ U → ∀ d d', Dec u d → Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' :=
  fun u hu _ _ _ _ => Or.inr fun _ _ hv hv' =>
    (eq_pt_of_mem_univZero (univ_zero (V := V) ▸ h u hu) hv).trans
      (eq_pt_of_mem_univZero (univ_zero (V := V) ▸ h u hu) hv').symm

namespace GraphRecKit

variable {ℓ : Nat} {U : V} (K : GraphRecKit ℓ U)

/-- The kit's graph-step existence witness. -/
theorem hasGraphStep : HasGraphStep ℓ U K.Dec K.pred K.B K.st :=
  hasGraphStep_of_def ℓ U K.hDec_def K.hpred_def K.hB_def K.hst_def

/-- The kit's graph. -/
noncomputable def G : V := gGraph ℓ U K.Dec K.pred K.B K.st K.hasGraphStep

/-- The kit's recursor: the graph's choice-free selector. -/
noncomputable def recAt (u : V) : V := recSel K.G u

theorem hasGraph_recAt (A : V) : HasGraph A (fun j => K.recAt j) :=
  hasGraph_recSel K.G A

theorem DefFun.recAt_const_apply {k : Nat} {M : (Fin k → V) → V} (hM : DefFun k M) :
    DefFun k fun env => K.recAt (M env) :=
  DefFun.recSel_apply (DefFun.const K.G) hM

theorem app_G_eq {u : V} (hu : u ∈ˢ U) :
    app K.G u = gFibre K.Dec K.pred K.B K.st K.G u (K.hasGraphStep.hSep K.G u) :=
  app_gGraph_eq K.hB K.hpred hu

theorem graph_mem_B {u v : V} (hu : u ∈ˢ U) (hv : v ∈ˢ app K.G u) : v ∈ˢ K.B u :=
  gGraph_mem_B K.hB K.hpred hu hv

/-- **The recursion theorem, from induction**: the graph has exactly
one value at every major. -/
theorem exu : ∀ u, u ∈ˢ U → Single K.G u := by
  refine K.ind (fun u => Single K.G u) (hasSep_of_defPred (defPred_single K.G)) ?_
  intro u hu ⟨d, hd, hP⟩
  -- the choice function over the decoding's predecessors
  have hg : graph (fun j => recSel K.G j) (K.pred d) (hasGraph_recSel K.G (K.pred d))
      ∈ˢ piSet (K.pred d) (fun j => app K.G j) (hasSigmaPairs_app (K.pred d) K.G) :=
    graph_mem_piSet fun j hj => recSel_mem (hP j hj)
  constructor
  · refine ⟨K.st d (graph (fun j => recSel K.G j) (K.pred d) (hasGraph_recSel K.G (K.pred d))), ?_⟩
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
  recSel_mem (K.exu u hu)

/-- **Typing**: the recursor's value lies in the bound. -/
theorem rec_mem_B {u : V} (hu : u ∈ˢ U) : K.recAt u ∈ˢ K.B u :=
  K.graph_mem_B hu (K.rec_mem_G hu)

/-- The recursor's graph over a decoding's predecessors is a choice of
graph values. -/
theorem recGraph_mem_piSet {u d : V} (hu : u ∈ˢ U) (hd : K.Dec u d)
    {hG : HasGraph (K.pred d) (fun j => K.recAt j)} :
    graph (fun j => K.recAt j) (K.pred d) hG ∈ˢ
      piSet (K.pred d) (fun j => app K.G j) (hasSigmaPairs_app (K.pred d) K.G) :=
  graph_mem_piSet fun j hj => K.rec_mem_G (K.hpred u hu d hd j hj)

/-- **The ι law, at ANY decoding**: the recursor at a major is the
step at that decoding, the `ih`s being the recursor at the
predecessors. -/
theorem rec_eq {u d : V} (hu : u ∈ˢ U) (hd : K.Dec u d)
    {hG : HasGraph (K.pred d) (fun j => K.recAt j)} :
    K.recAt u = K.st d (graph (fun j => K.recAt j) (K.pred d) hG) := by
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

/-- Joint parameter definability of `(K env).recAt (M env)` for a family of
kits varying over an outer parameter tuple `env : Fin k → V` (e.g. a prefix
spine in `BlockRecTower.famCandG`). -/
theorem DefFun.recAt_apply {k : Nat} {ℓ : Nat}
    {U : (Fin k → V) → V}
    (K : ∀ env : Fin k → V, GraphRecKit ℓ (U env))
    {M : (Fin k → V) → V}
    (hU : DefFun k U)
    (hDec : DefRel (k + 2) fun v => (K (ftail (ftail v))).Dec (v 0) (v 1))
    (hpred : DefFun (k + 1) fun v => (K (ftail v)).pred (v 0))
    (hB : DefFun (k + 1) fun v => (K (ftail v)).B (v 0))
    (hst : DefFun (k + 2) fun v => (K (ftail (ftail v))).st (v 0) (v 1))
    (hM : DefFun k M) :
    DefFun k fun env => (K env).recAt (M env) := by
  have hG : DefFun k fun env => (K env).G :=
    DefFun.gGraph_apply ℓ
      (h := fun env => (K env).hasGraphStep) hU hDec hpred hB hst
  exact DefFun.recSel_apply hG hM

end ConLeche.SetTheory
