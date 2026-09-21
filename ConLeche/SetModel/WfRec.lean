module

public import ConLeche.SetModel.UnionRec
public import ConLeche.SetTheory.Derive.TransClosure
@[expose] public section

/-!
# The recursor of a block by ∈-recursion on a GLOBAL subterm relation (falsifier F5)

The maintainer's formulation of a nested block's recursion (2026-09-21):
**recursion is well-founded recursion on the global subterm relation**

    x ⊏ y  :=  x ∈ˢ tc y            (`ConLeche/SetTheory/Derive/TransClosure.lean`)

pulled back along the payload of a tagged index — *not* on a
per-block accessibility relation read off the constructors.  The
predecessors of a tagged value `⟨c, i, x⟩` are ALL the members of the
recursion's index set whose payload is ∈-smaller than `x`
(`tcPred`); the recursion's well-foundedness is then regularity
(`tc_induction_map`), and it holds at an ARBITRARY index set — the
classes `C : Nat → V` are ordinary sets, with no fixed-point structure
assumed of them.

That is what this kit records, and it is what disappears compared to
`UnionRec.lean`'s lfp route:

* no `PredsFrom` — the kit states NOTHING about where predecessors
  come from, because `tcPred` is defined, not axiomatised;
* no `unionAcc_all` — accessibility is `tcAcc_all`, three lines of
  ∈-induction, and it needs no `MonoTuple`/`MapsTuple`/closed tuple;
* no requirement that the classes be components of one tuple lfp —
  `unionAcc_of_classAcc`'s obligation is discharged once and for all.

What the INSTANCE owes in exchange is the **encoding-depth**
obligation: each constructor's fields must really be ∈-below the
constructed value.  For the uniform tuple encoding
`inj j (mkTower (fs ++ [pt]))` that is `mem_tc_inj_mkTower` below —
one lemma, proved once from the Kuratowski pair — and for a
*reflexive* field (a function graph) the image of the field at an
argument is ∈-below it as well (`app_mem_tc`), hence ∈-below the value
(`app_field_mem_tc`).  Only the POSITIVE direction is ever needed: the
step function reads the predecessors it wants out of the graph and
ignores the rest, so no instance has to characterise `tcPred`
exactly — a marked simplification over the lfp route, where the
predecessor set had to be pinned down by `mkInj` at every constructor.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The payload of a tagged index -/

/-- The VALUE of a tagged recursion index `tagged c i x = ⟨c, i, x⟩`. -/
noncomputable def tagVal (u : V) : V := ssnd (ssnd u)

theorem tagVal_tagged (c : Nat) (i x : V) : tagVal (tagged c i x) = x := by
  unfold tagVal tagged
  rw [ssnd_kpair, ssnd_kpair]

/-! ## The ∈-predecessors, and their accessibility -/

/-- **The predecessor map of the maintainer's formulation**: the
members of the index set whose payload is a SUBTERM of this one's.
Nothing is assumed about the index set `U`. -/
noncomputable def tcPred (U : V) : V → V :=
  relPred U fun u v => tagVal v ∈ˢ tc (tagVal u)

theorem mem_tcPred {U u v : V} : v ∈ˢ tcPred U u ↔ v ∈ˢ U ∧ tagVal v ∈ˢ tc (tagVal u) :=
  mem_relPred

theorem tcPred_subset (U u : V) : tcPred U u ⊆ˢ U := relPred_subset _ _ u

/-- **Accessibility is free.**  Every member of an arbitrary index set
is accessible along `tcPred` — by ∈-induction on the payload
(`tc_induction_map`), with no fixed point, no monotonicity and no
closed tuple in sight.  This is the drop-in replacement for
`unionAcc_all`. -/
theorem tcAcc_all (U : V) :
    ∀ u, u ∈ˢ U → (pt : V) ∈ˢ app (accFam U (tcPred U) (fun _ => True)) u := by
  refine tc_induction_map (f := tagVal)
    (P := fun u => u ∈ˢ U → (pt : V) ∈ˢ app (accFam U (tcPred U) (fun _ => True)) u) ?_
  intro u ih hu
  refine accFam_intro (fun i _ => tcPred_subset U i) hu trivial fun v hv => ?_
  obtain ⟨hvU, hlt⟩ := mem_tcPred.mp hv
  exact ⟨pt, ih v hlt hvU⟩

/-! ## The encoding-depth lemmas

The fields of a value built by the uniform tuple encoding
`inj j (mkTower (fs ++ [pt]))` are ∈-below it, and so is the image of
a *reflexive* field at any argument.  These are the only facts an
instance needs to feed the kit. -/

theorem mem_tc_kpair_left (a b : V) : a ∈ˢ tc (kpair a b) :=
  mem_tc.mpr ⟨1, mem_sUnion_kpair_left a b⟩

theorem mem_tc_kpair_right (a b : V) : b ∈ˢ tc (kpair a b) :=
  mem_tc.mpr ⟨1, mem_sUnion_kpair_right a b⟩

/-- Every entry of a pair tower is a subterm of the tower. -/
theorem mem_tc_mkTower : ∀ (fs : List V) {a : V}, a ∈ fs → a ∈ˢ tc (Tower.mkTower fs)
  | [], _, h => absurd h (List.not_mem_nil)
  | b :: bs, a, h => by
    show a ∈ˢ tc (spair b (Tower.mkTower bs))
    rw [spair_eq_kpair]
    rcases List.mem_cons.mp h with rfl | h'
    · exact mem_tc_kpair_left _ _
    · exact tc_trans (mem_tc_mkTower bs h') (mem_tc_kpair_right _ _)

/-- **The constructor's fields are ∈-below the constructed value** —
at the uniform tuple encoding of a tagged constructor. -/
theorem mem_tc_inj_mkTower (j : Nat) (fs : List V) {a : V} (h : a ∈ fs) :
    a ∈ˢ tc (Tower.inj j (Tower.mkTower (fs ++ [pt]))) := by
  refine tc_trans (mem_tc_mkTower (fs ++ [pt]) (List.mem_append_left [pt] h)) ?_
  show _ ∈ˢ tc (spair (vnat j) _)
  rw [spair_eq_kpair]
  exact mem_tc_kpair_right _ _

theorem mem_tc_of_kpair_mem {f p v : V} (hm : kpair p v ∈ˢ f) : v ∈ˢ tc f :=
  tc_trans (mem_tc_kpair_right p v) (mem_tc_of_mem hm)

/-- **The image of a function is ∈-below it** — the reflexive field's
half of the depth obligation. -/
theorem app_mem_tc {A f p : V} {B : V → V} (hf : f ∈ˢ piSet A B) (hp : p ∈ˢ A) :
    app f p ∈ˢ tc f := by
  obtain ⟨-, htot⟩ := mem_piSet.mp hf
  obtain ⟨y, hy, huniq⟩ := htot p hp
  rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  exact mem_tc_of_kpair_mem hy

/-- **The reflexive telescope**: the image of a reflexive field at an
argument is ∈-below the constructed value. -/
theorem app_field_mem_tc {j : Nat} {fs : List V} {f : V} (hf : f ∈ fs) {A p : V} {B : V → V}
    (hpi : f ∈ˢ piSet A B) (hp : p ∈ˢ A) :
    app f p ∈ˢ tc (Tower.inj j (Tower.mkTower (fs ++ [pt]))) :=
  tc_trans (app_mem_tc hpi hp) (mem_tc_inj_mkTower j fs hf)

/-! ## The kit -/

section Kit

variable {ℓ k : Nat} {Is C : Nat → V}

/-- **The recursion data of a block over ORDINARY carriers**: the
motives and the step, with their two typing obligations — and nothing
else.  The predecessor map is not a parameter (it is `tcPred`), the
carriers `C` are arbitrary sets, and neither accessibility nor a
`PredsFrom`-style clause appears. -/
structure WfRecKit (ℓ k : Nat) (Is C : Nat → V) where
  /-- The motive fibres, over the tagged index. -/
  B : V → V
  /-- The step: the minors at the predecessors' recursive values. -/
  st : V → V → V
  /-- The motive is a set of the eliminating level. -/
  hB : ∀ u, u ∈ˢ unionSet k Is C → B u ∈ˢ (univ ℓ : V)
  /-- The step lands in the motive. -/
  hst : ∀ u, u ∈ˢ unionSet k Is C → ∀ g,
    g ∈ˢ piSet (tcPred (unionSet k Is C) u)
      (fun j => app (recGraph ℓ (unionSet k Is C) (tcPred (unionSet k Is C)) B st) j) →
    st u g ∈ˢ B u

namespace WfRecKit

variable (K : WfRecKit ℓ k Is C)

/-- The kit is a class kit at `tcPred`: `predSub` is separation and
`acc` is ∈-induction. -/
noncomputable def toC : UnionRecKitC ℓ k Is C :=
  ⟨tcPred (unionSet k Is C), K.B, K.st,
    fun u _ => tcPred_subset _ u,
    fun u hu => ⟨pt, tcAcc_all _ u hu⟩,
    K.hB, K.hst⟩

@[simp] theorem toC_pred : K.toC.pred = tcPred (unionSet k Is C) := rfl
@[simp] theorem toC_B : K.toC.B = K.B := rfl
@[simp] theorem toC_st : K.toC.st = K.st := rfl

/-- The kit's recursor at class `c`. -/
noncomputable def recAt (c : Nat) (i x : V) : V := K.toC.recAt c i x

theorem recAt_eq_recSel (c : Nat) (i x : V) :
    K.recAt c i x
      = recSel (recGraph ℓ (unionSet k Is C) (tcPred (unionSet k Is C)) K.B K.st)
          (tagged c i x) := rfl

/-- **Typing**: the recursor's value at a class element lies in the
motive. -/
theorem rec_mem_B {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    K.recAt c i x ∈ˢ K.B (tagged c i x) :=
  K.toC.rec_mem_B hc hi hx

/-- **The recursion equation**: the recursor at a class element is the
step at the recursor's graph over the value's ∈-predecessors. -/
theorem rec_eq {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    K.recAt c i x
      = K.st (tagged c i x)
          (graph
            (fun j => recSel (recGraph ℓ (unionSet k Is C) (tcPred (unionSet k Is C)) K.B K.st) j)
            (tcPred (unionSet k Is C) (tagged c i x))) :=
  K.toC.rec_eq hc hi hx

/-- The graph's values are typed — what the step's own proof consumes
at each predecessor. -/
theorem graph_mem_B {u v : V} (hu : u ∈ˢ unionSet k Is C)
    (hv : v ∈ˢ app (recGraph ℓ (unionSet k Is C) (tcPred (unionSet k Is C)) K.B K.st) u) :
    v ∈ˢ K.B u :=
  K.toC.graph_mem_B hu hv

end WfRecKit

end Kit

end ConLeche.SetTheory
