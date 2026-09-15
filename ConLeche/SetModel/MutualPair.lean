module

public import ConLeche.SetModel.UnionRec
@[expose] public section

/-!
# A two-member MUTUAL block, modelled UNIFORMLY (task #315)

The falsifying experiment for the uniform modelling of a mutual block:

    A ::= a0 | a1 (b : B)        B ::= b0 (a : A)

no parameters, no indices (each member's index-tuple set is `unitSet`,
whose only member is `pt`), constructors abstract injections into a
bounding set `U ∈ univ w` (`PairSig`).  Everything below is an
INSTANCE of the two kits — `ConLeche/SetTheory/Derive/LfpTuple.lean`
(the simultaneous carrier and Bekić's section law) and
`ConLeche/SetModel/UnionRec.lean` (the block's ONE recursion over the
disjoint union of its values) — with no new fixpoint machinery:

* the carrier is `pairL = lfpTuple w 2 pairIs pairPhi`, `A* = app
  (pairL 0) pt`, `B* = app (pairL 1) pt`, and the fixed-point equations
  read as the constructor descriptions (`mem_Astar`, `mem_Bstar`);
* **Bekić at each member** (`pairL_eq_section_A/B`): member `m`'s
  component IS the least pre-fixed family of its own section, and that
  section spells exactly the single-family reading, the OTHER member
  entering as the constant `B*` resp. `A*` — `app_secF_A`, `app_secF_B`
  — "the way a parameter does";
* the **simultaneous recursor** `pairRecA`/`pairRecB` is `unionRec` at a
  relation-defined predecessor map (`PairRel`, `pairPred`), with the
  three ι rules `pairRecA_a0`, `pairRecA_a1`, `pairRecB_b0` and the
  typing `pairRecA_mem`, `pairRecB_mem`.

**The hypotheses the instance needed beyond the kits** — all of them
fields of `PairSig`/`PairRecData`, none of them about the kits:

* `hU : U ∈ univ w` — the ONLY hypothesis the closed tuple needs: the
  constant tuple `i ↦ graph (_ ↦ U) unitSet` is closed because each
  component of `pairPhi` is a `sep U …` (`pairPhi_closed`); the
  constructors play no role there;
* closure, `mkA0 ∈ U`, `mkA1 : U → U`, `mkB0 : U → U` — needed ONLY to
  turn the `sep`-bounded fixed-point equation into the constructor
  description (`mem_Astar`, `mem_Bstar`), i.e. to put the constructors
  INTO the carrier;
* injectivity of `mkA1` and `mkB0` and the disjointness `mkA0 ≠ mkA1 b`
  — needed for the `PredsFrom` obligation (`pairPred_from`) and for the
  step's computation rules (`pairSt_a1`, `pairSt_b0`): they identify the
  predecessor set of a value with the tag of its recursive field.  The
  CROSS-member disjointness (`mkA0 ≠ mkB0 a`, `mkA1 b ≠ mkB0 a`) is NOT
  needed: the union's class tag separates the members;
* for the recursor, the motives' fibres in `univ ℓ` on the carriers and
  the three typed minors (`PairRecData`).

Everything is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The signature: two members, three abstract constructors -/

/-- The block's abstract constructor signature: injections into a
bounding set `U ∈ univ w`, injective and with `a0` apart from `a1`. -/
structure PairSig (V : Type u) [SetTheory V] where
  w : Nat
  U : V
  hU : U ∈ˢ (univ w : V)
  mkA0 : V
  mkA1 : V → V
  mkB0 : V → V
  mkA0_mem : mkA0 ∈ˢ U
  mkA1_mem : ∀ b, b ∈ˢ U → mkA1 b ∈ˢ U
  mkB0_mem : ∀ a, a ∈ˢ U → mkB0 a ∈ˢ U
  mkA1_inj : ∀ b b', mkA1 b = mkA1 b' → b = b'
  mkB0_inj : ∀ a a', mkB0 a = mkB0 a' → a = a'
  mkA0_ne_mkA1 : ∀ b, mkA0 ≠ mkA1 b

/-! ## The index sets, the operators, the tuple functor -/

/-- Neither member has indices: one index tuple, `pt`. -/
noncomputable def pairIs : Nat → V := fun _ => unitSet

theorem mem_pairIs {m : Nat} {i : V} (hi : i ∈ˢ (pairIs : Nat → V) m) : i = pt :=
  mem_unitSet_iff.mp hi

theorem pt_mem_pairIs (m : Nat) : (pt : V) ∈ˢ (pairIs : Nat → V) m := pt_mem_unitSet

/-- `A`'s operator: `a0`, or `a1` of a `B`-value. -/
noncomputable def pairOpA (S : PairSig V) (XB : V) : V :=
  sep S.U fun x => x = S.mkA0 ∨ ∃ b, b ∈ˢ XB ∧ x = S.mkA1 b

/-- `B`'s operator: `b0` of an `A`-value. -/
noncomputable def pairOpB (S : PairSig V) (XA : V) : V :=
  sep S.U fun x => ∃ a, a ∈ˢ XA ∧ x = S.mkB0 a

theorem pairOpA_mono (S : PairSig V) {XB XB' : V} (h : XB ⊆ˢ XB') :
    pairOpA S XB ⊆ˢ pairOpA S XB' := by
  intro x hx
  obtain ⟨hxU, hx⟩ := mem_sep.mp hx
  refine mem_sep.mpr ⟨hxU, ?_⟩
  rcases hx with hx | ⟨b, hb, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨b, h b hb, hx⟩

theorem pairOpB_mono (S : PairSig V) {XA XA' : V} (h : XA ⊆ˢ XA') :
    pairOpB S XA ⊆ˢ pairOpB S XA' := by
  intro x hx
  obtain ⟨hxU, a, ha, hx⟩ := mem_sep.mp hx
  exact mem_sep.mpr ⟨hxU, a, h a ha, hx⟩

/-- **The block's tuple functor**: component `0` is `A`'s operator read
at the `B` component, component `1` is `B`'s operator read at the `A`
component; positions `≥ 2` are junk. -/
noncomputable def pairPhi (S : PairSig V) (X : Nat → V) : Nat → V := fun m =>
  match m with
  | 0 => graph (fun _ => pairOpA S (app (X 1) pt)) unitSet
  | 1 => graph (fun _ => pairOpB S (app (X 0) pt)) unitSet
  | m + 2 => X (m + 2)

theorem app_pairPhi_zero (S : PairSig V) (X : Nat → V) :
    app (pairPhi S X 0) pt = pairOpA S (app (X 1) pt) :=
  app_graph pt_mem_unitSet

theorem app_pairPhi_one (S : PairSig V) (X : Nat → V) :
    app (pairPhi S X 1) pt = pairOpB S (app (X 0) pt) :=
  app_graph pt_mem_unitSet

/-- **The block's carrier**: the least pre-fixed tuple. -/
noncomputable def pairL (S : PairSig V) : Nat → V := lfpTuple S.w 2 pairIs (pairPhi S)

/-- `A`'s carrier. -/
noncomputable def Astar (S : PairSig V) : V := app (pairL S 0) pt

/-- `B`'s carrier. -/
noncomputable def Bstar (S : PairSig V) : V := app (pairL S 1) pt

/-! ## Step 1: the functor is monotone, space-preserving, and has a closed tuple -/

theorem pairPhi_mono (S : PairSig V) : MonoTuple S.w 2 pairIs (pairPhi S) := by
  intro X Y _ _ hle m hm
  have h0 : app (X 0) pt ⊆ˢ app (Y 0) pt := hle 0 (by omega) pt (pt_mem_pairIs 0)
  have h1 : app (X 1) pt ⊆ˢ app (Y 1) pt := hle 1 (by omega) pt (pt_mem_pairIs 1)
  intro i hi x hx
  obtain rfl := mem_pairIs hi
  match m, hm with
  | 0, _ =>
    rw [app_pairPhi_zero] at hx ⊢
    exact pairOpA_mono S h1 x hx
  | 1, _ =>
    rw [app_pairPhi_one] at hx ⊢
    exact pairOpB_mono S h0 x hx
  | _ + 2, hm => exact absurd hm (by omega)

theorem pairPhi_maps (S : PairSig V) : MapsTuple S.w 2 pairIs (pairPhi S) := by
  intro X _ m hm
  match m, hm with
  | 0, _ =>
    show graph (fun _ => pairOpA S (app (X 1) pt)) unitSet ∈ˢ famSpace S.w (unitSet : V)
    exact graph_mem_famSpace fun _ _ => univ_sep_mem S.hU
  | 1, _ =>
    show graph (fun _ => pairOpB S (app (X 0) pt)) unitSet ∈ˢ famSpace S.w (unitSet : V)
    exact graph_mem_famSpace fun _ _ => univ_sep_mem S.hU
  | _ + 2, hm => exact absurd hm (by omega)

/-- **The closed tuple**: the constant tuple at the bounding set `U` —
the only hypothesis used is `U ∈ univ w`, since every component of
`pairPhi` is a separation of `U`. -/
theorem pairPhi_closed (S : PairSig V) : ∃ L, IsClosedTuple S.w 2 pairIs (pairPhi S) L := by
  refine ⟨fun _ => graph (fun _ => S.U) unitSet, fun m _ => ?_, ?_⟩
  · show graph (fun _ => S.U) unitSet ∈ˢ famSpace S.w ((pairIs : Nat → V) m)
    exact graph_mem_famSpace fun _ _ => S.hU
  · intro m hm i hi x hx
    obtain rfl := mem_pairIs hi
    show x ∈ˢ app (graph (fun _ => S.U) unitSet) pt
    rw [app_graph pt_mem_unitSet]
    match m, hm with
    | 0, _ => rw [app_pairPhi_zero] at hx; exact sep_subset x hx
    | 1, _ => rw [app_pairPhi_one] at hx; exact sep_subset x hx
    | _ + 2, hm => exact absurd hm (by omega)

/-! ## Step 2: the fixed-point equations at the carriers -/

theorem Astar_eq (S : PairSig V) : pairOpA S (Bstar S) = Astar S := by
  have h := app_lfpTuple_eq (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (show 0 < 2 by omega) (pt_mem_pairIs 0)
  rw [app_pairPhi_zero] at h
  exact h

theorem Bstar_eq (S : PairSig V) : pairOpB S (Astar S) = Bstar S := by
  have h := app_lfpTuple_eq (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (show 1 < 2 by omega) (pt_mem_pairIs 1)
  rw [app_pairPhi_one] at h
  exact h

theorem Astar_subset_U (S : PairSig V) : Astar S ⊆ˢ S.U := by
  rw [← Astar_eq]
  exact sep_subset

theorem Bstar_subset_U (S : PairSig V) : Bstar S ⊆ˢ S.U := by
  rw [← Bstar_eq]
  exact sep_subset

/-- **`A`'s constructor description.** -/
theorem mem_Astar (S : PairSig V) {x : V} :
    x ∈ˢ Astar S ↔ x = S.mkA0 ∨ ∃ b, b ∈ˢ Bstar S ∧ x = S.mkA1 b := by
  rw [← Astar_eq]
  refine ⟨fun hx => (mem_sep.mp hx).2, ?_⟩
  rintro (rfl | ⟨b, hb, rfl⟩)
  · exact mem_sep.mpr ⟨S.mkA0_mem, Or.inl rfl⟩
  · exact mem_sep.mpr ⟨S.mkA1_mem b (Bstar_subset_U S b hb), Or.inr ⟨b, hb, rfl⟩⟩

/-- **`B`'s constructor description.** -/
theorem mem_Bstar (S : PairSig V) {x : V} :
    x ∈ˢ Bstar S ↔ ∃ a, a ∈ˢ Astar S ∧ x = S.mkB0 a := by
  rw [← Bstar_eq]
  refine ⟨fun hx => (mem_sep.mp hx).2, ?_⟩
  rintro ⟨a, ha, rfl⟩
  exact mem_sep.mpr ⟨S.mkB0_mem a (Astar_subset_U S a ha), a, ha, rfl⟩

theorem mkA0_mem_Astar (S : PairSig V) : S.mkA0 ∈ˢ Astar S :=
  (mem_Astar S).mpr (Or.inl rfl)

theorem mkA1_mem_Astar (S : PairSig V) {b : V} (hb : b ∈ˢ Bstar S) : S.mkA1 b ∈ˢ Astar S :=
  (mem_Astar S).mpr (Or.inr ⟨b, hb, rfl⟩)

theorem mkB0_mem_Bstar (S : PairSig V) {a : V} (ha : a ∈ˢ Astar S) : S.mkB0 a ∈ˢ Bstar S :=
  (mem_Bstar S).mpr ⟨a, ha, rfl⟩

/-! ## Step 3: Bekić — each member is the lfp of its own section -/

/-- **Bekić at member `A`**: `A`'s component of the carrier is the
least pre-fixed FAMILY of `A`'s section. -/
theorem pairL_eq_section_A (S : PairSig V) :
    pairL S 0 = lfpFamSet S.w unitSet (secF S.w pairIs (pairPhi S) (pairL S) 0) :=
  lfpTuple_eq_section (pairPhi_closed S) (pairPhi_mono S) (show 0 < 2 by omega)

/-- **Bekić at member `B`**. -/
theorem pairL_eq_section_B (S : PairSig V) :
    pairL S 1 = lfpFamSet S.w unitSet (secF S.w pairIs (pairPhi S) (pairL S) 1) :=
  lfpTuple_eq_section (pairPhi_closed S) (pairPhi_mono S) (show 1 < 2 by omega)

/-- **`A`'s section is the single-family reading**: the other member
enters as the CONSTANT `B*`, the way a parameter does. -/
theorem app_secF_A (S : PairSig V) {X : V} (hX : X ∈ˢ famSpace S.w (unitSet : V)) :
    app (secF S.w pairIs (pairPhi S) (pairL S) 0) X
      = graph (fun _ => sep S.U
          (fun x => x = S.mkA0 ∨ ∃ b, b ∈ˢ Bstar S ∧ x = S.mkA1 b)) unitSet := by
  have hX' : X ∈ˢ famSpace S.w ((pairIs : Nat → V) 0) := hX
  have h := app_secF (Φ := pairPhi S) (L := pairL S) (m := 0) hX'
  rw [h]
  show graph (fun _ => pairOpA S (app (updTuple (pairL S) 0 X 1) pt)) unitSet = _
  rw [updTuple_other (pairL S) X (by omega : (1 : Nat) ≠ 0)]
  rfl

/-- **`B`'s section is the single-family reading**, with `A*` constant. -/
theorem app_secF_B (S : PairSig V) {X : V} (hX : X ∈ˢ famSpace S.w (unitSet : V)) :
    app (secF S.w pairIs (pairPhi S) (pairL S) 1) X
      = graph (fun _ => sep S.U (fun x => ∃ a, a ∈ˢ Astar S ∧ x = S.mkB0 a)) unitSet := by
  have hX' : X ∈ˢ famSpace S.w ((pairIs : Nat → V) 1) := hX
  have h := app_secF (Φ := pairPhi S) (L := pairL S) (m := 1) hX'
  rw [h]
  show graph (fun _ => pairOpB S (app (updTuple (pairL S) 1 X 0) pt)) unitSet = _
  rw [updTuple_other (pairL S) X (by omega : (0 : Nat) ≠ 1)]
  rfl

/-! ## Step 4: the simultaneous recursor over the union -/

/-- The predecessor relation on tagged values, read off the
constructors: `a1 b`'s predecessor is `b` (in class `1`), `b0 a`'s is
`a` (in class `0`), `a0` has none. -/
def PairRel (S : PairSig V) (u v : V) : Prop :=
  (∃ b, u = tagged 0 pt (S.mkA1 b) ∧ v = tagged 1 pt b) ∨
  (∃ a, u = tagged 1 pt (S.mkB0 a) ∧ v = tagged 0 pt a)

/-- The predecessor SET: the relation separated off the union. -/
noncomputable def pairPred (S : PairSig V) (u : V) : V :=
  relPred (unionSet 2 pairIs (pairL S)) (PairRel S) u

theorem pairPred_subset (S : PairSig V) (u : V) :
    pairPred S u ⊆ˢ unionSet 2 pairIs (pairL S) := relPred_subset _ _ u

theorem mem_pairPred {S : PairSig V} {u v : V} :
    v ∈ˢ pairPred S u ↔ v ∈ˢ unionSet 2 pairIs (pairL S) ∧ PairRel S u v := mem_relPred

theorem not_mem_pairPred_a0 (S : PairSig V) {v : V} : ¬ v ∈ˢ pairPred S (tagged 0 pt S.mkA0) := by
  intro h
  rcases (mem_pairPred.mp h).2 with ⟨b, h1, -⟩ | ⟨a, h1, -⟩
  · exact S.mkA0_ne_mkA1 b (tagged_inj h1).2.2
  · exact absurd (tagged_inj h1).1 (by decide)

theorem mem_pairPred_a1 {S : PairSig V} {b v : V} :
    v ∈ˢ pairPred S (tagged 0 pt (S.mkA1 b)) ↔
      v ∈ˢ unionSet 2 pairIs (pairL S) ∧ v = tagged 1 pt b := by
  rw [mem_pairPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨b, rfl, h⟩⟩
  rcases h with ⟨b', h1, h2⟩ | ⟨a, h1, -⟩
  · rw [h2, S.mkA1_inj b b' (tagged_inj h1).2.2]
  · exact absurd (tagged_inj h1).1 (by decide)

theorem mem_pairPred_b0 {S : PairSig V} {a v : V} :
    v ∈ˢ pairPred S (tagged 1 pt (S.mkB0 a)) ↔
      v ∈ˢ unionSet 2 pairIs (pairL S) ∧ v = tagged 0 pt a := by
  rw [mem_pairPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inr ⟨a, rfl, h⟩⟩
  rcases h with ⟨b, h1, -⟩ | ⟨a', h1, h2⟩
  · exact absurd (tagged_inj h1).1 (by decide)
  · rw [h2, S.mkB0_inj a a' (tagged_inj h1).2.2]

/-- **The `PredsFrom` obligation**: at any tuple `X` below the carrier,
a value built by `pairPhi` from `X` has its predecessor in `X`'s union.
This is where injectivity of the constructors and the disjointness
`a0 ≠ a1 b` are used — they identify the predecessor set. -/
theorem pairPred_from (S : PairSig V) : PredsFrom S.w 2 pairIs (pairPhi S) (pairPred S) := by
  intro X _ _ c hc i hi x hx v hv
  obtain rfl := mem_pairIs hi
  obtain ⟨-, hrel⟩ := mem_pairPred.mp hv
  match c, hc with
  | 0, _ =>
    rw [app_pairPhi_zero] at hx
    obtain ⟨-, hx⟩ := mem_sep.mp hx
    rcases hrel with ⟨b', h1, rfl⟩ | ⟨a, h1, -⟩
    · have hx1 : x = S.mkA1 b' := (tagged_inj h1).2.2
      rcases hx with hx0 | ⟨b, hb, hxb⟩
      · exact absurd (hx0.symm.trans hx1) (S.mkA0_ne_mkA1 b')
      · rw [← S.mkA1_inj b b' (hxb.symm.trans hx1)]
        exact tagged_mem_unionSet (by omega) (pt_mem_pairIs 1) hb
    · exact absurd (tagged_inj h1).1 (by decide)
  | 1, _ =>
    rw [app_pairPhi_one] at hx
    obtain ⟨-, a, ha, hxa⟩ := mem_sep.mp hx
    rcases hrel with ⟨b, h1, -⟩ | ⟨a', h1, rfl⟩
    · exact absurd (tagged_inj h1).1 (by decide)
    · have hx1 : x = S.mkB0 a' := (tagged_inj h1).2.2
      rw [← S.mkB0_inj a a' (hxa.symm.trans hx1)]
      exact tagged_mem_unionSet (by omega) (pt_mem_pairIs 0) ha
  | _ + 2, hc => exact absurd hc (by omega)

/-! ### The bound and the step -/

open Classical in
/-- The bound: the two motives, dispatched on the class tag. -/
noncomputable def pairB (MA MB : V → V) (u : V) : V :=
  if h : ∃ x, u = tagged 0 pt x then MA (Classical.choose h)
  else if h : ∃ x, u = tagged 1 pt x then MB (Classical.choose h)
  else empty

theorem pairB_zero (MA MB : V → V) (x : V) : pairB MA MB (tagged 0 pt x) = MA x := by
  unfold pairB
  rw [dif_pos ⟨x, rfl⟩]
  have h := Classical.choose_spec (⟨x, rfl⟩ : ∃ y, (tagged 0 pt x : V) = tagged 0 pt y)
  exact congrArg MA (tagged_inj h).2.2.symm

theorem pairB_one (MA MB : V → V) (x : V) : pairB MA MB (tagged 1 pt x) = MB x := by
  unfold pairB
  rw [dif_neg (fun h : ∃ y, (tagged 1 pt x : V) = tagged 0 pt y =>
      absurd (tagged_inj h.choose_spec).1 (by decide)),
    dif_pos ⟨x, rfl⟩]
  have h := Classical.choose_spec (⟨x, rfl⟩ : ∃ y, (tagged 1 pt x : V) = tagged 1 pt y)
  exact congrArg MB (tagged_inj h).2.2.symm

open Classical in
/-- The step: the minor of the value's constructor, at the recursive
call read off the predecessor's tag. -/
noncomputable def pairSt (S : PairSig V) (mA0 : V) (mA1 mB0 : V → V → V) (u g : V) : V :=
  if u = tagged 0 pt S.mkA0 then mA0
  else if h : ∃ b, u = tagged 0 pt (S.mkA1 b) then
    mA1 (Classical.choose h) (app g (tagged 1 pt (Classical.choose h)))
  else if h : ∃ a, u = tagged 1 pt (S.mkB0 a) then
    mB0 (Classical.choose h) (app g (tagged 0 pt (Classical.choose h)))
  else empty

theorem pairSt_a0 (S : PairSig V) (mA0 : V) (mA1 mB0 : V → V → V) (g : V) :
    pairSt S mA0 mA1 mB0 (tagged 0 pt S.mkA0) g = mA0 := by
  unfold pairSt
  rw [if_pos rfl]

theorem pairSt_a1 (S : PairSig V) (mA0 : V) (mA1 mB0 : V → V → V) (b g : V) :
    pairSt S mA0 mA1 mB0 (tagged 0 pt (S.mkA1 b)) g = mA1 b (app g (tagged 1 pt b)) := by
  unfold pairSt
  rw [if_neg (fun h => S.mkA0_ne_mkA1 b (tagged_inj h).2.2.symm), dif_pos ⟨b, rfl⟩]
  have h := Classical.choose_spec
    (⟨b, rfl⟩ : ∃ b', (tagged 0 pt (S.mkA1 b) : V) = tagged 0 pt (S.mkA1 b'))
  rw [← S.mkA1_inj b _ (tagged_inj h).2.2]

theorem pairSt_b0 (S : PairSig V) (mA0 : V) (mA1 mB0 : V → V → V) (a g : V) :
    pairSt S mA0 mA1 mB0 (tagged 1 pt (S.mkB0 a)) g = mB0 a (app g (tagged 0 pt a)) := by
  unfold pairSt
  rw [if_neg (fun h => absurd (tagged_inj h).1 (by decide)),
    dif_neg (fun h : ∃ b, (tagged 1 pt (S.mkB0 a) : V) = tagged 0 pt (S.mkA1 b) =>
      absurd (tagged_inj h.choose_spec).1 (by decide)),
    dif_pos ⟨a, rfl⟩]
  have h := Classical.choose_spec
    (⟨a, rfl⟩ : ∃ a', (tagged 1 pt (S.mkB0 a) : V) = tagged 1 pt (S.mkB0 a'))
  rw [← S.mkB0_inj a _ (tagged_inj h).2.2]

/-! ### The recursion data, the recursor, the ι rules -/

/-- The recursion's motives and minors, typed at the carriers. -/
structure PairRecData {V : Type u} [SetTheory V] (S : PairSig V) where
  ℓ : Nat
  MA : V → V
  MB : V → V
  mA0 : V
  mA1 : V → V → V
  mB0 : V → V → V
  MA_mem : ∀ a, a ∈ˢ Astar S → MA a ∈ˢ (univ ℓ : V)
  MB_mem : ∀ b, b ∈ˢ Bstar S → MB b ∈ˢ (univ ℓ : V)
  mA0_typed : mA0 ∈ˢ MA S.mkA0
  mA1_typed : ∀ b ih, b ∈ˢ Bstar S → ih ∈ˢ MB b → mA1 b ih ∈ˢ MA (S.mkA1 b)
  mB0_typed : ∀ a ih, a ∈ˢ Astar S → ih ∈ˢ MA a → mB0 a ih ∈ˢ MB (S.mkB0 a)

section Recursion

variable {S : PairSig V} (D : PairRecData S)

/-- `A`'s recursor: the union recursor at class `0`. -/
noncomputable def pairRecA (x : V) : V :=
  unionRec D.ℓ S.w 2 pairIs (pairPhi S) (pairPred S) (pairB D.MA D.MB)
    (pairSt S D.mA0 D.mA1 D.mB0) 0 pt x

/-- `B`'s recursor: the union recursor at class `1`. -/
noncomputable def pairRecB (x : V) : V :=
  unionRec D.ℓ S.w 2 pairIs (pairPhi S) (pairPred S) (pairB D.MA D.MB)
    (pairSt S D.mA0 D.mA1 D.mB0) 1 pt x

theorem pairB_mem_univ :
    ∀ u, u ∈ˢ unionSet 2 pairIs (pairL S) → pairB D.MA D.MB u ∈ˢ (univ D.ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain rfl := mem_pairIs hi
  match c, hc with
  | 0, _ => rw [pairB_zero]; exact D.MA_mem x hx
  | 1, _ => rw [pairB_one]; exact D.MB_mem x hx
  | _ + 2, hc => exact absurd hc (by omega)

theorem pairSt_mem :
    ∀ u, u ∈ˢ unionSet 2 pairIs (pairL S) → ∀ g,
      g ∈ˢ piSet (pairPred S u) (fun j =>
        app (recGraph D.ℓ (unionSet 2 pairIs (pairL S)) (pairPred S) (pairB D.MA D.MB)
          (pairSt S D.mA0 D.mA1 D.mB0)) j) →
      pairSt S D.mA0 D.mA1 D.mB0 u g ∈ˢ pairB D.MA D.MB u := by
  intro u hu g hg
  have hval : ∀ j, j ∈ˢ pairPred S u → app g j ∈ˢ pairB D.MA D.MB j := by
    intro j hj
    have h := app_mem_of_mem_piSet hg hj
    rw [app_recGraph_eq (pairB_mem_univ D) (fun i _ => pairPred_subset S i)
      (pairPred_subset S u j hj)] at h
    exact (mem_recGraphFibre.mp h).1
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain rfl := mem_pairIs hi
  match c, hc with
  | 0, _ =>
    rcases (mem_Astar S).mp hx with rfl | ⟨b, hb, rfl⟩
    · rw [pairSt_a0, pairB_zero]
      exact D.mA0_typed
    · rw [pairSt_a1, pairB_zero]
      have h := hval (tagged 1 pt b)
        (mem_pairPred_a1.mpr ⟨tagged_mem_unionSet (by omega) (pt_mem_pairIs 1) hb, rfl⟩)
      rw [pairB_one] at h
      exact D.mA1_typed b _ hb h
  | 1, _ =>
    obtain ⟨a, ha, rfl⟩ := (mem_Bstar S).mp hx
    rw [pairSt_b0, pairB_one]
    have h := hval (tagged 0 pt a)
      (mem_pairPred_b0.mpr ⟨tagged_mem_unionSet (by omega) (pt_mem_pairIs 0) ha, rfl⟩)
    rw [pairB_zero] at h
    exact D.mB0_typed a _ ha h
  | _ + 2, hc => exact absurd hc (by omega)

/-- **Typing at `A`**: the recursor's value lies in the motive. -/
theorem pairRecA_mem {a : V} (ha : a ∈ˢ Astar S) : pairRecA D a ∈ˢ D.MA a := by
  have h := unionRec_mem_B (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (pairPred_from S) (pairB_mem_univ D) (pairSt_mem D) (show 0 < 2 by omega)
    (pt_mem_pairIs 0) ha
  rwa [pairB_zero] at h

/-- **Typing at `B`**. -/
theorem pairRecB_mem {b : V} (hb : b ∈ˢ Bstar S) : pairRecB D b ∈ˢ D.MB b := by
  have h := unionRec_mem_B (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (pairPred_from S) (pairB_mem_univ D) (pairSt_mem D) (show 1 < 2 by omega)
    (pt_mem_pairIs 1) hb
  rwa [pairB_one] at h

/-- **ι rule for `a0`**. -/
theorem pairRecA_a0 : pairRecA D S.mkA0 = D.mA0 := by
  have h := unionRec_eq (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (pairPred_from S) (pairB_mem_univ D) (pairSt_mem D) (show 0 < 2 by omega)
    (pt_mem_pairIs 0) (mkA0_mem_Astar S)
  rw [pairSt_a0] at h
  exact h

/-- **ι rule for `a1`**: the recursive call is `B`'s recursor. -/
theorem pairRecA_a1 {b : V} (hb : b ∈ˢ Bstar S) :
    pairRecA D (S.mkA1 b) = D.mA1 b (pairRecB D b) := by
  have h := unionRec_eq (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (pairPred_from S) (pairB_mem_univ D) (pairSt_mem D) (show 0 < 2 by omega)
    (pt_mem_pairIs 0) (mkA1_mem_Astar S hb)
  rw [pairSt_a1, app_graph (mem_pairPred_a1.mpr
    ⟨tagged_mem_unionSet (by omega) (pt_mem_pairIs 1) hb, rfl⟩)] at h
  exact h

/-- **ι rule for `b0`**: the recursive call is `A`'s recursor. -/
theorem pairRecB_b0 {a : V} (ha : a ∈ˢ Astar S) :
    pairRecB D (S.mkB0 a) = D.mB0 a (pairRecA D a) := by
  have h := unionRec_eq (pairPhi_closed S) (pairPhi_mono S) (pairPhi_maps S)
    (pairPred_from S) (pairB_mem_univ D) (pairSt_mem D) (show 1 < 2 by omega)
    (pt_mem_pairIs 1) (mkB0_mem_Bstar S ha)
  rw [pairSt_b0, app_graph (mem_pairPred_b0.mpr
    ⟨tagged_mem_unionSet (by omega) (pt_mem_pairIs 0) ha, rfl⟩)] at h
  exact h

end Recursion

end ConLeche.SetTheory
