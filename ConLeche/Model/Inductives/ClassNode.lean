module

public import ConLeche.SetModel.ClassFacts
public import ConLeche.Model.Annot.BlockLfp

public section

/-!
# A container class's node over the valuation space (P2d, DESIGN CLASSCHECK / P2D4)

The class facts' valuation space has one position per hole
(`ClassSpace.lean`).  A CONTAINER class `c` is read there as its
container's RECORDED clause: at a valuation `X`, its operator at a group
position `g` is the container's operator `D.Φ` at the frame `fr X` (the
key's parameters read at `X`, a function of `c`'s FREE positions only)
and the group read back through a section `s`, component `e g`
(`ClassNode.op`).  Two facts about it, both set-level:

* **the identification** (`ClassNode.car_eq`): in a class system whose
  class `c` is this operator, `c`'s carrier at a valuation `u` is the
  container's carrier at `fr u` — equality of least fixed points,
  `lfpTuple_group_eq` (no fill: `c`'s operator reads only its free and
  group positions);
* **goodness** (`ClassNode.opOk`): the operator maps, is monotone, and
  at a positive level accessible — from a SPINE PREDICATE `P` on
  valuations (the class's crests' fit at the valuation's hole frame), a
  good FILLER `fill` (the coherent classes' values and the duplicates'
  representatives, so the hole frame is coherent), and the
  identification `HFits ↔ P ∘ fill` (`Ident`).  The predicate's
  monotonicity and accessibility are T4's (`fieldD_mono`/`fieldD_acc` at
  the space's hole frames), its identification with the recorded fit is
  I2/I3 (`classCrest_spineFit_recorded`).

From them: the recorded carrier grows with the free positions and is
accessible in them (`carrier_mono`, `carrier_acc`), and the recorded fit
grows with the valuation (`hfits_mono`, the class kit's `fitMono`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-- **A container class's node over the valuation space** `(w, K, Is)`:
its container `D` at the levels `ψ`, its group positions `G` (component
`e g`, component `m`'s representative `s m`), its free positions `F`, and
the key's parameter frame `fr` at a valuation — reading only `F`,
satisfying the container's parameter telescope, at which the group's
index sets are the container's (N2). -/
structure ClassNode (acval : Name → (Name → Nat) → AnnotTerm) (w K : Nat) (Is : Nat → V) where
  D : LfpDatum V
  ψ : Name → Nat
  hcl : LfpClause acval D
  hw : D.w ψ = w
  G : Nat → Prop
  F : Nat → Prop
  e : Nat → Nat
  s : Nat → Nat
  fr : (Nat → V) → Nat → V
  hfr : ∀ Z Z', (∀ t, t < K → F t → Z t = Z' t) → fr Z = fr Z'
  hsat : ∀ Z, InTupleSpace w K Is Z → Sat V (D.params ψ).reverse (fr Z)
  hs : ∀ m, m < D.N → s m < K ∧ G (s m) ∧ e (s m) = m
  he : ∀ g, g < K → G g → e g < D.N
  hIs : ∀ Z, InTupleSpace w K Is Z → ∀ g, g < K → G g → Is g = D.idx ψ (fr Z) (e g)
  hGF : ∀ t, G t → ¬ F t

namespace ClassNode

variable {acval : Name → (Name → Nat) → AnnotTerm} {w K : Nat} {Is : Nat → V}
  (N : ClassNode acval w K Is)

/-- The empty tuple. -/
@[expose] noncomputable def emptyT (Is : Nat → V) : Nat → V := fun m => graph (fun _ => empty) (Is m)

theorem emptyT_mem : InTupleSpace w K Is (emptyT Is) :=
  fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ w

/-- The group read back through the section. -/
@[expose] noncomputable def thr (X : Nat → V) : Nat → V := thruT N.D.N N.s (fun _ => empty) X

open Classical in
/-- **The node's operator** on the whole space: the container's at the
key's frame, on the group; empty elsewhere. -/
@[expose] noncomputable def op : (Nat → V) → Nat → V :=
  fun X g => if N.G g then N.D.Φ N.ψ (N.fr X) (N.thr X) (N.e g) else emptyT Is g

theorem op_pos {X : Nat → V} {g : Nat} (hg : N.G g) :
    N.op X g = N.D.Φ N.ψ (N.fr X) (N.thr X) (N.e g) := by
  unfold op; rw [if_pos hg]

theorem op_neg {X : Nat → V} {g : Nat} (hg : ¬ N.G g) : N.op X g = emptyT Is g := by
  unfold op; rw [if_neg hg]

theorem hsIs (Z : Nat → V) (hZ : InTupleSpace w K Is Z) :
    ∀ g, g < K → N.G g → N.e g < N.D.N ∧ Is g = N.D.idx N.ψ (N.fr Z) (N.e g) :=
  fun g hg hG => ⟨N.he g hg hG, N.hIs Z hZ g hg hG⟩

/-- The group read back is in the container's tuple space at every frame. -/
theorem thr_mem {X : Nat → V} (hX : InTupleSpace w K Is X) (Z : Nat → V)
    (hZ : InTupleSpace w K Is Z) :
    InTupleSpace (N.D.w N.ψ) N.D.N (N.D.idx N.ψ (N.fr Z)) (N.thr X) := by
  rw [N.hw]
  exact inTupleSpace_through N.hs (N.hsIs Z hZ) hX

theorem thr_le {X X' : Nat → V} (hle : TupleLe K Is X X') (Z : Nat → V)
    (hZ : InTupleSpace w K Is Z) :
    TupleLe N.D.N (N.D.idx N.ψ (N.fr Z)) (N.thr X) (N.thr X') :=
  tupleLe_through N.hs (N.hsIs Z hZ) hle

/-- **The node's operator maps the space.** -/
theorem op_maps : MapsTuple w K Is N.op := by
  intro X hX g hg
  by_cases hG : N.G g
  · rw [N.op_pos hG]
    have hm := (N.hcl.functor N.ψ (N.fr X) (N.hsat X hX)).2.1 _ (N.thr_mem hX X hX) _
      (N.he g hg hG)
    rw [← N.hIs X hX g hg hG, N.hw] at hm
    exact hm
  · rw [N.op_neg hG]; exact emptyT_mem g hg

/-! ## The identification: the class's carrier is the container's -/

/-- **The identification** (see the module docstring): the node's
section at a valuation `u` (its group the lfp variable, its free
positions `u`, the rest `base`) has, on the group, the container's
carrier at the key's frame `fr u` as its least tuple. -/
theorem ccar_eq (base : Nat → V) {u : Nat → V} (hu : InTupleSpace w K Is u) :
    ∀ g, g < K → N.G g → ccar w K Is N.G N.F base N.op u g = N.D.carrier N.ψ (N.fr u) (N.e g) := by
  -- the frame of the section is `u`'s, its group read back `Y`'s
  have hfrm : ∀ Y, N.fr (mixT N.G (nrmT N.F base u) Y) = N.fr u := by
    intro Y
    refine N.hfr _ _ fun t _ ht => ?_
    unfold mixT nrmT mixT
    rw [if_neg (N.hGF t · ht), if_pos ht]
  have hthr : ∀ Y, N.thr (mixT N.G (nrmT N.F base u) Y) = N.thr Y := by
    intro Y
    unfold thr
    refine thruT_congr fun m hm => ?_
    unfold mixT
    rw [if_pos (N.hs m hm).2.1]
  have hfun := N.hcl.functor N.ψ (N.fr u) (N.hsat u hu)
  rw [N.hw] at hfun
  intro g hg hGg
  unfold ccar LfpDatum.carrier
  rw [N.hw]
  exact lfpTuple_group_eq (N := N.D.N) (IsD := N.D.idx N.ψ (N.fr u))
    (ΦD := N.D.Φ N.ψ (N.fr u)) (G := N.G) (e := N.e) (s := N.s) (C := emptyT Is)
    (C0 := fun _ => empty)
    N.hs (N.hsIs u hu) emptyT_mem
    (fun Y _ g _ hG => by
      show N.op _ g = _
      rw [N.op_pos hG, hfrm, hthr]; rfl)
    (fun Y _ g _ hG => by show N.op _ g = _; rw [N.op_neg hG])
    hfun.2.2 hfun.1 hfun.2.1 g hg hGg

/-- **The identification in a class system** whose class `c` is the node
(group `G`, free positions `F`, operator `op`, nothing filled). -/
theorem car_eq (S : ClassSys V) (c : Nat) (hSw : S.w = w) (hSK : S.K = K) (hSIs : S.Is = Is)
    (hG : S.grp c = N.G) (hF : S.free c = N.F) (hΦ : S.Φ c = N.op) (hfl : S.fl c = [])
    {u : Nat → V} (hu : InTupleSpace w K Is u) :
    ∀ g, g < K → N.G g → S.car c u g = N.D.carrier N.ψ (N.fr u) (N.e g) := by
  subst hSw hSK hSIs
  have hΨ : S.Ψ c = N.op := by
    funext v
    unfold ClassSys.Ψ
    rw [hfl, hΦ]
    rfl
  unfold ClassSys.car
  rw [hΨ, hG, hF]
  exact N.ccar_eq S.base hu

/-! ## Goodness, from a spine predicate at filled valuations -/

/-- **The node's identification data**: a filler and a spine predicate on
valuations such that the container's fit at a valuation's frame (the
group read back) is the predicate at the filled valuation. -/
structure Ident where
  fill : (Nat → V) → Nat → V
  P : (Nat → V) → Nat → V → Nat → List V → Prop
  hid : ∀ X, InTupleSpace w K Is X → ∀ g, g < K → N.G g → ∀ t, t ∈ˢ Is g → ∀ j fs,
    N.D.HFits N.ψ (N.fr X) (N.thr X) t (N.e g) j fs ↔ P (fill X) g t j fs

variable {N}

/-- The element predicate of an identification. -/
@[expose] def Ident.Pel (I : N.Ident) : (Nat → V) → Nat → V → V → Prop :=
  fun Z g t x => N.G g ∧ ∃ j fs, I.P Z g t j fs ∧ x = N.D.inj N.ψ (N.e g) j fs

/-- **The operator's fibres are the element predicate at the filled
valuation.** -/
theorem Ident.fibre (I : N.Ident) {X : Nat → V} (hX : InTupleSpace w K Is X) {g : Nat}
    (hg : g < K) {t : V} (ht : t ∈ˢ Is g) (x : V) :
    x ∈ˢ app (N.op X g) t ↔ I.Pel (I.fill X) g t x := by
  by_cases hG : N.G g
  · rw [N.op_pos hG]
    have hti : t ∈ˢ N.D.idx N.ψ (N.fr X) (N.e g) := by rw [← N.hIs X hX g hg hG]; exact ht
    rw [N.hcl.fibre N.ψ (N.fr X) (N.hsat X hX) (N.thr X) (N.thr_mem hX X hX) (N.e g)
      (N.he g hg hG) t hti x]
    unfold Ident.Pel
    refine ⟨fun ⟨j, fs, hf, hx⟩ => ⟨hG, j, fs, (I.hid X hX g hg hG t ht j fs).mp hf, hx⟩,
      fun ⟨_, j, fs, hf, hx⟩ => ⟨j, fs, (I.hid X hX g hg hG t ht j fs).mpr hf, hx⟩⟩
  · rw [N.op_neg hG]
    unfold emptyT Ident.Pel
    rw [app_graph ht]
    exact ⟨fun h => absurd h (not_mem_empty x), fun h => absurd h.1 hG⟩

/-- **The node's operator is good**: its fibres are a spine predicate at
a good filler's valuation, monotone and — at a positive level —
accessible. -/
theorem opOk (I : N.Ident) (hfill : OpOk w K Is I.fill)
    (hmono : ∀ Z Z', InTupleSpace w K Is Z → InTupleSpace w K Is Z' → TupleLe K Is Z Z' →
      ∀ g, g < K → N.G g → ∀ t, t ∈ˢ Is g → ∀ j fs, I.P Z g t j fs → I.P Z' g t j fs)
    (hacc : w ≠ 0 → ∃ A, A ∈ˢ (univ w : V) ∧ AccPred w K Is I.Pel A) :
    OpOk w K Is N.op :=
  opOk_of_pred hfill N.op_maps (fun _ hX _ hm _ hi x => I.fibre hX hm hi x)
    (fun Z Z' hZ hZ' hle m hm i hi _ ⟨hG, j, fs, hP, hx⟩ =>
      ⟨hG, j, fs, hmono Z Z' hZ hZ' hle m hm hG i hi j fs hP, hx⟩) hacc

variable (N)

/-! ## The consumers' facts -/

/-- **The container's carrier grows with the class's free positions.** -/
theorem carrier_mono (hok : OpOk w K Is N.op) {base : Nat → V} (hbase : InTupleSpace w K Is base)
    {u u' : Nat → V} (hu : InTupleSpace w K Is u) (hu' : InTupleSpace w K Is u')
    (hle : ∀ m, m < K → N.F m → FamLe (Is m) (u m) (u' m)) :
    ∀ g, g < K → N.G g →
      FamLe (Is g) (N.D.carrier N.ψ (N.fr u) (N.e g)) (N.D.carrier N.ψ (N.fr u') (N.e g)) := by
  intro g hg hG
  rw [← N.ccar_eq base hu g hg hG, ← N.ccar_eq base hu' g hg hG]
  exact ccar_mono_free hbase hok hu hu' hle g hg

/-- **The container's carrier is accessible in the class's valuation**
(at a positive level), through the node's section. -/
theorem carrier_acc (hok : OpOk w K Is N.op) (hw : w ≠ 0) {base : Nat → V}
    (hbase : InTupleSpace w K Is base) :
    ∃ A, A ∈ˢ (univ w : V) ∧ AccTuple w K Is K Is (ccar w K Is N.G N.F base N.op) A ∧
      ∀ u, InTupleSpace w K Is u → ∀ g, g < K → N.G g →
        ccar w K Is N.G N.F base N.op u g = N.D.carrier N.ψ (N.fr u) (N.e g) := by
  obtain ⟨A, hA, hacc⟩ := hok.2.2 hw
  exact ⟨accPaths A, accPaths_mem hw hA, ccar_acc hbase hok hacc,
    fun u hu => N.ccar_eq base hu⟩

/-- **(W) of the node's section at every valuation.** -/
theorem closed (hok : OpOk w K Is N.op) {base : Nat → V} (hbase : InTupleSpace w K Is base)
    {u : Nat → V} (hu : InTupleSpace w K Is u) :
    ∃ L, IsClosedTuple w K Is (secOp N.G N.F base N.op u) L :=
  secOp_closed hbase hok hu

variable {N}

/-- **The container's fit grows with the valuation** (the class kit's
`fitMono`): along the filler and the predicate. -/
theorem Ident.hfits_mono (I : N.Ident) (hfill : OpOk w K Is I.fill)
    (hmono : ∀ Z Z', InTupleSpace w K Is Z → InTupleSpace w K Is Z' → TupleLe K Is Z Z' →
      ∀ g, g < K → N.G g → ∀ t, t ∈ˢ Is g → ∀ j fs, I.P Z g t j fs → I.P Z' g t j fs)
    {X X' : Nat → V} (hX : InTupleSpace w K Is X) (hX' : InTupleSpace w K Is X')
    (hle : TupleLe K Is X X') {g : Nat} (hg : g < K) (hG : N.G g) {t : V} (ht : t ∈ˢ Is g)
    {j : Nat} {fs : List V} (hf : N.D.HFits N.ψ (N.fr X) (N.thr X) t (N.e g) j fs) :
    N.D.HFits N.ψ (N.fr X') (N.thr X') t (N.e g) j fs := by
  rw [I.hid X hX g hg hG t ht j fs] at hf
  rw [I.hid X' hX' g hg hG t ht j fs]
  exact hmono _ _ (hfill.1 X hX) (hfill.1 X' hX') (hfill.2.1 X X' hX hX' hle) g hg hG t ht j fs hf

end ClassNode



/-! ## The class system of the nodes, by rank -/

namespace ClassNode

variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- **Every node's operator is good, by rank**: in a class system whose
classes are nodes (nothing filled in the operators), if every node's
identification has a filler that is good as soon as every class of a
smaller rank spliced in is, and a spine predicate monotone and (at a
positive level) accessible, then every class's operator — and every
class spliced into the frame — is good. -/
theorem sys_good (S : ClassSys V) (N : Nat → ClassNode acval S.w S.K S.Is)
    (hΦ : ∀ c, S.Φ c = (N c).op) (I : ∀ c, (N c).Ident)
    (hfill : ∀ c, (∀ d, S.rk d < S.rk c → OpOk S.w S.K S.Is (S.T d)) →
      OpOk S.w S.K S.Is (I c).fill)
    (hmono : ∀ c Z Z', InTupleSpace S.w S.K S.Is Z → InTupleSpace S.w S.K S.Is Z' →
      TupleLe S.K S.Is Z Z' → ∀ g, g < S.K → (N c).G g → ∀ t, t ∈ˢ S.Is g → ∀ j fs,
        (I c).P Z g t j fs → (I c).P Z' g t j fs)
    (hacc : ∀ c, S.w ≠ 0 → ∃ A, A ∈ˢ (univ S.w : V) ∧ AccPred S.w S.K S.Is (I c).Pel A) :
    ∀ c, OpOk S.w S.K S.Is (S.Φ c) ∧ OpOk S.w S.K S.Is (S.T c) :=
  S.good_step fun c hlow => by
    rw [hΦ c]
    exact (N c).opOk (I c) (hfill c hlow) (hmono c) (hacc c)

end ClassNode

end ConLeche.Model
