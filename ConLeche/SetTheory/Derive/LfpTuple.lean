module

public import ConLeche.SetTheory.Derive.LfpFam
@[expose] public section

/-!
# Least pre-fixed points of TUPLE functors (task #315)

The carrier of a block of `k` inductive families `T₀ … T_{k-1}` is the
simultaneous least pre-fixed point of its constructor-tower functor
acting on **tuples of families** — a meta-level tuple `X : Nat → V`
whose `m`-th component (`m < k`) is a family over member `m`'s own
index-tuple set `Is m` (`famSpace w (Is m)`), ordered componentwise
(`TupleLe`).

In this first-order development:
* `DefTupleOp k Φ` packages `k`-cutoff extensionality and `DefFun k`
  definability of `(X₀, …, X_{k-1}) ↦ Φ (padTuple xs) m` for `m < k`,
  collapsing quantification over closed tuples `X : Nat → V` to a
  finite block of `k` first-order set quantifiers.
* `lfpTuple w k Is Φ hΦ` carries `DefTupleOp k Φ`, uses proof-carrying
  `sep` and `famOf`, and admits an extensional `DefFun` closure lemma
  (`DefFun.lfpTuple_apply` / `defFun_lfpTuple`) that never unfolds the
  `Classical.choose` upper bound.
* `sepTuple` and `lfpTuple_induction` carry explicit `HasSep` /
  `HasGraph` guards, with `sepTuple_of_def` and
  `lfpTuple_induction_of_def` discharging them from `DefRel 2`.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Finite tuple padding and `Fin k → V` quantifiers -/

/-- Pad a `Fin k → V` tuple to `Nat → V`, returning `empty` at indices `≥ k`. -/
noncomputable def padTuple {k : Nat} (xs : Fin k → V) (m : Nat) : V :=
  if h : m < k then xs ⟨m, h⟩ else empty

@[simp] theorem padTuple_lt {k : Nat} (xs : Fin k → V) {m : Nat} (hm : m < k) :
    padTuple xs m = xs ⟨m, hm⟩ := by
  simp [padTuple, hm]

@[simp] theorem padTuple_ge {k : Nat} (xs : Fin k → V) {m : Nat} (hm : k ≤ m) :
    padTuple xs m = empty := by
  simp [padTuple, Nat.not_lt_of_le hm]

/-- Prefix slice of `Fin (k + p) → V`. -/
def ftake {k p : Nat} (v : Fin (k + p) → V) : Fin k → V :=
  fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k p)⟩

/-- Suffix slice of `Fin (k + p) → V`. -/
def fdrop {k p : Nat} (v : Fin (k + p) → V) : Fin p → V :=
  fun j => v ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩

theorem DefFun.ftake_proj {k p : Nat} (i : Fin k) :
    DefFun (k + p) fun v : Fin (k + p) → V => ftake v i :=
  (DefFun.proj (V := V) ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k p)⟩).congr
    fun _ => rfl

theorem DefFun.fdrop_proj {k p : Nat} (j : Fin p) :
    DefFun (k + p) fun v : Fin (k + p) → V => fdrop v j :=
  (DefFun.proj (V := V) ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩).congr
    fun _ => rfl

omit [SetTheory V] in
@[simp] theorem ftake_fappend {k p : Nat} (xs : Fin k → V) (ps : Fin p → V) :
    ftake (fappend xs ps) = xs := by
  funext i; exact fappend_left xs ps i

omit [SetTheory V] in
@[simp] theorem fdrop_fappend {k p : Nat} (xs : Fin k → V) (ps : Fin p → V) :
    fdrop (fappend xs ps) = ps := by
  funext j; exact fappend_right xs ps j

theorem DefFun.fdrop_apply {k p : Nat} {G : (Fin p → V) → V} (hG : DefFun p G) :
    DefFun (k + p) fun v => G (fdrop v) :=
  hG.reIndex fun j => ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩

theorem DefRel.fdrop_apply {k p : Nat} {R : (Fin p → V) → Prop} (hR : DefRel p R) :
    DefRel (k + p) fun v => R (fdrop v) :=
  hR.reIndex fun j => ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩

theorem DefRel.exists_fin {k p : Nat} {R : (Fin (k + p) → V) → Prop}
    (hR : DefRel (k + p) R) :
    DefRel p fun env => ∃ xs : Fin k → V, R (fappend xs env) := by
  induction k with
  | zero =>
    refine (hR.reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add p)⟩).congr
      fun env => ?_
    have heqv : (fun i : Fin (0 + p) => env ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add p)⟩) =
        fappend Fin.elim0 env := by
      funext i
      rw [fappend_ge Fin.elim0 env (Nat.zero_le i.val)]
      rfl
    rw [heqv]
    exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨xs, h⟩ => by
      have h0 : xs = Fin.elim0 := funext fun i => Fin.elim0 i
      rwa [h0] at h⟩
  | succ k ih =>
    have h1 : DefRel ((k + p) + 1) fun w =>
        R (fun i => fcons (w 0) (ftail w) ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩) :=
      (hR.reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩).congr fun w => by
        rw [fcons_zero_ftail w]
    have h2 : DefRel (k + p) fun v =>
        ∃ x, R (fun i => fcons x v ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩) :=
      DefRel.exists_curry h1
    refine (ih h2).congr fun env => ?_
    constructor
    · rintro ⟨xs, x, h⟩
      refine ⟨fcons x xs, ?_⟩
      have heqv : (fun i : Fin ((k + 1) + p) =>
          fcons x (fappend xs env) ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩) =
          fappend (fcons x xs) env := by
        funext i
        exact fcons_fappend x xs env ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩
      rwa [heqv] at h
    · rintro ⟨xs, h⟩
      refine ⟨ftail xs, xs 0, ?_⟩
      have heqv : (fun i : Fin ((k + 1) + p) =>
          fcons (xs 0) (fappend (ftail xs) env) ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩) =
          fappend xs env := by
        funext i
        rw [fcons_fappend (xs 0) (ftail xs) env
          ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩]
        congr 1
        exact fcons_zero_ftail xs
      rwa [heqv]

theorem DefRel.forall_fin {k p : Nat} {R : (Fin (k + p) → V) → Prop}
    (hR : DefRel (k + p) R) :
    DefRel p fun env => ∀ xs : Fin k → V, R (fappend xs env) :=
  (DefRel.exists_fin hR.not).not.congr fun _env =>
    ⟨fun h xs => Classical.byContradiction fun hnx => h ⟨xs, hnx⟩,
     fun h ⟨xs, hnx⟩ => hnx (h xs)⟩

/-! ## The tuple space and its order -/

/-- The tuple lies in the product of the members' family spaces
(positions `≥ k` are unconstrained junk). -/
def InTupleSpace (w k : Nat) (Is : Nat → V) (X : Nat → V) : Prop :=
  ∀ m, m < k → X m ∈ˢ famSpace w (Is m)

/-- The tuple is a tuple of families of TYPES: each member's fibres lie
in `univ w`, not necessarily in the strict universe (task #342). -/
def InTupleSpaceU (w k : Nat) (Is : Nat → V) (X : Nat → V) : Prop :=
  ∀ m, m < k → X m ∈ˢ famSpaceIn (univ w) (Is m)

theorem InTupleSpace.toU {w k : Nat} {Is X : Nat → V} (h : InTupleSpace w k Is X) :
    InTupleSpaceU w k Is X :=
  fun m hm => famSpace_subset_univ w (Is m) _ (h m hm)

/-- The componentwise order on tuples of families. -/
def TupleLe (k : Nat) (Is : Nat → V) (X Y : Nat → V) : Prop :=
  ∀ m, m < k → FamLe (Is m) (X m) (Y m)

theorem TupleLe.refl (k : Nat) (Is X : Nat → V) : TupleLe k Is X X :=
  fun m _ => FamLe.refl (Is m) (X m)

/-- A `Φ`-closed tuple: a pre-fixed point of `Φ` in the tuple space. -/
def IsClosedTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (X : Nat → V) : Prop :=
  InTupleSpace w k Is X ∧ TupleLe k Is (Φ X) X

/-- Monotonicity of a tuple functor on the tuple space. -/
def MonoTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X Y, InTupleSpace w k Is X → InTupleSpace w k Is Y → TupleLe k Is X Y →
    TupleLe k Is (Φ X) (Φ Y)

/-- The functor maps the tuple space into itself. -/
def MapsTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X, InTupleSpace w k Is X → InTupleSpace w k Is (Φ X)

/-- First-order definability + `k`-cutoff extensionality for a tuple
functor `Φ : (Nat → V) → Nat → V`. -/
def DefTupleOp (k : Nat) (Φ : (Nat → V) → Nat → V) : Prop :=
  (∀ X Y, (∀ m, m < k → X m = Y m) → ∀ m, m < k → Φ X m = Φ Y m) ∧
  (∀ m, m < k → DefFun k fun xs : Fin k → V => Φ (padTuple xs) m)

theorem isClosedTuple_pad_iff {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) (X : Nat → V) :
    IsClosedTuple w k Is Φ X ↔
      IsClosedTuple w k Is Φ (padTuple fun i : Fin k => X i.val) := by
  have heq : ∀ m, m < k → X m = padTuple (fun i : Fin k => X i.val) m := fun m hm => by
    rw [padTuple_lt _ hm]
  have hΦeq : ∀ m, m < k → Φ X m = Φ (padTuple fun i : Fin k => X i.val) m :=
    hΦ.1 X _ heq
  unfold IsClosedTuple InTupleSpace TupleLe
  constructor
  · rintro ⟨hsp, hle⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [← heq m hm]; exact hsp m hm
    · rw [← heq m hm, ← hΦeq m hm]; exact hle m hm
  · rintro ⟨hsp, hle⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [heq m hm]; exact hsp m hm
    · rw [heq m hm, hΦeq m hm]; exact hle m hm

theorem exists_isClosedTuple_iff_fin {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) :
    (∃ L, IsClosedTuple w k Is Φ L) ↔
      ∃ xs : Fin k → V, IsClosedTuple w k Is Φ (padTuple xs) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun i => L i.val, (isClosedTuple_pad_iff hΦ L).mp hL⟩
  · rintro ⟨xs, hxs⟩
    exact ⟨padTuple xs, hxs⟩

theorem forall_isClosedTuple_iff_fin {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) {m : Nat} (hm : m < k) (i x : V) :
    (∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i) ↔
      (∀ xs : Fin k → V, IsClosedTuple w k Is Φ (padTuple xs) → x ∈ˢ app (xs ⟨m, hm⟩) i) := by
  constructor
  · intro h xs hxs
    have hmem := h (padTuple xs) hxs
    rwa [padTuple_lt xs hm] at hmem
  · intro h X hX
    have hmem := h (fun j => X j.val) ((isClosedTuple_pad_iff hΦ X).mp hX)
    exact hmem

theorem forall_isClosedTuple_ge_false {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) (hcl : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} (hm : ¬ m < k)
    (i x : V) :
    ¬ (∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i) := by
  intro hall
  obtain ⟨L, hL⟩ := hcl
  let L' : Nat → V := fun j => if j = m then empty else L j
  have hcut : ∀ j, j < k → L' j = L j := fun j hj => by
    dsimp only [L']
    have hne : j ≠ m := fun heq => hm (heq ▸ hj)
    exact ite_eq_right hne
  have hL' : IsClosedTuple w k Is Φ L' := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [hcut j hj]; exact hL.1 j hj
    · rw [hΦ.1 L' L hcut j hj, hcut j hj]; exact hL.2 j hj
  have hmem : x ∈ˢ app (L' m) i := hall L' hL'
  have hLm : L' m = empty := by dsimp only [L']; exact ite_eq_left rfl
  rw [hLm, app_empty] at hmem
  exact not_mem_empty x hmem

/-! ## Definability of closed tuples and `lfpTuple` -/

theorem defRel_isClosedTuple_pad {w k p : Nat}
    {Is : (Fin p → V) → Nat → V}
    {Φ : (Fin p → V) → (Nat → V) → Nat → V}
    (hIs : ∀ m, m < k → DefFun p fun env => Is env m)
    (hΦ_def : ∀ m, m < k → DefFun (k + p) fun v => Φ (fdrop v) (padTuple (ftake v)) m) :
    DefRel (k + p) fun v =>
      IsClosedTuple w k (Is (fdrop v)) (Φ (fdrop v)) (padTuple (ftake v)) := by
  unfold IsClosedTuple InTupleSpace TupleLe
  refine DefRel.and (DefRel.finForall_lt fun m hm => ?_) (DefRel.finForall_lt fun m hm => ?_)
  · exact DefRel.mem_apply
      ((DefFun.ftake_proj ⟨m, hm⟩).congr fun v => (padTuple_lt (ftake v) hm).symm)
      (DefFun.famSpace_apply w (DefFun.fdrop_apply (hIs m hm)))
  · exact DefRel.famLe_apply
      (DefFun.fdrop_apply (hIs m hm))
      (hΦ_def m hm)
      ((DefFun.ftake_proj ⟨m, hm⟩).congr fun v => (padTuple_lt (ftake v) hm).symm)

theorem hasSep_lfpTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (m : Nat) (a i : V) :
    HasSep a (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i) := by
  by_cases hm : m < k
  · have hcl : DefRel (k + 1) fun v =>
        IsClosedTuple w k Is Φ (padTuple (ftake v)) :=
      defRel_isClosedTuple_pad (p := 1) (Is := fun _ => Is) (Φ := fun _ => Φ)
        (fun j _ => DefFun.const (Is j))
        (fun j hj => (hΦ.2 j hj).reIndex fun c =>
          ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right k 1)⟩)
    have himp : DefRel (k + 1) fun v =>
        IsClosedTuple w k Is Φ (padTuple (ftake v)) →
          fdrop v 0 ∈ˢ app (ftake v ⟨m, hm⟩) i :=
      DefRel.imp hcl
        (DefRel.mem_apply
          (DefFun.fdrop_proj (k := k) (p := 1) 0)
          (DefFun.app_apply (DefFun.ftake_proj ⟨m, hm⟩) (DefFun.const i)))
    have hfin := DefRel.forall_fin himp
    have hpred : DefPred fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i :=
      hfin.congr fun v => by
        simp only [ftake_fappend, fdrop_fappend]
        exact (forall_isClosedTuple_iff_fin hΦ hm i (v 0)).symm
    exact hasSep_of_defPred hpred
  · by_cases hcl : ∃ L, IsClosedTuple w k Is Φ L
    · have hpred : DefPred fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i :=
        DefRel.false.congr fun v =>
          ⟨False.elim, fun hall => forall_isClosedTuple_ge_false hΦ hcl hm i (v 0) hall⟩
      exact hasSep_of_defPred hpred
    · have hpred : DefPred fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i :=
        DefRel.true.congr fun _ =>
          ⟨fun _ X hX => absurd ⟨X, hX⟩ hcl, fun _ => trivial⟩
      exact hasSep_of_defPred hpred

open Classical in
/-- Fibrewise construction of component `m` of `lfpTuple`. -/
noncomputable def lfpTupleFibre (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (m : Nat) (i : V) : V :=
  if h : ∃ L, IsClosedTuple w k Is Φ L then
    dropTo (strictU w) (sep (app (Classical.choose h m) i)
      (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i)
      (hasSep_lfpTuple w k Is Φ hΦ m (app (Classical.choose h m) i) i))
  else empty

theorem defFun_lfpTupleFibre_apply {w k p : Nat}
    {Is : (Fin p → V) → Nat → V}
    {Φ : (Fin p → V) → (Nat → V) → Nat → V}
    (hIs : ∀ m, m < k → DefFun p fun env => Is env m)
    (hΦ : ∀ env, DefTupleOp k (Φ env))
    (hΦ_def : ∀ m, m < k → DefFun (k + p) fun v => Φ (fdrop v) (padTuple (ftake v)) m)
    {m : Nat} (hm : m < k) :
    DefFun (p + 1) fun v =>
      lfpTupleFibre w k (Is (ftail v)) (Φ (ftail v)) (hΦ (ftail v)) m (v 0) := by
  let shift (r : Nat) (idx : Fin (k + p)) : Fin (k + (p + r)) :=
    if h : idx.val < k then ⟨idx.val, Nat.lt_of_lt_of_le h (Nat.le_add_right k (p + r))⟩
    else ⟨idx.val + r, by omega⟩
  have ftake_shift : ∀ (r : Nat) (v : Fin (k + (p + r)) → V),
      ftake (fun i => v (shift r i)) = ftake v := fun r v => by
    funext ⟨i, hi⟩
    dsimp only [ftake, shift]
    simp [hi]
  have fdrop_shift : ∀ (r : Nat) (v : Fin (k + (p + r)) → V),
      fdrop (fun i => v (shift r i)) = fun j : Fin p => fdrop v ⟨j.val + r, by omega⟩ := fun r v => by
    funext ⟨j, hj⟩
    have hge : ¬ (k + j < k) := by omega
    simp only [fdrop, shift, hge, ↓reduceDIte]
    congr 1
    apply Fin.ext
    dsimp
    omega
  have hIs₃ : ∀ j, j < k → DefFun (p + 3) fun v => Is (ftail (ftail (ftail v))) j :=
    fun j hj => (hIs j hj).weaken.weaken.weaken
  have hΦ₃ : ∀ j, j < k → DefFun (k + (p + 3)) fun v =>
      Φ (ftail (ftail (ftail (fdrop v)))) (padTuple (ftake v)) j := fun j hj =>
    ((hΦ_def j hj).reIndex (shift 3)).congr fun v => by
      rw [ftake_shift 3 v, fdrop_shift 3 v]
      rfl
  have hIs₅ : ∀ j, j < k → DefFun (p + 5) fun v =>
      Is (ftail (ftail (ftail (ftail (ftail v))))) j :=
    fun j hj => (hIs₃ j hj).weaken.weaken
  have hΦ₅ : ∀ j, j < k → DefFun (k + (p + 5)) fun v =>
      Φ (ftail (ftail (ftail (ftail (ftail (fdrop v)))))) (padTuple (ftake v)) j := fun j hj =>
    ((hΦ_def j hj).reIndex (shift 5)).congr fun v => by
      rw [ftake_shift 5 v, fdrop_shift 5 v]
      rfl
  have hexClosed3 : DefRel (p + 3) fun v =>
      ∃ xs : Fin k → V,
        IsClosedTuple w k (Is (ftail (ftail (ftail v))))
          (Φ (ftail (ftail (ftail v)))) (padTuple xs) := by
    refine (DefRel.exists_fin
      (defRel_isClosedTuple_pad (w := w)
        (Is := fun env => Is (ftail (ftail (ftail env))))
        (Φ := fun env => Φ (ftail (ftail (ftail env))))
        hIs₃ hΦ₃)).congr fun v => by
      simp only [ftake_fappend, fdrop_fappend]
  have hAll5 : DefRel (p + 5) fun v =>
      ∀ xs : Fin k → V,
        IsClosedTuple w k (Is (ftail (ftail (ftail (ftail (ftail v))))))
          (Φ (ftail (ftail (ftail (ftail (ftail v)))))) (padTuple xs) →
          v 0 ∈ˢ app (xs ⟨m, hm⟩) (v 4) := by
    refine (DefRel.forall_fin (DefRel.imp
      (defRel_isClosedTuple_pad (w := w)
        (Is := fun env => Is (ftail (ftail (ftail (ftail (ftail env))))))
        (Φ := fun env => Φ (ftail (ftail (ftail (ftail (ftail env))))))
        hIs₅ hΦ₅)
      (DefRel.mem_apply
        (DefFun.fdrop_proj (k := k) (p := p + 5) 0)
        (DefFun.app_apply
          (DefFun.ftake_proj ⟨m, hm⟩)
          (DefFun.fdrop_proj (k := k) (p := p + 5) ⟨4, by omega⟩))))).congr fun v => by
      simp only [ftake_fappend, fdrop_fappend]
      rfl
  have hrel : DefRel ((p + 1) + 1) fun u =>
      ∀ z, z ∈ˢ u 0 ↔
        (∃ L, IsClosedTuple w k (Is (ftail (ftail u))) (Φ (ftail (ftail u))) L) ∧
        ∃ Z,
          (∀ x, x ∈ˢ Z ↔
            ∀ X, IsClosedTuple w k (Is (ftail (ftail u))) (Φ (ftail (ftail u))) X →
              x ∈ˢ app (X m) (u 1)) ∧
          Z ∈ˢ (strictU w : V) ∧ z ∈ˢ Z := by
    refine DefRel.forall_curry (DefRel.iff
      (DefRel.mem_apply (DefFun.proj 0) (DefFun.proj 1))
      (DefRel.and
        (hexClosed3.congr fun v => (exists_isClosedTuple_iff_fin (hΦ (ftail (ftail (ftail v))))).symm)
        (DefRel.exists_curry (DefRel.and
          (DefRel.forall_curry (DefRel.iff
            (DefRel.mem_apply (DefFun.proj 0) (DefFun.proj 1))
            (hAll5.congr fun v =>
              (forall_isClosedTuple_iff_fin (hΦ (ftail (ftail (ftail (ftail (ftail v)))))) hm
                (v 4) (v 0)).symm)))
          (DefRel.and
            (DefRel.mem_apply (DefFun.proj 0) (DefFun.strictU_const w))
            (DefRel.mem_apply (DefFun.proj 1) (DefFun.proj 0)))))))
  refine hrel.congr fun u => ?_
  let is' := Is (ftail (ftail u))
  let ph' := Φ (ftail (ftail u))
  let hph' := hΦ (ftail (ftail u))
  let ix := u 1
  change (∀ z, z ∈ˢ u 0 ↔ (∃ L, IsClosedTuple w k is' ph' L) ∧
    ∃ Z, (∀ x, x ∈ˢ Z ↔ ∀ X, IsClosedTuple w k is' ph' X → x ∈ˢ app (X m) ix) ∧
      Z ∈ˢ (strictU w : V) ∧ z ∈ˢ Z) ↔
    u 0 = lfpTupleFibre w k is' ph' hph' m ix
  by_cases h : ∃ L, IsClosedTuple w k is' ph' L
  · let S := sep (app (Classical.choose h m) ix)
      (fun x => ∀ X, IsClosedTuple w k is' ph' X → x ∈ˢ app (X m) ix)
      (hasSep_lfpTuple w k is' ph' hph' m (app (Classical.choose h m) ix) ix)
    have hSmem : ∀ x, x ∈ˢ S ↔ ∀ X, IsClosedTuple w k is' ph' X → x ∈ˢ app (X m) ix := fun x => by
      dsimp only [S]; rw [mem_sep]
      exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩
    have hfib : lfpTupleFibre w k is' ph' hph' m ix = dropTo (strictU w) S := by
      unfold lfpTupleFibre; exact dite_eq_left h
    by_cases hSc : S ∈ˢ (strictU w : V)
    · have hdrop : lfpTupleFibre w k is' ph' hph' m ix = S := hfib.trans (dropTo_of_mem hSc)
      rw [hdrop]
      constructor
      · intro hw; apply ext; intro z
        rw [hw z]; constructor
        · rintro ⟨_, Z, hZ, _, hzZ⟩
          exact (hSmem z).mpr ((hZ z).mp hzZ)
        · intro hzS
          exact ⟨h, S, hSmem, hSc, hzS⟩
      · intro hw z; rw [hw]
        exact ⟨fun hz => ⟨h, S, hSmem, hSc, hz⟩,
          fun ⟨_, _, hZ, _, hzZ⟩ => (hSmem z).mpr ((hZ z).mp hzZ)⟩
    · have hdrop : lfpTupleFibre w k is' ph' hph' m ix = empty := by
        rw [hfib]; unfold dropTo; exact ite_eq_right hSc
      rw [hdrop]
      constructor
      · intro hw; apply eq_empty; intro z hz
        obtain ⟨_, Z, hZ, hZc, _⟩ := (hw z).mp hz
        have hZS : Z = S := ext fun x => (hZ x).trans (hSmem x).symm
        exact hSc (hZS ▸ hZc)
      · intro hw z; rw [hw]
        refine ⟨fun hz => absurd hz (not_mem_empty z), fun ⟨_, Z, hZ, hZc, _⟩ => ?_⟩
        have hZS : Z = S := ext fun x => (hZ x).trans (hSmem x).symm
        exact False.elim (hSc (hZS ▸ hZc))
  · have hdrop : lfpTupleFibre w k is' ph' hph' m ix = empty := by
      unfold lfpTupleFibre; exact dite_eq_right h
    rw [hdrop]
    constructor
    · intro hw; apply eq_empty; intro z hz
      exact absurd ((hw z).mp hz).1 h
    · intro hw z; rw [hw]
      exact ⟨fun hz => absurd hz (not_mem_empty z), fun ⟨hl, _⟩ => absurd hl h⟩

theorem hasGraph_lfpTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (m : Nat) :
    HasGraph (Is m) (lfpTupleFibre w k Is Φ hΦ m) := by
  by_cases hm : m < k
  · exact hasGraph_of_defFun1
      (defFun_lfpTupleFibre_apply (p := 0) (Is := fun _ => Is) (Φ := fun _ => Φ)
        (fun j _ => DefFun.const (Is j)) (fun _ => hΦ)
        (fun j hj => (hΦ.2 j hj).reIndex fun idx =>
          ⟨idx.val, Nat.lt_of_lt_of_le idx.isLt (Nat.le_add_right k 0)⟩)
        hm)
  · refine (hasGraph_const empty (Is m)).congr fun i _ => ?_
    unfold lfpTupleFibre
    split
    · case isTrue h =>
      have hemp : sep (app (Classical.choose h m) i)
          (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i)
          (hasSep_lfpTuple w k Is Φ hΦ m (app (Classical.choose h m) i) i) = empty := by
        apply eq_empty; intro x hx
        exact absurd (mem_sep.mp hx).2 (forall_isClosedTuple_ge_false hΦ h hm i x)
      rw [hemp, dropTo_of_mem (empty_mem_strictU w)]
    · rfl

/-! ## The least pre-fixed tuple -/

open Classical in
/-- **The least pre-fixed tuple of `Φ`** — componentwise, fibrewise the
intersection of the closed tuples when there is one (separated from a
chosen closed tuple), dropped to `∅` if it left `strictU w`; the empty
tuple otherwise. -/
noncomputable def lfpTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) : Nat → V :=
  fun m => famOf (lfpTupleFibre w k Is Φ hΦ m) (Is m) (hasGraph_lfpTuple w k Is Φ hΦ m)

/-- Extensional `DefFun` closure for `lfpTuple` with varying index sets
and varying tuple functor `Φ env`. -/
theorem DefFun.lfpTuple_apply {w k p : Nat}
    {Is : (Fin p → V) → Nat → V}
    {Φ : (Fin p → V) → (Nat → V) → Nat → V}
    (hIs : ∀ m, m < k → DefFun p fun env => Is env m)
    (hΦ : ∀ env, DefTupleOp k (Φ env))
    (hΦ_def : ∀ m, m < k → DefFun (k + p) fun v => Φ (fdrop v) (padTuple (ftake v)) m)
    {m : Nat} (hm : m < k) :
    DefFun p fun env => lfpTuple w k (Is env) (Φ env) (hΦ env) m := by
  unfold lfpTuple
  exact DefFun.famOf_apply_curry (defFun_lfpTupleFibre_apply hIs hΦ hΦ_def hm) (hIs m hm)

/-- Alias for `DefFun.lfpTuple_apply`. -/
theorem defFun_lfpTuple {w k p : Nat}
    {Is : (Fin p → V) → Nat → V}
    {Φ : (Fin p → V) → (Nat → V) → Nat → V}
    (hIs : ∀ m, m < k → DefFun p fun env => Is env m)
    (hΦ : ∀ env, DefTupleOp k (Φ env))
    (hΦ_def : ∀ m, m < k → DefFun (k + p) fun v => Φ (fdrop v) (padTuple (ftake v)) m)
    {m : Nat} (hm : m < k) :
    DefFun p fun env => lfpTuple w k (Is env) (Φ env) (hΦ env) m :=
  DefFun.lfpTuple_apply hIs hΦ hΦ_def hm

section Laws

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {hΦ : DefTupleOp k Φ}

theorem mem_app_lfpTuple_iff {m : Nat} {i y : V} (hi : i ∈ˢ Is m) :
    y ∈ˢ app (lfpTuple w k Is Φ hΦ m) i ↔
      (∃ L, IsClosedTuple w k Is Φ L) ∧
      ∃ Z, (∀ x, x ∈ˢ Z ↔ ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i) ∧
        Z ∈ˢ (strictU w : V) ∧ y ∈ˢ Z := by
  unfold lfpTuple
  rw [app_famOf hi]
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · let S := sep (app (Classical.choose h m) i)
      (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i)
      (hasSep_lfpTuple w k Is Φ hΦ m (app (Classical.choose h m) i) i)
    have hSmem : ∀ x, x ∈ˢ S ↔ ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i := fun x => by
      dsimp only [S]; rw [mem_sep]
      exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩
    have hfib : lfpTupleFibre w k Is Φ hΦ m i = dropTo (strictU w) S := by
      unfold lfpTupleFibre; exact dite_eq_left h
    rw [hfib]
    by_cases hSc : S ∈ˢ (strictU w : V)
    · rw [dropTo_of_mem hSc]
      exact ⟨fun hy => ⟨h, S, hSmem, hSc, hy⟩,
        fun ⟨_, _, hZ, _, hzZ⟩ => (hSmem y).mpr ((hZ y).mp hzZ)⟩
    · have hdrop : dropTo (strictU w) S = empty := by
        unfold dropTo; exact ite_eq_right hSc
      rw [hdrop]
      refine ⟨fun hy => absurd hy (not_mem_empty y), fun ⟨_, Z, hZ, hZc, _⟩ => ?_⟩
      have hZS : Z = S := ext fun x => (hZ x).trans (hSmem x).symm
      exact False.elim (hSc (hZS ▸ hZc))
  · have hfib : lfpTupleFibre w k Is Φ hΦ m i = empty := by
      unfold lfpTupleFibre; exact dite_eq_right h
    rw [hfib]
    exact ⟨fun hy => absurd hy (not_mem_empty y), fun ⟨hl, _⟩ => absurd hl h⟩

theorem lfpTuple_of_not (h : ¬ ∃ L, IsClosedTuple w k Is Φ L) (m : Nat) :
    lfpTuple w k Is Φ hΦ m = famOf (fun _ => empty) (Is m) (hasGraph_const empty (Is m)) := by
  unfold lfpTuple
  refine famOf_congr _ _ fun i _ => ?_
  unfold lfpTupleFibre
  exact dite_eq_right h

theorem forall_of_mem_app_lfpTuple (h : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} {i x : V}
    (hi : i ∈ˢ Is m) (hx : x ∈ˢ app (lfpTuple w k Is Φ hΦ m) i) :
    ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i := by
  unfold lfpTuple at hx
  rw [app_famOf hi] at hx
  unfold lfpTupleFibre at hx
  rw [dite_eq_left h] at hx
  exact (mem_sep.mp (mem_of_mem_dropTo hx)).2

/-- A member of the level below every closed tuple's fibre is below the
least tuple's. -/
theorem subset_app_lfpTuple (h : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} (hm : m < k)
    {i Y : V} (hi : i ∈ˢ Is m) (hY : Y ∈ˢ (strictU w : V))
    (hYX : ∀ X, IsClosedTuple w k Is Φ X → Y ⊆ˢ app (X m) i) :
    Y ⊆ˢ app (lfpTuple w k Is Φ hΦ m) i := by
  unfold lfpTuple
  rw [app_famOf hi]
  unfold lfpTupleFibre
  rw [dite_eq_left h]
  refine subset_dropTo (strictU_dropClosed w) (famSpace_app ((Classical.choose_spec h).1 m hm) hi)
    sep_subset hY fun x hx => mem_sep.mpr ⟨?_, fun X hX => hYX X hX x hx⟩
  exact hYX _ (Classical.choose_spec h) x hx

/-- **Leastness**: the least pre-fixed tuple lies below every closed
tuple. -/
theorem lfpTuple_le {X : Nat → V} (hX : IsClosedTuple w k Is Φ X) :
    TupleLe k Is (lfpTuple w k Is Φ hΦ) X :=
  fun _ _ _ hi _x hx => forall_of_mem_app_lfpTuple ⟨X, hX⟩ hi hx X hX

/-- **Formation, unconditional**: the least pre-fixed tuple is in the
tuple space. -/
theorem lfpTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) : InTupleSpace w k Is (lfpTuple w k Is Φ hΦ) := by
  intro m _
  unfold lfpTuple
  refine famOf_mem_famSpace fun i _ => ?_
  unfold lfpTupleFibre
  split
  · exact dropTo_mem (empty_mem_strictU w) _
  · exact empty_mem_strictU w

/-- **Closure**: the least pre-fixed tuple is a pre-fixed point. -/
theorem lfpTuple_closed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    TupleLe k Is (Φ (lfpTuple w k Is Φ hΦ)) (lfpTuple w k Is Φ hΦ) := by
  intro m hm i hi
  refine subset_app_lfpTuple h hm hi
    (famSpace_app (hmaps _ (lfpTuple_mem w k Is Φ hΦ) m hm) hi) fun X hX => ?_
  exact Subset.trans (hmono _ _ (lfpTuple_mem w k Is Φ hΦ) hX.1 (lfpTuple_le hX) m hm i hi)
    (hX.2 m hm i hi)

/-- The least pre-fixed tuple is a post-fixed point. -/
theorem lfpTuple_fixed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    TupleLe k Is (lfpTuple w k Is Φ hΦ) (Φ (lfpTuple w k Is Φ hΦ)) := by
  refine lfpTuple_le ⟨hmaps _ (lfpTuple_mem w k Is Φ hΦ), ?_⟩
  exact hmono _ _ (hmaps _ (lfpTuple_mem w k Is Φ hΦ)) (lfpTuple_mem w k Is Φ hΦ)
    (lfpTuple_closed h hmono hmaps)

/-- The fixed-point equation, componentwise and fibrewise. -/
theorem app_lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) {i : V} (hi : i ∈ˢ Is m) :
    app (Φ (lfpTuple w k Is Φ hΦ) m) i = app (lfpTuple w k Is Φ hΦ m) i :=
  Subset.antisymm (lfpTuple_closed h hmono hmaps m hm i hi)
    (lfpTuple_fixed h hmono hmaps m hm i hi)

/-- The fixed-point equation, componentwise. -/
theorem lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) :
    Φ (lfpTuple w k Is Φ hΦ) m = lfpTuple w k Is Φ hΦ m :=
  famSpace_ext (hmaps _ (lfpTuple_mem w k Is Φ hΦ) m hm) (lfpTuple_mem w k Is Φ hΦ m hm)
    fun _ hi => app_lfpTuple_eq h hmono hmaps hm hi

/-! ## Separation and simultaneous structural induction -/

open Classical in
/-- The tuple of separations of the carrier by a per-member property,
a fibre that left `strictU w` dropped to `∅` (proof-carrying in `hSep`
and `hGr`). -/
noncomputable def sepTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (P : Nat → V → V → Prop)
    (hSep : ∀ m, m < k → ∀ i, HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i))
    (hGr : ∀ m (hm : m < k), HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i))) :
    Nat → V :=
  fun m =>
    if hm : m < k then
      famOf (fun i =>
        dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i)))
        (Is m) (hGr m hm)
    else famOf (fun _ => empty) (Is m) (hasGraph_const empty (Is m))

theorem hasSep_sepTuple_of_def {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) {P : Nat → V → V → Prop}
    (hP : ∀ m, m < k → DefRel 2 fun v => P m (v 0) (v 1))
    (m : Nat) (hm : m < k) (i : V) :
    HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) :=
  hasSep_of_defPred ((hP m hm).fixParam i)

theorem hasGraph_sepTuple_of_def {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) {P : Nat → V → V → Prop}
    (hP : ∀ m, m < k → DefRel 2 fun v => P m (v 0) (v 1))
    (m : Nat) (hm : m < k) :
    HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i)
        (hasSep_sepTuple_of_def hΦ hP m hm i)) := by
  refine hasGraph_of_defFun1 ?_
  have hP' : DefRel 2 fun v => P m (v 1) (v 0) :=
    (hP m hm).reIndex (fun j => match j with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0)
  have hsep : DefFun 1 fun v =>
      sep (app (lfpTuple w k Is Φ hΦ m) (v 0)) (P m (v 0))
        (hasSep_sepTuple_of_def hΦ hP m hm (v 0)) :=
    DefFun.sep_apply_curry
      (DefFun.app_apply (DefFun.const (lfpTuple w k Is Φ hΦ m)) (DefFun.proj 0))
      (hP'.congr fun _ => Iff.rfl)
  exact DefFun.dropTo_apply (DefFun.strictU_const w) hsep

/-- Convenience wrapper constructing `sepTuple` when each `P m` is `DefRel 2`. -/
noncomputable def sepTuple_of_def (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (P : Nat → V → V → Prop)
    (hP : ∀ m, m < k → DefRel 2 fun v => P m (v 0) (v 1)) : Nat → V :=
  sepTuple w k Is Φ hΦ P (hasSep_sepTuple_of_def hΦ hP) (hasGraph_sepTuple_of_def hΦ hP)

/-- The separated tuple is in the tuple space. -/
theorem sepTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (P : Nat → V → V → Prop)
    (hSep : ∀ m, m < k → ∀ i, HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i))
    (hGr : ∀ m (hm : m < k), HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i))) :
    InTupleSpace w k Is (sepTuple w k Is Φ hΦ P hSep hGr) := fun m hm => by
  unfold sepTuple
  rw [dite_eq_left hm]
  exact famOf_mem_famSpace fun _ _ => dropTo_mem (empty_mem_strictU w) _

/-- A member of the separated tuple is in the carrier and has the
property. -/
theorem mem_app_sepTuple_imp {P : Nat → V → V → Prop}
    {hSep : ∀ m, m < k → ∀ i, HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i)}
    {hGr : ∀ m (hm : m < k), HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i))}
    {m : Nat} {i y : V} (hi : i ∈ˢ Is m)
    (hy : y ∈ˢ app (sepTuple w k Is Φ hΦ P hSep hGr m) i) :
    y ∈ˢ app (lfpTuple w k Is Φ hΦ m) i ∧ P m i y := by
  unfold sepTuple at hy
  by_cases hm : m < k
  · rw [dite_eq_left hm, app_famOf hi] at hy
    exact mem_sep.mp (mem_of_mem_dropTo hy)
  · rw [dite_eq_right hm, app_famOf hi] at hy
    exact absurd hy (not_mem_empty y)

/-- The separated tuple lies below the carrier. -/
theorem sepTuple_le (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (P : Nat → V → V → Prop)
    (hSep : ∀ m, m < k → ∀ i, HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i))
    (hGr : ∀ m (hm : m < k), HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i))) :
    TupleLe k Is (sepTuple w k Is Φ hΦ P hSep hGr) (lfpTuple w k Is Φ hΦ) :=
  fun _ _ _ hi _ hy => (mem_app_sepTuple_imp hi hy).1

/-- **Simultaneous structural induction** (guarded by `HasSep` / `HasGraph`):
a family of properties, one per member, closed under the functor on
the carrier holds on the whole carrier. -/
theorem lfpTuple_induction (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (P : Nat → V → V → Prop)
    (hSep : ∀ m, m < k → ∀ i, HasSep (app (lfpTuple w k Is Φ hΦ m) i) (P m i))
    (hGr : ∀ m (hm : m < k), HasGraph (Is m) fun i =>
      dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i) (hSep m hm i)))
    (hP : ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ (sepTuple w k Is Φ hΦ P hSep hGr) m) i → P m i x) :
    ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ hΦ m) i → P m i x := by
  intro m hm i hi x hx
  have hSmem := sepTuple_mem w k Is Φ hΦ P hSep hGr
  have hSle := sepTuple_le w k Is Φ hΦ P hSep hGr
  have hS : IsClosedTuple w k Is Φ (sepTuple w k Is Φ hΦ P hSep hGr) := by
    refine ⟨hSmem, fun m hm i hi => ?_⟩
    have heq : sepTuple w k Is Φ hΦ P hSep hGr m =
        famOf (fun i => dropTo (strictU w) (sep (app (lfpTuple w k Is Φ hΦ m) i) (P m i)
          (hSep m hm i))) (Is m) (hGr m hm) := by
      unfold sepTuple; exact dite_eq_left hm
    rw [heq, app_famOf hi]
    refine subset_dropTo (strictU_dropClosed w) (famSpace_app (lfpTuple_mem w k Is Φ hΦ m hm) hi)
      sep_subset (famSpace_app (hmaps _ hSmem m hm) hi) fun y hy => ?_
    refine mem_sep.mpr ⟨?_, hP m hm i hi y hy⟩
    exact lfpTuple_closed h hmono hmaps m hm i hi y
      (hmono _ _ hSmem (lfpTuple_mem w k Is Φ hΦ) hSle m hm i hi y hy)
  exact (mem_app_sepTuple_imp hi (lfpTuple_le hS m hm i hi x hx)).2

/-- **Simultaneous structural induction** for `DefRel 2` per-member
predicates (discharging `HasSep` and `HasGraph` automatically). -/
theorem lfpTuple_induction_of_def (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (P : Nat → V → V → Prop)
    (hPdef : ∀ m, m < k → DefRel 2 fun v => P m (v 0) (v 1))
    (hP : ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ (sepTuple_of_def w k Is Φ hΦ P hPdef) m) i → P m i x) :
    ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ hΦ m) i → P m i x :=
  lfpTuple_induction h hmono hmaps P
    (hasSep_sepTuple_of_def hΦ hPdef) (hasGraph_sepTuple_of_def hΦ hPdef) hP

end Laws

/-! ## Congruence: the least tuple reads its operator and index sets below `k` only -/

section Congr

variable {w k : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- Two presentations agreeing below `k` have the same closed tuples. -/
theorem isClosedTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {X : Nat → V} :
    IsClosedTuple w k Is Φ X ↔ IsClosedTuple w k Is' Φ' X := by
  have hsp : InTupleSpace w k Is X ↔ InTupleSpace w k Is' X := by
    constructor
    · intro h m hm; rw [← hIs m hm]; exact h m hm
    · intro h m hm; rw [hIs m hm]; exact h m hm
  constructor
  · rintro ⟨hX, hle⟩
    refine ⟨hsp.mp hX, fun m hm => ?_⟩
    rw [← hIs m hm, ← hΦ X hX m hm]; exact hle m hm
  · rintro ⟨hX, hle⟩
    have hX' := hsp.mpr hX
    refine ⟨hX', fun m hm => ?_⟩
    rw [hIs m hm, hΦ X hX' m hm]; exact hle m hm

/-- **The least tuple is a congruence** in the operator (on the tuple
space) and the index sets, below `k`. -/
theorem lfpTuple_congr {hΦ : DefTupleOp k Φ} {hΦ' : DefTupleOp k Φ'}
    (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦeq : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m)
    {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ hΦ m = lfpTuple w k Is' Φ' hΦ' m := by
  have hcl : (∃ L, IsClosedTuple w k Is Φ L) ↔ ∃ L, IsClosedTuple w k Is' Φ' L :=
    ⟨fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦeq).mp hL⟩,
      fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦeq).mpr hL⟩⟩
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · have h' := hcl.mp h
    refine famSpace_ext (lfpTuple_mem w k Is Φ hΦ m hm)
      (by rw [hIs m hm]; exact lfpTuple_mem w k Is' Φ' hΦ' m hm) fun i hi => ?_
    have hi' : i ∈ˢ Is' m := by rw [← hIs m hm]; exact hi
    unfold lfpTuple
    rw [app_famOf hi, app_famOf hi']
    unfold lfpTupleFibre
    rw [dite_eq_left h, dite_eq_left h']
    congr 1
    apply SetTheory.ext
    intro x
    rw [mem_sep, mem_sep]
    constructor
    · rintro ⟨_, hx⟩
      have hx' : ∀ X, IsClosedTuple w k Is' Φ' X → x ∈ˢ app (X m) i :=
        fun X hX => hx X ((isClosedTuple_congr hIs hΦeq).mpr hX)
      exact ⟨hx' _ (Classical.choose_spec h'), hx'⟩
    · rintro ⟨_, hx⟩
      have hx' : ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i :=
        fun X hX => hx X ((isClosedTuple_congr hIs hΦeq).mp hX)
      exact ⟨hx' _ (Classical.choose_spec h), hx'⟩
  · rw [lfpTuple_of_not h m, lfpTuple_of_not (fun h' => h (hcl.mpr h')) m]
    exact famOf_ext (hIs m hm) _ _ (fun _ _ => rfl)

/-- **The least tuple reads only the index sets below its width.** -/
theorem lfpTuple_congr_Is {hΦ : DefTupleOp k Φ}
    (hIs : ∀ m, m < k → Is m = Is' m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ hΦ m = lfpTuple w k Is' Φ hΦ m :=
  lfpTuple_congr hIs (fun _ _ _ _ => rfl) hm

end Congr

end ConLeche.SetTheory
