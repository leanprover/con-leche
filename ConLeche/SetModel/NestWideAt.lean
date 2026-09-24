module

public import ConLeche.SetModel.NestWide
public import ConLeche.SetModel.WideFlat
@[expose] public section

/-!
# The wide presentation of a nested block, as one record (lane NESTW, L7 step 2)

`WideAt w k Is Φ` packages what `closed_of_wide_groups` (NestWide) and
the flat kit at per-component injections (`UBlock.closedI_of_flat`,
WideFlat) need of a nested block's operator `Φ` on its `k` members at
the level `w`:

* `n` wide keys, the FRAME OCCURRENCES of the positivity walk (NESTW
  F-W3), and the wide block `ub` on `k + n` components whose first `k`
  index sets are the block's (`isLo`);
* the per-component injection `ι` (members: the block's own; keys: the
  container clause's, F-W2), a set of the level at every fitting spine
  (`hι`);
* the flat presentation of every wide constructor (`flat`, U4 at every
  non-ordinary field included: `HoleUnread`);
* the keys grouped by container group, with the containers' clause
  facts (`P`, `hP`);
* the substitution law at the members (`mem`).

`WideAt.closed` is (W) at `w ≠ 0`.  The wide operator is `ub`'s hole
operator at `ι`, at the frame `ρ` and a parameter `α` (a model's wide
fields never read it: a nested occurrence is a plain key hole; the
set-level instances do).
-/

namespace ConLeche.SetTheory

open Tower
open ConLeche.SetModel

universe u

variable {V : Type u} [SetTheory V]

/-- **The wide presentation of the operator `Φ`** (see the module
docstring). -/
structure WideAt (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Type u where
  /-- the number of wide keys -/
  n : Nat
  /-- the wide block: members, then keys -/
  ub : UBlock V w (k + n)
  /-- the members' index sets are the block's -/
  isLo : ∀ m, m < k → ub.Is m = Is m
  /-- the per-component injection -/
  ι : Nat → Nat → List V → V
  /-- the parameter frame the wide fields read -/
  ρ : Nat → V
  /-- the wide block's parameter (unread by a model's wide fields: a
  nested occurrence is a plain key hole; any set of the level) -/
  α : V
  hα : α ∈ˢ (univ w : V)
  /-- the injection is a set of the level at every fitting spine -/
  hι : ∀ X, InTupleSpace w (k + n) ub.Is X → ∀ c, c < k + n → ∀ j ct fs,
    (ub.ctors c)[j]? = some ct → FitsS (teleOf ct.fields ρ X α) fs → ι c j fs ∈ˢ (univ w : V)
  /-- every wide constructor is presented flat -/
  flat : ub.FlatAt ρ α
  /-- the keys, grouped by container group -/
  P : KeyGroups V
  /-- the containers' clause facts at the instantiation -/
  hP : P.Ok w k n ub.Is (uPhiI ub ι ρ α)
  /-- **the substitution law at the members**, `≤` form -/
  mem : ∀ X Y, InTupleSpace w k Is X → InTupleSpace w n (dropTup k ub.Is) Y →
    Dominated k n ub.Is (P.ev w) (catTup k X Y) → TupleLe k Is (Φ X) (uPhiI ub ι ρ α (catTup k X Y))

namespace WideAt

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

theorem inTupleSpace_lo (W : WideAt w k Is Φ) {X : Nat → V} :
    InTupleSpace w k W.ub.Is X ↔ InTupleSpace w k Is X :=
  ⟨fun h m hm => W.isLo m hm ▸ h m hm, fun h m hm => (W.isLo m hm).symm ▸ h m hm⟩

theorem tupleLe_lo (W : WideAt w k Is Φ) {X Y : Nat → V} :
    TupleLe k W.ub.Is X Y ↔ TupleLe k Is X Y :=
  ⟨fun h m hm => W.isLo m hm ▸ h m hm, fun h m hm => (W.isLo m hm).symm ▸ h m hm⟩

/-- **(W) from the wide presentation**, at `w ≠ 0`. -/
theorem closed (hw : w ≠ 0) (W : WideAt w k Is Φ) : ∃ L, IsClosedTuple w k Is Φ L := by
  obtain ⟨L, hL1, hL2⟩ := closed_of_wide_groups (Φ := Φ)
    (uPhiI_mono W.ub W.ι W.ρ W.hα)
    (UBlock.closedI_of_flat hw W.ub W.ι W.ρ W.α W.hι W.flat) W.P W.hP
    (fun X Y hX hY hd => W.tupleLe_lo.mpr (W.mem X Y (W.inTupleSpace_lo.mp hX) hY hd))
  exact ⟨L, W.inTupleSpace_lo.mp hL1, W.tupleLe_lo.mp hL2⟩

end WideAt

/-! ## Building the record from flat fields and the fibres' fits (L7 step 3)

The consumer side of the producer: a nested block's wide presentation
given as FLAT FIELD LISTS per wide constructor (members: the block's
constructors with every nested occurrence a key hole; keys: the
containers' constructors at the instantiation) and two fit statements —
every element of the block's fibre (resp. of a key's container fibre at
the group's tuple read at the keys) is an injection of a spine fitting
the flat fields at the wide tuple, under domination.  `WideFits.toWideAt`
builds the wide block (`fctor`: a flat field list as constructor fields),
the per-component injection (a key's the container's, cut to the level
off its fibres), the flat presentation and the key groups' `Ok`. -/

namespace RTel

/-- A well-formed recursive field type is positive (above `Prop`). -/
theorem pos {w K : Nat} (hw : w ≠ 0) : ∀ (r : RTel V), r.WF w K →
    Pos w K (fun ρ X _ => r.read ρ X)
  | hole m es, h => Pos.hole m h es
  | pi v A B, h => Pos.pi v (fun h0 => absurd h0 hw) A h.2.1 (fun ρ X _ => B.read ρ X) (pos hw B h.2.2)

end RTel

namespace FField

/-- A flat field as a constructor field (the parameter unread). -/
noncomputable def fn (f : FField V) : (Nat → V) → (Nat → V) → V → V := fun ρ X _ => f.read ρ X

theorem pos {w K : Nat} (hw : w ≠ 0) : ∀ (f : FField V), f.WF w K → Pos w K f.fn
  | plain A, h => Pos.const A h
  | recur r, h => r.pos hw h

end FField

theorem readsAs_map_fn (α : V) : ∀ ffs : List (FField V), ReadsAs α (ffs.map FField.fn) ffs
  | [] => trivial
  | _ :: ffs => ⟨fun _ _ => rfl, readsAs_map_fn α ffs⟩

open Classical in
/-- **A flat field list as a constructor** (at `w ≠ 0` and well-formed
fields; the empty constructor otherwise — never read). -/
noncomputable def fctor (w K : Nat) (ffs : List (FField V)) (idx : (Nat → V) → V) : UCtor V w K :=
  if h : w ≠ 0 ∧ ∀ f ∈ ffs, f.WF w K then
    ⟨ffs.map FField.fn, (fun F hF => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
      exact FField.pos h.1 f (h.2 f hf)), idx⟩
  else ⟨[], (fun _ h => nomatch h), idx⟩

theorem fctor_fields {w K : Nat} (hw : w ≠ 0) {ffs : List (FField V)} (hwf : ∀ f ∈ ffs, f.WF w K)
    (idx : (Nat → V) → V) : (fctor w K ffs idx).fields = ffs.map FField.fn := by
  unfold fctor; rw [dif_pos ⟨hw, hwf⟩]

theorem fctor_idx (w K : Nat) (ffs : List (FField V)) (idx : (Nat → V) → V) :
    (fctor w K ffs idx).idx = idx := by
  unfold fctor; split <;> rfl

/-- A fitting spine of a bounded telescope consists of sets of the level. -/
theorem fitsS_mem_univ {w : Nat} (hw : w ≠ 0) :
    ∀ {n} {T : TeleS V n} {fs : List V}, BoundS w T → FitsS T fs → ∀ y ∈ fs, y ∈ˢ (univ w : V)
  | _, .nil, [], _, _, _, hy => nomatch hy
  | _, .cons _ B, a :: fs, hB, hf, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (univ_isTGUniverse hw).transitive hB.1 hf.1
    · exact fitsS_mem_univ hw (hB.2 a hf.1) hf.2 y hy

/-- **The wide presentation as flat fits** (see the section docstring). -/
structure WideFits (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Type u where
  /-- the number of wide keys -/
  n : Nat
  /-- the keys' index sets -/
  kIs : Nat → V
  /-- the frame the flat fields read -/
  ρ₀ : Nat → V
  /-- the keys, grouped by container group -/
  P : KeyGroups V
  /-- member `c`'s constructor count, flat fields, result index, injection -/
  mn : Nat → Nat
  mf : Nat → Nat → List (FField V)
  mi : Nat → Nat → (Nat → V) → V
  mι : Nat → Nat → List V → V
  /-- key `q`'s constructor count, flat fields, result index, injection
  (its container's) -/
  kn : Nat → Nat
  kf : Nat → Nat → List (FField V)
  ki : Nat → Nat → (Nat → V) → V
  kι : Nat → Nat → List V → V
  mwf : ∀ c, c < k → ∀ j, j < mn c → ∀ f ∈ mf c j, f.WF w (k + n)
  kwf : ∀ q, q < n → ∀ j, j < kn q → ∀ f ∈ kf q j, f.WF w (k + n)
  /-- U4 at every non-ordinary field (F-W1) -/
  munread : ∀ c, c < k → ∀ j, j < mn c → HoleUnread (mf c j) ρ₀ ρ₀
  kunread : ∀ q, q < n → ∀ j, j < kn q → HoleUnread (kf q j) ρ₀ ρ₀
  /-- a member injection of sets of the level is one -/
  mιU : ∀ c, c < k → ∀ j fs, (∀ y ∈ fs, y ∈ˢ (univ w : V)) → mι c j fs ∈ˢ (univ w : V)
  cmp_lt : ∀ q, q < n → P.cmp q < P.g (P.grp q)
  inj : ∀ q q', q < n → q' < n → P.grp q = P.grp q' → P.cmp q = P.cmp q' → q = q'
  /-- N2 -/
  idx : ∀ q, q < n → ∀ W, InTupleSpace w (k + n) (catTup k Is kIs) W →
    P.IsG (P.grp q) W (P.cmp q) = kIs q
  /-- the containers' clauses' `functor` at the instantiation -/
  functor : ∀ W, InTupleSpace w (k + n) (catTup k Is kIs) W → ∀ q, q < n →
    MonoTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) ∧
    MapsTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) ∧
    ∃ L, IsClosedTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) L
  /-- **the members' fit**: an element of the block's fibre is a member
  injection of a spine fitting the flat fields at the wide tuple, under
  domination -/
  mfib : ∀ X Y, InTupleSpace w k Is X → InTupleSpace w n kIs Y →
    Dominated k n (catTup k Is kIs) (P.ev w) (catTup k X Y) →
    ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ x, x ∈ˢ app (Φ X c) t →
    ∃ j, j < mn c ∧ ∃ fs, FitsF (mf c j) ρ₀ (catTup k X Y) fs ∧ mi c j (fconsList fs ρ₀) = t ∧
      x = mι c j fs
  /-- **the keys' fit**: an element of a key's container fibre, at the
  group's tuple read at the keys, is the container's injection of a spine
  fitting the key's flat fields at the wide tuple, once the deeper keys
  dominate -/
  kfib : ∀ W, InTupleSpace w (k + n) (catTup k Is kIs) W → ∀ q, q < n →
    (∀ q', q' < n → P.dep (P.grp q) < P.dep (P.grp q') →
      FamLe (kIs q') (P.ev w q' W) (W (k + q'))) →
    ∀ t, t ∈ˢ kIs q → ∀ x, x ∈ˢ app (P.Θ (P.grp q) W (P.fill w k n (P.grp q) W) (P.cmp q)) t →
    ∃ j, j < kn q ∧ ∃ fs, FitsF (kf q j) ρ₀ W fs ∧ ki q j (fconsList fs ρ₀) = t ∧ x = kι q j fs

namespace WideFits

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} (F : WideFits w k Is Φ)

/-- The wide block. -/
noncomputable def ub : UBlock V w (k + F.n) where
  Is := catTup k Is F.kIs
  ctors := fun c =>
    if c < k then (List.range (F.mn c)).map fun j => fctor w (k + F.n) (F.mf c j) (F.mi c j)
    else (List.range (F.kn (c - k))).map fun j => fctor w (k + F.n) (F.kf (c - k) j) (F.ki (c - k) j)

open Classical in
/-- The per-component injection: a key's the container's, cut to the
level (off the container's fibres, never read). -/
noncomputable def ι : Nat → Nat → List V → V := fun c j fs =>
  if c < k then F.mι c j fs
  else if F.kι (c - k) j fs ∈ˢ (univ w : V) then F.kι (c - k) j fs else empty

variable {F}

theorem ub_ctors_lt {c : Nat} (hc : c < k) {j : Nat} {ct : UCtor V w (k + F.n)} :
    (F.ub.ctors c)[j]? = some ct ↔ j < F.mn c ∧ ct = fctor w (k + F.n) (F.mf c j) (F.mi c j) := by
  simp only [ub, if_pos hc, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨j', hj', rfl⟩
    obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hj'
    rw [List.getElem_range] at he
    rw [List.length_range] at hj
    subst he
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨j, List.getElem?_range hj, rfl⟩

theorem ub_ctors_key {q : Nat} {j : Nat} {ct : UCtor V w (k + F.n)} :
    (F.ub.ctors (k + q))[j]? = some ct ↔ j < F.kn q ∧ ct = fctor w (k + F.n) (F.kf q j) (F.ki q j) := by
  simp only [ub, if_neg (Nat.not_lt.mpr (Nat.le_add_right k q)), Nat.add_sub_cancel_left,
    List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨j', hj', rfl⟩
    obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hj'
    rw [List.getElem_range] at he
    rw [List.length_range] at hj
    subst he
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨j, List.getElem?_range hj, rfl⟩

theorem ub_Is_lt {c : Nat} (hc : c < k) : F.ub.Is c = Is c := catTup_lt _ _ hc

theorem ub_Is_key (q : Nat) : F.ub.Is (k + q) = F.kIs q := catTup_add _ _ q

theorem ι_lt {c : Nat} (hc : c < k) (j : Nat) (fs : List V) : F.ι c j fs = F.mι c j fs := by
  simp only [ι, if_pos hc]

open Classical in
theorem ι_key (q j : Nat) (fs : List V) :
    F.ι (k + q) j fs = if F.kι q j fs ∈ˢ (univ w : V) then F.kι q j fs else empty := by
  simp only [ι, if_neg (Nat.not_lt.mpr (Nat.le_add_right k q)), Nat.add_sub_cancel_left]

theorem fctor_flat {K : Nat} (hw : w ≠ 0) {ffs : List (FField V)} (hwf : ∀ f ∈ ffs, f.WF w K)
    {ρ : Nat → V} (hU : HoleUnread ffs ρ ρ) (idx : (Nat → V) → V) (α : V) :
    FlatCtor w K ρ α (fctor w K ffs idx) ffs :=
  ⟨by rw [fctor_fields hw hwf]; exact readsAs_map_fn α ffs, hwf, hU⟩

theorem fitsS_fctor {K : Nat} (hw : w ≠ 0) {ffs : List (FField V)} (hwf : ∀ f ∈ ffs, f.WF w K)
    {idx : (Nat → V) → V} {ρ X : Nat → V} {α : V} {fs : List V} :
    FitsS (teleOf (fctor w K ffs idx).fields ρ X α) fs ↔ FitsF ffs ρ X fs := by
  rw [fctor_fields hw hwf]; exact fitsS_teleOf_iff (readsAs_map_fn α ffs)

variable (F)

/-- The injection is a set of the level at every fitting spine. -/
theorem hι_of (hw : w ≠ 0) : ∀ X, InTupleSpace w (k + F.n) F.ub.Is X → ∀ c, c < k + F.n →
    ∀ j ct fs, (F.ub.ctors c)[j]? = some ct → FitsS (teleOf ct.fields F.ρ₀ X empty) fs →
    F.ι c j fs ∈ˢ (univ w : V) := by
  intro X hX c _ j ct fs _ hf
  by_cases hck : c < k
  · rw [ι_lt hck]
    exact F.mιU c hck j fs
      (fitsS_mem_univ hw (teleOf_bound hX (empty_mem_univ w) ct.fields ct.pos F.ρ₀) hf)
  · simp only [ι, if_neg hck]
    split
    · assumption
    · exact empty_mem_univ w

/-- Every wide constructor is presented flat. -/
theorem flat_of (hw : w ≠ 0) : F.ub.FlatAt F.ρ₀ empty := by
  intro c hc j ct hct
  by_cases hck : c < k
  · obtain ⟨hj, rfl⟩ := (ub_ctors_lt hck).mp hct
    exact ⟨_, fctor_flat hw (F.mwf c hck j hj) (F.munread c hck j hj) _ _⟩
  · obtain ⟨q, rfl⟩ : ∃ q, c = k + q := ⟨c - k, by omega⟩
    obtain ⟨hj, rfl⟩ := ub_ctors_key.mp hct
    have hq : q < F.n := by omega
    exact ⟨_, fctor_flat hw (F.kwf q hq j hj) (F.kunread q hq j hj) _ _⟩

/-- The key groups' facts at the wide operator; the substitution law
from the keys' fit. -/
theorem ok_of (hw : w ≠ 0) : F.P.Ok w k F.n F.ub.Is (uPhiI F.ub F.ι F.ρ₀ empty) where
  cmp_lt := F.cmp_lt
  inj := F.inj
  idx := fun q hq W hW => (F.idx q hq W hW).trans (ub_Is_key q).symm
  functor := fun W hW q hq => ⟨(F.functor W hW q hq).1, (F.functor W hW q hq).2.2⟩
  sub := fun W hW q hq hdeep => by
    intro t ht x hx
    rw [ub_Is_key] at ht
    have hdeep' : ∀ q', q' < F.n → F.P.dep (F.P.grp q) < F.P.dep (F.P.grp q') →
        FamLe (F.kIs q') (F.P.ev w q' W) (W (k + q')) := fun q' hq' hlt => by
      have := hdeep q' hq' hlt
      rwa [ub_Is_key] at this
    obtain ⟨j, hj, fs, hf, hi, rfl⟩ := F.kfib W hW q hq hdeep' t ht x hx
    have hfill := KeyGroups.fill_inTupleSpace (P := F.P) hW
      (fun q' hq' => (F.idx q' hq' W hW).trans (ub_Is_key q').symm) (F.P.grp q)
    have hmaps := (F.functor W hW q hq).2.1 _ hfill (F.P.cmp q) (F.cmp_lt q hq)
    have htG : t ∈ˢ F.P.IsG (F.P.grp q) W (F.P.cmp q) := by rw [F.idx q hq W hW]; exact ht
    have hxU : F.kι q j fs ∈ˢ (univ w : V) :=
      (univ_isTGUniverse hw).transitive (famSpace_app hmaps htG) hx
    refine (mem_uPhiI F.ub F.ι F.ρ₀ empty W (c := k + q) (by rw [ub_Is_key]; exact ht)).mpr
      ⟨j, fs, _, ub_ctors_key.mpr ⟨hj, rfl⟩, (fitsS_fctor hw (F.kwf q hq j hj)).mpr hf,
        by rw [fctor_idx]; exact hi, ?_⟩
    rw [uinjI_pos hw, ι_key, if_pos hxU]

/-- The substitution law at the members, from the members' fit. -/
theorem mem_of (hw : w ≠ 0) : ∀ X Y, InTupleSpace w k Is X →
    InTupleSpace w F.n (dropTup k F.ub.Is) Y → Dominated k F.n F.ub.Is (F.P.ev w) (catTup k X Y) →
    TupleLe k Is (Φ X) (uPhiI F.ub F.ι F.ρ₀ empty (catTup k X Y)) := by
  intro X Y hX hY hd c hc t ht x hx
  have hY' : InTupleSpace w F.n F.kIs Y := fun q hq => by
    have := hY q hq
    rwa [show dropTup k F.ub.Is q = F.kIs q from ub_Is_key q] at this
  obtain ⟨j, hj, fs, hf, hi, rfl⟩ := F.mfib X Y hX hY' hd c hc t ht x hx
  refine (mem_uPhiI F.ub F.ι F.ρ₀ empty _ (c := c) (by rw [ub_Is_lt hc]; exact ht)).mpr
    ⟨j, fs, _, (ub_ctors_lt hc).mpr ⟨hj, rfl⟩, (fitsS_fctor hw (F.mwf c hc j hj)).mpr hf,
      by rw [fctor_idx]; exact hi, ?_⟩
  rw [uinjI_pos hw, ι_lt hc]

/-- **The wide presentation from the flat fits.** -/
noncomputable def toWideAt (hw : w ≠ 0) : WideAt w k Is Φ where
  n := F.n
  ub := F.ub
  isLo := fun _ hm => ub_Is_lt hm
  ι := F.ι
  ρ := F.ρ₀
  α := empty
  hα := empty_mem_univ w
  hι := F.hι_of hw
  flat := F.flat_of hw
  P := F.P
  hP := F.ok_of hw
  mem := F.mem_of hw

include F in
/-- **(W) from the flat fits**, at `w ≠ 0`. -/
theorem closed (hw : w ≠ 0) : ∃ L, IsClosedTuple w k Is Φ L := (F.toWideAt hw).closed hw

end WideFits

end ConLeche.SetTheory
