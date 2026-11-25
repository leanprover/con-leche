module

public import ConLeche.SetTheory.Derive.Natrec
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.Iter

@[expose] public section

/-!
# (W) from ACCESSIBILITY, internal and ordinal-free

Replaces Lean-level Brouwer trees `BT V`, meta-level `Nat` iteration
`natUnion` / `accPathsN`, and global `Classical.choose` Skolemization
(`skolem_supp` / `skolem_suppG`) with purely first-order internal ZFC +
Grothendieck constructions:

* `occEnc m i y := kpair (vnat m) (kpair i y)` and `occSpace k Is X`
  encode tuple occurrences as sets in `V`; `AccTuple`, `AccRead`, and
  `AccJointG` carry set-level support graphs `g ∈ˢ piSet B (fun _ => occSpace ...) _`.
* `accPaths A` uses internal `omegaRec` + `omegaUnion` (valid in
  non-standard `ω` models).
* `closed_of_acc` uses internal well-founded `A`-trees `WF A ⊆ power (accPaths A)`,
  injectivity of `tree A f`, a local nested-`prod` tuple space
  `tupSpace w Is k` (no `ndTowerSet` import), Knaster–Tarski stage graph
  `G_stage`, `WF_ind`, and **one** `piSet_choose` call (`hΦ : DefTupleOp k Φ`).
* `skolem_supp` uses `piSet_choose` over `DefRel 3` support predicates;
  `accRead_pi`, `accRead_comp`, `lfpP_acc`, and `lfpP_acc_group` carry
  `DefRel`/`DefFun`/`DefTupleOp` hypotheses accordingly.
-/

namespace ConLeche.SetTheory

open ConLeche.SetTheory.Tower
  (boundFibre boundFibre_vnat_lt hasSigmaPairs_boundFibre
   omegaUnion mem_omegaUnion omegaUnion_mem_tg_pos)

universe u

variable {V : Type u} [SetTheory V]

/-! ## Kuratowski pair projections -/

open Classical in
/-- First component of a Kuratowski pair (`empty` if not uniquely paired). -/
noncomputable def kp1 (p : V) : V :=
  if h : ExistsUnique fun x => ∃ y, p = kpair x y then Classical.choose h else empty

open Classical in
/-- Second component of a Kuratowski pair (`empty` if not uniquely paired). -/
noncomputable def kp2 (p : V) : V :=
  if h : ExistsUnique fun y => ∃ x, p = kpair x y then Classical.choose h else empty

theorem kp1_kpair (a b : V) : kp1 (kpair a b) = a := by
  unfold kp1
  have hex : ExistsUnique fun x => ∃ y, kpair a b = kpair x y := by
    refine ⟨a, ⟨b, rfl⟩, fun x' ⟨y', h'⟩ => (kpair_inj h').1.symm⟩
  rw [dite_eq_left hex]
  obtain ⟨⟨y, hy⟩, _⟩ := Classical.choose_spec hex
  exact (kpair_inj hy).1.symm

theorem kp2_kpair (a b : V) : kp2 (kpair a b) = b := by
  unfold kp2
  have hex : ExistsUnique fun y => ∃ x, kpair a b = kpair x y := by
    refine ⟨b, ⟨a, rfl⟩, fun y' ⟨x', h'⟩ => (kpair_inj h').2.symm⟩
  rw [dite_eq_left hex]
  obtain ⟨⟨x, hx⟩, _⟩ := Classical.choose_spec hex
  exact (kpair_inj hx).2.symm

theorem DefFun.kp1_apply {k : Nat} {P : (Fin k → V) → V} (hP : DefFun k P) :
    DefFun k fun env => kp1 (P env) := by
  unfold kp1
  have hR : DefRel (k + 1) fun v => ∃ y, P (ftail v) = kpair (v 0) y :=
    DefRel.exists_curry
      (DefRel.eq_apply hP.weaken.weaken (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)))
  exact DefFun.uniqueChoice_curry hR

theorem DefFun.kp2_apply {k : Nat} {P : (Fin k → V) → V} (hP : DefFun k P) :
    DefFun k fun env => kp2 (P env) := by
  unfold kp2
  have hR : DefRel (k + 1) fun v => ∃ x, P (ftail v) = kpair x (v 0) :=
    DefRel.exists_curry
      (DefRel.eq_apply hP.weaken.weaken (DefFun.kpair_apply (DefFun.proj 0) (DefFun.proj 1)))
  exact DefFun.uniqueChoice_curry hR

/-! ## Set-encoded tuple occurrences and `AccTuple` -/

/-- Set encoding of an occurrence `(m, i, y)`. -/
noncomputable def occEnc (m : Nat) (i y : V) : V :=
  kpair (vnat m) (kpair i y)

theorem occEnc_inj {m₁ m₂ : Nat} {i₁ y₁ i₂ y₂ : V}
    (h : occEnc m₁ i₁ y₁ = occEnc m₂ i₂ y₂) : m₁ = m₂ ∧ i₁ = i₂ ∧ y₁ = y₂ := by
  unfold occEnc at h
  obtain ⟨h1, h2⟩ := kpair_inj h
  obtain ⟨h3, h4⟩ := kpair_inj h2
  exact ⟨vnat_inj h1, h3, h4⟩

theorem DefFun.occEnc_apply {p : Nat} (m : Nat) {I Y : (Fin p → V) → V}
    (hI : DefFun p I) (hY : DefFun p Y) :
    DefFun p fun env => occEnc m (I env) (Y env) :=
  DefFun.kpair_apply (DefFun.const (vnat m)) (DefFun.kpair_apply hI hY)

theorem hasSep_occDom (k : Nat) :
    HasSep (omega : V) fun c => ∃ n, n < k ∧ c = vnat n :=
  hasSep_of_defPred <|
    DefRel.finExists_lt fun n _ => DefRel.eq_apply (DefFun.proj 0) (DefFun.const (vnat n))

theorem hasSigmaPairs_app_local (A X : V) : HasSigmaPairs A (fun i => app X i) :=
  hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const X) (DefFun.proj 0))

/-- The set of all valid tuple occurrences `occEnc m i y` (`m < k`,
`i ∈ˢ Is m`, `y ∈ˢ app (X m) i`). -/
noncomputable def occSpace (k : Nat) (Is X : Nat → V) : V :=
  sigmaPairs (sep omega (fun c => ∃ n, n < k ∧ c = vnat n) (hasSep_occDom k))
    (boundFibre k fun c => sigmaPairs (Is c) (fun i => app (X c) i)
      (hasSigmaPairs_app_local (Is c) (X c)))
    (hasSigmaPairs_boundFibre _ k _)

theorem mem_occSpace {k : Nat} {Is X : Nat → V} {u : V} :
    u ∈ˢ occSpace k Is X ↔
      ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ ∃ y, y ∈ˢ app (X m) i ∧ u = occEnc m i y := by
  unfold occSpace
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨t, ht, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ht
    rw [boundFibre_vnat_lt _ hn] at hp
    obtain ⟨i, hi, y, hy, rfl⟩ := mem_sigmaPairs.mp hp
    exact ⟨n, hn, i, hi, y, hy, rfl⟩
  · rintro ⟨m, hm, i, hi, y, hy, rfl⟩
    refine ⟨vnat m, mem_sep.mpr ⟨vnat_mem_omega m, m, hm, rfl⟩, kpair i y, ?_, rfl⟩
    rw [boundFibre_vnat_lt _ hm]
    exact mem_sigmaPairs.mpr ⟨i, hi, y, hy, rfl⟩

theorem occEnc_mem_occSpace {k : Nat} {Is X : Nat → V} {m : Nat} {i y : V} :
    occEnc m i y ∈ˢ occSpace k Is X ↔ m < k ∧ i ∈ˢ Is m ∧ y ∈ˢ app (X m) i := by
  rw [mem_occSpace]
  constructor
  · rintro ⟨m', hm', i', hi', y', hy', heq⟩
    obtain ⟨rfl, rfl, rfl⟩ := occEnc_inj heq
    exact ⟨hm', hi', hy'⟩
  · rintro ⟨hm, hi, hy⟩
    exact ⟨m, hm, i, hi, y, hy, rfl⟩

theorem occSpace_congr {k : Nat} {Is Is' X X' : Nat → V}
    (hIs : ∀ m, m < k → Is m = Is' m) (hX : ∀ m, m < k → X m = X' m) :
    occSpace k Is X = occSpace k Is' X' := by
  apply ext fun u => ?_
  rw [mem_occSpace, mem_occSpace]
  constructor
  · rintro ⟨m, hm, i, hi, y, hy, rfl⟩
    exact ⟨m, hm, i, hIs m hm ▸ hi, y, hX m hm ▸ hy, rfl⟩
  · rintro ⟨m, hm, i, hi, y, hy, rfl⟩
    exact ⟨m, hm, i, (hIs m hm).symm ▸ hi, y, (hX m hm).symm ▸ hy, rfl⟩

theorem occSpace_mono {k : Nat} {Is X X' : Nat → V} (h : TupleLe k Is X X') :
    occSpace k Is X ⊆ˢ occSpace k Is X' := fun u hu => by
  obtain ⟨m, hm, i, hi, y, hy, rfl⟩ := mem_occSpace.mp hu
  exact mem_occSpace.mpr ⟨m, hm, i, hi, y, h m hm i hi y hy, rfl⟩

theorem DefFun.occSpace_apply {p : Nat} (k : Nat)
    {Is X : Nat → (Fin p → V) → V}
    (hIs : ∀ m, m < k → DefFun p (Is m)) (hX : ∀ m, m < k → DefFun p (X m)) :
    DefFun p fun env => occSpace k (fun m => Is m env) (fun m => X m env) := by
  unfold occSpace
  refine DefFun.sigmaPairs_apply_curry
    (DefFun.const (sep omega (fun c => ∃ n, n < k ∧ c = vnat n) (hasSep_occDom k))) ?_
  exact DefFun.boundFibre_apply k
    (fun m hm => DefFun.sigmaPairs_apply_curry (hIs m hm).weaken
      (DefFun.app_apply (hX m hm).weaken.weaken (DefFun.proj 0)))
    (DefFun.proj 0)

/-- Occurrence membership predicate (compatibility helper). -/
def InTup (k : Nat) (Is X : Nat → V) (u : V) : Prop :=
  u ∈ˢ occSpace k Is X

/-- **`A`-accessibility** of an operator from `kI`-tuples over `IsI` to
`kO`-tuples over `IsO`, using set-level support graphs `g`. -/
def AccTuple (w kI : Nat) (IsI : Nat → V) (kO : Nat) (IsO : Nat → V)
    (Φ : (Nat → V) → Nat → V) (A : V) : Prop :=
  ∀ X, InTupleSpace w kI IsI X → ∀ m, m < kO → ∀ i, i ∈ˢ IsO m → ∀ x, x ∈ˢ app (Φ X m) i →
    ∃ (B g : V), B ⊆ˢ A ∧
      g ∈ˢ piSet B (fun _ => occSpace kI IsI X) (hasSigmaPairs_const _ _) ∧
      ∀ X', InTupleSpace w kI IsI X' →
        (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kI IsI X') →
        x ∈ˢ app (Φ X' m) i

/-! ## Paths over `A` (internal `omegaRec` + `omegaUnion`) -/

/-- Step function for finite paths over `A`. -/
noncomputable def accPathsStep (A _k s : V) : V :=
  sigmaPairs A (fun _ => s) (hasSigmaPairs_const _ _)

theorem defFun_accPathsStep (A : V) :
    DefFun 2 fun v => accPathsStep A (v 0) (v 1) := by
  unfold accPathsStep
  exact DefFun.sigmaPairs_apply_curry (DefFun.const A) (DefFun.proj 2)

open Classical in
/-- Paths of length `n` over `A` via Dedekind recursion (`omegaRec` on `ω`). -/
noncomputable def accPathsN (A k : V) : V :=
  if h : ExistsUnique fun y => ∃ g, IsAttempt unitSet (accPathsStep A) k g ∧ kpair k y ∈ˢ g
  then Classical.choose h else empty

theorem accPathsN_eq_omegaRec (A : V) {k : V} (hk : k ∈ˢ (omega : V)) :
    accPathsN A k = omegaRec unitSet (accPathsStep A) (defFun_accPathsStep A) k hk := by
  unfold accPathsN omegaRec
  rfl

theorem accPathsN_empty (A : V) : accPathsN A empty = unitSet := by
  rw [accPathsN_eq_omegaRec A empty_mem_omega, omegaRec_empty]

theorem accPathsN_vsucc (A : V) {k : V} (hk : k ∈ˢ (omega : V)) :
    accPathsN A (vsucc k) = sigmaPairs A (fun _ => accPathsN A k) (hasSigmaPairs_const _ _) := by
  rw [accPathsN_eq_omegaRec A (vsucc_mem_omega hk), accPathsN_eq_omegaRec A hk, omegaRec_vsucc]
  rfl

theorem defFun_accPathsN (A : V) : DefFun 1 fun v => accPathsN A (v 0) := by
  unfold accPathsN
  have hS : DefFun ((1 + 2) + 2) fun w => accPathsStep A (w 0) (w 1) :=
    (defFun_accPathsStep A).reIndex (fun i => match i with | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1)
  have hAtt := defRel_isAttempt_param
    (Z := fun _ : Fin (1 + 2) → V => (unitSet : V))
    (S := fun w => accPathsStep A (w 0) (w 1))
    (N := fun w : Fin (1 + 2) → V => w 2)
    (G := fun w : Fin (1 + 2) → V => w 0)
    DefFun.unitSet hS (DefFun.proj 2) (DefFun.proj 0)
  have hAtt' : DefRel (1 + 2) fun env => IsAttempt unitSet (accPathsStep A) (env 2) (env 0) :=
    hAtt.congr fun env => by simp only [fcons_zero]; exact Iff.rfl
  have hR : DefRel (1 + 1) fun v =>
      ∃ g, IsAttempt unitSet (accPathsStep A) (v 1) g ∧ kpair (v 1) (v 0) ∈ˢ g :=
    DefRel.exists_curry (DefRel.and hAtt'
      (DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 2) (DefFun.proj 1)) (DefFun.proj 0)))
  exact DefFun.uniqueChoice_curry hR

theorem hasImage_accPathsN (A : V) : HasImage (accPathsN A) omega :=
  hasImage_of_defFun1 (defFun_accPathsN A) omega

theorem hasGraph_accPathsN (A : V) : HasGraph omega (accPathsN A) :=
  hasGraph_of_defFun1 (defFun_accPathsN A)

/-- All finite paths over `A`: `⋃_{k ∈ ω} accPathsN A k`. -/
noncomputable def accPaths (A : V) : V :=
  omegaUnion (accPathsN A) (hasImage_accPathsN A)

theorem pt_mem_accPaths (A : V) : (pt : V) ∈ˢ accPaths A :=
  mem_omegaUnion.mpr ⟨empty, empty_mem_omega, by rw [accPathsN_empty]; exact pt_mem_unitSet⟩

theorem kpair_mem_accPaths {A a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ accPaths A) :
    kpair a p ∈ˢ accPaths A := by
  obtain ⟨k, hk, hp'⟩ := mem_omegaUnion.mp hp
  refine mem_omegaUnion.mpr ⟨vsucc k, vsucc_mem_omega hk, ?_⟩
  rw [accPathsN_vsucc A hk]
  exact mem_sigmaPairs.mpr ⟨a, ha, p, hp', rfl⟩

theorem accPaths_mem {w : Nat} (hw : w ≠ 0) {A : V} (hA : A ∈ˢ (tg w : V)) :
    accPaths A ∈ˢ (tg w : V) := by
  have hU := tg_isGrothendieck (V := V) hw
  refine omegaUnion_mem_tg_pos hw (hasImage_accPathsN A) (hasGraph_accPathsN A) fun k hk => ?_
  have hP : DefPred fun k => accPathsN A k ∈ˢ (tg w : V) :=
    DefRel.mem_apply (defFun_accPathsN A) (DefFun.tg_const w)
  refine omega_ind_of_def (DefPredOn.of_defPred hP) ?_ ?_ k hk
  · rw [accPathsN_empty]; exact unitSet_mem_tg w
  · intro m hm ihm
    rw [accPathsN_vsucc A hm]
    exact hU.sigmaPairs_mem hA (fun _ _ => ihm) _

/-! ## Local nested-`prod` tuple space (no `Value.lean` / `ndTowerSet` import) -/

/-- Nested Cartesian product of `famSpace w (Is 0) × ⋯ × famSpace w (Is (k - 1))`. -/
noncomputable def tupSpace (w : Nat) (Is : Nat → V) : Nat → V
  | 0 => unitSet
  | m + 1 => prod (tupSpace w Is m) (famSpace w (Is m))

/-- Pack the first `k` components of `X : Nat → V` into `tupSpace w Is k`. -/
noncomputable def packTup (X : Nat → V) : Nat → V
  | 0 => pt
  | m + 1 => kpair (packTup X m) (X m)

/-- Strip `r` rightmost Kuratowski pairs from a nested left-associated tuple. -/
noncomputable def stripR : Nat → V → V
  | 0, t => t
  | r + 1, t => kp1 (stripR r t)

/-- Unpack component `m < k` from a packed tuple `t ∈ˢ tupSpace w Is k`. -/
noncomputable def unpackTup (k : Nat) (t : V) (m : Nat) : V :=
  if m < k then kp2 (stripR (k - 1 - m) t) else empty

theorem packTup_mem {w k : Nat} {Is X : Nat → V} (hX : InTupleSpace w k Is X) :
    packTup X k ∈ˢ tupSpace w Is k := by
  induction k with
  | zero => exact pt_mem_unitSet
  | succ k ih =>
    refine mem_prod.mpr ⟨packTup X k, ih (fun m hm => hX m (Nat.lt_succ_of_lt hm)),
      X k, hX k (Nat.lt_succ_self k), rfl⟩

theorem stripR_mem_tupSpace {w k r : Nat} {Is : Nat → V} {t : V}
    (hr : r ≤ k) (ht : t ∈ˢ tupSpace w Is k) :
    stripR r t ∈ˢ tupSpace w Is (k - r) := by
  induction r with
  | zero => simpa [stripR] using ht
  | succ r ih =>
    have hrk : r < k := Nat.lt_of_succ_le hr
    have hprev := ih (Nat.le_of_lt hrk)
    have hpos : ∃ m, k - r = m + 1 := ⟨k - r - 1, by omega⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm] at hprev
    obtain ⟨a, ha, b, _, heq⟩ := mem_prod.mp hprev
    have hsr : stripR (r + 1) t = a := by
      unfold stripR; rw [heq, kp1_kpair]
    rw [hsr, show k - (r + 1) = m by omega]
    exact ha

theorem unpackTup_mem {w k : Nat} {Is : Nat → V} {t : V}
    (ht : t ∈ˢ tupSpace w Is k) : InTupleSpace w k Is (unpackTup k t) := by
  intro m hm
  unfold unpackTup
  rw [ite_eq_left hm]
  have hle : k - 1 - m ≤ k := by omega
  have hsr := stripR_mem_tupSpace hle ht
  have heq_sub : k - (k - 1 - m) = m + 1 := by omega
  rw [heq_sub] at hsr
  obtain ⟨_, _, b, hb, heq⟩ := mem_prod.mp hsr
  rw [heq, kp2_kpair]
  exact hb

theorem unpackTup_packTup {k : Nat} (X : Nat → V) {m : Nat} (hm : m < k) :
    unpackTup k (packTup X k) m = X m := by
  unfold unpackTup
  rw [ite_eq_left hm]
  have gen : ∀ r (hr : r < k), stripR r (packTup X k) = packTup X (k - r) := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ r ih =>
      intro hr
      have hr' : r < k := Nat.lt_of_succ_lt hr
      have hpos : k - r = (k - r - 1) + 1 := by omega
      unfold stripR
      rw [ih hr', hpos, packTup, kp1_kpair, show k - (r + 1) = k - r - 1 by omega]
  have hlt : k - 1 - m < k := by omega
  rw [gen (k - 1 - m) hlt, show k - (k - 1 - m) = m + 1 by omega, packTup, kp2_kpair]

theorem packTup_unpackTup {w k : Nat} {Is : Nat → V} {t : V}
    (ht : t ∈ˢ tupSpace w Is k) : packTup (unpackTup k t) k = t := by
  induction k generalizing t with
  | zero =>
    unfold tupSpace at ht
    exact (mem_unitSet_iff.mp ht).symm
  | succ k ih =>
    obtain ⟨a, ha, b, _, rfl⟩ := mem_prod.mp ht
    have hfront : ∀ m, m < k → unpackTup (k + 1) (kpair a b) m = unpackTup k a m := by
      intro m hm
      unfold unpackTup
      rw [ite_eq_left (Nat.lt_succ_of_lt hm), ite_eq_left hm]
      have hsub : k + 1 - 1 - m = (k - 1 - m) + 1 := by omega
      rw [hsub]
      have hstrip : ∀ (r : Nat) (x y : V), stripR (r + 1) (kpair x y) = stripR r x := by
        intro r x y
        induction r with
        | zero => unfold stripR; exact kp1_kpair x y
        | succ r ihr => unfold stripR; rw [ihr]
      rw [hstrip]
    have hcut : ∀ j, j < k → packTup (unpackTup (k + 1) (kpair a b)) j = packTup (unpackTup k a) j := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ihj =>
        intro hj
        simp only [packTup]
        rw [ihj (Nat.lt_of_succ_lt hj), hfront j (Nat.lt_of_succ_lt hj)]
    have hkcut : packTup (unpackTup (k + 1) (kpair a b)) k = packTup (unpackTup k a) k := by
      cases k with
      | zero => rfl
      | succ k' =>
        simp only [packTup]
        rw [hcut k' (Nat.lt_succ_self k'), hfront k' (Nat.lt_succ_self k')]
    have hlast : unpackTup (k + 1) (kpair a b) k = b := by
      unfold unpackTup
      rw [ite_eq_left (Nat.lt_succ_self k), Nat.succ_sub_one, Nat.sub_self, stripR, kp2_kpair]
    simp only [packTup]
    rw [hkcut, ih ha, hlast]

theorem DefFun.stripR_apply {p : Nat} (r : Nat) {T : (Fin p → V) → V} (hT : DefFun p T) :
    DefFun p fun env => stripR r (T env) := by
  induction r with
  | zero => exact hT
  | succ r ih => exact DefFun.kp1_apply ih

theorem DefFun.unpackTup_apply {p : Nat} (k : Nat) {T : (Fin p → V) → V} (hT : DefFun p T)
    (m : Nat) : DefFun p fun env => unpackTup k (T env) m := by
  unfold unpackTup
  by_cases hm : m < k
  · simpa [hm] using DefFun.kp2_apply (DefFun.stripR_apply (k - 1 - m) hT)
  · simpa [hm] using DefFun.empty

theorem DefFun.packTup_apply {p : Nat} (k : Nat) {X : Nat → (Fin p → V) → V}
    (hX : ∀ m, m < k → DefFun p (X m)) :
    DefFun p fun env => packTup (fun m => X m env) k := by
  induction k with
  | zero => exact DefFun.pt
  | succ k ih =>
    exact DefFun.kpair_apply
      (ih fun m hm => hX m (Nat.lt_succ_of_lt hm))
      (hX k (Nat.lt_succ_self k))

/-! ## Internal well-founded `A`-trees and `(W)` from accessibility -/

namespace AccIter

section Iter

variable (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (A : V)

/-- The empty tuple. -/
noncomputable def emptyTup : Nat → V := fun m => famOf (fun _ => empty) (Is m) (hasGraph_const empty (Is m))

theorem emptyTup_mem : InTupleSpace w k Is (emptyTup Is) :=
  fun _ _ => famOf_mem_famSpace fun _ _ => empty_mem_strictU w

/-- The fibrewise union of an `A`-indexed family of tuples (carrying `HasImage`/`HasGraph`). -/
noncomputable def unionTup (F : V → Nat → V)
    (hImg : ∀ m i, HasImage (fun a => app (F a m) i) A)
    (hGr : ∀ m, HasGraph (Is m) fun i => sUnion (image (fun a => app (F a m) i) A (hImg m i))) :
    Nat → V :=
  fun m => famOf (fun i => sUnion (image (fun a => app (F a m) i) A (hImg m i))) (Is m) (hGr m)

theorem mem_unionTup_aux {Is : Nat → V} {A : V} {F : V → Nat → V}
    {hImg : ∀ m i, HasImage (fun a => app (F a m) i) A}
    {hGr : ∀ m, HasGraph (Is m) fun i => sUnion (image (fun a => app (F a m) i) A (hImg m i))}
    {m : Nat} {i y : V} (hi : i ∈ˢ Is m) :
    y ∈ˢ app (unionTup Is A F hImg hGr m) i ↔ ∃ a, a ∈ˢ A ∧ y ∈ˢ app (F a m) i := by
  unfold unionTup
  rw [app_famOf hi, mem_sUnion]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨_, mem_image.mpr ⟨a, ha, rfl⟩, hy⟩

theorem hasImage_kpair_const (a s : V) : HasImage (kpair a) s :=
  hasImage_of_defFun1 (DefFun.kpair_apply (DefFun.const a) (DefFun.proj 0)) s

theorem defFun_treeStep (f : V) :
    DefFun 1 fun v => image (kpair (v 0)) (app f (v 0)) (hasImage_kpair_const (v 0) (app f (v 0))) :=
  DefFun.image_apply_curry
    (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
    (DefFun.app_apply (DefFun.const f) (DefFun.proj 0))

theorem hasImage_treeStep (A f : V) :
    HasImage (fun a => image (kpair a) (app f a) (hasImage_kpair_const a (app f a))) A :=
  hasImage_of_defFun1 (defFun_treeStep f) A

/-- Internal `A`-branching tree constructor for `f ∈ˢ piSet A (fun _ => P) _`. -/
noncomputable def tree (A f : V) : V :=
  binUnion unitSet
    (sUnion (image (fun a => image (kpair a) (app f a) (hasImage_kpair_const a (app f a)))
      A (hasImage_treeStep A f)))

theorem DefFun.tree_apply {p : Nat} (A : V) {F : (Fin p → V) → V} (hF : DefFun p F) :
    DefFun p fun env => tree A (F env) := by
  unfold tree
  refine DefFun.binUnion_apply DefFun.unitSet (DefFun.sUnion_apply (DefFun.image_apply_curry ?_ (DefFun.const A)))
  exact DefFun.image_apply_curry
    (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
    (DefFun.app_apply hF.weaken (DefFun.proj 0))

variable {Is Φ A}

theorem mem_tree {A f z : V} :
    z ∈ˢ tree A f ↔ z = pt ∨ ∃ a, a ∈ˢ A ∧ ∃ q, q ∈ˢ app f a ∧ z = kpair a q := by
  unfold tree
  rw [mem_binUnion, mem_unitSet_iff, mem_sUnion]
  constructor
  · rintro (h | ⟨s, hs, hz⟩)
    · exact Or.inl h
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
      exact Or.inr ⟨a, ha, q, hq, rfl⟩
  · rintro (h | ⟨a, ha, q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, mem_image.mpr ⟨a, ha, rfl⟩, mem_image.mpr ⟨q, hq, rfl⟩⟩

theorem tree_ne_empty (A f : V) : tree A f ≠ empty :=
  ne_empty_of_mem (mem_tree.mpr (Or.inl rfl))

theorem tree_mem_power {A f : V}
    (hf : f ∈ˢ piSet A (fun _ => power (accPaths A)) (hasSigmaPairs_const _ _)) :
    tree A f ∈ˢ power (accPaths A) := by
  rw [mem_power]
  intro z hz
  rcases mem_tree.mp hz with rfl | ⟨a, ha, q, hq, rfl⟩
  · exact pt_mem_accPaths A
  · have haf : app f a ∈ˢ power (accPaths A) := app_mem_of_mem_piSet hf ha
    exact kpair_mem_accPaths ha (mem_power.mp haf q hq)

theorem tree_inj {A P f f' : V}
    (hf : f ∈ˢ piSet A (fun _ => P) (hasSigmaPairs_const _ _))
    (hf' : f' ∈ˢ piSet A (fun _ => P) (hasSigmaPairs_const _ _))
    (heq : tree A f = tree A f') : f = f' := by
  refine eq_of_mem_piSet_app_eq hf hf' fun a ha => ext fun q => ?_
  have hiff : ∀ g : V, q ∈ˢ app g a ↔ kpair a q ∈ˢ tree A g := fun g => by
    rw [mem_tree]
    constructor
    · intro hq; exact Or.inr ⟨a, ha, q, hq, rfl⟩
    · rintro (hpt | ⟨a', _, q', hq', hkp⟩)
      · exact absurd hpt.symm (pt_ne_kpair a q)
      · obtain ⟨rfl, rfl⟩ := kpair_inj hkp
        exact hq'
  rw [hiff f, heq, ← hiff f']

/-- Closure condition for well-founded `A`-tree codes inside `power (accPaths A)`. -/
def ClosedWF (A X : V) : Prop :=
  empty ∈ˢ X ∧ ∀ f, f ∈ˢ piSet A (fun _ => X) (hasSigmaPairs_const _ _) → tree A f ∈ˢ X

theorem DefRel.closedWF_apply {p : Nat} (A : V) {X : (Fin p → V) → V} (hX : DefFun p X) :
    DefRel p fun env => ClosedWF A (X env) := by
  unfold ClosedWF
  refine DefRel.and (DefRel.mem_apply DefFun.empty hX) ?_
  exact DefRel.bForall_curry
    (DefFun.piSet_apply_curry (DefFun.const A) hX.weaken)
    (DefRel.mem_apply (DefFun.tree_apply A (DefFun.proj 0)) hX.weaken)

theorem hasSep_WF (A : V) :
    HasSep (power (accPaths A))
      (fun c => ∀ X, X ∈ˢ power (power (accPaths A)) → ClosedWF A X → c ∈ˢ X) :=
  hasSep_of_defPred <|
    DefRel.bForall_curry (DefFun.power_apply (DefFun.const (power (accPaths A))))
      (DefRel.imp (DefRel.closedWF_apply A (DefFun.proj 0))
        (DefRel.mem_apply (DefFun.proj 1) (DefFun.proj 0)))

/-- Set of internal well-founded `A`-tree codes inside `power (accPaths A)`. -/
noncomputable def WF (A : V) : V :=
  sep (power (accPaths A))
    (fun c => ∀ X, X ∈ˢ power (power (accPaths A)) → ClosedWF A X → c ∈ˢ X)
    (hasSep_WF A)

theorem WF_subset (A : V) : WF A ⊆ˢ power (accPaths A) := sep_subset

theorem WF_mem {w : Nat} (hw : w ≠ 0) {A : V} (hA : A ∈ˢ (tg w : V)) :
    WF A ∈ˢ (tg w : V) :=
  (tg_isGrothendieck hw).mem_of_subset_mem
    ((tg_isGrothendieck hw).power_mem (accPaths_mem hw hA)) (WF_subset A)

theorem empty_mem_WF (A : V) : (empty : V) ∈ˢ WF A :=
  mem_sep.mpr ⟨mem_power.mpr (empty_subset _), fun _ _ hX => hX.1⟩

theorem tree_mem_WF {A f : V}
    (hf : f ∈ˢ piSet A (fun _ => WF A) (hasSigmaPairs_const _ _)) :
    tree A f ∈ˢ WF A := by
  have hfP : f ∈ˢ piSet A (fun _ => power (accPaths A)) (hasSigmaPairs_const _ _) := by
    rw [mem_piSet] at hf ⊢
    refine ⟨Subset.trans hf.1 fun p hp => ?_, hf.2⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨a, ha, y, WF_subset A y hy, rfl⟩
  refine mem_sep.mpr ⟨tree_mem_power hfP, fun X hXP hX => hX.2 f ?_⟩
  rw [mem_piSet] at hf ⊢
  refine ⟨Subset.trans hf.1 fun p hp => ?_, hf.2⟩
  obtain ⟨a, ha, y, hy, rfl⟩ := mem_sigmaPairs.mp hp
  exact mem_sigmaPairs.mpr ⟨a, ha, y, (mem_sep.mp hy).2 X hXP hX, rfl⟩

/-- Internal induction principle on `WF A` for any definable/separable predicate `Q`. -/
theorem WF_ind {A : V} {Q : V → Prop} (hSep : HasSep (WF A) Q)
    (h0 : Q empty)
    (hstep : ∀ f, f ∈ˢ piSet A (fun _ => WF A) (hasSigmaPairs_const _ _) →
      (∀ a, a ∈ˢ A → Q (app f a)) → Q (tree A f)) :
    ∀ c, c ∈ˢ WF A → Q c := by
  let X := sep (WF A) Q hSep
  have hXP : X ∈ˢ power (power (accPaths A)) :=
    mem_power.mpr (Subset.trans sep_subset (WF_subset A))
  have hXcl : ClosedWF A X := by
    refine ⟨mem_sep.mpr ⟨empty_mem_WF A, h0⟩, fun f hf => ?_⟩
    have hfW : f ∈ˢ piSet A (fun _ => WF A) (hasSigmaPairs_const _ _) := by
      rw [mem_piSet] at hf ⊢
      refine ⟨Subset.trans hf.1 fun p hp => ?_, hf.2⟩
      obtain ⟨a, ha, y, hy, rfl⟩ := mem_sigmaPairs.mp hp
      exact mem_sigmaPairs.mpr ⟨a, ha, y, sep_subset y hy, rfl⟩
    refine mem_sep.mpr ⟨tree_mem_WF hfW, hstep f hfW fun a ha => ?_⟩
    exact (mem_sep.mp (app_mem_of_mem_piSet hf ha)).2
  intro c hc
  exact (mem_sep.mp ((mem_sep.mp hc).2 X hXP hXcl)).2

/-- Knaster–Tarski closure for the stage graph `R ⊆ˢ WF A × TS`. -/
def ClosedStage (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (A R : V) : Prop :=
  kpair empty (packTup (emptyTup Is) k) ∈ˢ R ∧
  ∀ f, f ∈ˢ piSet A (fun _ => WF A) (hasSigmaPairs_const _ _) →
  ∀ s, s ∈ˢ piSet A (fun _ => tupSpace w Is k) (hasSigmaPairs_const _ _) →
    (∀ a, a ∈ˢ A → kpair (app f a) (app s a) ∈ˢ R) →
    kpair (tree A f)
      (packTup (Φ (unionTup Is A (fun a => unpackTup k (app s a))
        (fun m i => hasImage_of_defFun1 (f := fun a => app (unpackTup k (app s a) m) i)
          (DefFun.app_apply (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
            (DefFun.const i)) A)
        (fun m => hasGraph_of_defFun1
          (DefFun.sUnion_apply (DefFun.image_apply_curry
            (DefFun.app_apply
              (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
              (DefFun.proj 1))
            (DefFun.const A)))))) k) ∈ˢ R

theorem defFun_unionTup_pack (_w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) :
    DefFun 1 fun v : Fin 1 → V =>
      packTup (Φ (unionTup Is A (fun a => unpackTup k (app (v 0) a))
        (fun m i => hasImage_of_defFun1 (f := fun a => app (unpackTup k (app (v 0) a) m) i)
          (DefFun.app_apply (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
            (DefFun.const i)) A)
        (fun m => hasGraph_of_defFun1
          (DefFun.sUnion_apply (DefFun.image_apply_curry
            (DefFun.app_apply
              (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
              (DefFun.proj 1))
            (DefFun.const A)))))) k := by
  have hcomp : ∀ m, m < k → DefFun 1 fun v : Fin 1 → V =>
      unionTup Is A (fun a => unpackTup k (app (v 0) a))
        (fun m i => hasImage_of_defFun1 (f := fun a => app (unpackTup k (app (v 0) a) m) i)
          (DefFun.app_apply (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
            (DefFun.const i)) A)
        (fun m => hasGraph_of_defFun1
          (DefFun.sUnion_apply (DefFun.image_apply_curry
            (DefFun.app_apply
              (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
              (DefFun.proj 1))
            (DefFun.const A)))) m := by
    intro m _
    unfold unionTup
    refine DefFun.famOf_apply_curry ?_ (DefFun.const (Is m))
    exact DefFun.sUnion_apply
      (DefFun.image_apply_curry
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.proj 2) (DefFun.proj 0)) m)
          (DefFun.proj 1))
        (DefFun.const A))
  have hGs : ∀ m, m < k → DefFun 1 fun v : Fin 1 → V =>
      Φ (padTuple fun j : Fin k =>
        unionTup Is A (fun a => unpackTup k (app (v 0) a))
          (fun m i => hasImage_of_defFun1 (f := fun a => app (unpackTup k (app (v 0) a) m) i)
            (DefFun.app_apply (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
              (DefFun.const i)) A)
          (fun m => hasGraph_of_defFun1
            (DefFun.sUnion_apply (DefFun.image_apply_curry
              (DefFun.app_apply
                (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const (v 0)) (DefFun.proj 0)) m)
                (DefFun.proj 1))
              (DefFun.const A)))) j.val) m := fun m hm =>
    (hΦ.2 m hm).comp fun j => hcomp j.val j.isLt
  refine DefFun.packTup_apply k fun m hm => (hGs m hm).congr fun v => ?_
  exact hΦ.1 _ _ (fun j hj => by rw [padTuple_lt _ hj]) m hm

theorem defPred_closedStage (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) :
    DefPred fun R => ClosedStage w k Is Φ A R := by
  unfold ClosedStage
  refine DefRel.and
    (DefRel.mem_apply (DefFun.const (kpair empty (packTup (emptyTup Is) k))) (DefFun.proj 0)) ?_
  refine DefRel.bForall_curry
    (DefFun.const (piSet A (fun _ => WF A) (hasSigmaPairs_const _ _))) ?_
  refine DefRel.bForall_curry
    (DefFun.const (piSet A (fun _ => tupSpace w Is k) (hasSigmaPairs_const _ _))) ?_
  refine DefRel.imp ?_ ?_
  · refine DefRel.bForall_curry (DefFun.const A) ?_
    exact DefRel.mem_apply
      (DefFun.kpair_apply
        (DefFun.app_apply (DefFun.proj 2) (DefFun.proj 0))
        (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0)))
      (DefFun.proj 3)
  · exact DefRel.mem_apply
      (DefFun.kpair_apply
        (DefFun.tree_apply A (DefFun.proj 1))
        ((defFun_unionTup_pack w k Is Φ hΦ A).reIndex fun _ => (0 : Fin 3)))
      (DefFun.proj 2)

theorem hasSep_G_stage (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) :
    HasSep (prod (WF A) (tupSpace w Is k))
      (fun q => ∀ R, R ∈ˢ power (prod (WF A) (tupSpace w Is k)) → ClosedStage w k Is Φ A R → q ∈ˢ R) :=
  hasSep_of_defPred <|
    DefRel.bForall_curry (DefFun.power_apply (DefFun.const (prod (WF A) (tupSpace w Is k))))
      (DefRel.imp ((defPred_closedStage w k Is Φ hΦ A).reIndex fun _ => 0)
        (DefRel.mem_apply (DefFun.proj 1) (DefFun.proj 0)))

/-- Least stage graph `G_stage ⊆ˢ WF A × TS` mapping each internal tree `c ∈ˢ WF A`
to its tuple stage. -/
noncomputable def G_stage (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) : V :=
  sep (prod (WF A) (tupSpace w Is k))
    (fun q => ∀ R, R ∈ˢ power (prod (WF A) (tupSpace w Is k)) → ClosedStage w k Is Φ A R → q ∈ˢ R)
    (hasSep_G_stage w k Is Φ hΦ A)

theorem G_stage_subset {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    {hΦ : DefTupleOp k Φ} {A : V} :
    G_stage w k Is Φ hΦ A ⊆ˢ prod (WF A) (tupSpace w Is k) := sep_subset

theorem G_stage_min {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    {hΦ : DefTupleOp k Φ} {A R : V}
    (hRP : R ∈ˢ power (prod (WF A) (tupSpace w Is k))) (hR : ClosedStage w k Is Φ A R) :
    G_stage w k Is Φ hΦ A ⊆ˢ R := fun _ hq =>
  (mem_sep.mp hq).2 R hRP hR

theorem G_stage_closed {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) :
    ClosedStage w k Is Φ A (G_stage w k Is Φ hΦ A) := by
  refine ⟨mem_sep.mpr ⟨mem_prod.mpr ⟨empty, empty_mem_WF A, packTup (emptyTup Is) k,
    packTup_mem (emptyTup_mem (w := w) (k := k) (Is := Is)), rfl⟩, fun _ _ hR => hR.1⟩, ?_⟩
  intro f hf s hs hfs
  have hun_img : ∀ m i, HasImage (fun a => app (unpackTup k (app s a) m) i) A := fun m i =>
    hasImage_of_defFun1 (f := fun a => app (unpackTup k (app s a) m) i)
      (DefFun.app_apply
        (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
        (DefFun.const i)) A
  have hun_gr : ∀ m, HasGraph (Is m) fun i =>
      sUnion (image (fun a => app (unpackTup k (app s a) m) i) A (hun_img m i)) := fun m =>
    hasGraph_of_defFun1
      (DefFun.sUnion_apply (DefFun.image_apply_curry
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
          (DefFun.proj 1))
        (DefFun.const A)))
  have hun : InTupleSpace w k Is (unionTup Is A (fun a => unpackTup k (app s a)) hun_img hun_gr) := by
    intro m hm
    refine famOf_mem_famSpace fun i hi => ?_
    refine strictU_famUnion_mem hw hA (fun a ha => ?_) (hun_img m i)
      (hasGraph_of_defFun1
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
          (DefFun.const i)))
    exact famSpace_app (unpackTup_mem (app_mem_of_mem_piSet (B := fun _ => tupSpace w Is k) hs ha) m hm) hi
  refine mem_sep.mpr ⟨mem_prod.mpr ⟨tree A f, tree_mem_WF hf, _, packTup_mem (hmaps _ hun), rfl⟩,
    fun R hRP hR => hR.2 f hf s hs fun a ha => (mem_sep.mp (hfs a ha)).2 R hRP hR⟩

open Classical in
theorem existsUnique_stageOf {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) :
    ∀ c, c ∈ˢ WF A →
      ExistsUnique fun t => t ∈ˢ tupSpace w Is k ∧ kpair c t ∈ˢ G_stage w k Is Φ hΦ A := by
  let G := G_stage w k Is Φ hΦ A
  have hGcl := G_stage_closed hw hA hΦ hmaps
  let Q : V → Prop := fun c => ExistsUnique fun t => t ∈ˢ tupSpace w Is k ∧ kpair c t ∈ˢ G
  have hSepQ : HasSep (WF A) Q :=
    hasSep_of_defPred <|
      DefRel.existsUnique_curry
        (DefRel.and
          (DefRel.mem_apply (DefFun.proj 0) (DefFun.const (tupSpace w Is k)))
          (DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)) (DefFun.const G)))
  refine WF_ind hSepQ ?_ ?_
  · refine ⟨packTup (emptyTup Is) k, ⟨packTup_mem (emptyTup_mem (w := w) (k := k) (Is := Is)), hGcl.1⟩, ?_⟩
    rintro t ⟨_, hkt⟩
    refine Classical.byContradiction fun hne => ?_
    let R := sep G (fun q => q ≠ kpair empty t) (hasSep_of_defPred
      (DefRel.ne_apply (DefFun.proj 0) (DefFun.const (kpair empty t))))
    have hRP : R ∈ˢ power (prod (WF A) (tupSpace w Is k)) :=
      mem_power.mpr (Subset.trans sep_subset G_stage_subset)
    have hRcl : ClosedStage w k Is Φ A R := by
      refine ⟨mem_sep.mpr ⟨hGcl.1, fun h => hne (kpair_inj h).2.symm⟩, fun f hf s hs hfs => ?_⟩
      refine mem_sep.mpr ⟨hGcl.2 f hf s hs fun a ha => (mem_sep.mp (hfs a ha)).1, fun h => ?_⟩
      exact tree_ne_empty A f (kpair_inj h).1
    exact (mem_sep.mp (G_stage_min hRP hRcl _ hkt)).2 rfl
  · intro f hf ih
    let F_s : V → V := fun a =>
      if h : ExistsUnique fun t => t ∈ˢ tupSpace w Is k ∧ kpair (app f a) t ∈ˢ G
      then Classical.choose h else empty
    have hFs_def : DefFun 1 fun v => F_s (v 0) := by
      unfold F_s
      exact DefFun.uniqueChoice_curry
        (DefRel.and
          (DefRel.mem_apply (DefFun.proj 0) (DefFun.const (tupSpace w Is k)))
          (DefRel.mem_apply
            (DefFun.kpair_apply (DefFun.app_apply (DefFun.const f) (DefFun.proj 0)).weaken (DefFun.proj 0))
            (DefFun.const G)))
    have hFs_mem : ∀ a, a ∈ˢ A → F_s a ∈ˢ tupSpace w Is k ∧ kpair (app f a) (F_s a) ∈ˢ G := by
      intro a ha
      dsimp only [F_s]
      rw [dite_eq_left (ih a ha)]
      exact (Classical.choose_spec (ih a ha)).1
    let s := graph F_s A (hasGraph_of_defFun1 hFs_def)
    have hs_mem : s ∈ˢ piSet A (fun _ => tupSpace w Is k) (hasSigmaPairs_const _ _) :=
      graph_mem_piSet fun a ha => (hFs_mem a ha).1
    have hfs : ∀ a, a ∈ˢ A → kpair (app f a) (app s a) ∈ˢ G := fun a ha => by
      dsimp only [s]; rw [app_graph ha]; exact (hFs_mem a ha).2
    have hun_img : ∀ m i, HasImage (fun a => app (unpackTup k (app s a) m) i) A := fun m i =>
      hasImage_of_defFun1 (f := fun a => app (unpackTup k (app s a) m) i)
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
          (DefFun.const i)) A
    have hun_gr : ∀ m, HasGraph (Is m) fun i =>
        sUnion (image (fun a => app (unpackTup k (app s a) m) i) A (hun_img m i)) := fun m =>
      hasGraph_of_defFun1
        (DefFun.sUnion_apply (DefFun.image_apply_curry
          (DefFun.app_apply
            (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
            (DefFun.proj 1))
          (DefFun.const A)))
    have hun : InTupleSpace w k Is (unionTup Is A (fun a => unpackTup k (app s a)) hun_img hun_gr) := by
      intro m hm
      refine famOf_mem_famSpace fun i hi => ?_
      refine strictU_famUnion_mem hw hA (fun a ha => ?_) (hun_img m i)
        (hasGraph_of_defFun1
          (DefFun.app_apply
            (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m)
            (DefFun.const i)))
      exact famSpace_app (unpackTup_mem (app_mem_of_mem_piSet (B := fun _ => tupSpace w Is k) hs_mem ha) m hm) hi
    let Y := packTup (Φ (unionTup Is A (fun a => unpackTup k (app s a)) hun_img hun_gr)) k
    refine ⟨Y, ⟨packTup_mem (hmaps _ hun), hGcl.2 f hf s hs_mem hfs⟩, ?_⟩
    rintro t ⟨_, hkt⟩
    refine Classical.byContradiction fun hne => ?_
    let R := sep G (fun q => q ≠ kpair (tree A f) t) (hasSep_of_defPred
      (DefRel.ne_apply (DefFun.proj 0) (DefFun.const (kpair (tree A f) t))))
    have hRP : R ∈ˢ power (prod (WF A) (tupSpace w Is k)) :=
      mem_power.mpr (Subset.trans sep_subset G_stage_subset)
    have hRcl : ClosedStage w k Is Φ A R := by
      refine ⟨mem_sep.mpr ⟨hGcl.1, fun h => tree_ne_empty A f (kpair_inj h).1.symm⟩, ?_⟩
      intro f' hf' s' hs' hfs'
      refine mem_sep.mpr ⟨hGcl.2 f' hf' s' hs' fun a ha => (mem_sep.mp (hfs' a ha)).1, fun h => ?_⟩
      obtain ⟨htree, hpack⟩ := kpair_inj h
      have hff : f' = f := tree_inj hf' hf htree
      subst hff
      have hss : s' = s := eq_of_mem_piSet_app_eq hs' hs_mem fun a ha =>
        (ih a ha).unique ⟨app_mem_of_mem_piSet (B := fun _ => tupSpace w Is k) hs' ha, (mem_sep.mp (hfs' a ha)).1⟩
          ⟨app_mem_of_mem_piSet (B := fun _ => tupSpace w Is k) hs_mem ha, hfs a ha⟩
      subst hss
      exact hne hpack.symm
    exact (mem_sep.mp (G_stage_min hRP hRcl _ hkt)).2 rfl

open Classical in
/-- The unique tuple stage `G_stage(c)` at `c ∈ˢ WF A`. -/
noncomputable def stageOf (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A c : V) : V :=
  if h : ExistsUnique fun t => t ∈ˢ tupSpace w Is k ∧ kpair c t ∈ˢ G_stage w k Is Φ hΦ A
  then Classical.choose h else empty

theorem DefFun.stageOf_apply {w k p : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hΦ : DefTupleOp k Φ) (A : V) {C : (Fin p → V) → V} (hC : DefFun p C) :
    DefFun p fun env => stageOf w k Is Φ hΦ A (C env) := by
  unfold stageOf
  exact DefFun.uniqueChoice_curry
    (DefRel.and
      (DefRel.mem_apply (DefFun.proj 0) (DefFun.const (tupSpace w Is k)))
      (DefRel.mem_apply (DefFun.kpair_apply hC.weaken (DefFun.proj 0))
        (DefFun.const (G_stage w k Is Φ hΦ A))))

theorem stageOf_spec {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) {c : V} (hc : c ∈ˢ WF A) :
    stageOf w k Is Φ hΦ A c ∈ˢ tupSpace w Is k ∧
      kpair c (stageOf w k Is Φ hΦ A c) ∈ˢ G_stage w k Is Φ hΦ A := by
  have hex := existsUnique_stageOf hw hA hΦ hmaps c hc
  unfold stageOf
  rw [dite_eq_left hex]
  exact (Classical.choose_spec hex).1

theorem stageOf_eq_of_mem {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) {c t : V} (hc : c ∈ˢ WF A)
    (ht : t ∈ˢ tupSpace w Is k) (hmem : kpair c t ∈ˢ G_stage w k Is Φ hΦ A) :
    stageOf w k Is Φ hΦ A c = t :=
  (existsUnique_stageOf hw hA hΦ hmaps c hc).unique (stageOf_spec hw hA hΦ hmaps hc) ⟨ht, hmem⟩

theorem hasImage_limTup (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) (m : Nat) (i : V) :
    HasImage (fun c => app (unpackTup k (stageOf w k Is Φ hΦ A c) m) i) (WF A) :=
  hasImage_of_defFun1 (f := fun c => app (unpackTup k (stageOf w k Is Φ hΦ A c) m) i)
    (DefFun.app_apply
      (DefFun.unpackTup_apply k (DefFun.stageOf_apply hΦ A (DefFun.proj 0)) m)
      (DefFun.const i))
    (WF A)

theorem hasGraph_limTup (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) (m : Nat) :
    HasGraph (Is m) fun i =>
      sUnion (image (fun c => app (unpackTup k (stageOf w k Is Φ hΦ A c) m) i) (WF A)
        (hasImage_limTup w k Is Φ hΦ A m i)) :=
  hasGraph_of_defFun1
    (DefFun.sUnion_apply
      (DefFun.image_apply_curry
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.stageOf_apply hΦ A (DefFun.proj 0)) m)
          (DefFun.proj 1))
        (DefFun.const (WF A))))

/-- **The limit tuple**: the union of the stages over all internal tree codes `c ∈ˢ WF A`. -/
noncomputable def limTup (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (hΦ : DefTupleOp k Φ) (A : V) : Nat → V :=
  fun m => famOf
    (fun i => sUnion (image (fun c => app (unpackTup k (stageOf w k Is Φ hΦ A c) m) i) (WF A)
      (hasImage_limTup w k Is Φ hΦ A m i)))
    (Is m) (hasGraph_limTup w k Is Φ hΦ A m)

theorem mem_limTup {hΦ : DefTupleOp k Φ} {m : Nat} {i y : V} (hi : i ∈ˢ Is m) :
    y ∈ˢ app (limTup w k Is Φ hΦ A m) i ↔
      ∃ c, c ∈ˢ WF A ∧ y ∈ˢ app (unpackTup k (stageOf w k Is Φ hΦ A c) m) i := by
  unfold limTup
  rw [app_famOf hi, mem_sUnion]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hs
    exact ⟨c, hc, hy⟩
  · rintro ⟨c, hc, hy⟩
    exact ⟨_, mem_image.mpr ⟨c, hc, rfl⟩, hy⟩

theorem limTup_mem {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) :
    InTupleSpace w k Is (limTup w k Is Φ hΦ A) := by
  intro m hm
  refine famOf_mem_famSpace fun i hi => ?_
  refine strictU_famUnion_mem hw (WF_mem hw hA) (fun c hc => ?_) _
    (hasGraph_of_defFun1
      (DefFun.app_apply
        (DefFun.unpackTup_apply k (DefFun.stageOf_apply hΦ A (DefFun.proj 0)) m)
        (DefFun.const i)))
  exact famSpace_app (unpackTup_mem (stageOf_spec hw hA hΦ hmaps hc).1 m hm) hi

/-- **(W) from accessibility.**  At a positive level, a `DefTupleOp` operator
that maps the tuple space into itself and is `A`-accessible (`A ∈ˢ tg w`) has
a closed tuple. Uses **one** `piSet_choose` call over internal `WF A`. -/
theorem closed_of_acc {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (hw : w ≠ 0) (hA : A ∈ˢ (tg w : V)) (hΦ : DefTupleOp k Φ)
    (hmaps : MapsTuple w k Is Φ) (hacc : AccTuple w k Is k Is Φ A) :
    ∃ L, IsClosedTuple w k Is Φ L := by
  let L := limTup w k Is Φ hΦ A
  have hLmem := limTup_mem (w := w) (k := k) (Is := Is) hw hA hΦ hmaps
  refine ⟨L, hLmem, fun m hm i hi x hx => ?_⟩
  obtain ⟨B, g, hBA, hgL, hsupp⟩ := hacc L hLmem m hm i hi x hx
  have hSepCand : ∀ a, HasSep (WF A)
      (fun c => a ∈ˢ B → app g a ∈ˢ occSpace k Is (unpackTup k (stageOf w k Is Φ hΦ A c))) :=
    fun a => hasSep_of_defPred <|
      DefRel.imp (DefRel.mem_apply (DefFun.const a) (DefFun.const B))
        (DefRel.mem_apply (DefFun.const (app g a))
          (DefFun.occSpace_apply k (fun m _ => DefFun.const (Is m))
            (fun m _ => DefFun.unpackTup_apply k (DefFun.stageOf_apply hΦ A (DefFun.proj 0)) m)))
  let Cand : V → V := fun a =>
    sep (WF A) (fun c => a ∈ˢ B → app g a ∈ˢ occSpace k Is (unpackTup k (stageOf w k Is Φ hΦ A c)))
      (hSepCand a)
  have hCand_ne : ∀ a, a ∈ˢ A → ∃ c, c ∈ˢ Cand a := by
    intro a _
    by_cases haB : a ∈ˢ B
    · have hmem : app g a ∈ˢ occSpace k Is L := app_mem_of_mem_piSet hgL haB
      obtain ⟨m', hm', i', hi', y', hy', heq⟩ := mem_occSpace.mp hmem
      obtain ⟨c, hcWF, hyc⟩ := (mem_limTup (w := w) (k := k) (Is := Is) (hΦ := hΦ) hi').mp hy'
      refine ⟨c, mem_sep.mpr ⟨hcWF, fun _ => ?_⟩⟩
      rw [heq, occEnc_mem_occSpace]
      exact ⟨hm', hi', hyc⟩
    · exact ⟨empty, mem_sep.mpr ⟨empty_mem_WF A, fun h => absurd h haB⟩⟩
  have hCand_sig : HasSigmaPairs A Cand := by
    refine hasSigmaPairs_of_defFun1 ?_
    dsimp only [Cand]
    refine DefFun.sep_apply_curry (DefFun.const (WF A)) ?_
    exact DefRel.imp (DefRel.mem_apply (DefFun.proj 1) (DefFun.const B))
      (DefRel.mem_apply
        (DefFun.app_apply (DefFun.const g) (DefFun.proj 1))
        (DefFun.occSpace_apply k (fun m _ => DefFun.const (Is m))
          (fun m _ => DefFun.unpackTup_apply k (DefFun.stageOf_apply hΦ A (DefFun.proj 0)) m)))
  obtain ⟨f, hf_mem⟩ := piSet_choose hCand_sig hCand_ne
  have hf_WF : f ∈ˢ piSet A (fun _ => WF A) (hasSigmaPairs_const _ _) := by
    rw [mem_piSet] at hf_mem ⊢
    refine ⟨Subset.trans hf_mem.1 fun p hp => ?_, hf_mem.2⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨a, ha, y, sep_subset y hy, rfl⟩
  have hS_def : DefFun 1 fun v => stageOf w k Is Φ hΦ A (app f (v 0)) :=
    DefFun.stageOf_apply hΦ A (DefFun.app_apply (DefFun.const f) (DefFun.proj 0))
  let s := graph (fun a => stageOf w k Is Φ hΦ A (app f a)) A (hasGraph_of_defFun1 hS_def)
  have hs_mem : s ∈ˢ piSet A (fun _ => tupSpace w Is k) (hasSigmaPairs_const _ _) := by
    dsimp only [s]
    refine graph_mem_piSet fun a ha =>
      (stageOf_spec hw hA hΦ hmaps (app_mem_of_mem_piSet (B := fun _ => WF A) hf_WF ha)).1
  have hfs : ∀ a, a ∈ˢ A → kpair (app f a) (app s a) ∈ˢ G_stage w k Is Φ hΦ A := fun a ha => by
    dsimp only [s]; rw [app_graph ha]
    exact (stageOf_spec hw hA hΦ hmaps (app_mem_of_mem_piSet (B := fun _ => WF A) hf_WF ha)).2
  have hun_img : ∀ m' i', HasImage (fun a => app (unpackTup k (app s a) m') i') A := fun m' i' =>
    hasImage_of_defFun1 (f := fun a => app (unpackTup k (app s a) m') i')
      (DefFun.app_apply
        (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m')
        (DefFun.const i')) A
  have hun_gr : ∀ m', HasGraph (Is m') fun i' =>
      sUnion (image (fun a => app (unpackTup k (app s a) m') i') A (hun_img m' i')) := fun m' =>
    hasGraph_of_defFun1
      (DefFun.sUnion_apply (DefFun.image_apply_curry
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m')
          (DefFun.proj 1))
        (DefFun.const A)))
  let U_tup := unionTup Is A (fun a => unpackTup k (app s a)) hun_img hun_gr
  have hUmem : InTupleSpace w k Is U_tup := by
    intro m' hm'
    refine famOf_mem_famSpace fun i' hi' => ?_
    refine strictU_famUnion_mem hw hA (fun a ha => ?_) (hun_img m' i')
      (hasGraph_of_defFun1
        (DefFun.app_apply
          (DefFun.unpackTup_apply k (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) m')
          (DefFun.const i')))
    exact famSpace_app (unpackTup_mem (app_mem_of_mem_piSet (B := fun _ => tupSpace w Is k) hs_mem ha) m' hm') hi'
  have hx_U : x ∈ˢ app (Φ U_tup m) i := by
    refine hsupp U_tup hUmem fun a haB => ?_
    have haA : a ∈ˢ A := hBA a haB
    have hca : app f a ∈ˢ Cand a := app_mem_of_mem_piSet hf_mem haA
    have hoc : app g a ∈ˢ occSpace k Is (unpackTup k (stageOf w k Is Φ hΦ A (app f a))) :=
      (mem_sep.mp hca).2 haB
    obtain ⟨m', hm', i', hi', y', hy', heq⟩ := mem_occSpace.mp hoc
    rw [heq, occEnc_mem_occSpace]
    refine ⟨hm', hi', (mem_unionTup_aux hi').mpr ⟨a, haA, ?_⟩⟩
    dsimp only [s]; rw [app_graph haA]; exact hy'
  have htree_WF : tree A f ∈ˢ WF A := tree_mem_WF hf_WF
  have htree_stage : kpair (tree A f) (packTup (Φ U_tup) k) ∈ˢ G_stage w k Is Φ hΦ A :=
    (G_stage_closed hw hA hΦ hmaps).2 f hf_WF s hs_mem hfs
  have hstage_eq : stageOf w k Is Φ hΦ A (tree A f) = packTup (Φ U_tup) k :=
    stageOf_eq_of_mem hw hA hΦ hmaps htree_WF (packTup_mem (hmaps _ hUmem)) htree_stage
  refine (mem_limTup (w := w) (k := k) (Is := Is) (hΦ := hΦ) hi).mpr ⟨tree A f, htree_WF, ?_⟩
  rw [hstage_eq, unpackTup_packTup _ hm]
  exact hx_U

end Iter

end AccIter

export AccIter (closed_of_acc)

/-- **At a `Prop`-valued block the top tuple is closed**: every fibre
at `w = 0` is a subset of `{pt}`, so `MapsTuple` alone suffices. -/
theorem closedTuple_zero {k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hmaps : MapsTuple 0 k Is Φ) : ∃ L, IsClosedTuple 0 k Is Φ L := by
  have htop : InTupleSpace 0 k Is (fun m => famOf (fun _ => unitSet) (Is m) (hasGraph_const unitSet (Is m))) :=
    fun m _ => famOf_mem_famSpace fun _ _ => unitSet_mem_strictU_zero
  refine ⟨_, htop, fun m hm i hi x hx => ?_⟩
  change x ∈ˢ app (famOf (fun _ => unitSet) (Is m) (hasGraph_const unitSet (Is m))) i
  rw [app_famOf hi]
  have := famSpace_app (hmaps _ htop m hm) hi
  rw [strictU_zero] at this
  exact mem_univZero.mp this x hx

/-- **Accessibility, with a bound of the level at a `Type`-valued level**. -/
def AccW (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∃ A, (w ≠ 0 → A ∈ˢ (tg w : V)) ∧ AccTuple w k Is k Is Φ A

/-- **(W) from `AccW`**, at every level: `closed_of_acc` at `w ≠ 0`,
`closedTuple_zero` at `w = 0`. -/
theorem AccW.closed {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    {hΦ : DefTupleOp k Φ} (h : AccW w k Is Φ) (hmaps : MapsTuple w k Is Φ) :
    ∃ L, IsClosedTuple w k Is Φ L := by
  by_cases hw : w = 0
  · subst hw; exact closedTuple_zero hmaps
  · obtain ⟨A, hA, hacc⟩ := h
    exact closed_of_acc hw (hA hw) hΦ hmaps hacc

/-! ## Accessibility implies monotonicity -/

theorem AccTuple.monoTuple {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (h : AccTuple w k Is k Is Φ A) : MonoTuple w k Is Φ := by
  intro X Y hX hY hXY m hm i hi x hx
  obtain ⟨B, g, _, hg, hs⟩ := h X hX m hm i hi x hx
  exact hs Y hY fun a ha => occSpace_mono hXY _ (app_mem_of_mem_piSet hg ha)

/-- **Monotonicity from `AccW`**, at every level. -/
theorem AccW.mono {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} (h : AccW w k Is Φ) :
    MonoTuple w k Is Φ :=
  h.elim fun _ h => h.2.monoTuple

/-! ## Readings: accessibility of one fibre -/

/-- A READING `F` (a set depending on the tuple) is `A`-accessible. -/
def AccRead (w kI : Nat) (IsI : Nat → V) (F : (Nat → V) → V) (A : V) : Prop :=
  ∀ X, InTupleSpace w kI IsI X → ∀ x, x ∈ˢ F X →
    ∃ (B g : V), B ⊆ˢ A ∧
      g ∈ˢ piSet B (fun _ => occSpace kI IsI X) (hasSigmaPairs_const _ _) ∧
      ∀ X', InTupleSpace w kI IsI X' →
        (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kI IsI X') →
        x ∈ˢ F X'

section Readings

variable {w kI : Nat} {IsI : Nat → V}

theorem hasSigmaPairs_skolem (A U : V) :
    HasSigmaPairs (power A) (fun B => piSet B (fun _ => U) (hasSigmaPairs_const _ _)) :=
  hasSigmaPairs_of_defFun1 (DefFun.piSet_apply_curry (DefFun.proj 0) (DefFun.const U))

/-- First-order Skolemization of set-level supports via `piSet_choose`,
producing `DefFun 1` selectors `(Bf, gf)` over `S` from a `DefRel 3` support predicate `Q`. -/
theorem skolem_supp {S A U : V} {Q : V → V → V → Prop}
    (hQ : DefRel 3 fun v => Q (v 0) (v 1) (v 2))
    (h : ∀ a, a ∈ˢ S →
      ∃ B g, B ⊆ˢ A ∧ g ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _) ∧ Q a B g) :
    ∃ (Bf gf : V → V),
      (DefFun 1 fun v => Bf (v 0)) ∧
      (DefFun 1 fun v => gf (v 0)) ∧
      ∀ a, a ∈ˢ S →
        Bf a ⊆ˢ A ∧
        gf a ∈ˢ piSet (Bf a) (fun _ => U) (hasSigmaPairs_const _ _) ∧
        Q a (Bf a) (gf a) := by
  let P_sp := sigmaPairs (power A) (fun B => piSet B (fun _ => U) (hasSigmaPairs_const _ _))
    (hasSigmaPairs_skolem A U)
  have hRelSlice : DefRel 2 fun v => ∃ B g, v 0 = kpair B g ∧ Q (v 1) B g := by
    refine DefRel.exists_curry (DefRel.exists_curry (DefRel.and ?_ ?_))
    · exact DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
    · exact hQ.reIndex fun i => match i with | ⟨0, _⟩ => 3 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0
  have hSepSlice : ∀ a, HasSep P_sp (fun p => ∃ B g, p = kpair B g ∧ Q a B g) := fun a =>
    hasSep_of_defPred <|
      (hRelSlice.reIndex fun i => match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0).fixParam a
  let Slice : V → V := fun a =>
    sep P_sp (fun p => ∃ B g, p = kpair B g ∧ Q a B g) (hSepSlice a)
  have hSlice_def : DefFun 1 fun v => Slice (v 0) :=
    DefFun.sep_apply_curry (DefFun.const P_sp) hRelSlice
  have hSlice_sig : HasSigmaPairs S Slice := hasSigmaPairs_of_defFun1 hSlice_def
  have hSlice_ne : ∀ a, a ∈ˢ S → ∃ p, p ∈ˢ Slice a := fun a ha => by
    obtain ⟨B, g, hBA, hg, hQa⟩ := h a ha
    exact ⟨kpair B g, mem_sep.mpr ⟨mem_sigmaPairs.mpr ⟨B, mem_power.mpr hBA, g, hg, rfl⟩,
      B, g, rfl, hQa⟩⟩
  obtain ⟨c, hc_mem⟩ := piSet_choose hSlice_sig hSlice_ne
  refine ⟨fun a => kp1 (app c a), fun a => kp2 (app c a),
    DefFun.kp1_apply (DefFun.app_apply (DefFun.const c) (DefFun.proj 0)),
    DefFun.kp2_apply (DefFun.app_apply (DefFun.const c) (DefFun.proj 0)),
    fun a ha => ?_⟩
  have hc_mem' : app c a ∈ˢ Slice a := app_mem_of_mem_piSet hc_mem ha
  obtain ⟨hp_sp, B, g, hkp, hQa⟩ := mem_sep.mp hc_mem'
  obtain ⟨B', hB', g', hg', hkp'⟩ := mem_sigmaPairs.mp hp_sp
  rw [hkp] at hkp'
  obtain ⟨rfl, rfl⟩ := kpair_inj hkp'
  dsimp only
  simp only [hkp, kp1_kpair, kp2_kpair]
  exact ⟨mem_power.mp hB', hg', hQa⟩

/-- **Constant** readings (hole-free fields). -/
theorem accRead_const (C A : V) : AccRead w kI IsI (fun _ => C) A := fun _ _ _ hx =>
  ⟨empty, graph (fun _ => empty) empty (hasGraph_empty _), empty_subset _,
    graph_mem_piSet fun _ ha => absurd ha (not_mem_empty _),
    fun _ _ _ => hx⟩

/-- **A hole** read at a fixed index. -/
theorem accRead_hole {m : Nat} (hm : m < kI) {e A : V} (he : e ∈ˢ IsI m) (hA : (pt : V) ∈ˢ A) :
    AccRead w kI IsI (fun X => app (X m) e) A := fun _ _ x hx => by
  let g := graph (fun _ => occEnc m e x) unitSet (hasGraph_const _ _)
  refine ⟨unitSet, g, fun _ ha => (mem_unitSet_iff.mp ha) ▸ hA,
    graph_mem_piSet fun _ _ => occEnc_mem_occSpace.mpr ⟨hm, he, hx⟩, fun X' _ h' => ?_⟩
  have hg := h' pt pt_mem_unitSet
  dsimp only [g] at hg
  rw [app_graph pt_mem_unitSet, occEnc_mem_occSpace] at hg
  exact hg.2.2

theorem accRead_binUnion {A : V} {G H : (Nat → V) → V}
    (hG : AccRead w kI IsI G A) (hH : AccRead w kI IsI H A) :
    AccRead w kI IsI (fun X => binUnion (G X) (H X)) A := by
  intro X hX x hx
  rcases mem_binUnion.mp hx with h | h
  · obtain ⟨B, g, hB, hg, hs⟩ := hG X hX x h
    exact ⟨B, g, hB, hg, fun X' hX' h' => mem_binUnion.mpr (Or.inl (hs X' hX' h'))⟩
  · obtain ⟨B, g, hB, hg, hs⟩ := hH X hX x h
    exact ⟨B, g, hB, hg, fun X' hX' h' => mem_binUnion.mpr (Or.inr (hs X' hX' h'))⟩

/-- **Images** (constructor tags, injections). -/
theorem accRead_image {A : V} {G : (Nat → V) → V} (h : V → V)
    {hImg : ∀ X, HasImage h (G X)} (hG : AccRead w kI IsI G A) :
    AccRead w kI IsI (fun X => image h (G X) (hImg X)) A := by
  intro X hX x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  obtain ⟨B, g, hB, hg, hs⟩ := hG X hX y hy
  exact ⟨B, g, hB, hg, fun X' hX' h' => mem_image.mpr ⟨y, hs X' hX' h', rfl⟩⟩

/-- **A hole-free first component** (Σ over a constant set). -/
theorem accRead_sigma {C A : V} {G : V → (Nat → V) → V}
    {hS : ∀ X, HasSigmaPairs C fun c => G c X}
    (hG : ∀ c, c ∈ˢ C → AccRead w kI IsI (G c) A) :
    AccRead w kI IsI (fun X => sigmaPairs C (fun c => G c X) (hS X)) A := by
  intro X hX x hx
  obtain ⟨c, hc, y, hy, rfl⟩ := mem_sigmaPairs.mp hx
  obtain ⟨B, g, hB, hg, hs⟩ := hG c hc X hX y hy
  exact ⟨B, g, hB, hg, fun X' hX' h' => mem_sigmaPairs.mpr ⟨c, hc, y, hs X' hX' h', rfl⟩⟩

/-- **A Π-tower over a hole-free domain** (first-order definable fibres). -/
theorem accRead_pi {D A : V} {G : V → (Nat → V) → V}
    {hS : ∀ X, HasSigmaPairs D fun d => G d X}
    (hG_ext : ∀ d, d ∈ˢ D → ∀ X Y, (∀ m, m < kI → X m = Y m) → G d X = G d Y)
    (hG_def : DefFun (kI + 1) fun v => G (v 0) (padTuple (ftail v)))
    (hG : ∀ d, d ∈ˢ D → AccRead w kI IsI (G d) A) :
    AccRead w kI IsI (fun X => piSet D (fun d => G d X) (hS X))
      (sigmaPairs D (fun _ => A) (hasSigmaPairs_const _ _)) := by
  intro X hX f hf
  let Q : V → V → V → Prop := fun d B g =>
    ∀ xs : Fin kI → V,
      InTupleSpace w kI IsI (padTuple xs) →
      (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kI IsI (padTuple xs)) →
      app f d ∈ˢ G d (padTuple xs)
  have hQ_body : DefRel (kI + 3) fun v =>
      InTupleSpace w kI IsI (padTuple (ftake v)) →
      (∀ a, a ∈ˢ fdrop v 1 → app (fdrop v 2) a ∈ˢ occSpace kI IsI (padTuple (ftake v))) →
      app f (fdrop v 0) ∈ˢ G (fdrop v 0) (padTuple (ftake v)) := by
    refine DefRel.imp ?_ (DefRel.imp ?_ ?_)
    · refine DefRel.finForall_lt fun m hm => ?_
      exact DefRel.mem_apply
        ((DefFun.ftake_proj ⟨m, hm⟩).congr fun v => (padTuple_lt (ftake v) hm).symm)
        (DefFun.const (famSpace w (IsI m)))
    · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := kI) (p := 3) 1) ?_
      refine DefRel.mem_apply
        (DefFun.app_apply (DefFun.proj ⟨kI + 3, by omega⟩) (DefFun.proj 0))
        (DefFun.occSpace_apply kI (fun m _ => DefFun.const (IsI m))
          (fun m hm => ((DefFun.ftake_proj ⟨m, hm⟩).weaken.congr fun v =>
            (padTuple_lt (ftake (ftail v)) hm).symm)))
    · have hG' : DefFun (kI + 3) fun v => G (fdrop v 0) (padTuple (ftake v)) := by
        let re : Fin (kI + 1) → Fin (kI + 3)
          | ⟨0, _⟩ => ⟨kI, by omega⟩
          | ⟨i + 1, hi⟩ => ⟨i, by omega⟩
        exact (hG_def.reIndex re).congr fun v => by
          congr 1
      exact DefRel.mem_apply
        (DefFun.app_apply (DefFun.const f) (DefFun.fdrop_proj (k := kI) (p := 3) 0))
        hG'
  have hQ : DefRel 3 fun v => Q (v 0) (v 1) (v 2) :=
    (DefRel.forall_fin hQ_body).congr fun v => by
      dsimp only [Q]; simp only [ftake_fappend, fdrop_fappend]
  obtain ⟨Bf, gf, hBf_def, hgf_def, hsk⟩ := skolem_supp hQ fun d hd => by
    obtain ⟨B, g, hB, hg, hs⟩ := hG d hd X hX _ (app_mem_of_mem_piSet hf hd)
    refine ⟨B, g, hB, hg, fun xs hxs h' => ?_⟩
    exact hs (padTuple xs) hxs h'
  have hBf_sig : HasSigmaPairs D Bf := hasSigmaPairs_of_defFun1 hBf_def
  let B_tot := sigmaPairs D Bf hBf_sig
  have hg_def : DefFun 1 fun v => app (gf (kp1 (v 0))) (kp2 (v 0)) :=
    DefFun.app_apply (hgf_def.comp1 (DefFun.kp1_apply (DefFun.proj 0)))
      (DefFun.kp2_apply (DefFun.proj 0))
  let g_tot := graph (fun p => app (gf (kp1 p)) (kp2 p)) B_tot (hasGraph_of_defFun1 hg_def)
  refine ⟨B_tot, g_tot, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨d, hd, q, (hsk d hd).1 q hq, rfl⟩
  · refine graph_mem_piSet fun p hp => ?_
    obtain ⟨d, hd, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    rw [kp1_kpair, kp2_kpair]
    exact app_mem_of_mem_piSet (hsk d hd).2.1 hq
  · intro X' hX' h'
    rw [← eq_graph_app_of_mem_piSet hf]
    refine graph_mem_piSet fun d hd => ?_
    let xs : Fin kI → V := fun j => X' j.val
    have hxs_mem : InTupleSpace w kI IsI (padTuple xs) := fun m hm => by
      rw [padTuple_lt _ hm]; exact hX' m hm
    have hsub : ∀ q, q ∈ˢ Bf d → app (gf d) q ∈ˢ occSpace kI IsI (padTuple xs) := fun q hq => by
      have hp := h' (kpair d q) (mem_sigmaPairs.mpr ⟨d, hd, q, hq, rfl⟩)
      dsimp only [g_tot] at hp
      rw [app_graph (mem_sigmaPairs.mpr ⟨d, hd, q, hq, rfl⟩), kp1_kpair, kp2_kpair] at hp
      exact (occSpace_congr (fun _ _ => rfl) (fun m hm => (padTuple_lt xs hm).symm)) ▸ hp
    have hfin := (hsk d hd).2.2 xs hxs_mem hsub
    rwa [hG_ext d hd X' (padTuple xs) fun m hm => (padTuple_lt xs hm).symm]

open Classical in
/-- **A pair of two hole-reading components** (non-dependent product),
supports tagged by `∅`/`pt`. -/
theorem accRead_prod {A1 A2 : V} {G H : (Nat → V) → V}
    (hG : AccRead w kI IsI G A1) (hH : AccRead w kI IsI H A2) :
    AccRead w kI IsI (fun X => sigmaPairs (G X) (fun _ => H X) (hasSigmaPairs_const _ _))
      (sigmaPairs (upair empty pt) (fun t => if t = empty then A1 else A2)
        (hasSigmaPairs_of_defFun1
          (DefFun.ite (DefRel.eq_apply (DefFun.proj 0) DefFun.empty)
            (DefFun.const A1) (DefFun.const A2)))) := by
  intro X hX x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sigmaPairs.mp hx
  obtain ⟨B1, g1, hB1, hg1, hs1⟩ := hG X hX y hy
  obtain ⟨B2, g2, hB2, hg2, hs2⟩ := hH X hX z hz
  have hne : (pt : V) ≠ empty := pt_ne_empty
  have hB_sig : HasSigmaPairs (upair empty pt) fun t => if t = empty then B1 else B2 :=
    hasSigmaPairs_of_defFun1
      (DefFun.ite (DefRel.eq_apply (DefFun.proj 0) DefFun.empty)
        (DefFun.const B1) (DefFun.const B2))
  let B_tot := sigmaPairs (upair empty pt) (fun t => if t = empty then B1 else B2) hB_sig
  have hg_def : DefFun 1 fun v =>
      if kp1 (v 0) = empty then app g1 (kp2 (v 0)) else app g2 (kp2 (v 0)) :=
    DefFun.ite (DefRel.eq_apply (DefFun.kp1_apply (DefFun.proj 0)) DefFun.empty)
      (DefFun.app_apply (DefFun.const g1) (DefFun.kp2_apply (DefFun.proj 0)))
      (DefFun.app_apply (DefFun.const g2) (DefFun.kp2_apply (DefFun.proj 0)))
  let g_tot := graph (fun p => if kp1 p = empty then app g1 (kp2 p) else app g2 (kp2 p))
    B_tot (hasGraph_of_defFun1 hg_def)
  refine ⟨B_tot, g_tot, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨t, ht, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    refine mem_sigmaPairs.mpr ⟨t, ht, q, ?_, rfl⟩
    by_cases h : t = empty
    · simp only [h, ite_true] at hq ⊢; exact hB1 q hq
    · simp only [h, ite_false] at hq ⊢; exact hB2 q hq
  · refine graph_mem_piSet fun p hp => ?_
    obtain ⟨t, ht, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    rw [kp1_kpair, kp2_kpair]
    by_cases h : t = empty
    · simp only [h, ite_true] at hq ⊢; exact app_mem_of_mem_piSet hg1 hq
    · simp only [h, ite_false] at hq ⊢; exact app_mem_of_mem_piSet hg2 hq
  · intro X' hX' h'
    refine mem_sigmaPairs.mpr ⟨y, hs1 X' hX' fun q hq => ?_, z, hs2 X' hX' fun q hq => ?_, rfl⟩
    · have hp_mem : kpair empty q ∈ˢ B_tot :=
        mem_sigmaPairs.mpr ⟨empty, mem_upair_left _ _, q, by simp [hq], rfl⟩
      have hh := h' (kpair empty q) hp_mem
      dsimp only [g_tot] at hh
      rw [app_graph hp_mem, kp1_kpair, kp2_kpair] at hh
      simpa using hh
    · have hp_mem : kpair pt q ∈ˢ B_tot :=
        mem_sigmaPairs.mpr ⟨pt, mem_upair.mpr (Or.inr rfl), q, by simp [hne, hq], rfl⟩
      have hh := h' (kpair pt q) hp_mem
      dsimp only [g_tot] at hh
      rw [app_graph hp_mem, kp1_kpair, kp2_kpair] at hh
      simpa [hne] using hh

/-- **Composition**: a reading of a `DefFun`-definable accessible operator's
output is accessible in the operator's input (supports glued, `Σ A2, A1`). -/
theorem accRead_comp {kY : Nat} {IsY : Nat → V} {Ψ : (Nat → V) → Nat → V} {A1 A2 : V}
    {G : (Nat → V) → V}
    (hΨ_ext : ∀ X Y, (∀ m, m < kI → X m = Y m) → ∀ m, m < kY → Ψ X m = Ψ Y m)
    (hΨ_def : ∀ m, m < kY → DefFun kI fun xs => Ψ (padTuple xs) m)
    (hΨ : AccTuple w kI IsI kY IsY Ψ A1)
    (hmaps : ∀ X, InTupleSpace w kI IsI X → InTupleSpace w kY IsY (Ψ X))
    (hG : AccRead w kY IsY G A2) :
    AccRead w kI IsI (fun X => G (Ψ X)) (sigmaPairs A2 (fun _ => A1) (hasSigmaPairs_const _ _)) := by
  intro X hX x hx
  obtain ⟨B2, g2, hB2, hg2, hs2⟩ := hG (Ψ X) (hmaps X hX) x hx
  let Q : V → V → V → Prop := fun b B g =>
    ∀ xs : Fin kI → V,
      InTupleSpace w kI IsI (padTuple xs) →
      (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kI IsI (padTuple xs)) →
      app g2 b ∈ˢ occSpace kY IsY (Ψ (padTuple xs))
  have hQ_body : DefRel (kI + 3) fun v =>
      InTupleSpace w kI IsI (padTuple (ftake v)) →
      (∀ a, a ∈ˢ fdrop v 1 → app (fdrop v 2) a ∈ˢ occSpace kI IsI (padTuple (ftake v))) →
      app g2 (fdrop v 0) ∈ˢ occSpace kY IsY (Ψ (padTuple (ftake v))) := by
    refine DefRel.imp ?_ (DefRel.imp ?_ ?_)
    · refine DefRel.finForall_lt fun m hm => ?_
      exact DefRel.mem_apply
        ((DefFun.ftake_proj ⟨m, hm⟩).congr fun v => (padTuple_lt (ftake v) hm).symm)
        (DefFun.const (famSpace w (IsI m)))
    · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := kI) (p := 3) 1) ?_
      refine DefRel.mem_apply
        (DefFun.app_apply (DefFun.proj ⟨kI + 3, by omega⟩) (DefFun.proj 0))
        (DefFun.occSpace_apply kI (fun m _ => DefFun.const (IsI m))
          (fun m hm => ((DefFun.ftake_proj ⟨m, hm⟩).weaken.congr fun v =>
            (padTuple_lt (ftake (ftail v)) hm).symm)))
    · have hΨ' : ∀ m, m < kY → DefFun (kI + 3) fun v => Ψ (padTuple (ftake v)) m := fun m hm =>
        ((hΨ_def m hm).reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right kI 3)⟩).congr
          fun _ => rfl
      exact DefRel.mem_apply
        (DefFun.app_apply (DefFun.const g2) (DefFun.fdrop_proj (k := kI) (p := 3) 0))
        (DefFun.occSpace_apply kY (fun m _ => DefFun.const (IsY m)) hΨ')
  have hQ : DefRel 3 fun v => Q (v 0) (v 1) (v 2) :=
    (DefRel.forall_fin hQ_body).congr fun v => by
      dsimp only [Q]; simp only [ftake_fappend, fdrop_fappend]
  obtain ⟨Bf, gf, hBf_def, hgf_def, hsk⟩ := skolem_supp hQ fun b hb => by
    have hocc := app_mem_of_mem_piSet hg2 hb
    obtain ⟨m, hm, j, hj, y, hy, heq⟩ := mem_occSpace.mp hocc
    obtain ⟨B, g, hB, hg, hs⟩ := hΨ X hX m hm j hj y hy
    refine ⟨B, g, hB, hg, fun xs hxs h' => ?_⟩
    rw [heq, occEnc_mem_occSpace]
    exact ⟨hm, hj, hs (padTuple xs) hxs h'⟩
  have hBf_sig : HasSigmaPairs B2 Bf := hasSigmaPairs_of_defFun1 hBf_def
  let B_tot := sigmaPairs B2 Bf hBf_sig
  have hg_def : DefFun 1 fun v => app (gf (kp1 (v 0))) (kp2 (v 0)) :=
    DefFun.app_apply (hgf_def.comp1 (DefFun.kp1_apply (DefFun.proj 0)))
      (DefFun.kp2_apply (DefFun.proj 0))
  let g_tot := graph (fun p => app (gf (kp1 p)) (kp2 p)) B_tot (hasGraph_of_defFun1 hg_def)
  refine ⟨B_tot, g_tot, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨b, hB2 b hb, q, (hsk b hb).1 q hq, rfl⟩
  · refine graph_mem_piSet fun p hp => ?_
    obtain ⟨b, hb, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    rw [kp1_kpair, kp2_kpair]
    exact app_mem_of_mem_piSet (hsk b hb).2.1 hq
  · intro X' hX' h'
    refine hs2 (Ψ X') (hmaps X' hX') fun b hb => ?_
    let xs : Fin kI → V := fun j => X' j.val
    have hxs_mem : InTupleSpace w kI IsI (padTuple xs) := fun m hm => by
      rw [padTuple_lt _ hm]; exact hX' m hm
    have hsub : ∀ q, q ∈ˢ Bf b → app (gf b) q ∈ˢ occSpace kI IsI (padTuple xs) := fun q hq => by
      have hp := h' (kpair b q) (mem_sigmaPairs.mpr ⟨b, hb, q, hq, rfl⟩)
      dsimp only [g_tot] at hp
      rw [app_graph (mem_sigmaPairs.mpr ⟨b, hb, q, hq, rfl⟩), kp1_kpair, kp2_kpair] at hp
      exact (occSpace_congr (fun _ _ => rfl) (fun m hm => (padTuple_lt xs hm).symm)) ▸ hp
    have hfin := (hsk b hb).2.2 xs hxs_mem hsub
    rwa [occSpace_congr (fun _ _ => rfl) (hΨ_ext (padTuple xs) X' fun m hm => padTuple_lt xs hm)] at hfin

end Readings

/-! ## The least tuple in a parameter (the nested case) -/

/-- Concatenation of a `kX`-tuple and a tuple. -/
def catT (kX : Nat) (X Y : Nat → V) : Nat → V := fun i => if i < kX then X i else Y (i - kX)

section Param

variable {w kX kY : Nat} {IsX IsY : Nat → V}

theorem catT_mem {X Y : Nat → V} (hX : InTupleSpace w kX IsX X) (hY : InTupleSpace w kY IsY Y) :
    InTupleSpace w (kX + kY) (catT kX IsX IsY) (catT kX X Y) := by
  intro m hm
  unfold catT
  by_cases h : m < kX
  · simp only [h, ite_true]; exact hX m h
  · simp only [h, ite_false]; exact hY (m - kX) (by omega)

theorem occEnc_mem_occSpace_catT {X Y : Nat → V} {m : Nat} {i y : V} :
    occEnc m i y ∈ˢ occSpace (kX + kY) (catT kX IsX IsY) (catT kX X Y) ↔
      (m < kX ∧ occEnc m i y ∈ˢ occSpace kX IsX X) ∨
      (kX ≤ m ∧ occEnc (m - kX) i y ∈ˢ occSpace kY IsY Y) := by
  rw [occEnc_mem_occSpace, occEnc_mem_occSpace, occEnc_mem_occSpace]
  unfold catT
  by_cases h : m < kX
  · rw [ite_eq_left h, ite_eq_left h]
    constructor
    · rintro ⟨_, hi, hy⟩; exact Or.inl ⟨h, h, hi, hy⟩
    · rintro (⟨_, _, hi, hy⟩ | ⟨hle, _⟩)
      · exact ⟨by omega, hi, hy⟩
      · omega
  · rw [ite_eq_right h, ite_eq_right h]
    constructor
    · rintro ⟨hm, hi, hy⟩; exact Or.inr ⟨by omega, by omega, hi, hy⟩
    · rintro (⟨hlt, _⟩ | ⟨_, hsub, hi, hy⟩)
      · omega
      · exact ⟨by omega, hi, hy⟩

/-- Slice `DefTupleOp` for `fun Y => Θ (catT kX X Y)`. -/
theorem DefTupleOp.section {Θ : (Nat → V) → Nat → V}
    (hΘ : DefTupleOp (kX + kY) Θ) (X : Nat → V) :
    DefTupleOp kY (fun Y => Θ (catT kX X Y)) := by
  refine ⟨fun Y Y' hY m hm => hΘ.1 _ _ (fun j hj => ?_) m (by omega), fun m hm => ?_⟩
  · unfold catT
    by_cases hjx : j < kX
    · simp [hjx]
    · simp [hjx]; exact hY (j - kX) (by omega)
  · let Gs : Fin (kX + kY) → (Fin kY → V) → V := fun j ys =>
      if hj : j.val < kX then X j.val else ys ⟨j.val - kX, by omega⟩
    have hGs : ∀ j : Fin (kX + kY), DefFun kY (Gs j) := fun j => by
      dsimp only [Gs]
      by_cases hj : j.val < kX
      · simp only [hj, ↓reduceDIte]; exact DefFun.const (X j.val)
      · simp only [hj, ↓reduceDIte]; exact DefFun.proj ⟨j.val - kX, by omega⟩
    refine ((hΘ.2 m (by omega)).comp hGs).congr fun ys => ?_
    refine hΘ.1 _ _ (fun j hj => ?_) m (by omega)
    unfold catT
    by_cases hjx : j < kX
    · rw [ite_eq_left hjx, padTuple_lt _ hj]; dsimp only [Gs]; simp [hjx]
    · rw [ite_eq_right hjx, padTuple_lt _ hj, padTuple_lt _ (by omega)]; dsimp only [Gs]; simp [hjx]

variable (w kX kY IsY) in
/-- The least tuple of `Θ` at the parameter `X`: `Θ`'s section at `X`. -/
noncomputable def lfpP (Θ : (Nat → V) → Nat → V) (hΘ : DefTupleOp (kX + kY) Θ)
    (X : Nat → V) : Nat → V :=
  lfpTuple w kY IsY (fun Y => Θ (catT kX X Y)) (hΘ.section X)

theorem DefFun.lfpP_apply {Θ : (Nat → V) → Nat → V} (hΘ : DefTupleOp (kX + kY) Θ)
    {m : Nat} (hm : m < kY) :
    DefFun kX fun xs => lfpP w kX kY IsY Θ hΘ (padTuple xs) m := by
  unfold lfpP
  refine DefFun.lfpTuple_apply
    (Is := fun _ => IsY)
    (Φ := fun xs Y => Θ (catT kX (padTuple xs) Y))
    (fun j _ => DefFun.const (IsY j))
    (fun xs => hΘ.section (padTuple xs))
    (fun j hj => ?_)
    hm
  let Gs : Fin (kX + kY) → (Fin (kY + kX) → V) → V := fun c v =>
    if hc : c.val < kX then fdrop v ⟨c.val, hc⟩ else ftake v ⟨c.val - kX, by omega⟩
  have hGs : ∀ c : Fin (kX + kY), DefFun (kY + kX) (Gs c) := fun c => by
    dsimp only [Gs]
    by_cases hc : c.val < kX
    · simp only [hc, ↓reduceDIte]; exact DefFun.fdrop_proj ⟨c.val, hc⟩
    · simp only [hc, ↓reduceDIte]; exact DefFun.ftake_proj ⟨c.val - kX, by omega⟩
  refine ((hΘ.2 j (by omega)).comp hGs).congr fun v => ?_
  refine hΘ.1 _ _ (fun c hc => ?_) j (by omega)
  unfold catT
  by_cases hcx : c < kX
  · rw [ite_eq_left hcx, padTuple_lt _ hc, padTuple_lt _ hcx]; dsimp only [Gs]; simp [hcx]
  · rw [ite_eq_right hcx, padTuple_lt _ hc, padTuple_lt _ (by omega)]; dsimp only [Gs]; simp [hcx]

open Classical in
/-- Shift an occurrence encoded at `kX + c` (`c < kY`) down by `kX`. -/
noncomputable def shiftOcc (kX kY : Nat) (u : V) : V :=
  if h : ExistsUnique fun y => ∃ c, c < kY ∧ ∃ i' y', u = occEnc (kX + c) i' y' ∧ y = occEnc c i' y'
  then Classical.choose h else empty

theorem shiftOcc_eq {kX kY c : Nat} (hc : c < kY) (i' y' : V) :
    shiftOcc kX kY (occEnc (kX + c) i' y') = occEnc c i' y' := by
  unfold shiftOcc
  have hex : ExistsUnique fun y =>
      ∃ c', c' < kY ∧ ∃ i'' y'', occEnc (kX + c) i' y' = occEnc (kX + c') i'' y'' ∧
        y = occEnc c' i'' y'' := by
    refine ⟨occEnc c i' y', ⟨c, hc, i', y', rfl, rfl⟩, ?_⟩
    rintro y ⟨c', _, i'', y'', heq, rfl⟩
    obtain ⟨h1, rfl, rfl⟩ := occEnc_inj heq
    have hc_eq : c = c' := by omega
    rw [hc_eq]
  rw [dite_eq_left hex]
  exact hex.unique (Classical.choose_spec hex).1 ⟨c, hc, i', y', rfl, rfl⟩

theorem defFun_shiftOcc (kX kY : Nat) : DefFun (V := V) 1 fun v => shiftOcc kX kY (v 0) := by
  unfold shiftOcc
  refine DefFun.uniqueChoice_curry <|
    DefRel.finExists_lt fun c _ =>
      DefRel.exists_curry (DefRel.exists_curry (DefRel.and
        (DefRel.eq_apply (DefFun.proj 3) (DefFun.occEnc_apply (kX + c) (DefFun.proj 1) (DefFun.proj 0)))
        (DefRel.eq_apply (DefFun.proj 2) (DefFun.occEnc_apply c (DefFun.proj 1) (DefFun.proj 0)))))

/-- **The section at a parameter** inherits accessibility. -/
theorem AccTuple.section {kO : Nat} {IsO : Nat → V} {Θ : (Nat → V) → Nat → V} {A : V}
    (h : AccTuple w (kX + kY) (catT kX IsX IsY) kO IsO Θ A) {X : Nat → V} (hX : InTupleSpace w kX IsX X) :
    AccTuple w kY IsY kO IsO (fun Y => Θ (catT kX X Y)) A := by
  intro Y hY m hm i hi x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h _ (catT_mem hX hY) m hm i hi x hx
  have hSepB : HasSep B fun a => ∃ c, c < kY ∧ ∃ i' y', app g a = occEnc (kX + c) i' y' :=
    hasSep_of_defPred <|
      DefRel.finExists_lt fun c _ => DefRel.exists_curry (DefRel.exists_curry
        (DefRel.eq_apply (DefFun.app_apply (DefFun.const g) (DefFun.proj 2))
          (DefFun.occEnc_apply (kX + c) (DefFun.proj 1) (DefFun.proj 0))))
  let B' := sep B (fun a => ∃ c, c < kY ∧ ∃ i' y', app g a = occEnc (kX + c) i' y') hSepB
  have hg'_def : DefFun 1 fun v => shiftOcc kX kY (app g (v 0)) :=
    (defFun_shiftOcc (V := V) kX kY).comp1 (DefFun.app_apply (DefFun.const g) (DefFun.proj 0))
  let g' := graph (fun a => shiftOcc kX kY (app g a)) B' (hasGraph_of_defFun1 hg'_def)
  refine ⟨B', g', Subset.trans sep_subset hB, ?_, ?_⟩
  · refine graph_mem_piSet fun a ha => ?_
    obtain ⟨haB, c, hc, i', y', hga⟩ := mem_sep.mp ha
    have hocc := app_mem_of_mem_piSet hg haB
    rw [hga] at hocc
    rcases occEnc_mem_occSpace_catT.mp hocc with ⟨hlt, _⟩ | ⟨_, hy⟩
    · omega
    · rw [hga, shiftOcc_eq hc]
      rw [Nat.add_sub_cancel_left] at hy
      exact hy
  · intro Y' hY' h'
    refine hs _ (catT_mem hX hY') fun a ha => ?_
    have hocc := app_mem_of_mem_piSet hg ha
    obtain ⟨m', hm', i', hi', y', hy', hga⟩ := mem_occSpace.mp hocc
    rw [hga]
    rcases occEnc_mem_occSpace_catT.mp (hga ▸ hocc) with ⟨hlt, hx'⟩ | ⟨hle, hy'⟩
    · exact occEnc_mem_occSpace_catT.mpr (Or.inl ⟨hlt, hx'⟩)
    · have haB' : a ∈ˢ B' := mem_sep.mpr ⟨ha, m' - kX, by omega, i', y', by rw [hga, show kX + (m' - kX) = m' by omega]⟩
      have hsub := h' a haB'
      dsimp only [g'] at hsub
      rw [app_graph haB', hga] at hsub
      have hshift : shiftOcc kX kY (occEnc m' i' y') = occEnc (m' - kX) i' y' := by
        rw [show m' = kX + (m' - kX) by omega]
        rw [Nat.add_sub_cancel_left]
        exact shiftOcc_eq (kX := kX) (kY := kY) (c := m' - kX) (by omega) i' y'
      rw [hshift] at hsub
      exact occEnc_mem_occSpace_catT.mpr (Or.inr ⟨hle, hsub⟩)

/-- **THE NESTED CASE: the least tuple is accessible in its parameter.** -/
theorem lfpP_acc {Θ : (Nat → V) → Nat → V} {A : V}
    (hΘ : DefTupleOp (kX + kY) Θ) (hA : w ≠ 0 → A ∈ˢ (tg w : V))
    (hmaps : ∀ X Y, InTupleSpace w kX IsX X → InTupleSpace w kY IsY Y →
      InTupleSpace w kY IsY (Θ (catT kX X Y)))
    (hacc : AccTuple w (kX + kY) (catT kX IsX IsY) kY IsY Θ A) :
    AccTuple w kX IsX kY IsY (lfpP w kX kY IsY Θ hΘ) (accPaths A) := by
  have hcl : ∀ X, InTupleSpace w kX IsX X →
      ∃ L, IsClosedTuple w kY IsY (fun Y => Θ (catT kX X Y)) L :=
    fun X hX => AccW.closed (hΦ := hΘ.section X) ⟨A, hA, hacc.section hX⟩ fun Y hY => hmaps X Y hX hY
  have hmono : ∀ X, InTupleSpace w kX IsX X → MonoTuple w kY IsY (fun Y => Θ (catT kX X Y)) :=
    fun X hX => (hacc.section hX).monoTuple
  intro X hX
  let P : Nat → V → V → Prop := fun m i y =>
    ∃ (B g : V), B ⊆ˢ accPaths A ∧
      g ∈ˢ piSet B (fun _ => occSpace kX IsX X) (hasSigmaPairs_const _ _) ∧
      ∀ xs : Fin kX → V, InTupleSpace w kX IsX (padTuple xs) →
        (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kX IsX (padTuple xs)) →
        y ∈ˢ app (lfpP w kX kY IsY Θ hΘ (padTuple xs) m) i
  have hPdef : ∀ m, m < kY → DefRel 2 fun v => P m (v 0) (v 1) := fun m hm => by
    dsimp only [P]
    refine DefRel.exists_curry (DefRel.exists_curry (DefRel.and ?_ (DefRel.and ?_ ?_)))
    · exact DefRel.subset_apply (DefFun.proj 1) (DefFun.const (accPaths A))
    · exact DefRel.mem_apply (DefFun.proj 0)
        (DefFun.piSet_apply_curry (DefFun.proj 1) (DefFun.const (occSpace kX IsX X)))
    · have hP_body : DefRel (kX + 4) fun v =>
          InTupleSpace w kX IsX (padTuple (ftake v)) →
          (∀ a, a ∈ˢ fdrop v 1 → app (fdrop v 0) a ∈ˢ occSpace kX IsX (padTuple (ftake v))) →
          fdrop v 3 ∈ˢ app (lfpP w kX kY IsY Θ hΘ (padTuple (ftake v)) m) (fdrop v 2) := by
        refine DefRel.imp ?_ (DefRel.imp ?_ ?_)
        · refine DefRel.finForall_lt fun j hj => DefRel.mem_apply
            ((DefFun.ftake_proj ⟨j, hj⟩).congr fun v => (padTuple_lt (ftake v) hj).symm)
            (DefFun.const (famSpace w (IsX j)))
        · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := kX) (p := 4) 1) ?_
          refine DefRel.mem_apply
            (DefFun.app_apply (DefFun.fdrop_proj (k := kX) (p := 4) 0).weaken (DefFun.proj 0))
            (DefFun.occSpace_apply kX (fun j _ => DefFun.const (IsX j))
              (fun j hj => (DefFun.ftake_proj (k := kX) (p := 4) ⟨j, hj⟩).weaken.congr fun v =>
                (padTuple_lt (ftake (ftail v)) hj).symm))
        · have hlfp' : DefFun (kX + 4) fun v => lfpP w kX kY IsY Θ hΘ (padTuple (ftake v)) m :=
            ((DefFun.lfpP_apply (w := w) (IsY := IsY) hΘ hm).reIndex fun j =>
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right kX 4)⟩).congr fun _ => rfl
          exact DefRel.mem_apply
            (DefFun.fdrop_proj (k := kX) (p := 4) 3)
            (DefFun.app_apply hlfp' (DefFun.fdrop_proj (k := kX) (p := 4) 2))
      exact (DefRel.forall_fin hP_body).congr fun env => by
        simp only [ftake_fappend, fdrop_fappend]; exact Iff.rfl
  have hind := lfpTuple_induction_of_def (hΦ := hΘ.section X)
    (hcl X hX) (hmono X hX) (fun Y hY => hmaps X Y hX hY) P hPdef
    (by
      intro m hm i hi y hy
      have hSepP := hasSep_sepTuple_of_def (w := w) (Is := IsY) (hΘ.section X) hPdef
      have hGrP := hasGraph_sepTuple_of_def (w := w) (Is := IsY) (hΘ.section X) hPdef
      let S := sepTuple w kY IsY (fun Y => Θ (catT kX X Y)) (hΘ.section X) P hSepP hGrP
      have hS := sepTuple_mem w kY IsY (fun Y => Θ (catT kX X Y)) (hΘ.section X) P hSepP hGrP
      obtain ⟨B0, g0, hB0, hg0, hs0⟩ := hacc _ (catT_mem hX hS) m hm i hi y hy
      let Q : V → V → V → Prop := fun a B g =>
        (∀ xs : Fin kX → V, InTupleSpace w kX IsX (padTuple xs) →
          (∀ q, q ∈ˢ B → app g q ∈ˢ occSpace kX IsX (padTuple xs)) →
          app g0 a ∈ˢ occSpace (kX + kY) (catT kX IsX IsY)
            (catT kX (padTuple xs) (lfpP w kX kY IsY Θ hΘ (padTuple xs))))
      have hQ_body : DefRel (kX + 3) fun v =>
          InTupleSpace w kX IsX (padTuple (ftake v)) →
          (∀ q, q ∈ˢ fdrop v 1 → app (fdrop v 2) q ∈ˢ occSpace kX IsX (padTuple (ftake v))) →
          app g0 (fdrop v 0) ∈ˢ occSpace (kX + kY) (catT kX IsX IsY)
            (catT kX (padTuple (ftake v)) (lfpP w kX kY IsY Θ hΘ (padTuple (ftake v)))) := by
        refine DefRel.imp ?_ (DefRel.imp ?_ ?_)
        · refine DefRel.finForall_lt fun j hj => DefRel.mem_apply
            ((DefFun.ftake_proj ⟨j, hj⟩).congr fun v => (padTuple_lt (ftake v) hj).symm)
            (DefFun.const (famSpace w (IsX j)))
        · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := kX) (p := 3) 1) ?_
          refine DefRel.mem_apply
            (DefFun.app_apply (DefFun.fdrop_proj (k := kX) (p := 3) 2).weaken (DefFun.proj 0))
            (DefFun.occSpace_apply kX (fun j _ => DefFun.const (IsX j))
              (fun j hj => (DefFun.ftake_proj (k := kX) (p := 3) ⟨j, hj⟩).weaken.congr fun v =>
                (padTuple_lt (ftake (ftail v)) hj).symm))
        · have hcat : ∀ j, j < kX + kY → DefFun (kX + 3) fun v =>
              catT kX (padTuple (ftake v)) (lfpP w kX kY IsY Θ hΘ (padTuple (ftake v))) j := fun j hj => by
            unfold catT
            by_cases hjx : j < kX
            · simp only [hjx, ↓reduceIte]
              exact (DefFun.ftake_proj ⟨j, hjx⟩).congr fun v => (padTuple_lt (ftake v) hjx).symm
            · simp only [hjx, ↓reduceIte]
              exact ((DefFun.lfpP_apply (w := w) (IsY := IsY) hΘ (by omega)).reIndex fun c =>
                ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right kX 3)⟩).congr fun _ => rfl
          exact DefRel.mem_apply
            (DefFun.app_apply (DefFun.const g0) (DefFun.fdrop_proj (k := kX) (p := 3) 0))
            (DefFun.occSpace_apply (kX + kY) (fun j _ => DefFun.const (catT kX IsX IsY j)) hcat)
      have hQ : DefRel 3 fun v => Q (v 0) (v 1) (v 2) :=
        (DefRel.forall_fin hQ_body).congr fun v => by
          dsimp only [Q]; simp only [ftake_fappend, fdrop_fappend]
      obtain ⟨Bf, gf, hBf_def, hgf_def, hsk⟩ := skolem_supp (S := B0) (A := accPaths A)
        (U := occSpace kX IsX X) hQ fun a ha => by
          have hocc := app_mem_of_mem_piSet hg0 ha
          obtain ⟨m', hm', i', hi', y', hy', hga⟩ := mem_occSpace.mp hocc
          rcases occEnc_mem_occSpace_catT.mp (hga ▸ hocc) with ⟨hlt, hx_occ⟩ | ⟨hle, hy_occ⟩
          · refine ⟨unitSet, graph (fun _ => app g0 a) unitSet (hasGraph_const _ _),
              fun q hq => (mem_unitSet_iff.mp hq) ▸ pt_mem_accPaths A,
              graph_mem_piSet (fun _ _ => by rw [hga]; exact hx_occ), fun xs hxs h' => ?_⟩
            have h1 := h' pt pt_mem_unitSet
            rw [app_graph pt_mem_unitSet] at h1
            rw [hga] at h1 ⊢
            exact occEnc_mem_occSpace_catT.mpr (Or.inl ⟨hlt, h1⟩)
          · obtain ⟨_, hi'', hy''⟩ := occEnc_mem_occSpace.mp hy_occ
            obtain ⟨B, g, hB, hg, hs⟩ := (mem_app_sepTuple_imp hi'' hy'').2
            refine ⟨B, g, hB, hg, fun xs hxs h' => ?_⟩
            rw [hga]
            exact occEnc_mem_occSpace_catT.mpr
              (Or.inr ⟨hle, occEnc_mem_occSpace.mpr ⟨by omega, hi'', hs xs hxs h'⟩⟩)
      have hBf_sig : HasSigmaPairs B0 Bf := hasSigmaPairs_of_defFun1 hBf_def
      let B_tot := sigmaPairs B0 Bf hBf_sig
      have hg_def : DefFun 1 fun v => app (gf (kp1 (v 0))) (kp2 (v 0)) :=
        DefFun.app_apply (hgf_def.comp1 (DefFun.kp1_apply (DefFun.proj 0)))
          (DefFun.kp2_apply (DefFun.proj 0))
      let g_tot := graph (fun p => app (gf (kp1 p)) (kp2 p)) B_tot (hasGraph_of_defFun1 hg_def)
      refine ⟨B_tot, g_tot, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨a, ha, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
        exact kpair_mem_accPaths (hB0 a ha) ((hsk a ha).1 q hq)
      · refine graph_mem_piSet fun p hp => ?_
        obtain ⟨a, ha, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
        rw [kp1_kpair, kp2_kpair]
        exact app_mem_of_mem_piSet (hsk a ha).2.1 hq
      · intro xs hxs h'
        have hL' := lfpTuple_mem w kY IsY (fun Y => Θ (catT kX (padTuple xs) Y))
          (hΘ.section (padTuple xs))
        refine lfpTuple_closed (hcl _ hxs) (hmono _ hxs) (fun Y hY => hmaps _ Y hxs hY)
          m hm i hi y ?_
        refine hs0 _ (catT_mem hxs hL') fun a ha => ?_
        refine (hsk a ha).2.2 xs hxs fun q hq => ?_
        have hp := h' (kpair a q) (mem_sigmaPairs.mpr ⟨a, ha, q, hq, rfl⟩)
        dsimp only [g_tot] at hp
        rw [app_graph (mem_sigmaPairs.mpr ⟨a, ha, q, hq, rfl⟩), kp1_kpair, kp2_kpair] at hp
        exact hp)
  intro m hm i hi y hy
  obtain ⟨B, g, hB, hg, hs⟩ := hind m hm i hi y hy
  refine ⟨B, g, hB, hg, fun X' hX' h' => ?_⟩
  let xs : Fin kX → V := fun j => X' j.val
  have hxs : InTupleSpace w kX IsX (padTuple xs) := fun j hj => by
    rw [padTuple_lt _ hj]; exact hX' j hj
  have hsub : ∀ a, a ∈ˢ B → app g a ∈ˢ occSpace kX IsX (padTuple xs) := fun a ha => by
    exact (occSpace_congr (fun _ _ => rfl) (fun j hj => (padTuple_lt xs hj).symm)) ▸ h' a ha
  have hfin := hs xs hxs hsub
  have hcong : lfpP w kX kY IsY Θ hΘ (padTuple xs) m = lfpP w kX kY IsY Θ hΘ X' m := by
    unfold lfpP
    exact lfpTuple_congr (fun _ _ => rfl)
      (fun Y _ j hj => hΘ.1 _ _ (fun c hc => by
        unfold catT; by_cases hcx : c < kX
        · rw [ite_eq_left hcx, ite_eq_left hcx, padTuple_lt xs hcx]
        · rw [ite_eq_right hcx, ite_eq_right hcx]) j (by omega)) hm
  rwa [← hcong]

end Param

/-! ## The least tuple in a definable finite-tuple parameter, on a group -/

section ParamGroup

/-- Set-encoded support item of a parameterised operator: a parameter item
`kpair empty o`, or an occurrence `kpair pt u` (`u ∈ˢ occSpace kY IsY Y` on `G`). -/
def ItemIn (kY : Nat) (G : Nat → Prop) (HasP : V → Prop) (IsY Y : Nat → V) (item : V) : Prop :=
  (∃ o, item = kpair empty o ∧ HasP o) ∨
  (∃ m, m < kY ∧ G m ∧ ∃ i y, i ∈ˢ IsY m ∧ y ∈ˢ app (Y m) i ∧ item = kpair pt (occEnc m i y))

/-- Joint accessibility of a parameterised operator on the group `G`,
using set-level support graphs over `Fin d → V` parameters. -/
def AccJointG {d : Nat} (w kY : Nat) (IsY : (Fin d → V) → Nat → V)
    (Sp : (Fin d → V) → Prop) (Rp : (Fin d → V) → (Fin d → V) → Prop)
    (HasP : (Fin d → V) → V → Prop) (G : Nat → Prop)
    (Θ : (Fin d → V) → (Nat → V) → Nat → V) (A O_sp : (Fin d → V) → V) : Prop :=
  ∀ p Y, Sp p → InTupleSpace w kY (IsY p) Y → ∀ m, m < kY → G m → ∀ i, i ∈ˢ IsY p m →
    ∀ x, x ∈ˢ app (Θ p Y m) i →
      ∃ (B g : V), B ⊆ˢ A p ∧
        g ∈ˢ piSet B (fun _ => binUnion (image (kpair empty) (O_sp p) (AccIter.hasImage_kpair_const empty _))
          (image (kpair pt) (occSpace kY (IsY p) Y) (AccIter.hasImage_kpair_const pt _)))
          (hasSigmaPairs_const _ _) ∧
        (∀ b, b ∈ˢ B → ItemIn kY G (HasP p) (IsY p) Y (app g b)) ∧
        ∀ p' Y', Rp p p' → Sp p' → InTupleSpace w kY (IsY p') Y' →
          (∀ b, b ∈ˢ B → ItemIn kY G (HasP p') (IsY p') Y' (app g b)) →
          x ∈ˢ app (Θ p' Y' m) i

private theorem defRel_hasP_fix {d : Nat} {HasP : (Fin d → V) → V → Prop}
    (hHasP : DefRel (d + 1) fun v => HasP (ftail v) (v 0)) (p : Fin d → V) :
    DefPred fun o => HasP p o := by
  let Gs : Fin (d + 1) → (Fin 1 → V) → V := fun j v =>
    if hj : j.val = 0 then v 0 else p ⟨j.val - 1, by omega⟩
  have hGs : ∀ j : Fin (d + 1), DefFun 1 (Gs j) := fun j => by
    dsimp only [Gs]; split
    · exact DefFun.proj 0
    · exact DefFun.const _
  refine (hHasP.comp hGs).congr fun v => ?_
  have h0 : Gs 0 v = v 0 := rfl
  have htail : ftail (fun j => Gs j v) = p := by
    funext ⟨j, hj⟩
    change Gs ⟨j + 1, _⟩ v = p ⟨j, hj⟩
    dsimp only [Gs]
    simp
  rw [htail]; exact Iff.rfl

private theorem defRel_hasP_param {d n : Nat} {HasP : (Fin d → V) → V → Prop}
    (hHasP : DefRel (d + 1) fun v => HasP (ftail v) (v 0))
    {P_fn : Fin d → (Fin n → V) → V} (hP_fn : ∀ i : Fin d, DefFun n (P_fn i))
    {O_fn : (Fin n → V) → V} (hO_fn : DefFun n O_fn) :
    DefRel n fun env => HasP (fun i => P_fn i env) (O_fn env) := by
  let Gs : Fin (d + 1) → (Fin n → V) → V := fun j env =>
    if hj : j.val = 0 then O_fn env else P_fn ⟨j.val - 1, by omega⟩ env
  have hGs : ∀ j : Fin (d + 1), DefFun n (Gs j) := fun j => by
    dsimp only [Gs]
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte]; exact hO_fn
    · simp only [hj, ↓reduceDIte]; exact hP_fn ⟨j.val - 1, by omega⟩
  refine (hHasP.comp hGs).congr fun env => ?_
  have h0 : Gs 0 env = O_fn env := rfl
  have htail : ftail (fun j => Gs j env) = fun i => P_fn i env := by
    funext ⟨j, hj⟩
    change Gs ⟨j + 1, _⟩ env = P_fn ⟨j, hj⟩ env
    dsimp only [Gs]
    simp
  rw [htail]; exact Iff.rfl

private theorem defRel_itemIn_param {d n kY : Nat} {G : Nat → Prop}
    {HasP : (Fin d → V) → V → Prop} {IsY : (Fin d → V) → Nat → V}
    {Y : (Fin d → V) → Nat → V}
    (hHasP : DefRel (d + 1) fun v => HasP (ftail v) (v 0))
    {P_fn : Fin d → (Fin n → V) → V} (hP_fn : ∀ i : Fin d, DefFun n (P_fn i))
    (hIsY : ∀ m, m < kY → DefFun n fun env => IsY (fun i => P_fn i env) m)
    (hY : ∀ m, m < kY → DefFun n fun env => Y (fun i => P_fn i env) m)
    {item_fn : (Fin n → V) → V} (hitem : DefFun n item_fn) :
    DefRel n fun env =>
      ItemIn kY G (HasP fun i => P_fn i env) (IsY fun i => P_fn i env)
        (Y fun i => P_fn i env) (item_fn env) := by
  unfold ItemIn
  refine DefRel.or ?_ ?_
  · refine DefRel.exists_curry (DefRel.and ?_ ?_)
    · exact DefRel.eq_apply hitem.weaken (DefFun.kpair_apply DefFun.empty (DefFun.proj 0))
    · exact defRel_hasP_param hHasP (fun i => (hP_fn i).weaken) (DefFun.proj 0)
  · refine DefRel.finExists_lt fun m hm => ?_
    by_cases hGm : G m
    · have hsub : DefRel n fun env =>
          ∃ i y, i ∈ˢ IsY (fun idx => P_fn idx env) m ∧
            y ∈ˢ app (Y (fun idx => P_fn idx env) m) i ∧
            item_fn env = kpair pt (occEnc m i y) :=
        DefRel.exists_curry (DefRel.exists_curry (DefRel.and
          (DefRel.mem_apply (DefFun.proj 1) (hIsY m hm).weaken.weaken)
          (DefRel.and
            (DefRel.mem_apply (DefFun.proj 0)
              (DefFun.app_apply (hY m hm).weaken.weaken (DefFun.proj 1)))
            (DefRel.eq_apply hitem.weaken.weaken
              (DefFun.kpair_apply DefFun.pt (DefFun.occEnc_apply m (DefFun.proj 1) (DefFun.proj 0)))))))
      exact hsub.congr fun _ =>
        ⟨fun ⟨i, y, hi, hy, hitem'⟩ => ⟨hGm, i, y, hi, hy, hitem'⟩,
         fun ⟨_, i, y, hi, hy, hitem'⟩ => ⟨i, y, hi, hy, hitem'⟩⟩
    · exact DefRel.false.congr fun _ => ⟨False.elim, fun ⟨hG, _⟩ => absurd hG hGm⟩

/-- **The container case at a frame's group** (`Fin d → V` parameter, first-order). -/
theorem lfpP_acc_group {d w kY : Nat} {IsY : (Fin d → V) → Nat → V}
    {Sp : (Fin d → V) → Prop} {Rp : (Fin d → V) → (Fin d → V) → Prop}
    {HasP : (Fin d → V) → V → Prop} {G : Nat → Prop}
    {Θ : (Fin d → V) → (Nat → V) → Nat → V} {A O_sp : (Fin d → V) → V}
    (hSp : DefRel d Sp)
    (hRp : DefRel (d + d) fun v => Rp (ftake v) (fdrop v))
    (hHasP : DefRel (d + 1) fun v => HasP (ftail v) (v 0))
    (hIsY_def : ∀ m, m < kY → DefFun d fun p => IsY p m)
    (hΘ : ∀ p, DefTupleOp kY (Θ p))
    (hΘ_def : ∀ m, m < kY → DefFun (kY + d) fun v => Θ (fdrop v) (padTuple (ftake v)) m)
    (hIs : ∀ p p', Rp p p' → ∀ m, G m → IsY p m = IsY p' m)
    (hcl : ∀ p, Sp p → ∃ L, IsClosedTuple w kY (IsY p) (Θ p) L)
    (hmaps : ∀ p, Sp p → MapsTuple w kY (IsY p) (Θ p))
    (hsacc : ∀ p, Sp p → ∃ A', AccTuple w kY (IsY p) kY (IsY p) (Θ p) A')
    (hacc : AccJointG w kY IsY Sp Rp HasP G Θ A O_sp) :
    ∀ p, Sp p → ∀ m, m < kY → G m → ∀ i, i ∈ˢ IsY p m →
      ∀ x, x ∈ˢ app (lfpTuple w kY (IsY p) (Θ p) (hΘ p) m) i →
        ∃ (B g : V), B ⊆ˢ accPaths (A p) ∧
          g ∈ˢ piSet B (fun _ => O_sp p) (hasSigmaPairs_const _ _) ∧
          (∀ b, b ∈ˢ B → HasP p (app g b)) ∧
          ∀ p', Rp p p' → Sp p' → (∀ b, b ∈ˢ B → HasP p' (app g b)) →
            x ∈ˢ app (lfpTuple w kY (IsY p') (Θ p') (hΘ p') m) i := by
  have hmono : ∀ p, Sp p → MonoTuple w kY (IsY p) (Θ p) := fun p hp =>
    (hsacc p hp).elim fun _ h => h.monoTuple
  intro p hp
  let Q : Nat → V → V → Prop := fun m i y => G m →
    ∃ (B g : V), B ⊆ˢ accPaths (A p) ∧
      g ∈ˢ piSet B (fun _ => O_sp p) (hasSigmaPairs_const _ _) ∧
      (∀ b, b ∈ˢ B → HasP p (app g b)) ∧
      ∀ p' : Fin d → V, Rp p p' → Sp p' → (∀ b, b ∈ˢ B → HasP p' (app g b)) →
        y ∈ˢ app (lfpTuple w kY (IsY p') (Θ p') (hΘ p') m) i
  have hHasP_p : DefPred fun o => HasP p o := defRel_hasP_fix hHasP p
  have hRp_fix : ∀ n, DefRel (d + n) fun v => Rp p (ftake v) := fun n => by
    let Gs : Fin (d + d) → (Fin (d + n) → V) → V := fun j v =>
      if hj : j.val < d then p ⟨j.val, hj⟩ else v ⟨j.val - d, by omega⟩
    have hGs : ∀ j : Fin (d + d), DefFun (d + n) (Gs j) := fun j => by
      dsimp only [Gs]; split
      · exact DefFun.const _
      · exact DefFun.proj ⟨_, by omega⟩
    refine (hRp.comp hGs).congr fun v => ?_
    have ht : ftake (fun j => Gs j v) = p := by
      funext ⟨j, hj⟩; dsimp only [ftake, Gs]; simp [hj]
    have hd : fdrop (fun j => Gs j v) = ftake v := by
      funext ⟨j, hj⟩
      dsimp only [fdrop, ftake, Gs]
      have hge : ¬ (d + j < d) := by omega
      simp [hge]
    rw [ht, hd]
  have hSp_take : ∀ n, DefRel (d + n) fun v => Sp (ftake v) := fun n =>
    (hSp.reIndex fun j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right d n)⟩).congr fun _ => Iff.rfl
  have hlfp_take : ∀ {n m : Nat} (hm : m < kY),
      DefFun (d + n) fun v => lfpTuple w kY (IsY (ftake v)) (Θ (ftake v)) (hΘ (ftake v)) m := by
    intro n m hm
    exact ((DefFun.lfpTuple_apply hIsY_def hΘ hΘ_def hm).reIndex fun j =>
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right d n)⟩).congr fun _ => rfl
  have hQdef : ∀ m, m < kY → DefRel 2 fun v => Q m (v 0) (v 1) := fun m hm => by
    dsimp only [Q]
    by_cases hGm : G m
    · refine (DefRel.exists_curry (DefRel.exists_curry
        (DefRel.and ?_ (DefRel.and ?_ (DefRel.and ?_ ?_))))).congr fun v =>
          ⟨fun h _ => h, fun h => h hGm⟩
      · exact DefRel.subset_apply (DefFun.proj 1) (DefFun.const (accPaths (A p)))
      · exact DefRel.mem_apply (DefFun.proj 0)
          (DefFun.piSet_apply_curry (DefFun.proj 1) (DefFun.const (O_sp p)))
      · exact DefRel.bForall_curry (DefFun.proj 1)
          (hHasP_p.comp fun _ => DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0))
      · have hQ_body : DefRel (d + 4) fun v =>
            Rp p (ftake v) → Sp (ftake v) →
            (∀ b, b ∈ˢ fdrop v 1 → HasP (ftake v) (app (fdrop v 0) b)) →
            fdrop v 3 ∈ˢ app (lfpTuple w kY (IsY (ftake v)) (Θ (ftake v)) (hΘ (ftake v)) m) (fdrop v 2) := by
          refine DefRel.imp (hRp_fix 4) (DefRel.imp (hSp_take 4) (DefRel.imp ?_ ?_))
          · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := d) (p := 4) 1) ?_
            exact defRel_hasP_param hHasP
              (fun idx => (DefFun.ftake_proj (k := d) (p := 4) idx).weaken)
              (DefFun.app_apply (DefFun.fdrop_proj (k := d) (p := 4) 0).weaken (DefFun.proj 0))
          · exact DefRel.mem_apply
              (DefFun.fdrop_proj (k := d) (p := 4) 3)
              (DefFun.app_apply (hlfp_take (n := 4) hm) (DefFun.fdrop_proj (k := d) (p := 4) 2))
        refine (DefRel.forall_fin hQ_body).congr fun env => by
          simp only [fdrop_fappend]
          constructor <;> intro h xs
          · have h1 := h xs
            rwa [congrArg (fun fn : Fin d → V => Rp p fn → Sp fn →
              (∀ b, b ∈ˢ env 1 → HasP fn (app (env 0) b)) →
              env 3 ∈ˢ app (lfpTuple w kY (IsY fn) (Θ fn) (hΘ fn) m) (env 2))
              (ftake_fappend xs env)] at h1
          · have h1 := h xs
            rwa [congrArg (fun fn : Fin d → V => Rp p fn → Sp fn →
              (∀ b, b ∈ˢ env 1 → HasP fn (app (env 0) b)) →
              env 3 ∈ˢ app (lfpTuple w kY (IsY fn) (Θ fn) (hΘ fn) m) (env 2))
              (ftake_fappend xs env)]
    · exact DefRel.true.congr fun _ => ⟨fun _ h => absurd h hGm, fun _ => trivial⟩
  have hind := lfpTuple_induction_of_def (hΦ := hΘ p)
    (hcl p hp) (hmono p hp) (hmaps p hp) Q hQdef
    (by
      intro m hm i hi y hy hGm
      have hSepQ := hasSep_sepTuple_of_def (w := w) (Is := IsY p) (hΘ p) hQdef
      have hGrQ := hasGraph_sepTuple_of_def (w := w) (Is := IsY p) (hΘ p) hQdef
      let S := sepTuple w kY (IsY p) (Θ p) (hΘ p) Q hSepQ hGrQ
      have hS := sepTuple_mem w kY (IsY p) (Θ p) (hΘ p) Q hSepQ hGrQ
      obtain ⟨B0, g0, hB0, hg0, hitem0, hs0⟩ := hacc p _ hp hS m hm hGm i hi y hy
      let Qs : V → V → V → Prop := fun a B g =>
        (∀ b, b ∈ˢ B → HasP p (app g b)) ∧
        ∀ p' : Fin d → V, Rp p p' → Sp p' → (∀ q, q ∈ˢ B → HasP p' (app g q)) →
          ItemIn kY G (HasP p') (IsY p') (lfpTuple w kY (IsY p') (Θ p') (hΘ p')) (app g0 a)
      have hQs_body : DefRel (d + 3) fun v =>
          Rp p (ftake v) → Sp (ftake v) → (∀ q, q ∈ˢ fdrop v 1 → HasP (ftake v) (app (fdrop v 2) q)) →
          ItemIn kY G (HasP (ftake v)) (IsY (ftake v))
            (lfpTuple w kY (IsY (ftake v)) (Θ (ftake v)) (hΘ (ftake v))) (app g0 (fdrop v 0)) := by
        refine DefRel.imp (hRp_fix 3) (DefRel.imp (hSp_take 3) (DefRel.imp ?_ ?_))
        · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := d) (p := 3) 1) ?_
          exact defRel_hasP_param hHasP
            (fun idx => (DefFun.ftake_proj (k := d) (p := 3) idx).weaken)
            (DefFun.app_apply (DefFun.fdrop_proj (k := d) (p := 3) 2).weaken (DefFun.proj 0))
        · exact defRel_itemIn_param (Y := fun p => lfpTuple w kY (IsY p) (Θ p) (hΘ p))
            hHasP (fun idx => DefFun.ftake_proj idx)
            (fun m hm => ((hIsY_def m hm).reIndex fun j =>
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right d 3)⟩).congr fun _ => rfl)
            (fun m hm => (hlfp_take (n := 3) hm).congr fun _ => rfl)
            (DefFun.app_apply (DefFun.const g0) (DefFun.fdrop_proj (k := d) (p := 3) 0))
      have hQs : DefRel 3 fun v => Qs (v 0) (v 1) (v 2) := by
        refine DefRel.and ?_ ((DefRel.forall_fin hQs_body).congr fun v => ?_)
        · exact DefRel.bForall_curry (DefFun.proj 1)
            (hHasP_p.comp fun _ => DefFun.app_apply (DefFun.proj 3) (DefFun.proj 0))
        · simp only [fdrop_fappend]
          constructor <;> intro h p'
          · have h1 := h p'
            rwa [congrArg (fun fn : Fin d → V => Rp p fn → Sp fn →
              (∀ q, q ∈ˢ v 1 → HasP fn (app (v 2) q)) →
              ItemIn kY G (HasP fn) (IsY fn) (lfpTuple w kY (IsY fn) (Θ fn) (hΘ fn)) (app g0 (v 0)))
              (ftake_fappend p' v)] at h1
          · have h1 := h p'
            rwa [congrArg (fun fn : Fin d → V => Rp p fn → Sp fn →
              (∀ q, q ∈ˢ v 1 → HasP fn (app (v 2) q)) →
              ItemIn kY G (HasP fn) (IsY fn) (lfpTuple w kY (IsY fn) (Θ fn) (hΘ fn)) (app g0 (v 0)))
              (ftake_fappend p' v)]
      obtain ⟨Bf, gf, hBf_def, hgf_def, hsk⟩ := skolem_supp (S := B0) (A := accPaths (A p))
        (U := O_sp p) hQs fun a ha => by
          have hmem_g0 := app_mem_of_mem_piSet hg0 ha
          rcases mem_binUnion.mp hmem_g0 with ho | hu
          · obtain ⟨o, ho_mem, hga⟩ := mem_image.mp ho
            have ho_has : HasP p o := by
              rcases hitem0 a ha with ⟨o', hkp, hp'⟩ | ⟨m', _, _, i', y', _, _, hkp⟩
              · rw [hga] at hkp; obtain ⟨_, rfl⟩ := kpair_inj hkp; exact hp'
              · rw [hga] at hkp; exact absurd (kpair_inj hkp).1 pt_ne_empty.symm
            refine ⟨unitSet, graph (fun _ => o) unitSet (hasGraph_const _ _),
              fun q hq => (mem_unitSet_iff.mp hq) ▸ pt_mem_accPaths (A p),
              graph_mem_piSet (fun _ _ => ho_mem), fun q hq => by
                rw [app_graph hq]; exact ho_has,
              fun p' _ _ h' => by
                refine Or.inl ⟨o, hga, ?_⟩
                have := h' pt pt_mem_unitSet
                rwa [app_graph pt_mem_unitSet] at this⟩
          · obtain ⟨u, hu_occ, hga⟩ := mem_image.mp hu
            obtain ⟨m', hm', i', hi', y', hy', rfl⟩ := mem_occSpace.mp hu_occ
            have hGm' : G m' := by
              rcases hitem0 a ha with ⟨o', hkp, _⟩ | ⟨m'', _, hG'', i'', y'', _, _, hkp⟩
              · rw [hga] at hkp; exact absurd (kpair_inj hkp).1 pt_ne_empty
              · rw [hga] at hkp
                obtain ⟨_, hocc_eq⟩ := kpair_inj hkp
                obtain ⟨rfl, -, -⟩ := occEnc_inj hocc_eq
                exact hG''
            obtain ⟨B, g, hB, hg, hHp, hs⟩ := (mem_app_sepTuple_imp hi' hy').2 hGm'
            exact ⟨B, g, hB, hg, hHp, fun p' hRp' hp' h' =>
              Or.inr ⟨m', hm', hGm', i', y', hIs p p' hRp' m' hGm' ▸ hi', hs p' hRp' hp' h', hga⟩⟩
      have hBf_sig : HasSigmaPairs B0 Bf := hasSigmaPairs_of_defFun1 hBf_def
      let B_tot := sigmaPairs B0 Bf hBf_sig
      have hg_def : DefFun 1 fun v => app (gf (kp1 (v 0))) (kp2 (v 0)) :=
        DefFun.app_apply (hgf_def.comp1 (DefFun.kp1_apply (DefFun.proj 0)))
          (DefFun.kp2_apply (DefFun.proj 0))
      let g_tot := graph (fun q => app (gf (kp1 q)) (kp2 q)) B_tot (hasGraph_of_defFun1 hg_def)
      refine ⟨B_tot, g_tot, ?_, ?_, ?_, ?_⟩
      · intro r hr
        obtain ⟨a, ha, q, hq, rfl⟩ := mem_sigmaPairs.mp hr
        exact kpair_mem_accPaths (hB0 a ha) ((hsk a ha).1 q hq)
      · refine graph_mem_piSet fun r hr => ?_
        obtain ⟨a, ha, q, hq, rfl⟩ := mem_sigmaPairs.mp hr
        rw [kp1_kpair, kp2_kpair]
        exact app_mem_of_mem_piSet (hsk a ha).2.1 hq
      · intro r hr
        obtain ⟨a, ha, q, hq, rfl⟩ := mem_sigmaPairs.mp hr
        dsimp only [g_tot]
        rw [app_graph hr, kp1_kpair, kp2_kpair]
        exact (hsk a ha).2.2.1 q hq
      · intro p' hR hp' h'
        have hL' := lfpTuple_mem w kY (IsY p') (Θ p') (hΘ p')
        have hi' : i ∈ˢ IsY p' m := hIs p p' hR m hGm ▸ hi
        refine lfpTuple_closed (hcl p' hp') (hmono p' hp') (hmaps p' hp') m hm i hi' y ?_
        refine hs0 p' _ hR hp' hL' fun a ha => ?_
        refine (hsk a ha).2.2.2 p' hR hp' fun q hq => ?_
        have hmem := h' (kpair a q) (mem_sigmaPairs.mpr ⟨a, ha, q, hq, rfl⟩)
        dsimp only [g_tot] at hmem
        rwa [app_graph (mem_sigmaPairs.mpr ⟨a, ha, q, hq, rfl⟩), kp1_kpair, kp2_kpair] at hmem)
  intro m hm hG i hi y hy
  exact hind m hm i hi y hy hG

end ParamGroup

/-! ## The group's section of a least tuple (Bekić at a group) -/

section MixGroup

open Classical in
/-- The tuple `Y` on the group `G`, `C` elsewhere. -/
noncomputable def mixT (G : Nat → Prop) (C Y : Nat → V) : Nat → V :=
  fun c => if G c then Y c else C c

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {G : Nat → Prop}

omit [SetTheory V] in
theorem mixT_self (C : Nat → V) : mixT G C C = C := by
  funext c; unfold mixT; split <;> rfl

theorem mixT_mem {C Y : Nat → V} (hC : InTupleSpace w k Is C) (hY : InTupleSpace w k Is Y) :
    InTupleSpace w k Is (mixT G C Y) := by
  intro m hm; unfold mixT; split
  · exact hY m hm
  · exact hC m hm

theorem mixT_le {C Y Y' : Nat → V} (h : TupleLe k Is Y Y') :
    TupleLe k Is (mixT G C Y) (mixT G C Y') := by
  intro m hm; unfold mixT; split
  · exact h m hm
  · exact FamLe.refl _ _

open Classical in
/-- `DefTupleOp` closure under `mixT`. -/
theorem mixT_defTupleOp (G : Nat → Prop) (C : Nat → V) (hΦ : DefTupleOp k Φ) :
    DefTupleOp k (fun Y => Φ (mixT G C Y)) := by
  refine ⟨fun Y Y' hY m hm => hΦ.1 _ _ (fun j hj => ?_) m hm, fun m hm => ?_⟩
  · unfold mixT; split
    · exact hY j hj
    · rfl
  · let Gs : Fin k → (Fin k → V) → V := fun j ys => if G j.val then ys j else C j.val
    have hGs : ∀ j : Fin k, DefFun k (Gs j) := fun j => by
      dsimp only [Gs]; split
      · exact DefFun.proj j
      · exact DefFun.const (C j.val)
    refine ((hΦ.2 m hm).comp hGs).congr fun ys => ?_
    refine hΦ.1 _ _ (fun j hj => ?_) m hm
    unfold mixT; by_cases hGj : G j
    · rw [ite_eq_left hGj, padTuple_lt _ hj, padTuple_lt _ hj]; dsimp only [Gs]; simp [hGj]
    · rw [ite_eq_right hGj, padTuple_lt _ hj]; dsimp only [Gs]; simp [hGj]

/-- **The group operator is monotone.** -/
theorem mixT_monoTuple (hmono : MonoTuple w k Is Φ) {C : Nat → V}
    (hC : InTupleSpace w k Is C) : MonoTuple w k Is (fun Y => Φ (mixT G C Y)) :=
  fun _ _ hX hY hXY => hmono _ _ (mixT_mem hC hX) (mixT_mem hC hY) (mixT_le hXY)

/-- **The group operator maps the tuple space into itself.** -/
theorem mixT_mapsTuple (hmaps : MapsTuple w k Is Φ) {C : Nat → V}
    (hC : InTupleSpace w k Is C) : MapsTuple w k Is (fun Y => Φ (mixT G C Y)) :=
  fun _ hY => hmaps _ (mixT_mem hC hY)

open Classical in
/-- **The group operator is accessible**, with the operator's bound: a
support item off the group lies in the fixed tuple `C`, so it is
dropped. -/
theorem accTuple_mixT {A : V} (h : AccTuple w k Is k Is Φ A) {C : Nat → V}
    (hC : InTupleSpace w k Is C) : AccTuple w k Is k Is (fun Y => Φ (mixT G C Y)) A := by
  intro Y hY m hm i hi x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h _ (mixT_mem hC hY) m hm i hi x hx
  have hSep : HasSep B fun a => ∃ c, c < k ∧ G c ∧ ∃ i' y', app g a = occEnc c i' y' :=
    hasSep_of_defPred <|
      DefRel.finExists_lt fun c _ =>
        if hc : G c then
          (DefRel.exists_curry (DefRel.exists_curry
            (DefRel.eq_apply (DefFun.app_apply (DefFun.const g) (DefFun.proj 2))
              (DefFun.occEnc_apply c (DefFun.proj 1) (DefFun.proj 0))))).congr fun _ =>
            ⟨fun h => ⟨hc, h⟩, fun ⟨_, h⟩ => h⟩
        else DefRel.false.congr fun _ => ⟨False.elim, fun ⟨hGc, _⟩ => absurd hGc hc⟩
  let B' := sep B (fun a => ∃ c, c < k ∧ G c ∧ ∃ i' y', app g a = occEnc c i' y') hSep
  have hg'_def : DefFun 1 fun v => app g (v 0) :=
    DefFun.app_apply (DefFun.const g) (DefFun.proj 0)
  let g' := graph (app g) B' (hasGraph_of_defFun1 hg'_def)
  refine ⟨B', g', Subset.trans sep_subset hB, graph_mem_piSet fun a ha => ?_, fun Y' hY' h' => ?_⟩
  · obtain ⟨haB, c, hc, hGc, i', y', hga⟩ := mem_sep.mp ha
    have hocc := app_mem_of_mem_piSet hg haB
    rw [hga, occEnc_mem_occSpace] at hocc ⊢
    obtain ⟨_, hi', hy'⟩ := hocc
    unfold mixT at hy'
    rw [ite_eq_left hGc] at hy'
    exact ⟨hc, hi', hy'⟩
  · refine hs _ (mixT_mem hC hY') fun a ha => ?_
    have hocc := app_mem_of_mem_piSet hg ha
    obtain ⟨c, hc, i', hi', y', hy', hga⟩ := mem_occSpace.mp hocc
    rw [hga, occEnc_mem_occSpace]
    unfold mixT at hy' ⊢
    by_cases hGc : G c
    · rw [ite_eq_left hGc]
      have haB' : a ∈ˢ B' := mem_sep.mpr ⟨ha, c, hc, hGc, i', y', hga⟩
      have hh := h' a haB'
      dsimp only [g'] at hh
      rw [app_graph haB', hga, occEnc_mem_occSpace] at hh
      exact hh
    · rw [ite_eq_right hGc] at hy' ⊢
      exact ⟨hc, hi', hy'⟩

/-- **The least tuple is closed for the group operator.** -/
theorem mixT_isClosed {hΦ : DefTupleOp k Φ}
    (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    IsClosedTuple w k Is (fun Y => Φ (mixT G (lfpTuple w k Is Φ hΦ) Y)) (lfpTuple w k Is Φ hΦ) := by
  refine ⟨lfpTuple_mem w k Is Φ hΦ, ?_⟩
  show TupleLe k Is (Φ (mixT G (lfpTuple w k Is Φ hΦ) (lfpTuple w k Is Φ hΦ))) _
  rw [mixT_self]
  exact lfpTuple_closed h hmono hmaps

/-- **Bekić at a group**: on the group, the least tuple of the group
operator (the rest fixed at the least tuple) is the least tuple. -/
theorem lfpTuple_mixT {hΦ : DefTupleOp k Φ}
    (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    ∀ m, m < k → G m →
      lfpTuple w k Is (fun Y => Φ (mixT G (lfpTuple w k Is Φ hΦ) Y))
        (mixT_defTupleOp G (lfpTuple w k Is Φ hΦ) hΦ) m = lfpTuple w k Is Φ hΦ m := by
  intro m hm hG
  have hCmem : InTupleSpace w k Is (lfpTuple w k Is Φ hΦ) := lfpTuple_mem w k Is Φ hΦ
  have hcl := mixT_isClosed (G := G) (hΦ := hΦ) h hmono hmaps
  have hmonoΘ := mixT_monoTuple (G := G) hmono hCmem
  have hLcl := lfpTuple_closed (hΦ := mixT_defTupleOp G _ hΦ) ⟨_, hcl⟩ hmonoΘ
    (mixT_mapsTuple hmaps hCmem)
  have hLC := lfpTuple_le (hΦ := mixT_defTupleOp G _ hΦ) hcl
  have hLmem := lfpTuple_mem w k Is (fun Y => Φ (mixT G (lfpTuple w k Is Φ hΦ) Y))
    (mixT_defTupleOp G _ hΦ)
  have hCcl := lfpTuple_closed (hΦ := hΦ) h hmono hmaps
  generalize lfpTuple w k Is (fun Y => Φ (mixT G (lfpTuple w k Is Φ hΦ) Y))
    (mixT_defTupleOp G _ hΦ) = L at hLcl hLC hLmem ⊢
  generalize hCe : lfpTuple w k Is Φ hΦ = C at hCmem hLcl hLC hCcl ⊢
  have hmix : IsClosedTuple w k Is Φ (mixT G C L) := by
    refine ⟨mixT_mem hCmem hLmem, fun c hc => ?_⟩
    by_cases hGc : G c
    · have e : mixT G C L c = L c := by unfold mixT; rw [ite_eq_left hGc]
      rw [e]; exact hLcl c hc
    · have e : mixT G C L c = C c := by unfold mixT; rw [ite_eq_right hGc]
      rw [e]
      have hle : TupleLe k Is (mixT G C L) C := by
        intro c' hc'; unfold mixT; split
        · exact hLC c' hc'
        · exact FamLe.refl _ _
      exact (hmono _ _ (mixT_mem hCmem hLmem) hCmem hle c hc).trans (hCcl c hc)
  have hCL : TupleLe k Is C (mixT G C L) := by
    have := lfpTuple_le (hΦ := hΦ) hmix
    rw [hCe] at this
    exact this
  have e : mixT G C L m = L m := by unfold mixT; rw [ite_eq_left hG]
  refine famSpace_ext (hLmem m hm) (hCmem m hm) fun i hi => Subset.antisymm (hLC m hm i hi) ?_
  have := hCL m hm i hi
  rw [e] at this
  exact this

end MixGroup

end ConLeche.SetTheory


