module

public import ConLeche.SetModel.HoleClose
@[expose] public section

/-!
# (W) for a NESTED block through a transient wide operator (lane NESTW-KIT, set half of L7)

Charter items 2 and 4.  A nested block's operator `Φ` (on its `k`
members) reads a nested field `C (t[X])` through `C`'s lfp clause: the
container's value at the instantiation is a component of the least tuple
of `C`'s own operator at the parameter frame `⟦t[X]⟧`.  Its closure
witness (W) comes from a TRANSIENT WIDE operator `Ψ` on `k + n`
components — the members, then one component per container KEY the
positivity walk reached (`nestPos`'s keys: an instantiation `C_q (t_q)`,
a container reached from a key's own constructors included, a mutual
container group reached by restart included) — in which every nested
occurrence is a plain hole at its key.  `Ψ` is flat, so its closed tuple
comes from the container kit (`SetModel/WideFlat.lean`,
`UBlock.closed_of_flat`, whose U4 premise `HoleUnread` is R3's caveat);
this module composes the keys away.

* `catTup`/`dropTup` — a wide tuple as members `X` then keys `Y`;
* `keySec`, `keyLfp`, `composeKeys` — the keys' joint section at a
  member tuple, its least tuple, and `Ψ` with ALL keys replaced by it at
  once (no iteration in key order, no Bekić);
* `closedTuple_composeKeys` — a closed tuple of `Ψ` is a closed tuple of
  the composed operator (leastness of the keys' lfp + `Ψ`'s
  monotonicity);
* `closed_of_wide` — **the block's closed tuple**, when the block's
  operator lies below `Ψ` at every key tuple DOMINATING the containers'
  values (`hmem`), and the keys' least tuple dominates them (`hdom`);
  `Φ` need not EQUAL the composed operator — `≤` suffices;
* `KeyGroups`, `dominated_of_groups` — `hdom` from exactly what the
  containers' lfp clauses provide: per reached container group, at the
  instantiation read off the wide tuple, its operator is monotone and
  closed (the clause's `functor`), a key's value is its component of the
  group's least tuple (the clause's `leaf`), and the substitution law in
  `≤` form (`sub`: the group's operator, its reached components read at
  the keys, lies below `Ψ`'s key component once the DEEPER keys dominate
  their values).  Proved by `lfpTuple_le_on` (HoleClose) per group, in
  decreasing depth; unreached components of a group (D2) are read at the
  group's own least tuple.  Nothing is asked of a container in its
  parameter (charter item 4: no parameter-monotonicity, no container
  law): a container's parameter enters only through the instantiation
  read off the tuple;
* `composeKeys_eq` — composing all keys away is `Ψ` at the containers'
  values, so it LEAVES the block's operator where that reads them as `Ψ`
  reads the keys (the equation is not needed for (W)).

Instances: `SetModel/NestWideEx.lean`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Wide tuples: members, then keys -/

/-- The wide tuple: members `X` below `k`, keys `Y` from `k`. -/
def catTup (k : Nat) (X Y : Nat → V) : Nat → V := fun i => if i < k then X i else Y (i - k)

/-- The keys of a wide tuple (also: the keys' index sets). -/
def dropTup (k : Nat) (L : Nat → V) : Nat → V := fun q => L (k + q)

omit [SetTheory V] in
theorem catTup_lt {k : Nat} (X Y : Nat → V) {i : Nat} (hi : i < k) : catTup k X Y i = X i :=
  if_pos hi

omit [SetTheory V] in
theorem catTup_add {k : Nat} (X Y : Nat → V) (q : Nat) : catTup k X Y (k + q) = Y q := by
  unfold catTup; rw [if_neg (by omega), Nat.add_sub_cancel_left]

omit [SetTheory V] in
theorem catTup_dropTup (k : Nat) (L : Nat → V) : catTup k L (dropTup k L) = L := by
  funext i
  unfold catTup dropTup
  split
  · rfl
  · congr 1; omega

theorem inTupleSpace_catTup {w k n : Nat} {Is X Y : Nat → V} (hX : InTupleSpace w k Is X)
    (hY : InTupleSpace w n (dropTup k Is) Y) : InTupleSpace w (k + n) Is (catTup k X Y) := by
  intro i hi
  by_cases hik : i < k
  · rw [catTup_lt X Y hik]; exact hX i hik
  · obtain ⟨q, rfl⟩ : ∃ q, i = k + q := ⟨i - k, by omega⟩
    rw [catTup_add]; exact hY q (by omega)

theorem inTupleSpace_dropTup {w k n : Nat} {Is L : Nat → V} (hL : InTupleSpace w (k + n) Is L) :
    InTupleSpace w n (dropTup k Is) (dropTup k L) := fun q hq => hL (k + q) (by omega)

theorem inTupleSpace_of_add {w k n : Nat} {Is L : Nat → V} (hL : InTupleSpace w (k + n) Is L) :
    InTupleSpace w k Is L := fun m hm => hL m (by omega)

theorem tupleLe_catTup {k n : Nat} {Is X X' Y Y' : Nat → V} (hX : TupleLe k Is X X')
    (hY : TupleLe n (dropTup k Is) Y Y') : TupleLe (k + n) Is (catTup k X Y) (catTup k X' Y') := by
  intro i hi
  by_cases hik : i < k
  · rw [catTup_lt X Y hik, catTup_lt X' Y' hik]; exact hX i hik
  · obtain ⟨q, rfl⟩ : ∃ q, i = k + q := ⟨i - k, by omega⟩
    rw [catTup_add, catTup_add]; exact hY q (by omega)

/-! ## The keys' joint section, its least tuple, the composed operator -/

section Compose

variable (w k n : Nat) (Is : Nat → V) (Ψ : (Nat → V) → Nat → V)

/-- **The keys' joint section** at a member tuple `X`: `Ψ`'s key
components as an operator on the key tuple, the members held at `X`. -/
def keySec (X : Nat → V) : (Nat → V) → Nat → V := fun Y q => Ψ (catTup k X Y) (k + q)

/-- **The keys' least tuple** at a member tuple. -/
noncomputable def keyLfp (X : Nat → V) : Nat → V := lfpTuple w n (dropTup k Is) (keySec k Ψ X)

/-- **The composed operator**: `Ψ` with ALL keys replaced by their
least tuple at the members. -/
noncomputable def composeKeys (X : Nat → V) : Nat → V := Ψ (catTup k X (keyLfp w k n Is Ψ X))

end Compose

section ComposeLaws

variable {w k n : Nat} {Is : Nat → V} {Ψ : (Nat → V) → Nat → V}

theorem keyLfp_mem (X : Nat → V) : InTupleSpace w n (dropTup k Is) (keyLfp w k n Is Ψ X) :=
  lfpTuple_mem _ _ _ _

/-- The keys' section is monotone, from `Ψ`'s monotonicity. -/
theorem keySec_mono (hmono : MonoTuple w (k + n) Is Ψ) {X : Nat → V} (hX : InTupleSpace w k Is X) :
    MonoTuple w n (dropTup k Is) (keySec k Ψ X) := by
  intro Y Y' hY hY' hYY' q hq
  exact hmono _ _ (inTupleSpace_catTup hX hY) (inTupleSpace_catTup hX hY')
    (tupleLe_catTup (TupleLe.refl _ _ _) hYY') (k + q) (by omega)

/-- A closed tuple of `Ψ` gives, at its own members, a closed tuple of
the keys' section: its keys. -/
theorem keySec_closed_of {L : Nat → V} (hL : IsClosedTuple w (k + n) Is Ψ L) :
    IsClosedTuple w n (dropTup k Is) (keySec k Ψ L) (dropTup k L) := by
  refine ⟨inTupleSpace_dropTup hL.1, fun q hq => ?_⟩
  show FamLe _ (Ψ (catTup k L (dropTup k L)) (k + q)) (L (k + q))
  rw [catTup_dropTup]
  exact hL.2 (k + q) (by omega)

/-- **The keys' least tuple is pre-fixed** for the keys' section, once
the section has a closed tuple. -/
theorem keyLfp_prefixed (hmono : MonoTuple w (k + n) Is Ψ) {X : Nat → V} (hX : InTupleSpace w k Is X)
    (hcl : ∃ Lk, IsClosedTuple w n (dropTup k Is) (keySec k Ψ X) Lk) :
    ∀ q, q < n → FamLe (Is (k + q)) (Ψ (catTup k X (keyLfp w k n Is Ψ X)) (k + q))
      (keyLfp w k n Is Ψ X q) :=
  lfpTuple_closed hcl (keySec_mono hmono hX)

/-- **(W) through the composed operator**: a closed tuple of `Ψ` is a
closed tuple of `Ψ` with all keys composed away — by leastness of the
keys' lfp below the closed tuple's keys, and `Ψ`'s monotonicity. -/
theorem closedTuple_composeKeys (hmono : MonoTuple w (k + n) Is Ψ) {L : Nat → V}
    (hL : IsClosedTuple w (k + n) Is Ψ L) :
    IsClosedTuple w k Is (composeKeys w k n Is Ψ) L := by
  refine ⟨inTupleSpace_of_add hL.1, fun m hm => ?_⟩
  have hle : TupleLe (k + n) Is (catTup k L (keyLfp w k n Is Ψ L)) L := by
    have h := tupleLe_catTup (Is := Is) (TupleLe.refl k Is L) (lfpTuple_le (keySec_closed_of hL))
    rwa [catTup_dropTup] at h
  exact (hmono _ _ (inTupleSpace_catTup (inTupleSpace_of_add hL.1) (keyLfp_mem L)) hL.1 hle m
    (by omega)).trans (hL.2 m (by omega))

/-- **Composing all keys away**: when a key tuple `T` is pre-fixed for
the keys' section and lies below the keys' least tuple (the containers'
values, dominated by the keys' lfp), the composed operator IS `Ψ` with
the keys at `T` — so, when the block's operator reads the containers'
values where `Ψ` reads the keys, composing all keys away leaves the
block's operator. -/
theorem composeKeys_eq (hmono : MonoTuple w (k + n) Is Ψ) (hmaps : MapsTuple w (k + n) Is Ψ)
    {X T : Nat → V} (hX : InTupleSpace w k Is X) (hT : InTupleSpace w n (dropTup k Is) T)
    (hpre : TupleLe n (dropTup k Is) (keySec k Ψ X T) T)
    (hle : TupleLe n (dropTup k Is) T (keyLfp w k n Is Ψ X)) :
    ∀ m, m < k + n → composeKeys w k n Is Ψ X m = Ψ (catTup k X T) m := by
  have hK : TupleLe n (dropTup k Is) (keyLfp w k n Is Ψ X) T := lfpTuple_le ⟨hT, hpre⟩
  have hS1 := inTupleSpace_catTup hX (keyLfp_mem (w := w) (k := k) (n := n) (Is := Is) (Ψ := Ψ) X)
  have hS2 := inTupleSpace_catTup hX hT
  have h1 := hmono _ _ hS1 hS2 (tupleLe_catTup (TupleLe.refl _ _ _) hK)
  have h2 := hmono _ _ hS2 hS1 (tupleLe_catTup (TupleLe.refl _ _ _) hle)
  intro m hm
  exact famSpace_ext (hmaps _ hS1 m hm) (hmaps _ hS2 m hm) fun i hi =>
    Subset.antisymm (h1 m hm i hi) (h2 m hm i hi)

end ComposeLaws

/-! ## The block's closed tuple -/

/-- **The keys dominate the containers' values** at a wide tuple `W`:
key `q`'s value read off `W` (`ev q W`, a family over the key's index
set) lies below `W`'s key slot. -/
def Dominated (k n : Nat) (Is : Nat → V) (ev : Nat → (Nat → V) → V) (W : Nat → V) : Prop :=
  ∀ q, q < n → FamLe (Is (k + q)) (ev q W) (W (k + q))

/-- **(W) for a nested block from the transient wide operator.**

* `Ψ` — the wide operator on the members and `n` keys, monotone and
  closed (positivity of the wide fields; the flat kit);
* `ev` — the keys' container values, read off a wide tuple (the
  containers' lfp clauses at the instantiation);
* `hdom` — at a member tuple where the keys' section has a closed
  tuple, the keys' least tuple dominates the values
  (`dominated_of_groups`);
* `hmem` — the substitution law at the members, in `≤` form: the
  block's operator lies below `Ψ` at every key tuple dominating the
  values (a nested field `C (t[X])` reads `ev`, `Ψ` reads the key slot).

No equation `Ψ^(n) = Φ` is needed, and nothing about a container in its
parameter. -/
theorem closed_of_wide {w k n : Nat} {Is : Nat → V} {Φ Ψ : (Nat → V) → Nat → V}
    (hmono : MonoTuple w (k + n) Is Ψ) (hcl : ∃ L, IsClosedTuple w (k + n) Is Ψ L)
    (ev : Nat → (Nat → V) → V)
    (hdom : ∀ X, InTupleSpace w k Is X → (∃ Lk, IsClosedTuple w n (dropTup k Is) (keySec k Ψ X) Lk) →
      Dominated k n Is ev (catTup k X (keyLfp w k n Is Ψ X)))
    (hmem : ∀ X Y, InTupleSpace w k Is X → InTupleSpace w n (dropTup k Is) Y →
      Dominated k n Is ev (catTup k X Y) → TupleLe k Is (Φ X) (Ψ (catTup k X Y))) :
    ∃ L, IsClosedTuple w k Is Φ L := by
  obtain ⟨L, hL⟩ := hcl
  have hLk : InTupleSpace w k Is L := inTupleSpace_of_add hL.1
  have hC := closedTuple_composeKeys hmono hL
  refine ⟨L, hLk, fun m hm => ?_⟩
  refine (hmem L _ hLk (keyLfp_mem L) (hdom L hLk ⟨_, keySec_closed_of hL⟩) m hm).trans ?_
  exact hC.2 m hm

/-! ## Domination from the containers' lfp clauses -/

/-- The largest value of `f` below `n`, plus one: a bound for `f` on `[0, n)`. -/
def boundBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (f n + 1) (boundBelow f n)

theorem lt_boundBelow (f : Nat → Nat) : ∀ {n q : Nat}, q < n → f q < boundBelow f n
  | n + 1, q, hq => by
    unfold boundBelow
    by_cases h : q = n
    · subst h; omega
    · have := lt_boundBelow f (n := n) (q := q) (by omega); omega

/-- **The keys, grouped by the container group each reaches.**  Key
`q` is component `cmp q` of group `grp q`; group `G`, at the
instantiation read off a wide tuple `W`, has `g G` components with index
sets `IsG G W` and operator `Θ G W` (the container group's operator at
that parameter frame — ITS clause's `Φ`); `dep G` is the group's depth
in the walk (a group's substitution law reads only DEEPER keys'
domination). -/
structure KeyGroups (V : Type u) [SetTheory V] where
  /-- key ↦ its group -/
  grp : Nat → Nat
  /-- key ↦ its component in its group -/
  cmp : Nat → Nat
  /-- group ↦ its width -/
  g : Nat → Nat
  /-- group, wide tuple ↦ the group's index sets at the instantiation -/
  IsG : Nat → (Nat → V) → Nat → V
  /-- group, wide tuple ↦ the group's operator at the instantiation -/
  Θ : Nat → (Nat → V) → (Nat → V) → Nat → V
  /-- group ↦ its depth -/
  dep : Nat → Nat

namespace KeyGroups

variable (P : KeyGroups V) (w k n : Nat)

/-- **Key `q`'s value** at the wide tuple `W`: its component of its
group's least tuple at the instantiation (the container clause's
`leaf`). -/
noncomputable def ev (q : Nat) (W : Nat → V) : V :=
  lfpTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) (P.cmp q)

/-- Group `G`'s component `j` is reached by a key. -/
def Reached (G j : Nat) : Prop := ∃ q, q < n ∧ P.grp q = G ∧ P.cmp q = j

open Classical in
/-- **The group's tuple read at the keys**: a reached component reads
its key's slot of `W`, an unreached one (D2) the group's own least
tuple. -/
noncomputable def fill (G : Nat) (W : Nat → V) : Nat → V := fun j =>
  if h : P.Reached n G j then W (k + h.choose) else lfpTuple w (P.g G) (P.IsG G W) (P.Θ G W) j

/-- **What the containers' lfp clauses provide**, keyed by the
instantiation (charter item 4). -/
structure Ok (Is : Nat → V) (Ψ : (Nat → V) → Nat → V) : Prop where
  /-- a key's component is one of its group's -/
  cmp_lt : ∀ q, q < n → P.cmp q < P.g (P.grp q)
  /-- distinct keys are distinct components -/
  inj : ∀ q q', q < n → q' < n → P.grp q = P.grp q' → P.cmp q = P.cmp q' → q = q'
  /-- a key's index set is its component's -/
  idx : ∀ q, q < n → ∀ W, P.IsG (P.grp q) W (P.cmp q) = Is (k + q)
  /-- **the clause's `functor`** at the instantiation: monotone, closed -/
  functor : ∀ W, InTupleSpace w (k + n) Is W → ∀ q, q < n →
    MonoTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) ∧
    ∃ L, IsClosedTuple w (P.g (P.grp q)) (P.IsG (P.grp q) W) (P.Θ (P.grp q) W) L
  /-- **the substitution law**, `≤` form: the group's operator, its
  reached components read at the keys, lies below `Ψ`'s key component,
  once every DEEPER key dominates its value -/
  sub : ∀ W, InTupleSpace w (k + n) Is W → ∀ q, q < n →
    (∀ q', q' < n → P.dep (P.grp q) < P.dep (P.grp q') →
      FamLe (Is (k + q')) (P.ev w q' W) (W (k + q'))) →
    FamLe (Is (k + q)) (P.Θ (P.grp q) W (P.fill w k n (P.grp q) W) (P.cmp q)) (Ψ W (k + q))

variable {P w k n}

theorem fill_reached {q : Nat} (hq : q < n)
    (hinj : ∀ q q', q < n → q' < n → P.grp q = P.grp q' → P.cmp q = P.cmp q' → q = q')
    (W : Nat → V) : P.fill w k n (P.grp q) W (P.cmp q) = W (k + q) := by
  have hR : P.Reached n (P.grp q) (P.cmp q) := ⟨q, hq, rfl, rfl⟩
  unfold fill
  rw [dif_pos hR]
  obtain ⟨hq', hg, hc⟩ := hR.choose_spec
  rw [hinj _ _ hq' hq hg hc]

/-- One group, at a wide tuple pre-fixed at the keys whose deeper keys
dominate: every key of the group dominates — `lfpTuple_le_on` at the
group's operator, the reached components compared with `fill`. -/
theorem dominated_group {Is : Nat → V} {Ψ : (Nat → V) → Nat → V} (hP : P.Ok w k n Is Ψ)
    {W : Nat → V} (hW : InTupleSpace w (k + n) Is W)
    (hpre : ∀ q, q < n → FamLe (Is (k + q)) (Ψ W (k + q)) (W (k + q)))
    {q : Nat} (hq : q < n)
    (hdeep : ∀ q', q' < n → P.dep (P.grp q) < P.dep (P.grp q') →
      FamLe (Is (k + q')) (P.ev w q' W) (W (k + q'))) :
    FamLe (Is (k + q)) (P.ev w q W) (W (k + q)) := by
  classical
  let G := P.grp q
  obtain ⟨hmonoG, hclG⟩ := hP.functor W hW q hq
  have hfillS : InTupleSpace w (P.g G) (P.IsG G W) (P.fill w k n G W) := by
    intro j hj
    unfold fill
    split
    · next h =>
      obtain ⟨hq', hg, hc⟩ := h.choose_spec
      have := hW (k + h.choose) (by omega)
      rw [← hP.idx _ hq' W, hg, hc] at this
      exact this
    · exact lfpTuple_mem _ _ _ _ j hj
  have hle := lfpTuple_le_on hclG hmonoG (P.Reached n G) hfillS (fun j hj hR => by
    have hfill_eq : (fun x => if P.Reached n G x then P.fill w k n G W x
        else lfpTuple w (P.g G) (P.IsG G W) (P.Θ G W) x) = P.fill w k n G W := by
      funext x
      by_cases hx : P.Reached n G x
      · rw [if_pos hx]
      · rw [if_neg hx]; unfold fill; rw [dif_neg hx]
    rw [hfill_eq]
    obtain ⟨q', hq', hg, rfl⟩ := hR
    have e : P.grp q = P.grp q' := hg.symm
    show FamLe (P.IsG (P.grp q) W (P.cmp q'))
      (P.Θ (P.grp q) W (P.fill w k n (P.grp q) W) (P.cmp q')) (P.fill w k n (P.grp q) W (P.cmp q'))
    rw [e, hP.idx _ hq' W, fill_reached hq' hP.inj W]
    exact (hP.sub W hW q' hq' (by rw [← e]; exact hdeep)).trans (hpre q' hq'))
    (P.cmp q) (hP.cmp_lt q hq) ⟨q, hq, rfl, rfl⟩
  rw [hP.idx _ hq W, fill_reached hq hP.inj W] at hle
  exact hle

/-- **Every key dominates**, at a wide tuple pre-fixed at the keys —
by `dominated_group`, deeper groups first. -/
theorem dominated_of_prefixed {Is : Nat → V} {Ψ : (Nat → V) → Nat → V} (hP : P.Ok w k n Is Ψ)
    {W : Nat → V} (hW : InTupleSpace w (k + n) Is W)
    (hpre : ∀ q, q < n → FamLe (Is (k + q)) (Ψ W (k + q)) (W (k + q))) :
    Dominated k n Is (P.ev w) W := by
  let M := boundBelow (fun q => P.dep (P.grp q)) n
  have hM : ∀ q, q < n → P.dep (P.grp q) < M := fun q hq => lt_boundBelow (fun q => P.dep (P.grp q)) hq
  suffices h : ∀ d q, q < n → M - P.dep (P.grp q) ≤ d →
      FamLe (Is (k + q)) (P.ev w q W) (W (k + q)) from
    fun q hq => h _ q hq (Nat.le_refl _)
  intro d
  induction d with
  | zero => intro q hq hd; have := hM q hq; omega
  | succ d ih =>
    intro q hq hd
    refine dominated_group hP hW hpre hq fun q' hq' hlt => ih q' hq' ?_
    have := hM q' hq'
    omega

/-- **`closed_of_wide`'s `hdom` from the containers' clauses.** -/
theorem dominated_of_groups {Is : Nat → V} {Ψ : (Nat → V) → Nat → V} (hP : P.Ok w k n Is Ψ)
    (hmono : MonoTuple w (k + n) Is Ψ) {X : Nat → V} (hX : InTupleSpace w k Is X)
    (hcl : ∃ Lk, IsClosedTuple w n (dropTup k Is) (keySec k Ψ X) Lk) :
    Dominated k n Is (P.ev w) (catTup k X (keyLfp w k n Is Ψ X)) := by
  refine dominated_of_prefixed hP (inTupleSpace_catTup hX (keyLfp_mem X)) fun q hq => ?_
  rw [catTup_add]
  exact keyLfp_prefixed hmono hX hcl q hq

end KeyGroups

/-- **(W) for a nested block, from the wide operator and the
containers' lfp clauses** — `closed_of_wide` with `hdom` discharged by
`KeyGroups.dominated_of_groups`. -/
theorem closed_of_wide_groups {w k n : Nat} {Is : Nat → V} {Φ Ψ : (Nat → V) → Nat → V}
    (hmono : MonoTuple w (k + n) Is Ψ) (hcl : ∃ L, IsClosedTuple w (k + n) Is Ψ L)
    (P : KeyGroups V) (hP : P.Ok w k n Is Ψ)
    (hmem : ∀ X Y, InTupleSpace w k Is X → InTupleSpace w n (dropTup k Is) Y →
      Dominated k n Is (P.ev w) (catTup k X Y) → TupleLe k Is (Φ X) (Ψ (catTup k X Y))) :
    ∃ L, IsClosedTuple w k Is Φ L :=
  closed_of_wide hmono hcl (P.ev w) (fun _ hX hcl' => KeyGroups.dominated_of_groups hP hmono hX hcl')
    hmem

end ConLeche.SetTheory
