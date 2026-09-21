module

public import ConLeche.SetModel.EnvClauseTreeList
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# `TV ::= node (n : ω) (v : Vec TV n)` — an INDEXED container through the env clause (falsifier F4)

The fifth falsifier of the *uniform* nested route
(`DESIGN-theory.md` §6.1, the case F1/F2 left open — `F12-REPORT.md`
finding (3): "with INDEXED pins `lfpTuple_seg_congr`'s `hIs` would
consume the lower-rank identification; unindexed it is `rfl`").
F0–F2 identify a group's segment with the container's recorded table
at index sets that are ALL one-point sets; F3 exercises the RECURSION
kit at real indices but has no container at all.  This file is the
missing corner: a block whose group is an **indexed container
instance**, identified through the container's env clause.

The block is official's `TV` row (`SURVEY-official.md` §2.4):

    inductive Vec (α : Type) : Nat → Type
      | nil  : Vec α 0
      | cons : (n : Nat) → α → Vec α n → Vec α (n + 1)
    inductive TV | node : (n : Nat) → Vec TV n → TV

with `Nat` the kit's own `ω` and `n + 1` the von Neumann successor
`vsucc`.  Two components, ONE group of rank `0`:

| c | component | index set | group |
|---|---|---|---|
| 0 | `TV` | `unitSet` | the member |
| 1 | `Vec TV` | `ω` | `g₁` = `Vec` at the pin `TV`, component `0` of `Vec`'s table |

`VecClause` is `DESIGN-theory.md` §1.2's record at `N = 1` with a
**non-trivial index set** `Is 0 = ω` and a fibre law that is read PER
INDEX: the `nil` arm exists only at the index `0`, the `cons` arm only
at a successor index, and the constructor's own index field is the
predecessor.  Official (`SURVEY-official.md` §1.4, probe D1) REJECTS
an aux former whose type mentions the block, so a container's index
TYPES never depend on the block — the container's index set is
**block-free**, which is exactly what makes `hIs` trivial here (§3).

**Pass criterion met**: no hypothesis beyond the clause.  What the
indexed case costs is bookkeeping, not assumptions, and it is listed
in the last section under `-- F4 FINDING:`.

Everything here is over the bare `SetTheory` interface; no syntax.
`stdInj`, `vnat_ne`, `app_mem_univ` and `pt_mem_univ` are F0's
(`ConLeche/SetModel/EnvClauseTreeList.lean`); the file's shape follows
F2 (`EnvClauseP4.lean`) and F3 (`UnionRecIndexed.lean`).
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

namespace TVBlock

/-! ## §0 `ω` as an index set -/

/-- `ω` is a member of every positive universe (`vnat_mem_univ_pos`'s
source). -/
theorem omega_mem_univ_pos {w : Nat} (hw : w ≠ 0) : (omega : V) ∈ˢ (univ w : V) := by
  match w, hw with
  | w + 1, _ => exact omega_mem_univ_succ w

/-- The successor index of a NAMED finite ordinal. -/
theorem vnat_succ (k : Nat) : (vnat (k + 1) : V) = vsucc (vnat k) := rfl

/-- `0` is not a successor index. -/
theorem vnat_zero_ne_vsucc (n : V) : (vnat 0 : V) ≠ vsucc n := fun h =>
  vsucc_ne_empty n h.symm

/-- The successor is injective on the named ordinals. -/
theorem vsucc_vnat_inj {a b : Nat} (h : (vsucc (vnat a) : V) = vsucc (vnat b)) : a = b :=
  Nat.succ.inj (vnat_inj (V := V) h)

/-- The index sets of the block: the member is unindexed, the
container's component is indexed by `ω`. -/
noncomputable def tvIs : Nat → V
  | 0 => unitSet
  | _ => omega

@[simp] theorem tvIs_zero : (tvIs 0 : V) = unitSet := rfl

@[simp] theorem tvIs_succ (c : Nat) : (tvIs (c + 1) : V) = omega := rfl

/-- The container's OWN index sets, at its one component. -/
noncomputable def vIs : Nat → V := fun _ => omega

@[simp] theorem vIs_apply (c : Nat) : (vIs c : V) = omega := rfl

/-! ## §1 The container's arm, as a family over `ω`

`Vec`'s fibre at an index is the arm the index SELECTS: `{nil}` at
`0`, the `cons` image at `n + 1`.  It is built over the meta-level
name of the index (`natFibre`), and read back in the index-set form
the clause states (`mem_vecFam`). -/

/-- The arm at the NAMED index: `nil` at `0`, `cons` at `k + 1` with
its own index field `vnat k`, an element of `A` and a tail from the
fibre of `T` at `vnat k`. -/
noncomputable def vArm (inj : Nat → List V → V) (A T : V) : Nat → V
  | 0 => sing (inj 0 [])
  | k + 1 => image (fun q => inj 1 [vnat k, sfst q, ssnd q]) (sigmaPairs A fun _ => app T (vnat k))

theorem mem_vArm_zero {inj : Nat → List V → V} {A T x : V} :
    x ∈ˢ vArm inj A T 0 ↔ x = inj 0 [] := mem_sing

theorem mem_vArm_succ {inj : Nat → List V → V} {A T x : V} {k : Nat} :
    x ∈ˢ vArm inj A T (k + 1) ↔
      ∃ a, a ∈ˢ A ∧ ∃ t, t ∈ˢ app T (vnat k) ∧ x = inj 1 [vnat k, a, t] := by
  show x ∈ˢ image _ _ ↔ _
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨a, ha, t, ht, rfl⟩ := mem_sigmaPairs.mp hq
    rw [sfst_kpair, ssnd_kpair]
    exact ⟨a, ha, t, ht, rfl⟩
  · rintro ⟨a, ha, t, ht, rfl⟩
    refine mem_image.mpr ⟨kpair a t, mem_sigmaPairs.mpr ⟨a, ha, t, ht, rfl⟩, ?_⟩
    rw [sfst_kpair, ssnd_kpair]

/-- **The container's family over `ω`** at an element set `A` and a
tail family `T`. -/
noncomputable def vecFam (inj : Nat → List V → V) (A T : V) : V :=
  graph (natFibre (vArm inj A T)) omega

theorem app_vecFam (inj : Nat → List V → V) (A T : V) (k : Nat) :
    app (vecFam inj A T) (vnat k) = vArm inj A T k := by
  unfold vecFam
  rw [app_graph (vnat_mem_omega k), natFibre_vnat]

/-- **The fibre law in index-set form** — the shape `VecClause.fibre`
states: at the index `0` the `nil` value, at a successor index the
`cons` values whose index field is the predecessor. -/
theorem mem_vecFam {inj : Nat → List V → V} {A T i x : V} (hi : i ∈ˢ (omega : V)) :
    x ∈ˢ app (vecFam inj A T) i ↔
      (i = vnat 0 ∧ x = inj 0 []) ∨
        ∃ n, n ∈ˢ (omega : V) ∧ i = vsucc n ∧
          ∃ a, a ∈ˢ A ∧ ∃ t, t ∈ˢ app T n ∧ x = inj 1 [n, a, t] := by
  obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
  rw [app_vecFam]
  match k with
  | 0 =>
    rw [mem_vArm_zero]
    constructor
    · intro hx; exact Or.inl ⟨rfl, hx⟩
    · rintro (⟨-, hx⟩ | ⟨n, -, he, -⟩)
      · exact hx
      · exact absurd he (vnat_zero_ne_vsucc n)
  | k + 1 =>
    rw [mem_vArm_succ]
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact Or.inr ⟨vnat k, vnat_mem_omega k, rfl, a, ha, t, ht, rfl⟩
    · rintro (⟨he, -⟩ | ⟨n, hn, he, a, ha, t, ht, rfl⟩)
      · exact absurd (vnat_inj he) (by omega)
      · obtain ⟨j, rfl⟩ := mem_omega_iff.mp hn
        obtain rfl : j = k := (vsucc_vnat_inj (V := V) he).symm
        exact ⟨a, ha, t, ht, rfl⟩

/-- The arm's formation, above `Prop`. -/
theorem vArm_mem_univ {w : Nat} (hw : w ≠ 0) {inj : Nat → List V → V} {A T : V}
    (hA : A ∈ˢ (univ w : V)) (hT : ∀ n, n ∈ˢ (omega : V) → app T n ∈ˢ (univ w : V))
    (hnil : inj 0 [] ∈ˢ (univ w : V))
    (hcons : ∀ n a t, n ∈ˢ (omega : V) → a ∈ˢ (univ w : V) → t ∈ˢ (univ w : V) →
      inj 1 [n, a, t] ∈ˢ (univ w : V)) :
    ∀ k : Nat, vArm inj A T k ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  intro k
  match k with
  | 0 => exact hU.sing_mem hnil hnil
  | k + 1 =>
    refine hU.image_mem (hU.sigmaPairs_mem hA fun _ _ => hT _ (vnat_mem_omega k)) fun q hq => ?_
    obtain ⟨a, ha, t, ht, rfl⟩ := mem_sigmaPairs.mp hq
    rw [sfst_kpair, ssnd_kpair]
    exact hcons _ a t (vnat_mem_omega k) (hU.transitive hA ha)
      (hU.transitive (hT _ (vnat_mem_omega k)) ht)

/-- The family's formation. -/
theorem vecFam_mem_famSpace {w : Nat} {inj : Nat → List V → V} {A T : V}
    (h : ∀ k : Nat, vArm inj A T k ∈ˢ (univ w : V)) :
    vecFam inj A T ∈ˢ famSpace w (omega : V) := by
  refine graph_mem_famSpace fun i hi => ?_
  obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
  rw [natFibre_vnat]
  exact h k

/-- The family is monotone in the element set and in the tail family. -/
theorem vecFam_mono {inj : Nat → List V → V} {A A' T T' : V} (hA : A ⊆ˢ A')
    (hT : ∀ n, n ∈ˢ (omega : V) → app T n ⊆ˢ app T' n) {i : V} (hi : i ∈ˢ (omega : V)) :
    app (vecFam inj A T) i ⊆ˢ app (vecFam inj A' T') i := by
  intro x hx
  rcases (mem_vecFam hi).mp hx with ⟨hi0, rfl⟩ | ⟨n, hn, hin, a, ha, t, ht, rfl⟩
  · exact (mem_vecFam hi).mpr (Or.inl ⟨hi0, rfl⟩)
  · exact (mem_vecFam hi).mpr (Or.inr ⟨n, hn, hin, a, hA a ha, t, hT n hn t ht, rfl⟩)

/-! ## §2 The container's env clause — INDEXED

`DESIGN-theory.md` §1.2's `BlockModelAt` at `N = 1` (one member, no
instance components of its own), one type parameter, and ONE INDEX
whose set is `ω`.  Note what is and is not indexed: `Is` is the
container's own datum (`vIs`, block-free, §1.4 of the survey), and the
`fibre` clause quantifies over the index, each constructor arm naming
the index at which it lives. -/
structure VecClause (w : Nat) (VEC : V → V) (ΨV : V → (Nat → V) → Nat → V)
    (injV : Nat → List V → V) : Prop where
  /-- `leaf`: the stored reading is the one-component least tuple over
  the container's own index sets. -/
  leaf : ∀ α, α ∈ˢ (univ w : V) → VEC α = lfpTuple w 1 vIs (ΨV α) 0
  /-- `functor`, monotonicity. -/
  mono : ∀ α, α ∈ˢ (univ w : V) → MonoTuple w 1 vIs (ΨV α)
  /-- `functor`, space preservation. -/
  maps : ∀ α, α ∈ˢ (univ w : V) → MapsTuple w 1 vIs (ΨV α)
  /-- `functor`, the closed tuple. -/
  closed : ∀ α, α ∈ˢ (univ w : V) → ∃ L, IsClosedTuple w 1 vIs (ΨV α) L
  /-- `fibre`, PER INDEX: `nil` at `0`, `cons` at a successor index
  with the predecessor as its own index field. -/
  fibre : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 1 vIs Y → ∀ i, i ∈ˢ (omega : V) →
    ∀ x, x ∈ˢ app (ΨV α Y 0) i ↔
      (i = vnat 0 ∧ x = injV 0 []) ∨
        ∃ n, n ∈ˢ (omega : V) ∧ i = vsucc n ∧
          ∃ a, a ∈ˢ α ∧ ∃ t, t ∈ˢ app (Y 0) n ∧ x = injV 1 [n, a, t]
  /-- `mkZero`. -/
  mkZero : w = 0 → ∀ j fs, injV j fs = (pt : V)
  /-- `mkInj`. -/
  mkInj : w ≠ 0 → ∀ j j' fs fs', injV j fs = injV j' fs' → j = j' ∧ fs = fs'

namespace VecClause

variable {w : Nat} {VEC : V → V} {ΨV : V → (Nat → V) → Nat → V} {injV : Nat → List V → V}

/-- Formation of a constructor's value, derived from `maps` + `fibre`
at a parameter and a tuple chosen to hold exactly the wanted fields
(F0's recipe (F0-1), now at an INDEX chosen with the arm). -/
theorem inj_mem_univ_of (hC : VecClause w VEC ΨV injV) (hw : w ≠ 0) {α : V}
    (hα : α ∈ˢ (univ w : V)) {Y : Nat → V} (hY : InTupleSpace w 1 vIs Y) {i : V}
    (hi : i ∈ˢ (omega : V)) {x : V}
    (hx : (i = vnat 0 ∧ x = injV 0 []) ∨
      ∃ n, n ∈ˢ (omega : V) ∧ i = vsucc n ∧
        ∃ a, a ∈ˢ α ∧ ∃ t, t ∈ˢ app (Y 0) n ∧ x = injV 1 [n, a, t]) :
    x ∈ˢ (univ w : V) :=
  (univ_isTGUniverse (V := V) hw).transitive
    (famSpace_app (hC.maps α hα Y hY 0 Nat.one_pos) hi)
    ((hC.fibre α hα Y hY i hi x).mpr hx)

/-- `nil`'s value is a set of the container's level. -/
theorem nil_mem_univ (hC : VecClause w VEC ΨV injV) (hw : w ≠ 0) :
    injV 0 [] ∈ˢ (univ w : V) :=
  hC.inj_mem_univ_of hw (unitSet_mem_univ (V := V) w)
    (Y := fun _ => graph (fun _ => empty) omega)
    (fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ w)
    (vnat_mem_omega 0) (Or.inl ⟨rfl, rfl⟩)

/-- `cons`'s value is a set of the container's level. -/
theorem cons_mem_univ (hC : VecClause w VEC ΨV injV) (hw : w ≠ 0) {n a t : V}
    (hn : n ∈ˢ (omega : V)) (ha : a ∈ˢ (univ w : V)) (ht : t ∈ˢ (univ w : V)) :
    injV 1 [n, a, t] ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine hC.inj_mem_univ_of hw (α := sing a) (hU.sing_mem ha ha)
    (Y := fun _ => graph (fun _ => sing t) omega)
    (fun _ _ => graph_mem_famSpace fun _ _ => hU.sing_mem ht ht)
    (vsucc_mem_omega hn) (Or.inr ⟨n, hn, rfl, a, mem_sing.mpr rfl, t, ?_, rfl⟩)
  rw [app_graph hn]
  exact mem_sing.mpr rfl

end VecClause

/-! ## §3 The member's tags and the block's datum -/

/-- The member's own tag laws (`DESIGN-theory.md` §1.2's `ctor` clause
at `TV`'s one constructor, which has TWO fields — the index field `n`
and the container value). -/
structure NodeTags (w : Nat) (injT : Nat → List V → V) : Prop where
  /-- Formation above `Prop`. -/
  memU : w ≠ 0 → ∀ n v, n ∈ˢ (univ w : V) → v ∈ˢ (univ w : V) → injT 0 [n, v] ∈ˢ (univ w : V)
  /-- `mkZero`. -/
  mkZero : w = 0 → ∀ j fs, injT j fs = (pt : V)
  /-- `mkInj`. -/
  mkInj : w ≠ 0 → ∀ j j' fs fs', injT j fs = injT j' fs' → j = j' ∧ fs = fs'

/-- The data F4 reasons about.  ONE level `w`. -/
structure TVSig (V : Type u) [SetTheory V] where
  /-- The value level. -/
  w : Nat
  /-- `⟦Vec α⟧`, as a family over `ω`. -/
  VEC : V → V
  /-- `Vec`'s own operator at a parameter, one component. -/
  ΨV : V → (Nat → V) → Nat → V
  /-- `Vec`'s member-local tags. -/
  injV : Nat → List V → V
  /-- `TV`'s tags. -/
  injT : Nat → List V → V

/-- The hypotheses: the container's env clause and the member's tag
laws.  Nothing else. -/
structure TVOk (S : TVSig V) : Prop where
  /-- `Vec`'s env clause, `DESIGN-theory.md` §1.2 at `N = 1` with the
  index set `ω`. -/
  vec : VecClause S.w S.VEC S.ΨV S.injV
  /-- The member's own tag laws. -/
  mem : NodeTags S.w S.injT

variable {S : TVSig V}

/-! ## §4 The two-component operator -/

/-- `TV.node`'s arm: `{ node n v | n ∈ ω, v ∈ (X 1) n }` — the index
field `n` is an ORDINARY field at the block-free type `ω`, and the
container value is a slot at component `1`, AT THE INDEX `n`. -/
noncomputable def nodeArm (S : TVSig V) (X : Nat → V) : V :=
  image (fun q => S.injT 0 [sfst q, ssnd q]) (sigmaPairs omega fun n => app (X 1) n)

theorem mem_nodeArm {X : Nat → V} {x : V} :
    x ∈ˢ nodeArm S X ↔
      ∃ n, n ∈ˢ (omega : V) ∧ ∃ v, v ∈ˢ app (X 1) n ∧ x = S.injT 0 [n, v] := by
  unfold nodeArm
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨n, hn, v, hv, rfl⟩ := mem_sigmaPairs.mp hq
    rw [sfst_kpair, ssnd_kpair]
    exact ⟨n, hn, v, hv, rfl⟩
  · rintro ⟨n, hn, v, hv, rfl⟩
    refine mem_image.mpr ⟨kpair n v, mem_sigmaPairs.mpr ⟨n, hn, v, hv, rfl⟩, ?_⟩
    rw [sfst_kpair, ssnd_kpair]

/-- **The block's operator**: the member at the one-point index set,
the container's component as a family over `ω` whose element set is
the pin's value `app (X 0) pt`. -/
noncomputable def blkΨ (S : TVSig V) (X : Nat → V) : Nat → V
  | 0 => graph (fun _ => nodeArm S X) unitSet
  | _ => vecFam S.injV (app (X 0) pt) (X 1)

theorem app_blkΨ_zero (S : TVSig V) (X : Nat → V) :
    app (blkΨ S X 0) pt = nodeArm S X := app_graph pt_mem_unitSet

theorem blkΨ_one (S : TVSig V) (X : Nat → V) :
    blkΨ S X 1 = vecFam S.injV (app (X 0) pt) (X 1) := rfl

/-! ### (a) The functor clauses -/

theorem blkΨ_mono (S : TVSig V) : MonoTuple S.w 2 tvIs (blkΨ S) := by
  intro X Y hX hY hle c hc i hi x hx
  match c, hc with
  | 0, _ =>
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_blkΨ_zero] at hx ⊢
    obtain ⟨n, hn, v, hv, rfl⟩ := mem_nodeArm.mp hx
    exact mem_nodeArm.mpr ⟨n, hn, v, hle 1 (by omega) n hn v hv, rfl⟩
  | 1, _ =>
    rw [blkΨ_one] at hx ⊢
    exact vecFam_mono (fun a ha => hle 0 (by omega) pt pt_mem_unitSet a ha)
      (fun n hn t ht => hle 1 (by omega) n hn t ht) hi x hx

theorem blkΨ_maps (hS : TVOk S) : MapsTuple S.w 2 tvIs (blkΨ S) := by
  intro X hX c hc
  by_cases hw : S.w = 0
  · -- at `Prop` every fibre is a subset of `{pt}`
    have hz : ∀ (G : V → V), (∀ i, i ∈ˢ (tvIs c : V) → G i ⊆ˢ (unitSet : V)) →
        graph G (tvIs c) ∈ˢ famSpace S.w (tvIs c) := by
      intro G hG
      refine graph_mem_famSpace fun i hi => ?_
      rw [hw, univ_zero]
      exact mem_univZero.mpr (hG i hi)
    match c, hc with
    | 0, _ =>
      have : blkΨ S X 0 = graph (fun _ => nodeArm S X) (tvIs 0) := rfl
      rw [this]
      refine hz _ fun i hi x hx => ?_
      obtain ⟨n, -, v, -, rfl⟩ := mem_nodeArm.mp hx
      rw [hS.mem.mkZero hw 0 [n, v]]
      exact pt_mem_unitSet
    | 1, _ =>
      have : blkΨ S X 1 = graph (natFibre (vArm S.injV (app (X 0) pt) (X 1))) (tvIs 1) := rfl
      rw [this]
      refine hz _ fun i hi x hx => ?_
      obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
      rw [natFibre_vnat] at hx
      match k with
      | 0 => rw [mem_vArm_zero.mp hx, hS.vec.mkZero hw 0 []]; exact pt_mem_unitSet
      | k + 1 =>
        obtain ⟨a, -, t, -, rfl⟩ := mem_vArm_succ.mp hx
        rw [hS.vec.mkZero hw 1 [vnat k, a, t]]
        exact pt_mem_unitSet
  · have hU := univ_isTGUniverse (V := V) hw
    have hap : ∀ n, n ∈ˢ (omega : V) → app (X 1) n ∈ˢ (univ S.w : V) := fun n hn =>
      famSpace_app (hX 1 (by omega)) hn
    match c, hc with
    | 0, _ =>
      refine graph_mem_famSpace fun i _ => ?_
      refine hU.image_mem (hU.sigmaPairs_mem (omega_mem_univ_pos hw) fun n hn => hap n hn)
        fun q hq => ?_
      obtain ⟨n, hn, v, hv, rfl⟩ := mem_sigmaPairs.mp hq
      rw [sfst_kpair, ssnd_kpair]
      exact hS.mem.memU hw n v (hU.transitive (omega_mem_univ_pos hw) hn)
        (hU.transitive (hap n hn) hv)
    | 1, _ =>
      rw [blkΨ_one]
      exact vecFam_mem_famSpace (vArm_mem_univ hw (famSpace_app (hX 0 (by omega)) pt_mem_unitSet)
        hap (hS.vec.nil_mem_univ hw)
        (fun n a t hn ha ht => hS.vec.cons_mem_univ hw hn ha ht))

/-! ### (b) (W): the closed tuple

Three constructors over two components.  `tupleContainer_closed_exists`
reads the positions `B` and the targets `tgtM`/`tgtI` off the SHAPE
alone, so at an INDEXED block the shape must carry everything the
index contributes — here `Vec.cons`'s own index field, which is the
FIBRE's predecessor index (F3 FINDING (1), sharpened: the shape set
itself varies with the index).  The shapes are tagged by
(component, constructor) as the general generator must emit them
(`F12-REPORT.md` finding (4)), with the constructor's hole-free
payload third. -/

/-- A shape: the COMPONENT, the CONSTRUCTOR, and the constructor's
hole-free payload (`TV.node`'s index field, `Vec.cons`'s index
field; `pt` for `Vec.nil`). -/
noncomputable def shp3 (c j : Nat) (p : V) : V := kpair (vnat c) (kpair (vnat j) p)

/-- A shape's constructor tag. -/
noncomputable def ctag (a : V) : V := sfst (ssnd a)

/-- A shape's payload. -/
noncomputable def cpay (a : V) : V := ssnd (ssnd a)

@[simp] theorem ctag_shp3 (c j : Nat) (p : V) : ctag (shp3 c j p : V) = vnat j := by
  unfold ctag shp3; rw [ssnd_kpair, sfst_kpair]

@[simp] theorem cpay_shp3 (c j : Nat) (p : V) : cpay (shp3 c j p : V) = p := by
  unfold cpay shp3; rw [ssnd_kpair, ssnd_kpair]

theorem shp3_mem_univ {w : Nat} (hw : w ≠ 0) (c j : Nat) {p : V} (hp : p ∈ˢ (univ w : V)) :
    shp3 c j p ∈ˢ (univ w : V) :=
  (univ_isTGUniverse (V := V) hw).kpair_mem hp (vnat_mem_univ_pos hw c)
    ((univ_isTGUniverse (V := V) hw).kpair_mem hp (vnat_mem_univ_pos hw j) hp)

/-- The container component's shapes AT THE NAMED INDEX: `nil` at `0`,
`cons` at `k + 1` with the predecessor in the shape. -/
noncomputable def vShpN : Nat → V
  | 0 => sing (shp3 1 1 pt)
  | k + 1 => sing (shp3 1 2 (vnat k))

/-- The shapes, per component and index. -/
noncomputable def tvShp : Nat → V → V
  | 0, _ => image (fun n => shp3 0 0 n) omega
  | _, i => natFibre vShpN i

theorem tvShp_zero (i : V) : (tvShp 0 i : V) = image (fun n => shp3 0 0 n) omega := rfl

theorem tvShp_one (k : Nat) : (tvShp 1 (vnat k) : V) = vShpN k := natFibre_vnat _ k

open Classical in
/-- A shape's positions: `TV.node` has one slot (the container value),
`Vec.nil` none, `Vec.cons` two (the element and the tail) — the index
fields are NOT positions, they are payload. -/
noncomputable def posOf (a : V) : V :=
  if ctag a = (vnat 0 : V) then sing (vnat 0)
  else if ctag a = (vnat 1 : V) then empty
  else upair (vnat 0) (vnat 1)

open Classical in
/-- A position's target component. -/
noncomputable def tgtM (a p : V) : Nat :=
  if ctag a = (vnat 0 : V) then 1
  else if p = (vnat 0 : V) then 0 else 1

open Classical in
/-- A position's target INDEX: `TV.node`'s slot sits at the index the
shape carries, `Vec.cons`'s element at the member's one point and its
tail at the shape's predecessor index. -/
noncomputable def tgtI (a p : V) : V :=
  if ctag a = (vnat 0 : V) then cpay a
  else if p = (vnat 0 : V) then pt else cpay a

open Classical in
/-- The builder: the index fields come from the SHAPE, the slots from
the position function. -/
noncomputable def mkC (S : TVSig V) (_m : Nat) (a g : V) : V :=
  if ctag a = (vnat 0 : V) then S.injT 0 [cpay a, app g (vnat 0)]
  else if ctag a = (vnat 1 : V) then S.injV 0 []
  else S.injV 1 [cpay a, app g (vnat 0), app g (vnat 1)]

open Classical in
/-- **(W)**: the block's operator has a closed tuple. -/
theorem blkΨ_closed (hS : TVOk S) : ∃ L, IsClosedTuple S.w 2 tvIs (blkΨ S) L := by
  by_cases hw : S.w = 0
  · rw [hw]
    exact closedTuple_zero (hw ▸ blkΨ_maps hS)
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ S.w : V) := fun j => vnat_mem_univ_pos hw j
  have homega : (omega : V) ∈ˢ (univ S.w : V) := omega_mem_univ_pos hw
  refine tupleContainer_closed_exists hw (Is := tvIs) (blkΨ S) tvShp posOf tgtM tgtI
    (mkC S) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    match m, hm with
    | 0, _ =>
      rw [tvShp_zero]
      exact hU.image_mem homega fun n hn => shp3_mem_univ hw 0 0 (hU.transitive homega hn)
    | 1, _ =>
      obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
      rw [tvShp_one]
      match k with
      | 0 =>
        show sing (shp3 1 1 pt) ∈ˢ (univ S.w : V)
        exact hU.sing_mem (shp3_mem_univ hw 1 1 (pt_mem_univ hw))
          (shp3_mem_univ hw 1 1 (pt_mem_univ hw))
      | k + 1 =>
        show sing (shp3 1 2 (vnat k)) ∈ˢ (univ S.w : V)
        exact hU.sing_mem (shp3_mem_univ hw 1 2 (hv k)) (shp3_mem_univ hw 1 2 (hv k))
  case hB =>
    intro m hm i a hi ha
    have : posOf a = sing (vnat 0) ∨ posOf a = empty ∨ posOf a = upair (vnat 0) (vnat 1) := by
      unfold posOf
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    rcases this with h | h | h
    · rw [h]; exact hU.sing_mem (hv 0) (hv 0)
    · rw [h]; exact hU.empty_mem (hv 0)
    · rw [h]; exact hU.upair_mem (hv 0) (hv 0) (hv 1)
  case htgt =>
    intro m hm i a p hi ha hp
    match m, hm with
    | 0, _ =>
      rw [tvShp_zero] at ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
      refine ⟨?_, ?_⟩
      · show tgtM (shp3 0 0 n) p < 2
        unfold tgtM
        rw [if_pos (by rw [ctag_shp3])]
        omega
      · show tgtI (shp3 0 0 n) p ∈ˢ tvIs (tgtM (shp3 0 0 n) p)
        unfold tgtM tgtI
        rw [if_pos (by rw [ctag_shp3]), if_pos (by rw [ctag_shp3]), cpay_shp3]
        exact hn
    | 1, _ =>
      obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
      rw [tvShp_one] at ha
      match k with
      | 0 =>
        obtain rfl : a = shp3 1 1 pt := mem_sing.mp ha
        rw [show posOf (shp3 1 1 (pt : V)) = empty from by
          unfold posOf; rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)),
            if_pos (by rw [ctag_shp3])]] at hp
        exact absurd hp (not_mem_empty p)
      | k + 1 =>
        obtain rfl : a = shp3 1 2 (vnat k) := mem_sing.mp ha
        have hct : ctag (shp3 1 2 (vnat k) : V) = vnat 2 := ctag_shp3 1 2 _
        rw [show posOf (shp3 1 2 (vnat k) : V) = upair (vnat 0) (vnat 1) from by
          unfold posOf
          rw [if_neg (by rw [hct]; exact vnat_ne (by omega)),
            if_neg (by rw [hct]; exact vnat_ne (by omega))]] at hp
        rcases mem_upair.mp hp with rfl | rfl
        · refine ⟨?_, ?_⟩
          · show tgtM (shp3 1 2 (vnat k)) (vnat 0) < 2
            unfold tgtM
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_pos rfl]
            omega
          · show tgtI (shp3 1 2 (vnat k)) (vnat 0) ∈ˢ tvIs (tgtM (shp3 1 2 (vnat k)) (vnat 0))
            unfold tgtM tgtI
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_pos rfl,
              if_neg (by rw [hct]; exact vnat_ne (by omega)), if_pos rfl]
            exact pt_mem_unitSet
        · refine ⟨?_, ?_⟩
          · show tgtM (shp3 1 2 (vnat k)) (vnat 1) < 2
            unfold tgtM
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_neg (vnat_ne (by omega))]
            omega
          · show tgtI (shp3 1 2 (vnat k)) (vnat 1) ∈ˢ tvIs (tgtM (shp3 1 2 (vnat k)) (vnat 1))
            unfold tgtM tgtI
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
              if_neg (by rw [hct]; exact vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
              cpay_shp3]
            exact vnat_mem_omega k
  case hmkU =>
    intro m hm i a g hi ha hg
    match m, hm with
    | 0, _ =>
      rw [tvShp_zero] at ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
      show mkC S 0 (shp3 0 0 n) g ∈ˢ (univ S.w : V)
      unfold mkC
      rw [if_pos (by rw [ctag_shp3]), cpay_shp3]
      exact hS.mem.memU hw n _ (hU.transitive homega hn) (app_mem_univ hw hg _)
    | 1, _ =>
      obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
      rw [tvShp_one] at ha
      match k with
      | 0 =>
        obtain rfl : a = shp3 1 1 pt := mem_sing.mp ha
        show mkC S 1 (shp3 1 1 pt) g ∈ˢ (univ S.w : V)
        unfold mkC
        rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)), if_pos (by rw [ctag_shp3])]
        exact hS.vec.nil_mem_univ hw
      | k + 1 =>
        obtain rfl : a = shp3 1 2 (vnat k) := mem_sing.mp ha
        have hct : ctag (shp3 1 2 (vnat k) : V) = vnat 2 := ctag_shp3 1 2 _
        show mkC S 1 (shp3 1 2 (vnat k)) g ∈ˢ (univ S.w : V)
        unfold mkC
        rw [if_neg (by rw [hct]; exact vnat_ne (by omega)),
          if_neg (by rw [hct]; exact vnat_ne (by omega)), cpay_shp3]
        exact hS.vec.cons_mem_univ hw (vnat_mem_omega k) (app_mem_univ hw hg _)
          (app_mem_univ hw hg _)
  case helim =>
    intro X hX m hm i hi x hx
    match m, hm with
    | 0, _ =>
      obtain rfl := mem_unitSet_iff.mp hi
      rw [app_blkΨ_zero] at hx
      obtain ⟨n, hn, v, hv, rfl⟩ := mem_nodeArm.mp hx
      refine ⟨shp3 0 0 n, by rw [tvShp_zero]; exact mem_image.mpr ⟨n, hn, rfl⟩,
        graph (fun _ => v) (sing (vnat 0)), ?_, ?_⟩
      · rw [show posOf (shp3 0 0 n : V) = sing (vnat 0) from by
          unfold posOf; rw [if_pos (by rw [ctag_shp3])]]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show v ∈ˢ app (X (tgtM (shp3 0 0 n) (vnat 0))) (tgtI (shp3 0 0 n) (vnat 0))
        unfold tgtM tgtI
        rw [if_pos (by rw [ctag_shp3]), if_pos (by rw [ctag_shp3]), cpay_shp3]
        exact hv
      · show _ = mkC S 0 (shp3 0 0 n) _
        unfold mkC
        rw [if_pos (by rw [ctag_shp3]), cpay_shp3, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
      rw [blkΨ_one, app_vecFam] at hx
      match k with
      | 0 =>
        obtain rfl := mem_vArm_zero.mp hx
        refine ⟨shp3 1 1 pt, by rw [tvShp_one]; exact mem_sing.mpr rfl,
          graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [show posOf (shp3 1 1 (pt : V)) = empty from by
            unfold posOf; rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)),
              if_pos (by rw [ctag_shp3])]]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · show _ = mkC S 1 (shp3 1 1 pt) _
          unfold mkC
          rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)), if_pos (by rw [ctag_shp3])]
      | k + 1 =>
        obtain ⟨a, ha, t, ht, rfl⟩ := mem_vArm_succ.mp hx
        have hct : ctag (shp3 1 2 (vnat k) : V) = vnat 2 := ctag_shp3 1 2 _
        have hpos : posOf (shp3 1 2 (vnat k) : V) = upair (vnat 0) (vnat 1) := by
          unfold posOf
          rw [if_neg (by rw [hct]; exact vnat_ne (by omega)),
            if_neg (by rw [hct]; exact vnat_ne (by omega))]
        refine ⟨shp3 1 2 (vnat k), by rw [tvShp_one]; exact mem_sing.mpr rfl,
          graph (fun p => if p = (vnat 0 : V) then a else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [hpos]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl]
            show a ∈ˢ app (X (tgtM (shp3 1 2 (vnat k)) (vnat 0)))
              (tgtI (shp3 1 2 (vnat k)) (vnat 0))
            unfold tgtM tgtI
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_pos rfl,
              if_neg (by rw [hct]; exact vnat_ne (by omega)), if_pos rfl]
            exact ha
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtM (shp3 1 2 (vnat k)) (vnat 1)))
              (tgtI (shp3 1 2 (vnat k)) (vnat 1))
            unfold tgtM tgtI
            rw [if_neg (by rw [hct]; exact vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
              if_neg (by rw [hct]; exact vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
              cpay_shp3]
            exact ht
        · show _ = mkC S 1 (shp3 1 2 (vnat k)) _
          unfold mkC
          rw [if_neg (by rw [hct]; exact vnat_ne (by omega)),
            if_neg (by rw [hct]; exact vnat_ne (by omega)), cpay_shp3,
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]

/-! ## §5 The carrier -/

/-- The block's carrier tuple, two components. -/
noncomputable def car (S : TVSig V) : Nat → V := lfpTuple S.w 2 tvIs (blkΨ S)

/-- `⟦TV⟧` — and the group's PIN value. -/
noncomputable def carT (S : TVSig V) : V := app (car S 0) pt

theorem car_mem (S : TVSig V) : InTupleSpace S.w 2 tvIs (car S) := lfpTuple_mem _ _ _ _

/-- The pin's value lies in `Vec`'s `Sat` domain — `famSpace_app` at
the SAME level (F0's (F0-3) again). -/
theorem carT_mem_univ (S : TVSig V) : carT S ∈ˢ (univ S.w : V) :=
  famSpace_app (car_mem S 0 (by omega)) pt_mem_unitSet

/-! ## §6 THE IDENTIFICATION: the group's segment is the INDEXED container's table

One group, rank `0`, the segment `[1, 1 + N_Vec) = [1, 2)` — ONE
`lfpTuple_seg_congr` at `s = 1`.

**The `hIs` premise** (`∀ i < s, Is (a + i) = Is' i`) is where an
indexed pin could have cost something, and it is the question
`F12-REPORT.md` finding (3) left open.  Here it is `rfl`: the
segment's index set `tvIs 1` and the container's own `vIs 0` are the
SAME set `ω`, because a container's index TYPES are block-free —
official rejects an aux former whose type mentions the block
(`SURVEY-official.md` §1.4, probe D1), so the index set of a copy is
the container's stored one, read at the pins' *parameter* positions
only.  If a container's index set DID depend on a pin — `Is' i` a
function of `⟦Ds⟧^ord` — then `hIs` would have to be proved at the
pin's value, i.e. it would consume the lower-rank identification
exactly as the fibre agreement does, and the rank induction of §2.4
would carry the index sets alongside the carriers.  It does not
arise. -/

/-- The segment `[1, 2)`'s section operator agrees, on the segment's
one-tuple space, with `Vec`'s own operator at the parameter `⟦TV⟧` —
index by index over `ω`. -/
theorem segSec_eq_ΨV (hS : TVOk S) {Y : Nat → V}
    (hY : InTupleSpace S.w 1 (fun i => tvIs (1 + i)) Y) (i : Nat) (hi : i < 1) :
    blkΨ S (segJoin 1 1 (car S) Y) (1 + i) = S.ΨV (carT S) Y i := by
  have hY' : InTupleSpace S.w 1 vIs Y := by
    intro m hm
    obtain rfl := Nat.lt_one_iff.mp hm
    exact hY 0 hm
  have hZ : InTupleSpace S.w 2 tvIs (segJoin 1 1 (car S) Y) :=
    inTupleSpace_segJoin (car_mem S) hY
  have h0 : segJoin 1 1 (car S) Y 0 = car S 0 := segJoin_lt _ _ (by omega)
  have h1 : segJoin 1 1 (car S) Y 1 = Y 0 := segJoin_add (q := 0) _ _ (by omega)
  obtain rfl := Nat.lt_one_iff.mp hi
  show blkΨ S (segJoin 1 1 (car S) Y) 1 = S.ΨV (carT S) Y 0
  refine famSpace_ext (blkΨ_maps hS _ hZ 1 (by omega))
    (hS.vec.maps (carT S) (carT_mem_univ S) Y hY' 0 (by omega)) ?_
  intro j hj
  apply SetTheory.ext
  intro x
  rw [blkΨ_one, h0, h1, mem_vecFam hj,
    hS.vec.fibre (carT S) (carT_mem_univ S) Y hY' j hj x]
  exact Iff.rfl

/-- **THE IDENTIFICATION**: the group's component IS `Vec`'s table at
the pin's value.  `hIs` is `rfl` (see above); the whole content is the
fibre agreement. -/
theorem car_seg_eq (hS : TVOk S) {q : Nat} (hq : q < 1) :
    car S (1 + q) = lfpTuple S.w 1 vIs (S.ΨV (carT S)) q :=
  lfpTuple_seg_congr (blkΨ_closed hS) (blkΨ_mono S) (by omega)
    (fun i hi => by obtain rfl := Nat.lt_one_iff.mp hi; rfl)
    (fun Y hY i hi => segSec_eq_ΨV hS hY i hi) hq

/-- **`car 1 = ⟦Vec⟧ ⟦TV⟧`** — the ordinary-reading form, by the
container's `leaf`. -/
theorem car_one_eq (hS : TVOk S) : car S 1 = S.VEC (carT S) := by
  have h := car_seg_eq hS (q := 0) (by omega)
  rw [show (1 : Nat) + 0 = 1 from rfl] at h
  rw [h, ← hS.vec.leaf (carT S) (carT_mem_univ S)]

/-- **THE IDENTIFICATION, fibrewise** — `∀ n, L 1 n = ⟦Vec⟧ (L 0 pt) n`,
the form the constructor typings and the ι rules consume. -/
theorem app_car_one_eq (hS : TVOk S) (n : V) :
    app (car S 1) n = app (S.VEC (carT S)) n := by rw [car_one_eq hS]

/-! ## §7 The fixed-point equations and the constructors' typing -/

theorem app_car_eq (hS : TVOk S) {c : Nat} (hc : c < 2) {i : V} (hi : i ∈ˢ (tvIs c : V)) :
    app (car S c) i = app (blkΨ S (car S) c) i :=
  (app_lfpTuple_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc hi).symm

theorem mem_carT (hS : TVOk S) {x : V} :
    x ∈ˢ carT S ↔
      ∃ n, n ∈ˢ (omega : V) ∧ ∃ v, v ∈ˢ app (car S 1) n ∧ x = S.injT 0 [n, v] := by
  unfold carT
  rw [app_car_eq hS (by omega) (show (pt : V) ∈ˢ tvIs 0 from pt_mem_unitSet), app_blkΨ_zero]
  exact mem_nodeArm

theorem mem_carV (hS : TVOk S) {i : V} (hi : i ∈ˢ (omega : V)) {x : V} :
    x ∈ˢ app (car S 1) i ↔
      (i = vnat 0 ∧ x = S.injV 0 []) ∨
        ∃ n, n ∈ˢ (omega : V) ∧ i = vsucc n ∧
          ∃ a, a ∈ˢ carT S ∧ ∃ t, t ∈ˢ app (car S 1) n ∧ x = S.injV 1 [n, a, t] := by
  rw [app_car_eq hS (by omega) (show i ∈ˢ tvIs 1 from hi), blkΨ_one, mem_vecFam hi]
  exact Iff.rfl

/-- **`TV.node`'s typing, with its domain read ORDINARILY**: the index
field is a natural number and the container value a member of
`⟦Vec⟧ ⟦TV⟧` AT THAT INDEX. -/
theorem node_mem_carT (hS : TVOk S) {n v : V} (hn : n ∈ˢ (omega : V))
    (hv : v ∈ˢ app (S.VEC (carT S)) n) : S.injT 0 [n, v] ∈ˢ carT S :=
  (mem_carT hS).mpr ⟨n, hn, v, by rw [app_car_one_eq hS]; exact hv, rfl⟩

/-- `Vec.nil`'s value at the pin `TV`, read ordinarily — at the index
`0`. -/
theorem nil_mem_carV (hS : TVOk S) : S.injV 0 [] ∈ˢ app (S.VEC (carT S)) (vnat 0) := by
  rw [← app_car_one_eq hS]
  exact (mem_carV hS (vnat_mem_omega 0)).mpr (Or.inl ⟨rfl, rfl⟩)

/-- `Vec.cons`'s value at the pin `TV`, read ordinarily — its own
index field is the predecessor of the index it lands at. -/
theorem cons_mem_carV (hS : TVOk S) {n a t : V} (hn : n ∈ˢ (omega : V)) (ha : a ∈ˢ carT S)
    (ht : t ∈ˢ app (S.VEC (carT S)) n) :
    S.injV 1 [n, a, t] ∈ˢ app (S.VEC (carT S)) (vsucc n) := by
  rw [← app_car_one_eq hS] at ht ⊢
  exact (mem_carV hS (vsucc_mem_omega hn)).mpr (Or.inr ⟨n, hn, rfl, a, ha, t, ht, rfl⟩)

/-! ## §8 The recursor: `UnionRecKit` at TWO components, INDEXED

Official's rules for the block (`SURVEY-official.md` §2.4's `TV` row):

    TV.rec        (TV.node n v)        = node n v (TV.rec_1 … n v)
    TV.rec_1 0     Vec.nil             = nil
    TV.rec_1 (n+1) (Vec.cons n a t)    = cons n a t (TV.rec … a) (TV.rec_1 … n t)

— the `cons` rule CROSSES to the member on its element field, and the
minor's conclusion is the motive at the SUCCESSOR index, while the
tail's ih is at the predecessor. -/

section Rec

/-- The motives and the minors, bundled. -/
structure RecData (V : Type u) [SetTheory V] where
  /-- The two motives, by component, at the index and the value. -/
  M : Nat → V → V → V
  /-- `TV.node`'s minor: the index field, the container value, the ih. -/
  node : V → V → V → V
  /-- `Vec.nil`'s minor at the pin `TV`. -/
  nil : V
  /-- `Vec.cons`'s minor at the pin `TV`: the index field, the
  element, the tail, and the two ihs. -/
  cons : V → V → V → V → V → V

variable {ℓ : Nat} {R : RecData V}

/-- The minors' typing hypotheses — all the recursor consumes. -/
structure RecOk (S : TVSig V) (ℓ : Nat) (R : RecData V) : Prop where
  /-- The motives take values in `univ ℓ`. -/
  motive : ∀ c, c < 2 → ∀ i, i ∈ˢ (tvIs c : V) → ∀ x, x ∈ˢ app (car S c) i →
    R.M c i x ∈ˢ (univ ℓ : V)
  /-- `TV.node`. -/
  node : ∀ n v ih, n ∈ˢ (omega : V) → v ∈ˢ app (car S 1) n → ih ∈ˢ R.M 1 n v →
    R.node n v ih ∈ˢ R.M 0 pt (S.injT 0 [n, v])
  /-- `Vec.nil`, at the index `0`. -/
  nil : R.nil ∈ˢ R.M 1 (vnat 0) (S.injV 0 [])
  /-- `Vec.cons`, at the SUCCESSOR index. -/
  cons : ∀ n a t ih₁ ih₂, n ∈ˢ (omega : V) → a ∈ˢ carT S → t ∈ˢ app (car S 1) n →
    ih₁ ∈ˢ R.M 0 pt a → ih₂ ∈ˢ R.M 1 n t →
    R.cons n a t ih₁ ih₂ ∈ˢ R.M 1 (vsucc n) (S.injV 1 [n, a, t])

/-- The index set of the recursion: the union of the carrier's values,
tagged by the component AND its own index. -/
noncomputable def blkIdx (S : TVSig V) : V := unionSet 2 tvIs (car S)

theorem tagged_mem_blkIdx {c : Nat} (hc : c < 2) {i : V} (hi : i ∈ˢ (tvIs c : V)) {x : V}
    (hx : x ∈ˢ app (car S c) i) : tagged c i x ∈ˢ blkIdx S := tagged_mem_unionSet hc hi hx

theorem mem_blkIdx {u : V} :
    u ∈ˢ blkIdx S ↔
      ∃ c, c < 2 ∧ ∃ i, i ∈ˢ (tvIs c : V) ∧ ∃ x, x ∈ˢ app (car S c) i ∧ u = tagged c i x :=
  mem_unionSet

/-- The predecessor relation, read off the three constructors. -/
def BlkRel (S : TVSig V) (u v : V) : Prop :=
  (∃ n t, u = tagged 0 pt (S.injT 0 [n, t]) ∧ v = tagged 1 n t) ∨
  (∃ n a t, u = tagged 1 (vsucc n) (S.injV 1 [n, a, t]) ∧
    (v = tagged 0 pt a ∨ v = tagged 1 n t))

/-- The predecessor sets. -/
noncomputable def blkPred (S : TVSig V) (u : V) : V := relPred (blkIdx S) (BlkRel S) u

theorem blkPred_subset (S : TVSig V) (u : V) : blkPred S u ⊆ˢ blkIdx S := relPred_subset _ _ u

theorem mem_blkPred {u v : V} : v ∈ˢ blkPred S u ↔ v ∈ˢ blkIdx S ∧ BlkRel S u v := mem_relPred

section Decompose

variable (hS : TVOk S) (hw : S.w ≠ 0)

include hS hw

theorem mem_blkPred_node {n v z : V} :
    z ∈ˢ blkPred S (tagged 0 pt (S.injT 0 [n, v])) ↔ z ∈ˢ blkIdx S ∧ z = tagged 1 n v := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨n, v, rfl, h⟩⟩
  rcases h with ⟨n', v', h₁, h₂⟩ | ⟨_, _, _, h₁, -⟩
  · obtain ⟨-, he⟩ := hS.mem.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_blkPred_nil {z : V} : ¬ z ∈ˢ blkPred S (tagged 1 (vnat 0) (S.injV 0 [])) := by
  intro h
  rcases (mem_blkPred.mp h).2 with ⟨_, _, h₁, -⟩ | ⟨_, _, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (hS.vec.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)

theorem mem_blkPred_cons {n a t z : V} :
    z ∈ˢ blkPred S (tagged 1 (vsucc n) (S.injV 1 [n, a, t])) ↔
      z ∈ˢ blkIdx S ∧ (z = tagged 0 pt a ∨ z = tagged 1 n t) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inr ⟨n, a, t, rfl, h⟩⟩
  rcases h with ⟨_, _, h₁, -⟩ | ⟨n', a', t', h₁, h₂⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.vec.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, he''⟩ := List.cons.inj he'
    obtain ⟨rfl, -⟩ := List.cons.inj he''
    exact h₂

/-- **The predecessors come from the argument tuple** — at an indexed
block the witness is placed at ITS OWN index (`pt` for the member's
element field, the predecessor `n` for `cons`'s tail). -/
theorem blkPred_predsFrom : PredsFrom S.w 2 tvIs (blkΨ S) (blkPred S) := by
  intro X hX _hXle c hc i hi x hx z hz
  obtain ⟨-, hrel⟩ := mem_relPred.mp hz
  match c, hc with
  | 0, _ =>
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_blkΨ_zero] at hx
    obtain ⟨n, hn, v, hv, rfl⟩ := mem_nodeArm.mp hx
    rcases hrel with ⟨n', v', h₁, rfl⟩ | ⟨_, _, _, h₁, -⟩
    · obtain ⟨-, he⟩ := hS.mem.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
      obtain ⟨rfl, he'⟩ := List.cons.inj he
      obtain ⟨rfl, -⟩ := List.cons.inj he'
      exact tagged_mem_unionSet (by omega) (show n ∈ˢ (tvIs 1 : V) from hn) hv
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 1, _ =>
    have hi' : i ∈ˢ (omega : V) := hi
    rw [blkΨ_one, mem_vecFam hi'] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨n, hn, rfl, a, ha, t, ht, rfl⟩
    · rcases hrel with ⟨_, _, h₁, -⟩ | ⟨_, _, _, h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (hS.vec.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
    · rcases hrel with ⟨_, _, h₁, -⟩ | ⟨n', a', t', h₁, h₂⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · obtain ⟨-, he⟩ := hS.vec.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
        obtain ⟨rfl, he'⟩ := List.cons.inj he
        obtain ⟨rfl, he''⟩ := List.cons.inj he'
        obtain ⟨rfl, -⟩ := List.cons.inj he''
        rcases h₂ with rfl | rfl
        · exact tagged_mem_unionSet (by omega)
            (show (pt : V) ∈ˢ (tvIs 0 : V) from pt_mem_unitSet) ha
        · exact tagged_mem_unionSet (by omega) (show n ∈ˢ (tvIs 1 : V) from hn) ht

end Decompose

/-! ### The bound and the step -/

/-- The bound: the motive of the value's component, at the value's own
index and value. -/
noncomputable def blkB (M : Nat → V → V → V) (u : V) : V :=
  natFibre (fun c => M c (sfst (ssnd u)) (ssnd (ssnd u))) (sfst u)

theorem blkB_at (M : Nat → V → V → V) (c : Nat) (i x : V) : blkB M (tagged c i x) = M c i x := by
  unfold blkB tagged
  rw [sfst_kpair, ssnd_kpair, sfst_kpair, ssnd_kpair, natFibre_vnat]

open Classical in
/-- The step: the minors at the predecessors' recursive values. -/
noncomputable def blkSt (S : TVSig V) (R : RecData V) (u g : V) : V :=
  if h : ∃ q : V × V, u = tagged 0 pt (S.injT 0 [q.1, q.2]) then
    R.node h.choose.1 h.choose.2 (app g (tagged 1 h.choose.1 h.choose.2))
  else if u = tagged 1 (vnat 0) (S.injV 0 []) then R.nil
  else if h : ∃ q : V × V × V, u = tagged 1 (vsucc q.1) (S.injV 1 [q.1, q.2.1, q.2.2]) then
    R.cons h.choose.1 h.choose.2.1 h.choose.2.2 (app g (tagged 0 pt h.choose.2.1))
      (app g (tagged 1 h.choose.1 h.choose.2.2))
  else empty

section StEq

variable (hS : TVOk S) (hw : S.w ≠ 0)

include hS hw

theorem blkSt_node (n v g : V) :
    blkSt S R (tagged 0 pt (S.injT 0 [n, v])) g = R.node n v (app g (tagged 1 n v)) := by
  unfold blkSt
  rw [dif_pos ⟨(n, v), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(n, v), rfl⟩ :
      ∃ q : V × V, (tagged 0 pt (S.injT 0 [n, v]) : V) = tagged 0 pt (S.injT 0 [q.1, q.2]))
  obtain ⟨-, he⟩ := hS.mem.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, -⟩ := List.cons.inj he'
  rw [← h₁, ← h₂]

omit hS hw in
theorem blkSt_nil (g : V) : blkSt S R (tagged 1 (vnat 0) (S.injV 0 [])) g = R.nil := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)), if_pos rfl]

theorem blkSt_cons (n a t g : V) :
    blkSt S R (tagged 1 (vsucc n) (S.injV 1 [n, a, t])) g
      = R.cons n a t (app g (tagged 0 pt a)) (app g (tagged 1 n t)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    if_neg (fun h => absurd (hS.vec.mkInj hw _ _ _ _ (tagged_inj h).2.2).1 (by omega)),
    dif_pos ⟨(n, a, t), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(n, a, t), rfl⟩ :
      ∃ q : V × V × V, (tagged 1 (vsucc n) (S.injV 1 [n, a, t]) : V)
        = tagged 1 (vsucc q.1) (S.injV 1 [q.1, q.2.1, q.2.2]))
  obtain ⟨-, he⟩ := hS.vec.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, he''⟩ := List.cons.inj he'
  obtain ⟨h₃, -⟩ := List.cons.inj he''
  rw [← h₁, ← h₂, ← h₃]

end StEq

/-! ### The kit -/

section Kit

variable (hS : TVOk S) (hw : S.w ≠ 0) (hR : RecOk S ℓ R)

include hR in
theorem blkB_mem_univ : ∀ u, u ∈ˢ blkIdx S → blkB R.M u ∈ˢ (univ ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_blkIdx.mp hu
  rw [blkB_at]
  exact hR.motive c hc i hi x hx

include hR in
theorem blkGraph_mem_B {u v : V} (hu : u ∈ˢ blkIdx S)
    (hv : v ∈ˢ app (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) u) :
    v ∈ˢ blkB R.M u := by
  rw [app_recGraph_eq (blkB_mem_univ hR) (fun u _ => blkPred_subset S u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hR in
/-- **The step is typed** — from the minors' typing alone. -/
theorem blkSt_mem : ∀ u, u ∈ˢ blkIdx S → ∀ g,
    g ∈ˢ piSet (blkPred S u)
      (fun j => app (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) j) →
    blkSt S R u g ∈ˢ blkB R.M u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ blkPred S u → app g v ∈ˢ blkB R.M v := fun v hv =>
    blkGraph_mem_B hR (blkPred_subset S u v hv) (app_mem_of_mem_piSet hg hv)
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_blkIdx.mp hu
  match c, hc with
  | 0, _ =>
    obtain rfl := mem_unitSet_iff.mp hi
    obtain ⟨n, hn, v, hv, rfl⟩ := (mem_carT hS).mp hx
    rw [blkSt_node hS hw, blkB_at]
    have h := hval (tagged 1 n v)
      ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hn hv, rfl⟩)
    rw [blkB_at] at h
    exact hR.node n v _ hn hv h
  | 1, _ =>
    have hi' : i ∈ˢ (omega : V) := hi
    rcases (mem_carV hS hi').mp hx with ⟨rfl, rfl⟩ | ⟨n, hn, rfl, a, ha, t, ht, rfl⟩
    · rw [blkSt_nil, blkB_at]; exact hR.nil
    · rw [blkSt_cons hS hw, blkB_at]
      have h₁ := hval (tagged 0 pt a)
        ((mem_blkPred_cons hS hw).mpr
          ⟨tagged_mem_blkIdx (by omega)
            (show (pt : V) ∈ˢ (tvIs 0 : V) from pt_mem_unitSet) ha, Or.inl rfl⟩)
      have h₂ := hval (tagged 1 n t)
        ((mem_blkPred_cons hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hn ht, Or.inr rfl⟩)
      rw [blkB_at] at h₁ h₂
      exact hR.cons n a t _ _ hn ha ht h₁ h₂

/-- **The block's recursion kit** at `N = 2` indexed components. -/
noncomputable def blkKit : UnionRecKit ℓ S.w 2 tvIs (blkΨ S) :=
  ⟨blkPred S, blkB R.M, blkSt S R, blkPred_predsFrom hS hw, blkB_mem_univ hR,
    blkSt_mem hS hw hR⟩

local notation "K*" => blkKit hS hw hR

@[simp] theorem blkKit_pred : (K*).pred = blkPred S := rfl
@[simp] theorem blkKit_B : (K*).B = blkB R.M := rfl
@[simp] theorem blkKit_st : (K*).st = blkSt S R := rfl

theorem blkKit_recAt (c : Nat) (i x : V) :
    (K*).recAt c i x
      = recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) (tagged c i x) := rfl

/-- The recursor at a component: `TV.rec` at `0`, `TV.rec_1` at `1`
(whose extra argument is the INDEX). -/
noncomputable def recAt (c : Nat) (i x : V) : V := (blkKit hS hw hR).recAt c i x

include hS hw hR in
/-- **Typing**: the recursor's value lies in the component's motive at
the index and the value. -/
theorem recAt_mem {c : Nat} (hc : c < 2) {i : V} (hi : i ∈ˢ (tvIs c : V)) {x : V}
    (hx : x ∈ˢ app (car S c) i) : recAt hS hw hR c i x ∈ˢ R.M c i x := by
  have h := (K*).rec_mem_B (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc hi hx
  rw [blkKit_B, blkB_at] at h
  exact h

include hS hw hR in
theorem blkRec_eq {c : Nat} (hc : c < 2) {i : V} (hi : i ∈ˢ (tvIs c : V)) {x : V}
    (hx : x ∈ˢ app (car S c) i) :
    (K*).recAt c i x
      = blkSt S R (tagged c i x)
          (graph (fun j => recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) j)
            (blkPred S (tagged c i x))) :=
  (K*).rec_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc hi hx

/-! ### The ι rules -/

include hS hw hR in
/-- ι 1 — `TV.rec (TV.node n v) = node n v (TV.rec_1 n v)`: the ih is
taken at the container component AT THE FIELD'S INDEX. -/
theorem rec_node {n v : V} (hn : n ∈ˢ (omega : V)) (hv : v ∈ˢ app (car S 1) n) :
    recAt hS hw hR 0 pt (S.injT 0 [n, v]) = R.node n v (recAt hS hw hR 1 n v) := by
  show (K*).recAt 0 pt (S.injT 0 [n, v]) = R.node n v ((K*).recAt 1 n v)
  rw [blkRec_eq hS hw hR (show (0:Nat) < 2 by omega)
      (show (pt : V) ∈ˢ (tvIs 0 : V) from pt_mem_unitSet)
      ((mem_carT hS).mpr ⟨n, hn, v, hv, rfl⟩),
    blkSt_node hS hw,
    app_graph ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hn hv, rfl⟩),
    blkKit_recAt]

include hS hw hR in
/-- ι 2 — `TV.rec_1 0 Vec.nil = nil`, at the index `0`. -/
theorem rec_nil : recAt hS hw hR 1 (vnat 0) (S.injV 0 []) = R.nil := by
  show (K*).recAt 1 (vnat 0) (S.injV 0 []) = R.nil
  rw [blkRec_eq hS hw hR (show (1:Nat) < 2 by omega)
      (show (vnat 0 : V) ∈ˢ (tvIs 1 : V) from vnat_mem_omega 0)
      ((mem_carV hS (vnat_mem_omega 0)).mpr (Or.inl ⟨rfl, rfl⟩)),
    blkSt_nil]

include hS hw hR in
/-- ι 3 — `TV.rec_1 (n+1) (Vec.cons n a t) = cons n a t (TV.rec a) (TV.rec_1 n t)`:
**the crossing rule at an index**, whose element ih is at the MEMBER
(index `pt`) and whose tail ih is at the PREDECESSOR index. -/
theorem rec_cons {n a t : V} (hn : n ∈ˢ (omega : V)) (ha : a ∈ˢ carT S)
    (ht : t ∈ˢ app (car S 1) n) :
    recAt hS hw hR 1 (vsucc n) (S.injV 1 [n, a, t])
      = R.cons n a t (recAt hS hw hR 0 pt a) (recAt hS hw hR 1 n t) := by
  show (K*).recAt 1 (vsucc n) (S.injV 1 [n, a, t])
    = R.cons n a t ((K*).recAt 0 pt a) ((K*).recAt 1 n t)
  rw [blkRec_eq hS hw hR (show (1:Nat) < 2 by omega)
      (show (vsucc n : V) ∈ˢ (tvIs 1 : V) from vsucc_mem_omega hn)
      ((mem_carV hS (vsucc_mem_omega hn)).mpr (Or.inr ⟨n, hn, rfl, a, ha, t, ht, rfl⟩)),
    blkSt_cons hS hw,
    app_graph ((mem_blkPred_cons hS hw).mpr
      ⟨tagged_mem_blkIdx (by omega) (show (pt : V) ∈ˢ (tvIs 0 : V) from pt_mem_unitSet) ha,
        Or.inl rfl⟩),
    app_graph ((mem_blkPred_cons hS hw).mpr
      ⟨tagged_mem_blkIdx (by omega) hn ht, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

end Kit

end Rec

/-! ## §9 What the clause must record (the F4 record)

**PASS.**  The indexed group needs the container's recorded clause and
nothing else: `car_seg_eq` identifies the segment `[1, 2)` with
`lfpTuple w 1 vIs (ΨV ⟦TV⟧)` in one `lfpTuple_seg_congr`, with
`VecClause`'s `functor`/`fibre` as the only container input, and
`car_one_eq`/`app_car_one_eq` read it off `leaf`.  No narrow clause,
no clamp (`meetT`), no `composeΦ`, no `pinsCar`, no class
accessibility, ONE level `w`, and the group's rank is `0` (its pin is
the member) exactly as in F2.

**F4 FINDING (1) — `hIs` is `rfl`, and the reason is official's probe
D1.**  `F12-REPORT.md` finding (3) left this open: with INDEXED pins
`lfpTuple_seg_congr`'s `hIs` (`∀ i < s, Is (a + i) = Is' i`) might
have to consume the lower-rank identification.  It does not, and the
reason is structural rather than accidental:

* the copy's index sets ARE the container's own (`tvIs 1 = vIs 0 = ω`)
  because a container's index TYPES are read from its stored datum;
* they could only mention the block through a PIN, and an index type
  that mentions a pin whose reading mentions the block makes the aux
  former's own type mention the block — which official REJECTS
  (`SURVEY-official.md` §1.4, probe D1: `_nested.C_i`'s type may not
  mention the block).  So `Is'` is always computed from BLOCK-FREE
  data.

Consequence for the design: `hIs` is an equation between two readings
of block-free data — `rfl` when the index set is closed (the `Vec`
case: `ω` on both sides), and at worst an ORDINARY-reading equation
for a container whose index type depends on a block-free parameter
(`C (α) (n : Nat) : Fin n → …` at a closed `n`).  It never consumes a
group's identification, so §2.4's rank induction carries the CARRIERS
only, and the topological sort of §2.1 step 5 still orders the claims
alone (F12's finding (3) is answered: the exception it feared is
excluded by the positivity check, not by luck).

**F4 FINDING (2) — an indexed `fibre` is a GUARDED union of arms, and
the guard is the constructor's result index.**  §1.2's `fibre` reads
`x ∈ app (Ψ ψ ρp X t c) ↔ ∃ j fs, ChainFit … t c j fs ∧ x = inj ψ c j fs`:
at an indexed block `ChainFit` must, per constructor, equate the
fibre's index `t` with the constructor's RESULT index at its fields
(`Vec.nil` only at `0`; `Vec.cons n a t'` only at `n + 1`), and must
read the recursive slot at the field's OWN index (`t' ∈ app (Y 0) n`).
`VecClause.fibre` is that shape written out, and `mem_vecFam` (20
lines) is the only place in this file where the index algebra of `ω`
is used — everything downstream reads the guarded form.  This is not a
new clause, but it IS a constraint on `ChainFit`'s statement that the
unindexed falsifiers could not see.

**F4 FINDING (3) — for (W) the shape SET varies with the index, and a
constructor's own index fields are shape payload, never positions.**
F3's finding (1) already asked for member-and-index-tagged shapes;
here the shape family at component `1` is genuinely index-dependent
(`vShpN`: one shape at `0`, a different one at every successor), and
`Vec.cons`'s index field must sit IN the shape because
`tupleContainer_closed_exists` computes the tail's target index
(`tgtI`) from the shape alone.  The (component, constructor, payload)
shape `shp3` is what a general generator must emit.  §10 confirms the
per-copy half of F12's finding (6) in the sharpest form: `Vec.cons`'s
ELEMENT is a POSITION in the block's copy (it targets the pin) and a
SHAPE entry in the container's own table (there it is a value of the
parameter) — same constructor, two copies, two different shape
vocabularies.

**F4 NON-FINDING (4) — the recursion kit needs nothing new for
indices.**  The predecessor relation places every field at ITS OWN
index (`pt` for `Vec.cons`'s element, the predecessor `n` for its
tail), `blkB`/`blkSt` read the index off the tag `tagged c i x` as
F3's do, and official's "the minor's conclusion is
`motive_2 (n+1) (Vec.cons a a_1)`" is `RecOk.cons`'s conclusion
VERBATIM: no index transport, no `Eq.mpr`, because a set-level motive
`M : Nat → V → V → V` takes the index as an ordinary argument.  The
three ι rules are the same four-line pattern as F0–F2's.

**F4 NON-FINDING (5) — the pin's `Sat` guard and the seeding are
F0/F2's.**  The only fact used of the pin is `carT_mem_univ`
(`famSpace_app`, three lines), and the member's index field is an
ORDINARY field at the block-free type `ω` — it costs one `sigmaPairs`
in `nodeArm` and nothing in the identification. -/

/-! ## §10 Non-vacuity: `VecClause` has a model

The indexed clause carries a fibre law that SELECTS its arms by the
index, so — as in F1/F2 — the falsifier would prove nothing without a
model of it.  `Vec` at F0's standard tags is one, at every level.
Note the (W) recipe here against the block's above: at the
CONTAINER's own table `Vec.cons`'s element is a value of the
PARAMETER, hence hole-free, hence part of the SHAPE, while in the
block's copy the same field targets the pin and is a POSITION — F12's
"hole-free ⇒ shape, per field, per copy", now with the index field in
the shape in both. -/

section StdVec

/-- `Vec`'s own operator at a parameter `α`: one component over `ω`. -/
noncomputable def stdΨV (w : Nat) (α : V) (Y : Nat → V) : Nat → V :=
  fun _ => vecFam (stdInj w) α (Y 0)

/-- The container's recorded reading `⟦Vec⟧ α`. -/
noncomputable def stdVEC (w : Nat) (α : V) : V := lfpTuple w 1 vIs (stdΨV w α) 0

theorem stdΨV_mono {w : Nat} (α : V) : MonoTuple w 1 vIs (stdΨV w α) := by
  intro X Y _hX _hY hle m hm i hi
  obtain rfl := Nat.lt_one_iff.mp hm
  exact vecFam_mono (fun _ ha => ha) (fun n hn => hle 0 Nat.one_pos n hn) hi

theorem stdΨV_maps {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) : MapsTuple w 1 vIs (stdΨV w α) := by
  intro Y hY m hm
  obtain rfl := Nat.lt_one_iff.mp hm
  by_cases hw : w = 0
  · refine graph_mem_famSpace fun i hi => ?_
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
    rw [hw, univ_zero, natFibre_vnat]
    refine mem_univZero.mpr fun x hx => ?_
    match k with
    | 0 => rw [mem_vArm_zero.mp hx, stdInj_zero]; exact pt_mem_unitSet
    | k + 1 =>
      obtain ⟨a, -, t, -, rfl⟩ := mem_vArm_succ.mp hx
      rw [stdInj_zero]
      exact pt_mem_unitSet
  · exact vecFam_mem_famSpace (vArm_mem_univ hw hα
      (fun n hn => famSpace_app (hY 0 Nat.one_pos) hn)
      (stdInj_mem_univ hw (by simp))
      (fun n a t hn ha ht => stdInj_mem_univ hw (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (univ_isTGUniverse (V := V) hw).transitive (omega_mem_univ_pos hw) hn
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ht
            · exact absurd hx (List.not_mem_nil))))

/-- The container's shapes at the NAMED index: `nil` at `0`, and at
`k + 1` one shape per ELEMENT of the parameter (hole-free ⇒ shape),
carrying the index field beside it. -/
noncomputable def sShpN (α : V) : Nat → V
  | 0 => sing (shp3 0 1 pt)
  | k + 1 => image (fun a => shp3 0 2 (kpair (vnat k) a)) α

open Classical in
/-- The positions: none for `nil`, the tail for `cons`. -/
noncomputable def sPos (a : V) : V := if ctag a = (vnat 1 : V) then empty else sing (vnat 0)

/-- The tail's target index: the shape's index field. -/
noncomputable def sTgtI (a _p : V) : V := sfst (cpay a)

open Classical in
/-- The builder: the index field and the element come from the SHAPE. -/
noncomputable def sMk (w : Nat) (_m : Nat) (a g : V) : V :=
  if ctag a = (vnat 1 : V) then stdInj w 0 []
  else stdInj w 1 [sfst (cpay a), ssnd (cpay a), app g (vnat 0)]

open Classical in
theorem stdΨV_closed {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) :
    ∃ L, IsClosedTuple w 1 vIs (stdΨV w α) L := by
  by_cases hw : w = 0
  · rw [hw]; exact closedTuple_zero (hw ▸ stdΨV_maps hα)
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ w : V) := fun j => vnat_mem_univ_pos hw j
  have hshp : ∀ k : Nat, (sShpN α k : V) ∈ˢ (univ w : V) := by
    intro k
    match k with
    | 0 =>
      show sing (shp3 0 1 pt) ∈ˢ (univ w : V)
      exact hU.sing_mem (shp3_mem_univ hw 0 1 (pt_mem_univ hw))
        (shp3_mem_univ hw 0 1 (pt_mem_univ hw))
    | k + 1 =>
      show image (fun a => shp3 0 2 (kpair (vnat k) a)) α ∈ˢ (univ w : V)
      refine hU.image_mem hα fun a ha => ?_
      have haU : a ∈ˢ (univ w : V) := hU.transitive hα ha
      exact shp3_mem_univ hw 0 2 (hU.kpair_mem haU (hv k) haU)
  refine tupleContainer_closed_exists hw (Is := vIs) (stdΨV w α)
    (fun _ i => natFibre (sShpN α) i) sPos (fun _ _ => 0) sTgtI (sMk w) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
    rw [natFibre_vnat]
    exact hshp k
  case hB =>
    intro m hm i a hi ha
    unfold sPos
    split
    · exact hU.empty_mem (hv 0)
    · exact hU.sing_mem (hv 0) (hv 0)
  case htgt =>
    intro m hm i a p hi ha hp
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
    rw [natFibre_vnat] at ha
    refine ⟨Nat.one_pos, ?_⟩
    match k with
    | 0 =>
      obtain rfl : a = shp3 0 1 pt := mem_sing.mp ha
      rw [show sPos (shp3 0 1 (pt : V)) = empty from by unfold sPos; rw [if_pos (by rw [ctag_shp3])]]
        at hp
      exact absurd hp (not_mem_empty p)
    | k + 1 =>
      obtain ⟨b, -, rfl⟩ := mem_image.mp ha
      show sfst (cpay (shp3 0 2 (kpair (vnat k) b) : V)) ∈ˢ (omega : V)
      rw [cpay_shp3, sfst_kpair]
      exact vnat_mem_omega k
  case hmkU =>
    intro m hm i a g hi ha hg
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
    rw [natFibre_vnat] at ha
    match k with
    | 0 =>
      obtain rfl : a = shp3 0 1 pt := mem_sing.mp ha
      show sMk w 0 (shp3 0 1 pt) g ∈ˢ (univ w : V)
      unfold sMk
      rw [if_pos (by rw [ctag_shp3])]
      exact stdInj_mem_univ hw (by simp)
    | k + 1 =>
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      show sMk w 0 (shp3 0 2 (kpair (vnat k) b)) g ∈ˢ (univ w : V)
      unfold sMk
      rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)), cpay_shp3, sfst_kpair, ssnd_kpair]
      refine stdInj_mem_univ hw ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv k
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hU.transitive hα hb
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact app_mem_univ hw hg _
          · exact absurd hx (List.not_mem_nil)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := Nat.lt_one_iff.mp hm
    obtain ⟨k, rfl⟩ := mem_omega_iff.mp hi
    have hx' : x ∈ˢ vArm (stdInj w) α (X 0) k := by
      have h : x ∈ˢ app (vecFam (stdInj w) α (X 0)) (vnat k) := hx
      rwa [app_vecFam] at h
    match k with
    | 0 =>
      obtain rfl := mem_vArm_zero.mp hx'
      refine ⟨shp3 0 1 pt, by rw [natFibre_vnat]; exact mem_sing.mpr rfl,
        graph (fun _ => pt) empty, ?_, ?_⟩
      · rw [show sPos (shp3 0 1 (pt : V)) = empty from by
          unfold sPos; rw [if_pos (by rw [ctag_shp3])]]
        exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
      · show _ = sMk w 0 (shp3 0 1 pt) _
        unfold sMk
        rw [if_pos (by rw [ctag_shp3])]
    | k + 1 =>
      obtain ⟨a, ha, t, ht, rfl⟩ := mem_vArm_succ.mp hx'
      refine ⟨shp3 0 2 (kpair (vnat k) a),
        by rw [natFibre_vnat]; exact mem_image.mpr ⟨a, ha, rfl⟩,
        graph (fun _ => t) (sing (vnat 0)), ?_, ?_⟩
      · rw [show sPos (shp3 0 2 (kpair (vnat k) a) : V) = sing (vnat 0) from by
          unfold sPos; rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega))]]
        refine graph_mem_piSet fun p hp => ?_
        show t ∈ˢ app (X 0) (sTgtI (shp3 0 2 (kpair (vnat k) a)) p)
        unfold sTgtI
        rw [cpay_shp3, sfst_kpair]
        exact ht
      · show _ = sMk w 0 (shp3 0 2 (kpair (vnat k) a)) _
        unfold sMk
        rw [if_neg (by rw [ctag_shp3]; exact vnat_ne (by omega)), cpay_shp3, sfst_kpair,
          ssnd_kpair, app_graph (mem_sing.mpr rfl)]

/-- **`VecClause` is not an empty hypothesis**: the standard reading
of `Vec` satisfies it, index-selected fibre law and all, at every
level. -/
theorem stdVecClause (w : Nat) :
    VecClause w (stdVEC (V := V) w) (stdΨV w) (stdInj w) where
  leaf := fun _ _ => rfl
  mono := fun α _ => stdΨV_mono α
  maps := fun _ hα => stdΨV_maps hα
  closed := fun _ hα => stdΨV_closed hα
  fibre := fun α hα Y hY i hi x => mem_vecFam hi
  mkZero := fun hw j fs => by rw [hw, stdInj_zero]
  mkInj := fun hw j j' fs fs' h => stdInj_inj hw j j' fs fs' h

/-- The member's tags have a model too (F0's `stdInj`, at a TWO-field
constructor). -/
theorem nodeTags_stdInj (w : Nat) : NodeTags w (stdInj (V := V) w) where
  memU := fun hw n v hn hv => stdInj_mem_univ hw (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact absurd hx (List.not_mem_nil))
  mkZero := fun hw j fs => by rw [hw, stdInj_zero]
  mkInj := fun hw j j' fs fs' h => stdInj_inj hw j j' fs fs' h

/-- The whole hypothesis of F4 is satisfiable. -/
theorem tvOk_std (w : Nat) :
    TVOk (V := V) ⟨w, stdVEC w, stdΨV w, stdInj w, stdInj w⟩ :=
  ⟨stdVecClause w, nodeTags_stdInj w⟩

end StdVec

end TVBlock

end ConLeche.SetTheory
