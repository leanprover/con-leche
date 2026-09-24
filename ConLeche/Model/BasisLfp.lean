module

public import ConLeche.Model.Annot.EnvModelM
import ConLeche.SetTheory.Derive.Universe
public section

/-!
# The pinned basis types' LFP CLAUSES, by hand (lane ENVLFP)

The environment invariant's lfp clause (`Model/Annot/BlockLfp.lean`)
is PRODUCED by the uniform install for every block it checks.  The
pinned basis types are not installed by it: their denotations are
hand-written (`bval`, `SetModel/Value.lean`).  This file proves the
clause for them by hand, once, at their pinned leaves:

| type | sort | pinned leaf | operator's fibre at `S` | carrier |
|---|---|---|---|---|
| `Empty` | `1` | `bval .empty = ∅` | `∅` (no constructor) | `∅` |
| `False` | `0` | `bval .empty = ∅` | `∅` | `∅` |
| `PUnit.{u}` | `u` | `bval .punit = {pt}` | `{pt}` (`unit`, no field) | `{pt}` |
| `Nat` | `1` | `bval .nat = ω` | `{∅} ∪ {vsucc m ∣ m ∈ S}` (inside `ω`) | `ω` |

All four are one component, unparameterized and unindexed, so they
share one datum shape (`lfp0`) and one clause theorem (`lfp0_clause`);
each type contributes its fibre function `F`, the carrier `C`, and
`C`'s LEASTNESS among the `F`-closed sets (for `Nat` that is `ω`'s own
induction, `omega_subset_inductive` — GRAPH-F's `natT_eq_omega`).

`Eq` and `Quot` are argued in the lane report rather than proved: `Quot`
is not an inductive for the recursor check (official installs it as a
builtin; no recursor is checked against it and no nested occurrence
goes through it), and `Eq` — the only pinned type with a TYPE parameter,
hence the only one a nested block can use as a container — needs its
clause only when a nested block through it is installed (GRAPH-F's
`eqKit` is its induction), which the uniform route does not do yet.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.SetModel
open ConLeche.SetTheory.Tower (towerSet_nil)

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## One component, no parameters, no indices -/

/-- The index set of an unindexed component: the unit set. -/
theorem idxSet_nil (u : Nat) (ρp : Nat → V) : idxSet u ρp [] = (unitSet : V) := towerSet_nil

/-- **The datum of an unparameterized, unindexed one-member block**:
its operator's only fibre (at the point) is `F` of the family's own
fibre. -/
@[expose] noncomputable def lfp0 (nm : Name) (w : (Name → Nat) → Nat) (F : V → V)
    (fits : V → Nat → List V → Prop) (inj : Nat → List V → V) (n : Nat) (cn : Nat → Name)
    (flds : Nat → List AnnotTerm) : LfpDatum V where
  names := [nm]
  k := 1
  N := 1
  w := w
  params := fun _ => []
  pars := fun _ _ => []
  ids := fun _ _ => []
  u := fun _ _ => 0
  Φ := fun _ _ X _ => graph (fun _ => F (app (X 0) pt)) unitSet
  fits := fun _ _ X _ _ j fs => fits (app (X 0) pt) j fs
  inj := fun _ _ j fs => inj j fs
  nctors := fun _ => n
  ctorName := fun _ j => cn j
  fields := fun _ _ j => flds j
  resIdx := fun _ _ _ => []

section Lfp0

variable {nm : Name} {w : (Name → Nat) → Nat} {F : V → V} {fits : V → Nat → List V → Prop}
  {inj : Nat → List V → V} {n : Nat} {cn : Nat → Name} {flds : Nat → List AnnotTerm}

theorem lfp0_idx (ψ : Name → Nat) (ρp : Nat → V) (c : Nat) :
    (lfp0 nm w F fits inj n cn flds).idx ψ ρp c = (unitSet : V) := idxSet_nil 0 ρp

theorem app_lfp0_Φ (ψ : Name → Nat) (ρp X : Nat → V) (c : Nat) :
    app ((lfp0 nm w F fits inj n cn flds).Φ ψ ρp X c) pt = F (app (X 0) pt) :=
  app_graph pt_mem_unitSet

/-- **The hole frame of a one-member unparameterized unindexed block**:
the family's only fibre at the one hole. -/
theorem lfp0_frame (ψ : Name → Nat) (ρp X : Nat → V) :
    (lfp0 nm w F fits inj n cn flds).frame ψ ρp X = cons (app (X 0) pt) ρp := by
  show consList [holeFam (shiftE 0 0 ρp) ([] ++ []) fun vs => app (X 0) (tupW 0 (vs.drop 0))] ρp
    = cons (app (X 0) pt) ρp
  rw [consList_cons, consList_nil]
  show cons (app (X 0) (tupW 0 [])) ρp = _
  rw [tupW_zero]

/-- **The carrier's only fibre is `C`**, when `C` is an `F`-closed set
of the level lying below every `F`-closed set of the level. -/
theorem lfp0_carrier {ψ : Name → Nat} {ρp : Nat → V} {C : V}
    (hmono : ∀ S S', S ⊆ˢ S' → F S ⊆ˢ F S')
    (hCu : C ∈ˢ (univ (w ψ) : V)) (hC : F C ⊆ˢ C)
    (hleast : ∀ S, S ∈ˢ (univ (w ψ) : V) → F S ⊆ˢ S → C ⊆ˢ S) :
    app ((lfp0 nm w F fits inj n cn flds).carrier ψ ρp 0) pt = C := by
  let D := lfp0 nm w F fits inj n cn flds
  have hI : D.idx ψ ρp = fun _ => (unitSet : V) := funext (lfp0_idx ψ ρp)
  -- the constant tuple at `C` is closed
  have hclC : IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)
      (fun _ => graph (fun _ => C) unitSet) := by
    rw [hI]
    refine ⟨fun _ _ => graph_mem_famSpace fun _ _ => hCu, fun m _ i hi x hx => ?_⟩
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_lfp0_Φ, app_graph pt_mem_unitSet] at hx
    rw [app_graph pt_mem_unitSet]
    exact hC x hx
  have hmonoT : MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) := by
    rw [hI]
    intro X Y _ _ hle m _ i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_lfp0_Φ] at hx ⊢
    exact hmono _ _ (hle 0 Nat.one_pos pt pt_mem_unitSet) x hx
  refine Subset.antisymm ?_ ?_
  · have h := lfpTuple_le hclC 0 Nat.one_pos pt (by rw [hI]; exact pt_mem_unitSet)
    rwa [app_graph pt_mem_unitSet] at h
  · have hpt : pt ∈ˢ D.idx ψ ρp 0 := by rw [hI]; exact pt_mem_unitSet
    refine hleast _ (famSpace_app (lfpTuple_mem _ _ _ _ 0 Nat.one_pos) hpt) fun x hx => ?_
    refine lfpTuple_closed ⟨_, hclC⟩ hmonoT 0 Nat.one_pos pt hpt x ?_
    show x ∈ˢ app (D.Φ ψ ρp (D.carrier ψ ρp) 0) pt
    rw [app_lfp0_Φ]
    exact hx

/-- **The lfp clause of an unparameterized, unindexed one-member
block**, from its fibre function's monotonicity, level, fibre
description, and the leaf's value as the least `F`-closed set. -/
theorem lfp0_clause {acval : Name → (Name → Nat) → AnnotTerm} {C : (Name → Nat) → V}
    (hmono : ∀ S S', S ⊆ˢ S' → F S ⊆ˢ F S')
    (hmaps : ∀ (ψ : Name → Nat) S, S ∈ˢ (univ (w ψ) : V) → F S ∈ˢ (univ (w ψ) : V))
    (hfib : ∀ S x, x ∈ˢ F S ↔ ∃ j fs, fits S j fs ∧ x = inj j fs)
    (hCu : ∀ ψ, C ψ ∈ˢ (univ (w ψ) : V)) (hC : ∀ ψ, F (C ψ) ⊆ˢ C ψ)
    (hleast : ∀ ψ S, S ∈ˢ (univ (w ψ) : V) → F S ⊆ˢ S → C ψ ⊆ˢ S)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = C ψ)
    -- the hole reading (lane HOLE2): the fit IS the fields' fit at the hole
    (hholes : ∀ (ρp : Nat → V) S j fs, fits S j fs ↔ j < n ∧ SpineFit (cons S ρp) (flds j) fs)
    (hzero : ∀ ψ, w ψ = 0 → ∀ j fs, inj j fs = pt)
    (hinjI : ∀ ψ, w ψ ≠ 0 → ∀ j fs j' fs', j < n → j' < n →
      fs.length = (flds j).length → fs'.length = (flds j').length →
      inj j fs = inj j' fs' → j = j' ∧ fs = fs')
    (hctor : ∀ j, j < n → ∀ (ψ : Name → Nat) (ρ : Nat → V) (fs : List V),
      SpineFit (cons (C ψ) ρ) (flds j) fs → fs.foldl app (interp V ρ (acval (cn j) ψ)) = inj j fs) :
    LfpClause acval (lfp0 nm w F fits inj n cn flds) where
  kN := Nat.le_refl 1
  functor := fun ψ ρp _ => by
    have hI : (lfp0 nm w F fits inj n cn flds).idx ψ ρp = fun _ => (unitSet : V) :=
      funext (lfp0_idx ψ ρp)
    refine ⟨?_, ?_, ?_⟩
    · rw [hI]
      intro X Y _ _ hle m _ i hi x hx
      obtain rfl := mem_unitSet_iff.mp hi
      rw [app_lfp0_Φ] at hx ⊢
      exact hmono _ _ (hle 0 Nat.one_pos pt pt_mem_unitSet) x hx
    · rw [hI]
      intro X hX m _
      exact graph_mem_famSpace fun _ _ =>
        hmaps ψ _ (famSpace_app (hX 0 Nat.one_pos) pt_mem_unitSet)
    · refine ⟨fun _ => graph (fun _ => C ψ) unitSet, ?_⟩
      rw [hI]
      refine ⟨fun _ _ => graph_mem_famSpace fun _ _ => hCu ψ, fun m _ i hi x hx => ?_⟩
      obtain rfl := mem_unitSet_iff.mp hi
      rw [app_lfp0_Φ, app_graph pt_mem_unitSet] at hx
      rw [app_graph pt_mem_unitSet]
      exact hC ψ x hx
  fibre := fun ψ ρp _ X _ c _ t ht x => by
    rw [lfp0_idx] at ht
    obtain rfl := mem_unitSet_iff.mp ht
    rw [app_lfp0_Φ]
    exact hfib _ x
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero hsa.length_eq
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero hsi.length_eq
    show interp V ρ (acval nm ψ) = app ((lfp0 nm w F fits inj n cn flds).carrier ψ (consList [] ρ) 0) pt
    rw [hleaf ψ ρ, lfp0_carrier hmono (hCu ψ) (hC ψ) (hleast ψ)]
  holes := fun ψ ρp _ X _ c _ t _ j fs => by
    show fits (app (X 0) pt) j fs ↔ (j < n ∧ SpineFit (LfpDatum.frame _ ψ ρp X) (flds j) fs ∧
      ∀ l, l < 0 → _)
    rw [lfp0_frame, hholes ρp]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, fun l hl => absurd hl (Nat.not_lt_zero l)⟩,
      fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  mkZero := fun ψ hw _ j fs => hzero ψ hw j fs
  mkInj := fun ψ hw _ _ j fs j' fs' hj hj' hl hl' h => hinjI ψ hw j fs j' fs' hj hj' hl hl' h
  ctor := fun c _ j ψ ρ as fs t hsa _ hf => by
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero hsa.length_eq
    obtain ⟨hj, hsp, -⟩ := hf
    have hsp' : SpineFit (cons (C ψ) ρ) (flds j) fs := by
      have := hsp
      rw [lfp0_frame, consList_nil, lfp0_carrier hmono (hCu ψ) (hC ψ) (hleast ψ)] at this
      exact this
    exact hctor j hj ψ ρ fs hsp'

end Lfp0

/-! ## `Empty` and `False`: no constructor -/

/-- The zero-constructor datum at sort level `w`. -/
@[expose] noncomputable def emptyLfp (nm : Name) (w : Nat) : LfpDatum V :=
  lfp0 nm (fun _ => w) (fun _ => empty) (fun _ _ _ => False) (fun _ _ => pt) 0 (fun _ => nm)
    (fun _ => [])

/-- **The clause of a zero-constructor type** whose pinned leaf is the
empty set — `Empty` at `w = 1`, `False` at `w = 0` (both pinned to
`bval .empty`). -/
theorem emptyLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm : Name} (w : Nat)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = empty) :
    LfpClause acval (emptyLfp (V := V) nm w) :=
  lfp0_clause (C := fun _ => empty) (fun _ _ _ => Subset.refl _)
    (fun _ _ _ => empty_mem_univ w)
    (fun _ x => ⟨fun h => absurd h (not_mem_empty x), fun ⟨_, _, h, _⟩ => h.elim⟩)
    (fun _ => empty_mem_univ w) (fun _ => Subset.refl _)
    (fun _ _ _ _ x hx => absurd hx (not_mem_empty x)) hleaf
    (fun _ _ j _ => ⟨False.elim, fun h => absurd h.1 (Nat.not_lt_zero j)⟩)
    (fun _ _ _ _ => rfl)
    (fun _ _ j _ _ _ hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => absurd hj (Nat.not_lt_zero j))

/-! ## `PUnit`: one constructor, no field -/

theorem spineFit_nil_iff {ρ : Nat → V} {fs : List V} : SpineFit ρ [] fs ↔ fs = [] := by
  cases fs <;> simp [SpineFit]

/-- The one-constructor, no-field datum at sort level `w`, its
constructor `cn`. -/
@[expose] noncomputable def punitLfp (nm cn : Name) (w : (Name → Nat) → Nat) : LfpDatum V :=
  lfp0 nm w (fun _ => unitSet) (fun _ j fs => j = 0 ∧ fs = []) (fun _ _ => pt) 1 (fun _ => cn)
    (fun _ => [])

/-- **The clause of a one-constructor, no-field type** whose pinned
leaf is the unit set and whose constructor's the point (`PUnit.{u}`,
pinned to `bval .punit`, `PUnit.unit` to `bval .punitUnit`). -/
theorem punitLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm cn : Name}
    (w : (Name → Nat) → Nat)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = unitSet)
    (hctor : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval cn ψ) = pt) :
    LfpClause acval (punitLfp (V := V) nm cn w) :=
  lfp0_clause (C := fun _ => unitSet) (fun _ _ _ => Subset.refl _)
    (fun ψ _ _ => unitSet_mem_univ (w ψ))
    (fun _ x => by
      rw [mem_unitSet_iff]
      exact ⟨fun h => ⟨0, [], ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, _, h⟩ => h⟩)
    (fun ψ => unitSet_mem_univ (w ψ)) (fun _ => Subset.refl _)
    (fun _ _ _ hS => hS) hleaf
    (fun _ _ j fs => by
      rw [spineFit_nil_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩)
    (fun _ _ _ _ => rfl)
    (fun _ _ j fs j' fs' hj hj' hl hl' _ => by
      refine ⟨by omega, ?_⟩
      rw [List.eq_nil_of_length_eq_zero hl, List.eq_nil_of_length_eq_zero hl'])
    (fun j _ ψ ρ fs hsp => by
      obtain rfl := spineFit_nil_iff.mp hsp
      exact hctor ψ ρ)

/-! ## `Nat`: zero and successor -/

/-- The zero/successor fibre (lane HOLE2: the operator of the fields with
holes, `{∅} ∪ {vsucc m ∣ m ∈ S}` — no `m ∈ ω` beside the hole; its least
fixed point is `ω` all the same). -/
@[expose] noncomputable def natF (S : V) : V :=
  sUnion (upair (upair empty empty) (image vsucc S))

/-- `Nat`'s constructors' fit: `zero` with no field, `succ` with one
field in the family. -/
@[expose] def natFits (S : V) (j : Nat) (fs : List V) : Prop :=
  (j = 0 ∧ fs = []) ∨ (j = 1 ∧ ∃ m, fs = [m] ∧ m ∈ˢ S)

/-- `Nat`'s injections: `zero ↦ ∅`, `succ m ↦ vsucc m`. -/
@[expose] noncomputable def natInj (j : Nat) (fs : List V) : V :=
  if j = 0 then empty else vsucc (fs.headD empty)

/-- `Nat`'s constructors' fields with holes: `zero` none, `succ` the hole. -/
@[expose] def natFlds (j : Nat) : List AnnotTerm := if j = 0 then [] else [.bvar 0]

/-- The pinned `Nat`'s datum (sort `Type`, level `1`), its constructors
`zn` and `sn`. -/
@[expose] noncomputable def natLfp (nm zn sn : Name) : LfpDatum V :=
  lfp0 nm (fun _ => 1) natF natFits natInj 2 (fun j => if j = 0 then zn else sn) natFlds

theorem mem_natF {S x : V} : x ∈ˢ natF S ↔ x = empty ∨ ∃ m, m ∈ˢ S ∧ x = vsucc m := by
  unfold natF
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases mem_upair.mp hy with rfl | rfl
    · rcases mem_upair.mp hxy with h | h <;> exact Or.inl h
    · obtain ⟨m, hm, rfl⟩ := mem_image.mp hxy
      exact Or.inr ⟨m, hm, rfl⟩
  · rintro (rfl | ⟨m, hm, rfl⟩)
    · exact ⟨_, mem_upair.mpr (Or.inl rfl), mem_upair.mpr (Or.inl rfl)⟩
    · exact ⟨_, mem_upair.mpr (Or.inr rfl), mem_image.mpr ⟨m, hm, rfl⟩⟩

/-- `∈` is asymmetric (regularity at the pair). -/
theorem mem_asymm' {x y : V} (hxy : x ∈ˢ y) (hyx : y ∈ˢ x) : False := by
  obtain ⟨z, hz, hmin⟩ := regularity (upair x y) ⟨x, mem_upair.mpr (Or.inl rfl)⟩
  rcases mem_upair.mp hz with rfl | rfl
  · exact hmin ⟨y, hyx, mem_upair.mpr (Or.inr rfl)⟩
  · exact hmin ⟨x, hxy, mem_upair.mpr (Or.inl rfl)⟩

/-- The von Neumann successor is injective. -/
theorem vsucc_inj {m m' : V} (h : vsucc m = vsucc m') : m = m' := by
  have h1 : m ∈ˢ vsucc m' := h ▸ mem_vsucc.mpr (Or.inr rfl)
  have h2 : m' ∈ˢ vsucc m := h ▸ mem_vsucc.mpr (Or.inr rfl)
  rcases mem_vsucc.mp h1 with h1 | h1
  · rcases mem_vsucc.mp h2 with h2 | h2
    · exact (mem_asymm' h1 h2).elim
    · exact h2.symm
  · exact h1

/-- **The pinned `Nat`'s clause**: `ω` is the least fixed point of the
zero/successor operator (GRAPH-F's `natT_eq_omega`, re-derived here at
the clause's operator), its constructors `∅` and `natSuccV`. -/
theorem natLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm zn sn : Name}
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = omega)
    (hzero : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval zn ψ) = empty)
    (hsucc : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval sn ψ) = natSuccV V) :
    LfpClause acval (natLfp (V := V) nm zn sn) :=
  lfp0_clause (C := fun _ => omega)
    (fun S S' hS x hx => by
      rcases mem_natF.mp hx with h | ⟨m, hm, rfl⟩
      · exact mem_natF.mpr (Or.inl h)
      · exact mem_natF.mpr (Or.inr ⟨m, hS m hm, rfl⟩))
    (fun _ S hS => by
      have hU : IsTGUniverse (Mem (V := V)) (univ 1) := univ_isTGUniverse (by decide)
      have h0 : (empty : V) ∈ˢ univ 1 := hU.empty_mem hS
      refine hU.sUnion_mem (hU.upair_mem hS (hU.upair_mem hS h0 h0) (hU.image_mem hS ?_))
      intro m hm
      have hmU : m ∈ˢ (univ 1 : V) := hU.transitive hS hm
      exact hU.binUnion_mem hS hmU (hU.sing_mem hS hmU))
    (fun S x => by
      rw [mem_natF]
      constructor
      · rintro (rfl | ⟨m, hm, rfl⟩)
        · exact ⟨0, [], Or.inl ⟨rfl, rfl⟩, rfl⟩
        · exact ⟨1, [m], Or.inr ⟨rfl, m, rfl, hm⟩, rfl⟩
      · rintro ⟨j, fs, ⟨rfl, rfl⟩ | ⟨rfl, m, rfl, hm⟩, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨m, hm, rfl⟩)
    (fun _ => omega_mem_univ_succ 0)
    (fun _ x hx => by
      rcases mem_natF.mp hx with rfl | ⟨m, hm, rfl⟩
      · exact empty_mem_omega
      · exact vsucc_mem_omega hm)
    (fun _ S _ hS => by
      intro n hn
      have hI : Inductive (sep (omega : V) fun x => x ∈ˢ S) := by
        refine ⟨mem_sep.mpr ⟨empty_mem_omega, hS _ (mem_natF.mpr (Or.inl rfl))⟩,
          fun m hm => ?_⟩
        obtain ⟨hmo, hmS⟩ := mem_sep.mp hm
        exact mem_sep.mpr ⟨vsucc_mem_omega hmo, hS _ (mem_natF.mpr (Or.inr ⟨m, hmS, rfl⟩))⟩
      exact (mem_sep.mp (omega_subset_inductive hI n hn)).2)
    hleaf
    (fun ρp S j fs => by
      unfold natFits natFlds
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, m, rfl, hm⟩)
        · exact ⟨by omega, trivial⟩
        · exact ⟨by omega, ⟨by simpa using hm, trivial⟩⟩
      · rintro ⟨hj, hsp⟩
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · exact Or.inl ⟨rfl, spineFit_nil_iff.mp hsp⟩
        · simp only [if_neg (show (1 : Nat) ≠ 0 by decide)] at hsp
          match fs, hsp with
          | [m], hsp => exact Or.inr ⟨rfl, m, rfl, by simpa using hsp.1⟩)
    (fun _ h => absurd h (by decide))
    (fun _ _ j fs j' fs' hj hj' hl hl' h => by
      unfold natFlds at hl hl'
      unfold natInj at h
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
        rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
      · simp only [if_pos] at hl hl'
        rw [List.eq_nil_of_length_eq_zero hl, List.eq_nil_of_length_eq_zero hl']
        exact ⟨rfl, rfl⟩
      · simp only [if_pos, if_neg (show (1 : Nat) ≠ 0 by decide)] at h
        exact absurd h.symm (vsucc_ne_empty _)
      · simp only [if_pos, if_neg (show (1 : Nat) ≠ 0 by decide)] at h
        exact absurd h (vsucc_ne_empty _)
      · simp only [if_neg (show (1 : Nat) ≠ 0 by decide)] at hl hl' h
        match fs, fs', hl, hl' with
        | [m], [m'], _, _ =>
          have h' : vsucc m = vsucc m' := by simpa using h
          exact ⟨rfl, by rw [vsucc_inj h']⟩)
    (fun j hj ψ ρ fs hsp => by
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · have := spineFit_nil_iff.mp (by simpa [natFlds] using hsp)
        subst this
        show interp V ρ (acval (if (0 : Nat) = 0 then zn else sn) ψ) = natInj 0 []
        rw [if_pos rfl, hzero]; rfl
      · simp only [natFlds, if_neg (show (1 : Nat) ≠ 0 by decide)] at hsp
        match fs, hsp with
        | [m], hsp =>
          have hm : m ∈ˢ (omega : V) := by simpa using hsp.1
          show app (interp V ρ (acval (if (1 : Nat) = 0 then zn else sn) ψ)) m = natInj 1 [m]
          rw [if_neg (by decide), hsucc, natSuccV_app (V := V) hm]
          simp [natInj, natsucc])

/-! ## Recording a pinned block at its install -/

/-- **Record the lfp clause of a pinned one-member block at its former's
cons.**  The basis installs build the former's carrier as an existential
at the cons' leaf valuation (`declStep_preserves_of_basis_cons*`); this
adds the block's clause, whose leaf is the former's pinned leaf. -/
theorem nonempty_addLfp_of_exists {μ : ConLeche.CheckMode} {env : ConLeche.Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {c₀ : ConLeche.ConstantInfo}
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩, mp'.base2.acval = acval)
    (D : LfpDatum V) (hL : LfpClause acval D) (hst : LfpStored ⟨c₀ :: env.consts⟩ D) :
    Nonempty (EnvModelM V μ ⟨c₀ :: env.consts⟩) := by
  obtain ⟨mp', hac⟩ := h
  exact ⟨mp'.addLfp D (by rw [hac]; exact hL) hst⟩

/-- A one-member block without constructors is stored once its former is
the head of the cons. -/
theorem lfp0_stored {env : ConLeche.Env} {cv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    {w : (Name → Nat) → Nat} {F : V → V} {fits : V → Nat → List V → Prop}
    {inj : Nat → List V → V} {cn : Nat → Name} {flds : Nat → List AnnotTerm} :
    LfpStored (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env)
      (lfp0 cv.name w F fits inj 0 cn flds) := by
  refine ⟨fun mm hmm => ?_, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact ⟨cv, caps, by
    show (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env).find? cv.name = _
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl⟩

/-- A one-member block is stored at an environment holding its former and
its constructors. -/
theorem lfp0_stored_of {env : ConLeche.Env} {nm : Name} {w : (Name → Nat) → Nat} {F : V → V}
    {fits : V → Nat → List V → Prop} {inj : Nat → List V → V} {n : Nat} {cn : Nat → Name}
    {flds : Nat → List AnnotTerm}
    (hT : ∃ cv caps, env.find? nm = some (.indInfo cv caps))
    (hC : ∀ j, j < n → ∃ cv nP nF, env.find? (cn j) = some (.ctorInfo cv nP nF)) :
    LfpStored env (lfp0 nm w F fits inj n cn flds) := by
  refine ⟨fun mm hmm => ?_, fun _ _ j hj => hC j hj⟩
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact hT

end ConLeche.Model
