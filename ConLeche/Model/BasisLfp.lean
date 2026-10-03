module

public import ConLeche.Model.Annot.EnvModelM
import ConLeche.SetTheory.Derive.Universe
public section

/-!
# The pinned basis types' LFP CLAUSES, by hand

The environment invariant's lfp clause (`Model/Annot/BlockLfp.lean`)
is PRODUCED by the uniform install for every block it checks.  The
pinned basis types are not installed by it: their denotations are
hand-written (`bval`, `SetModel/Value.lean`).  This file proves the
clause for them by hand, once, at their pinned leaves:

| type | sort | pinned leaf | operator's fibre at `S` | carrier |
|---|---|---|---|---|
| `Empty` | `1` | `bval .empty = ∅` | `∅` (no constructor) | `∅` |
| `False` | `0` | `bval .empty = ∅` | `∅` | `∅` |
| `Nat` | `1` | `bval .nat = ω` | `{∅} ∪ {vsucc m ∣ m ∈ S}` (inside `ω`) | `ω` |

All three are one component, unparameterized and unindexed, so they
share one datum shape (`lfp0`) and one clause theorem (`lfp0_clause`);
each type contributes its fibre function `F`, the carrier `C`, and
`C`'s LEASTNESS among the `F`-closed sets (for `Nat` that is `ω`'s own
induction, `omega_subset_inductive`).

`Eq` has its own datum (`eqLfp`): two parameters `α a`, the
index `b`, one field-less constructor, so its operator is constant — the
fibre over the index tuple is the truth value of `a = b` (`eqFib`) — and
its clause (`eqLfp_clause`) is recorded at `Eq.refl`'s cons
(`declBasisPB_eqK`, `Model/BasisEq.lean`).  `Quot` is argued rather than
proved: it is not an inductive for the recursor check (official installs
it as a builtin; no recursor is checked against it and no nested
occurrence goes through it), and coverage excludes it by name.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.SetModel
open ConLeche.SetTheory.Tower (towerSet_nil projS mkTower)

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
    (inj : Nat → List V → V) (n : Nat) (cn : Nat → Name)
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
  inj := fun _ _ j fs => inj j fs
  nctors := fun _ => n
  ctorName := fun _ j => cn j
  fields := fun _ _ j => flds j
  resIdx := fun _ _ _ => []

section Lfp0

variable {nm : Name} {w : (Name → Nat) → Nat} {F : V → V} {fits : V → Nat → List V → Prop}
  {inj : Nat → List V → V} {n : Nat} {cn : Nat → Name} {flds : Nat → List AnnotTerm}

theorem lfp0_idx (ψ : Name → Nat) (ρp : Nat → V) (c : Nat) :
    (lfp0 nm w F inj n cn flds).idx ψ ρp c = (unitSet : V) := idxSet_nil 0 ρp

theorem app_lfp0_Φ (ψ : Name → Nat) (ρp X : Nat → V) (c : Nat) :
    app ((lfp0 nm w F inj n cn flds).Φ ψ ρp X c) pt = F (app (X 0) pt) :=
  app_graph pt_mem_unitSet

/-- **The hole frame of a one-member unparameterized unindexed block**:
the family's only fibre at the one hole. -/
theorem lfp0_frame (ψ : Name → Nat) (ρp X : Nat → V) :
    (lfp0 nm w F inj n cn flds).frame ψ ρp X = cons (app (X 0) pt) ρp := by
  show consList [holeFam ρp [] fun vs => app (X 0) (tupW 0 vs)] ρp = cons (app (X 0) pt) ρp
  rw [consList_cons, consList_nil]
  show cons (app (X 0) (tupW 0 [])) ρp = _
  rw [tupW_zero]

/-- **The carrier's only fibre is `C`**, when `C` is an `F`-closed set
of the level lying below every `F`-closed set of the level. -/
theorem lfp0_carrier {ψ : Name → Nat} {ρp : Nat → V} {C : V}
    (hmono : ∀ S S', S ⊆ˢ S' → F S ⊆ˢ F S')
    (hCu : C ∈ˢ (univ (w ψ) : V)) (hC : F C ⊆ˢ C)
    (hleast : ∀ S, S ∈ˢ (univ (w ψ) : V) → F S ⊆ˢ S → C ⊆ˢ S) :
    app ((lfp0 nm w F inj n cn flds).carrier ψ ρp 0) pt = C := by
  let D := lfp0 nm w F inj n cn flds
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
    -- the hole reading: the fit IS the fields' fit at the hole
    (hholes : ∀ (ρp : Nat → V) S j fs, fits S j fs ↔ j < n ∧ SpineFit (cons S ρp) (flds j) fs)
    (hfitsMono : ∀ S S' j fs, S ⊆ˢ S' → fits S j fs → fits S' j fs)
    (hzero : ∀ ψ, w ψ = 0 → ∀ j fs, inj j fs = pt)
    (hinjI : ∀ ψ, w ψ ≠ 0 → ∀ j fs j' fs', j < n → j' < n →
      fs.length = (flds j).length → fs'.length = (flds j').length →
      inj j fs = inj j' fs' → j = j' ∧ fs = fs')
    (hctor : ∀ j, j < n → ∀ (ψ : Name → Nat) (ρ : Nat → V) (fs : List V),
      SpineFit (cons (C ψ) ρ) (flds j) fs → fs.foldl app (interp V ρ (acval (cn j) ψ)) = inj j fs)
    (hfok : ∀ (ψ : Name → Nat) (ρp : Nat → V) (S : V), w ψ ≠ 0 → S ∈ˢ (univ (w ψ) : V) →
      ∀ j, j < n → FieldsOkB (w ψ) (cons S ρp) (flds j))
    -- the fibre function is accessible with a bound of the level (at `Type`)
    (hFacc : ∀ ψ, w ψ ≠ 0 → ∃ A, A ∈ˢ (univ (w ψ) : V) ∧ ∀ S x, x ∈ˢ F S →
      ∃ (B : V) (g : V → V), B ⊆ˢ A ∧ (∀ b, b ∈ˢ B → g b ∈ˢ S) ∧
        ∀ S', (∀ b, b ∈ˢ B → g b ∈ˢ S') → x ∈ˢ F S') :
    LfpClause acval (lfp0 nm w F inj n cn flds) where
  kN := Nat.le_refl 1
  idxOk := fun _ _ _ _ _ => ⟨trivial, trivial⟩
  maps := fun ψ ρp _ => by
    have hI : (lfp0 nm w F inj n cn flds).idx ψ ρp = fun _ => (unitSet : V) :=
      funext (lfp0_idx ψ ρp)
    rw [hI]
    intro X hX m _
    exact graph_mem_famSpace fun _ _ =>
      hmaps ψ _ (famSpace_app (hX 0 Nat.one_pos) pt_mem_unitSet)
  acc := fun ψ ρp _ hw => by
    obtain ⟨A, hA, hF⟩ := hFacc ψ hw
    have hpt : ∀ c, (pt : V) ∈ˢ (lfp0 nm w F inj n cn flds).idx ψ ρp c := fun c => by
      rw [lfp0_idx]; exact pt_mem_unitSet
    refine ⟨A, hA, fun X _ m _ i hi x hx => ?_⟩
    rw [lfp0_idx] at hi
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_lfp0_Φ] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := hF _ x hx
    refine ⟨B, fun b => (0, pt, g b), hB, fun b hb => ⟨Nat.one_pos, hpt 0, hg b hb⟩,
      fun X' _ h' => ?_⟩
    rw [app_lfp0_Φ]
    exact hs _ fun b hb => (h' b hb).2.2
  fibre := fun ψ ρp _ X _ c _ t ht x => by
    rw [lfp0_idx] at ht
    obtain rfl := mem_unitSet_iff.mp ht
    rw [app_lfp0_Φ, hfib _ x]
    refine exists_congr fun j => exists_congr fun fs => and_congr_left fun _ => ?_
    show fits (app (X 0) pt) j fs ↔ (j < n ∧ SpineFit (LfpDatum.frame _ ψ ρp X) (flds j) fs ∧
      ∀ l, l < 0 → _)
    rw [lfp0_frame, hholes ρp]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, fun l hl => absurd hl (Nat.not_lt_zero l)⟩,
      fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  fitsMono := fun ψ ρp _ X Y _ _ hXY c _ t j fs hf => by
    obtain ⟨hj, hsp, -⟩ := hf
    rw [lfp0_frame] at hsp
    have hsub : app (X 0) pt ⊆ˢ app (Y 0) pt :=
      hXY 0 Nat.one_pos pt (by rw [lfp0_idx]; exact pt_mem_unitSet)
    obtain ⟨hj', hsp'⟩ := (hholes ρp (app (Y 0) pt) j fs).mp
      (hfitsMono _ _ j fs hsub ((hholes ρp (app (X 0) pt) j fs).mpr ⟨hj, hsp⟩))
    refine ⟨hj', ?_, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    rw [lfp0_frame]
    exact hsp'
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero hsa.length_eq
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero hsi.length_eq
    show interp V ρ (acval nm ψ) = app ((lfp0 nm w F inj n cn flds).carrier ψ (consList [] ρ) 0) pt
    rw [hleaf ψ ρ, lfp0_carrier hmono (hCu ψ) (hC ψ) (hleast ψ)]
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
  parsLen := fun _ _ _ => rfl
  parsSat := fun _ _ _ ρ _ => Sat_nil V ρ
  parsSatInv := fun _ _ _ ρ _ => Sat_nil V ρ
  resIdxFit := fun _ _ _ _ _ _ _ _ _ => trivial
  injNePt := fun _ _ h => absurd rfl h
  fieldsOk := fun ψ ρp _ hw X hX _ _ j hj => by
    show FieldsOkB (w ψ) ((lfp0 nm w F inj n cn flds).frame ψ ρp X) (flds j)
    rw [lfp0_frame]
    exact hfok ψ ρp _ hw (famSpace_app (hX 0 Nat.one_pos)
      (by rw [lfp0_idx]; exact pt_mem_unitSet)) j hj

end Lfp0

/-! ## `Empty` and `False`: no constructor -/

/-- The zero-constructor datum at sort level `w`. -/
@[expose] noncomputable def emptyLfp (nm : Name) (w : Nat) : LfpDatum V :=
  lfp0 nm (fun _ => w) (fun _ => empty) (fun _ _ => pt) 0 (fun _ => nm)
    (fun _ => [])

/-- **The clause of a zero-constructor type** whose pinned leaf is the
empty set — `Empty` at `w = 1`, `False` at `w = 0` (both pinned to
`bval .empty`). -/
theorem emptyLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm : Name} (w : Nat)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = empty) :
    LfpClause acval (emptyLfp (V := V) nm w) :=
  lfp0_clause (C := fun _ => empty) (fits := fun _ _ _ => False) (fun _ _ _ => Subset.refl _)
    (fun _ _ _ => empty_mem_univ w)
    (fun _ x => ⟨fun h => absurd h (not_mem_empty x), fun ⟨_, _, h, _⟩ => h.elim⟩)
    (fun _ => empty_mem_univ w) (fun _ => Subset.refl _)
    (fun _ _ _ _ x hx => absurd hx (not_mem_empty x)) hleaf
    (fun _ _ j _ => ⟨False.elim, fun h => absurd h.1 (Nat.not_lt_zero j)⟩)
    (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ => rfl)
    (fun _ _ j _ _ _ hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun _ _ _ _ _ j hj => absurd hj (Nat.not_lt_zero j))
    (fun _ _ => ⟨empty, empty_mem_univ w, fun _ x hx => absurd hx (not_mem_empty x)⟩)

theorem spineFit_nil_iff {ρ : Nat → V} {fs : List V} : SpineFit ρ [] fs ↔ fs = [] := by
  cases fs <;> simp [SpineFit]

/-! ## `Nat`: zero and successor -/

/-- The zero/successor fibre (the operator of the fields with
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
  lfp0 nm (fun _ => 1) natF natInj 2 (fun j => if j = 0 then zn else sn) natFlds

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

/-- The von Neumann successor is injective. -/
theorem vsucc_inj {m m' : V} (h : vsucc m = vsucc m') : m = m' := by
  have h1 : m ∈ˢ vsucc m' := h ▸ mem_vsucc.mpr (Or.inr rfl)
  have h2 : m' ∈ˢ vsucc m := h ▸ mem_vsucc.mpr (Or.inr rfl)
  rcases mem_vsucc.mp h1 with h1 | h1
  · rcases mem_vsucc.mp h2 with h2 | h2
    · exact (SetTheory.no_two_cycle h1 h2).elim
    · exact h2.symm
  · exact h1

/-- **The pinned `Nat`'s clause**: `ω` is the least fixed point of the
zero/successor operator, its constructors `∅` and `natSuccV`. -/
theorem natLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm zn sn : Name}
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = omega)
    (hzero : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval zn ψ) = empty)
    (hsucc : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval sn ψ) = natSuccV V) :
    LfpClause acval (natLfp (V := V) nm zn sn) :=
  lfp0_clause (C := fun _ => omega) (fits := natFits)
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
    (fun S S' j fs hSS' h => by
      rcases h with h | ⟨hj, m, hfs, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨hj, m, hfs, hSS' m hm⟩)
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
    (fun _ _ S _ hS j _ => by
      unfold natFlds
      split
      · trivial
      · exact ⟨by simp, fun _ => by simpa using hS, fun _ _ => trivial⟩)
    -- the successor's support is its predecessor
    (fun _ _ => by
      refine ⟨unitSet, unitSet_mem_univ 1, fun S x hx => ?_⟩
      rcases mem_natF.mp hx with rfl | ⟨m, hm, rfl⟩
      · exact ⟨empty, fun _ => empty, empty_subset _, fun b hb => absurd hb (not_mem_empty b),
          fun _ _ => mem_natF.mpr (Or.inl rfl)⟩
      · exact ⟨unitSet, fun _ => m, Subset.refl _, fun _ _ => hm,
          fun _ h => mem_natF.mpr (Or.inr ⟨m, h pt pt_mem_unitSet, rfl⟩)⟩)

/-! ## `Eq`: two parameters, one index, one field-less constructor

`Eq.{u} {α : Sort u} (a : α) : α → Prop` is the one pinned block with
parameters and an index.  Its constructor `refl` has no field, so its operator is
CONSTANT in the tuple: at the parameter frame `ρp` (`a` at `0`, `α` at
`1`) the fibre over the index tuple `t` is the truth value of
`a = projS 0 t` (`eqFib`), and the least fixed point is that constant.
The index tuple is at `α`'s level (`tupW`): at `Prop` (level `0`) it
collapses to the point, where `a` and `b` are the point too. -/

/-- `Eq`'s fibre at the parameter frame `ρp` over the index tuple `t`:
`a = t.0`, as a truth value. -/
@[expose] noncomputable def eqFib (ρp : Nat → V) (t : V) : V := truthVal (ρp 0 = projS 0 t)

/-- **`Eq`'s datum**: parameters `α : Sort lv` and `a : α`, the index
`b : α`, the constructor `cn` with no field and the result index `a`
(the variable `1` below the one hole). -/
@[expose] noncomputable def eqLfp (nm cn : Name) (lv : (Name → Nat) → Nat) : LfpDatum V where
  names := [nm]
  k := 1
  N := 1
  w := fun _ => 0
  params := fun ψ => [.sort (lv ψ), .bvar 0]
  pars := fun _ ψ => [.sort (lv ψ), .bvar 0]
  ids := fun _ _ => [.bvar 1]
  u := fun _ ψ => lv ψ
  Φ := fun ψ ρp _ _ => graph (eqFib ρp) (idxSet (lv ψ) ρp [.bvar 1])
  inj := fun _ _ _ _ => pt
  nctors := fun _ => 1
  ctorName := fun _ _ => cn
  fields := fun _ _ _ => []
  resIdx := fun _ _ _ => [.bvar 1]

section EqLfp

variable {nm cn : Name} {lv : (Name → Nat) → Nat}

/-- `Eq`'s operator is constant, so its carrier IS the operator's value. -/
theorem app_eqLfp_carrier {ψ : Name → Nat} {ρp : Nat → V} {t : V}
    (ht : t ∈ˢ idxSet (lv ψ) ρp [.bvar 1]) :
    app ((eqLfp (V := V) nm cn lv).carrier ψ ρp 0) t = eqFib ρp t := by
  let D := eqLfp (V := V) nm cn lv
  let K : Nat → V := fun _ => graph (eqFib ρp) (idxSet (lv ψ) ρp [.bvar 1])
  have hK : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) K := fun _ _ =>
    graph_mem_famSpace fun _ _ => by
      show _ ∈ˢ (univ 0 : V); rw [univ_zero]; exact truthVal_mem_univZero _
  have hcl : IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) K :=
    ⟨hK, TupleLe.refl _ _ _⟩
  have hmono : MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) :=
    fun _ _ _ _ _ => TupleLe.refl _ _ _
  have h1 := lfpTuple_le hcl 0 Nat.one_pos t ht
  have h2 := lfpTuple_closed ⟨K, hcl⟩ hmono 0 Nat.one_pos t ht
  have hKt : app (K 0) t = eqFib ρp t := app_graph ht
  rw [← hKt]
  exact Subset.antisymm h1 h2

/-- The index tuple's first projection is the index — at `Prop` both are
the point. -/
theorem eqFib_tupW {ψ : Name → Nat} {ρ : Nat → V} {A a b : V}
    (hA : A ∈ˢ (univ (lv ψ) : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    eqFib (consList [A, a] ρ) (tupW (lv ψ) [b]) = eqv a b := by
  unfold eqFib eqv
  refine truthVal_congr ?_
  show a = projS 0 (tupW (lv ψ) [b]) ↔ a = b
  by_cases hu : lv ψ = 0
  · rw [hu, univ_zero] at hA
    rw [hu, tupW_zero, eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
    show pt = sfst pt ↔ pt = pt
    rw [sfst_pt]
  · rw [tupW_pos hu]
    show a = sfst (spair b (mkTower [])) ↔ a = b
    rw [sfst_spair]

/-- **`Eq`'s clause**, from its former's value at a fitting spine (the
truth value of the equation) and its constructor's (the point). -/
theorem eqLfp_clause {acval : Name → (Name → Nat) → AnnotTerm}
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V) (A a b : V), A ∈ˢ (univ (lv ψ) : V) →
      a ∈ˢ A → b ∈ˢ A → [A, a, b].foldl app (interp V ρ (acval nm ψ)) = eqv a b)
    (hctor : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval cn ψ) = pt) :
    LfpClause acval (eqLfp (V := V) nm cn lv) where
  kN := Nat.le_refl 1
  idxOk := fun ψ ρp hs _ _ => by
    have hA : ρp 1 ∈ˢ (univ (lv ψ) : V) := by
      have := hs 1 (.sort (lv ψ)) rfl
      simpa using this
    exact ⟨⟨by simp, fun _ => hA, fun _ _ => trivial⟩, ⟨hA, fun _ _ => trivial⟩⟩
  maps := fun ψ ρp _ X _ _ _ =>
    graph_mem_famSpace fun _ _ => by
      show _ ∈ˢ (univ 0 : V); rw [univ_zero]; exact truthVal_mem_univZero _
  acc := fun _ _ _ hw => absurd rfl hw
  fibre := fun ψ ρp _ X _ c _ t ht x => by
    have hfr : (eqLfp (V := V) nm cn lv).frame ψ ρp X 1 = ρp 0 := by
      show consList [_] ρp 1 = ρp 0
      rw [consList_cons, consList_nil]; rfl
    have hfits : ∀ j fs, (j = 0 ∧ fs = [] ∧ ρp 0 = projS 0 t) ↔
        (eqLfp (V := V) nm cn lv).HFits ψ ρp X t c j fs := by
      intro j fs
      show (j = 0 ∧ fs = [] ∧ ρp 0 = projS 0 t) ↔ (j < 1 ∧ SpineFit _ [] fs ∧
        ∀ l, l < 1 → ∃ e, ([AnnotTerm.bvar 1] : List AnnotTerm)[l]? = some e ∧
          interp V (consList fs ((eqLfp (V := V) nm cn lv).frame ψ ρp X)) e = projS l t)
      rw [spineFit_nil_iff]
      constructor
      · rintro ⟨rfl, rfl, h⟩
        refine ⟨Nat.one_pos, rfl, fun l hl => ?_⟩
        obtain rfl : l = 0 := Nat.lt_one_iff.mp hl
        refine ⟨_, rfl, ?_⟩
        rw [consList_nil, interp_bvar, hfr, h]
      · rintro ⟨hj, rfl, h⟩
        obtain ⟨e, he, hv⟩ := h 0 Nat.one_pos
        obtain rfl := Option.some.inj he.symm
        rw [consList_nil, interp_bvar, hfr] at hv
        exact ⟨Nat.lt_one_iff.mp hj, rfl, hv⟩
    show x ∈ˢ app (graph (eqFib ρp) _) t ↔ _
    rw [app_graph (show t ∈ˢ idxSet (lv ψ) ρp [.bvar 1] from ht)]
    unfold eqFib
    rw [mem_truthVal]
    exact ⟨fun ⟨h, hx⟩ => ⟨0, [], (hfits 0 []).mp ⟨rfl, rfl, h⟩, hx⟩,
      fun ⟨j, fs, hf, hx⟩ => ⟨((hfits j fs).mpr hf).2.2, hx⟩⟩
  fitsMono := fun ψ ρp _ X Y _ _ _ c _ t j fs hf => by
    have hfr : ∀ Z, (eqLfp (V := V) nm cn lv).frame ψ ρp Z 1 = ρp 0 := by
      intro Z
      show consList [_] ρp 1 = ρp 0
      rw [consList_cons, consList_nil]; rfl
    obtain ⟨hj, hsp, hidx⟩ := hf
    have hfs : fs = [] := spineFit_nil_iff.mp hsp
    subst hfs
    refine ⟨hj, trivial, fun l hl => ?_⟩
    obtain ⟨e, he, hv⟩ := hidx l hl
    refine ⟨e, he, ?_⟩
    have hl0 : l = 0 := Nat.lt_one_iff.mp hl
    subst hl0
    obtain rfl := Option.some.inj he.symm
    rw [consList_nil, interp_bvar, hfr] at hv ⊢
    exact hv
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
    match as, is, hsa, hsi with
    | [A, a], [b], ⟨hA, ha, _⟩, ⟨hb, _⟩ =>
      have hA' : A ∈ˢ (univ (lv ψ) : V) := by simpa using hA
      have ha' : a ∈ˢ A := by simpa [cons] using ha
      have hb' : b ∈ˢ A := by simpa [consList_cons, consList_nil, cons] using hb
      show ([A, a] ++ [b]).foldl app (interp V ρ (acval nm ψ))
        = app ((eqLfp (V := V) nm cn lv).carrier ψ (consList [A, a] ρ) 0) (tupW (lv ψ) [b])
      rw [app_eqLfp_carrier (tupW_mem (u := lv ψ) (show SpineFit (consList [A, a] ρ)
        [AnnotTerm.bvar 1] [b] from ⟨hb, trivial⟩)), eqFib_tupW hA' ha' hb']
      exact hleaf ψ ρ A a b hA' ha' hb'
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ hw => absurd rfl hw
  injNePt := fun _ hw => absurd rfl hw
  fieldsOk := fun _ _ _ hw => absurd rfl hw
  ctor := fun _ _ _ ψ ρ as fs _ _ _ _ => by
    show (as ++ fs).foldl app (interp V ρ (acval cn ψ)) = pt
    rw [hctor]
    exact foldl_app_pt' _
  parsLen := fun _ _ _ => rfl
  parsSat := fun _ _ _ _ h => h
  parsSatInv := fun _ _ _ _ h => h
  resIdxFit := fun ψ ρp hs _ _ _ _ fs hsp => by
    -- the result index `a` fits the index telescope `α`: `a : α` is a parameter
    have hfs : fs = [] := spineFit_nil_iff.mp hsp
    subst hfs
    have ha : ρp 0 ∈ˢ ρp 1 := by simpa using hs 0 (.bvar 0) rfl
    show SpineFit ρp [AnnotTerm.bvar 1]
      [interp V (consList [] ((eqLfp (V := V) nm cn lv).frame ψ ρp
        ((eqLfp (V := V) nm cn lv).carrier ψ ρp))) (.bvar 1)]
    refine ⟨?_, trivial⟩
    have hfr : (eqLfp (V := V) nm cn lv).frame ψ ρp
        ((eqLfp (V := V) nm cn lv).carrier ψ ρp) 1 = ρp 0 := by
      show consList [_] ρp 1 = ρp 0
      rw [consList_cons, consList_nil]; rfl
    rw [consList_nil, interp_bvar, hfr, interp_bvar]
    exact ha

/-- `Eq`'s former reads as its hole telescope (M4). -/
theorem eqLfp_reads {acval : Name → (Name → Nat) → AnnotTerm} {env : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    (hf : env.find? nm = some (.indInfo cv caps))
    (hty : ∀ ψ, denoteMeta acval env ψ 0 cv.type = some
      (.pi 0 1 (.sort (lv ψ)) (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0))))) :
    LfpReads acval env (eqLfp (V := V) nm cn lv) := fun mm hmm => by
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact ⟨cv, caps, hf, fun ψ => ⟨[(0, 1, .sort (lv ψ)), (0, 1, .bvar 0), (0, 1, .bvar 1)],
    hty ψ, rfl, fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact Nat.one_ne_zero⟩⟩

/-- `Eq` is stored at an environment holding its former and constructor. -/
theorem eqLfp_stored {env : ConLeche.Env}
    (hT : ∃ cv caps, env.find? nm = some (.indInfo cv caps))
    (hC : ∃ cv nP nF, env.find? cn = some (.ctorInfo cv nP nF)) :
    LfpStored env (eqLfp (V := V) nm cn lv) := by
  refine ⟨fun mm hmm => ?_, fun _ _ _ _ => hC⟩
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact hT

end EqLfp

/-! ## Recording a pinned block at its install -/

/-- **A one-member unparameterized unindexed block's former reads as its
sort** (M4: the hole telescope is empty). -/
theorem lfp0_reads {acval : Name → (Name → Nat) → AnnotTerm} {env : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps} {nm : Name} {w : (Name → Nat) → Nat}
    {F : V → V} {inj : Nat → List V → V} {n : Nat}
    {cn : Nat → Name} {flds : Nat → List AnnotTerm}
    (hf : env.find? nm = some (.indInfo cv caps))
    (hty : ∀ ψ, denoteMeta acval env ψ 0 cv.type = some (.sort (w ψ))) :
    LfpReads acval env (lfp0 nm w F inj n cn flds) := fun mm hmm => by
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact ⟨cv, caps, hf, fun ψ => ⟨[], hty ψ, rfl, fun _ h => nomatch h⟩⟩

/-- **A one-member unparameterized unindexed block's constructors read as
their hole telescopes** (M2): the canonical abstraction has no parameter,
and the member's hole is the variable `0`. -/
theorem lfp0_ctorReads {acval : Name → (Name → Nat) → AnnotTerm} {env : ConLeche.Env}
    {nm : Name} {w : (Name → Nat) → Nat}
    {F : V → V} {inj : Nat → List V → V} {n : Nat}
    {cn : Nat → Name} {flds : Nat → List AnnotTerm}
    {cvT : ConLeche.ConstantVal} {capsT : ConLeche.IndCaps}
    (hfT : env.find? nm = some (.indInfo cvT capsT))
    (htyT : ∀ ψ, ∃ Ty, denoteMeta acval env ψ 0 cvT.type = some Ty)
    (h : ∀ j, j < n → ∃ cv nF, env.find? (cn j) = some (.ctorInfo cv 0 nF) ∧
      cv.type.hasFvar = false ∧
      (∃ cvm caps, env.find? nm = some (.indInfo cvm caps) ∧ cvm.levelParams = cv.levelParams) ∧
      ∃ A, ConLeche.nestCanonCrest [nm] (cv.levelParams.map .param) 0 cv.type = some A ∧
      A.nestOcc [nm] 0 0 = false ∧
      ∀ ψ : Name → Nat, (flds j).length = nF ∧ ∃ ab : List (Nat × Nat × AnnotTerm),
        denoteMeta acval env ψ 1 A = some (mkPisAV ab (.bvar nF)) ∧ ab.map (·.2.2) = flds j) :
    LfpCtorReads acval env (lfp0 nm w F inj n cn flds) := by
  refine ⟨rfl, fun c hc j hj => ?_⟩
  obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
  obtain ⟨cv, nF, hf, hcf, ⟨cvm, caps, hfm, hl⟩, A, hA, hocc, hrd⟩ := h j hj
  refine ⟨cv, 0, nF, hf, hcf, fun mm hmm => ?_,
    fun _ _ _ _ _ ρ _ => by rw [List.take_zero]; exact Sat_nil V ρ, A, hA, hocc, fun ψ => ?_⟩
  · obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
    exact ⟨cvm, caps, hfm, hl⟩
  · obtain ⟨hlen, ab, hab, hmap⟩ := hrd ψ
    obtain ⟨Ty, hTy⟩ := htyT ψ
    refine ⟨rfl, hlen, ab, [Ty], ?_, by rw [← hlen, ← hmap, List.length_map], rfl,
      fun mm hmm => ?_, ?_⟩
    · show denoteMeta acval env ψ 1 A = _
      rw [hab]
      simp [lfp0]
    · obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
      exact ⟨cvT, capsT, cvT.type, hfT, rfl, hTy⟩
    · show FieldsEqOn V _ (ab.map (·.2.2)) (flds j)
      rw [hmap]
      exact FieldsEqOn.refl _ _

/-- A one-member block without constructors is stored once its former is
the head of the cons. -/
theorem lfp0_stored {env : ConLeche.Env} {cv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    {w : (Name → Nat) → Nat} {F : V → V}
    {inj : Nat → List V → V} {cn : Nat → Name} {flds : Nat → List AnnotTerm} :
    LfpStored (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env)
      (lfp0 cv.name w F inj 0 cn flds) := by
  refine ⟨fun mm hmm => ?_, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact ⟨cv, caps, by
    show (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env).find? cv.name = _
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl⟩

/-- A one-member block is stored at an environment holding its former and
its constructors. -/
theorem lfp0_stored_of {env : ConLeche.Env} {nm : Name} {w : (Name → Nat) → Nat} {F : V → V}
    {inj : Nat → List V → V} {n : Nat} {cn : Nat → Name}
    {flds : Nat → List AnnotTerm}
    (hT : ∃ cv caps, env.find? nm = some (.indInfo cv caps))
    (hC : ∀ j, j < n → ∃ cv nP nF, env.find? (cn j) = some (.ctorInfo cv nP nF)) :
    LfpStored env (lfp0 nm w F inj n cn flds) := by
  refine ⟨fun mm hmm => ?_, fun _ _ j hj => hC j hj⟩
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact hT

end ConLeche.Model
