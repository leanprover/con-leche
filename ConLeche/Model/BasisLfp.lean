module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Annot.BlockLfpMono
import ConLeche.SetTheory.Derive.Omega
import ConLeche.SetTheory.Derive.Univ
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
    (fits : V → Nat → List V → Prop) (inj : Nat → List V → V) : LfpDatum V where
  names := [nm]
  k := 1
  N := 1
  w := w
  params := fun _ => []
  ids := fun _ _ => []
  u := fun _ _ => 0
  Φ := fun _ _ X _ => graph (fun _ => F (app (X 0) pt)) unitSet
  fits := fun _ _ X _ _ j fs => fits (app (X 0) pt) j fs
  inj := fun _ _ j fs => inj j fs

section Lfp0

variable {nm : Name} {w : (Name → Nat) → Nat} {F : V → V} {fits : V → Nat → List V → Prop}
  {inj : Nat → List V → V}

theorem lfp0_idx (ψ : Name → Nat) (ρp : Nat → V) (c : Nat) :
    (lfp0 nm w F fits inj).idx ψ ρp c = (unitSet : V) := idxSet_nil 0 ρp

theorem app_lfp0_Φ (ψ : Name → Nat) (ρp X : Nat → V) (c : Nat) :
    app ((lfp0 nm w F fits inj).Φ ψ ρp X c) pt = F (app (X 0) pt) :=
  app_graph pt_mem_unitSet

/-- **The carrier's only fibre is `C`**, when `C` is an `F`-closed set
of the level lying below every `F`-closed set of the level. -/
theorem lfp0_carrier {ψ : Name → Nat} {ρp : Nat → V} {C : V}
    (hmono : ∀ S S', S ⊆ˢ S' → F S ⊆ˢ F S')
    (hCu : C ∈ˢ (univ (w ψ) : V)) (hC : F C ⊆ˢ C)
    (hleast : ∀ S, S ∈ˢ (univ (w ψ) : V) → F S ⊆ˢ S → C ⊆ˢ S) :
    app ((lfp0 nm w F fits inj).carrier ψ ρp 0) pt = C := by
  let D := lfp0 nm w F fits inj
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
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = C ψ) :
    LfpClause acval (lfp0 nm w F fits inj) where
  kN := Nat.le_refl 1
  functor := fun ψ ρp _ => by
    have hI : (lfp0 nm w F fits inj).idx ψ ρp = fun _ => (unitSet : V) :=
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
    show interp V ρ (acval nm ψ) = app ((lfp0 nm w F fits inj).carrier ψ (consList [] ρ) 0) pt
    rw [hleaf ψ ρ, lfp0_carrier hmono (hCu ψ) (hC ψ) (hleast ψ)]

end Lfp0

/-! ## `Empty` and `False`: no constructor -/

/-- The zero-constructor datum at sort level `w`. -/
@[expose] noncomputable def emptyLfp (nm : Name) (w : Nat) : LfpDatum V :=
  lfp0 nm (fun _ => w) (fun _ => empty) (fun _ _ _ => False) (fun _ _ => pt)

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

/-! ## `PUnit`: one constructor, no field -/

/-- The one-constructor, no-field datum at sort level `w`. -/
@[expose] noncomputable def punitLfp (nm : Name) (w : (Name → Nat) → Nat) : LfpDatum V :=
  lfp0 nm w (fun _ => unitSet) (fun _ j fs => j = 0 ∧ fs = []) (fun _ _ => pt)

/-- **The clause of a one-constructor, no-field type** whose pinned
leaf is the unit set (`PUnit.{u}`, pinned to `bval .punit`). -/
theorem punitLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm : Name}
    (w : (Name → Nat) → Nat)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = unitSet) :
    LfpClause acval (punitLfp (V := V) nm w) :=
  lfp0_clause (C := fun _ => unitSet) (fun _ _ _ => Subset.refl _)
    (fun ψ _ _ => unitSet_mem_univ (w ψ))
    (fun _ x => by
      rw [mem_unitSet_iff]
      exact ⟨fun h => ⟨0, [], ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, _, h⟩ => h⟩)
    (fun ψ => unitSet_mem_univ (w ψ)) (fun _ => Subset.refl _)
    (fun _ _ _ hS => hS) hleaf

/-! ## `Nat`: zero and successor -/

/-- The zero/successor fibre, inside `ω`. -/
@[expose] noncomputable def natF (S : V) : V :=
  sep omega fun x => x = empty ∨ ∃ m, m ∈ˢ S ∧ m ∈ˢ (omega : V) ∧ x = vsucc m

/-- `Nat`'s constructors' fit: `zero` with no field, `succ` with one
field in the family (a numeral). -/
@[expose] def natFits (S : V) (j : Nat) (fs : List V) : Prop :=
  (j = 0 ∧ fs = []) ∨ (j = 1 ∧ ∃ m, fs = [m] ∧ m ∈ˢ S ∧ m ∈ˢ (omega : V))

/-- `Nat`'s injections: `zero ↦ ∅`, `succ m ↦ vsucc m`. -/
@[expose] noncomputable def natInj (j : Nat) (fs : List V) : V :=
  if j = 0 then empty else vsucc (fs.headD empty)

/-- The pinned `Nat`'s datum (sort `Type`, level `1`). -/
@[expose] noncomputable def natLfp (nm : Name) : LfpDatum V :=
  lfp0 nm (fun _ => 1) natF natFits natInj

theorem mem_natF {S x : V} :
    x ∈ˢ natF S ↔ x ∈ˢ (omega : V) ∧ (x = empty ∨ ∃ m, m ∈ˢ S ∧ m ∈ˢ (omega : V) ∧ x = vsucc m) :=
  mem_sep

/-- **The pinned `Nat`'s clause**: `ω` is the least fixed point of the
zero/successor operator (GRAPH-F's `natT_eq_omega`, re-derived here at
the clause's operator). -/
theorem natLfp_clause {acval : Name → (Name → Nat) → AnnotTerm} {nm : Name}
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (acval nm ψ) = omega) :
    LfpClause acval (natLfp (V := V) nm) :=
  lfp0_clause (C := fun _ => omega)
    (fun S S' hS x hx => by
      obtain ⟨hxo, h | ⟨m, hm, hmo, rfl⟩⟩ := mem_natF.mp hx
      · exact mem_natF.mpr ⟨hxo, Or.inl h⟩
      · exact mem_natF.mpr ⟨hxo, Or.inr ⟨m, hS m hm, hmo, rfl⟩⟩)
    (fun _ _ _ => univ_sep_mem (omega_mem_univ_succ 0))
    (fun S x => by
      rw [mem_natF]
      constructor
      · rintro ⟨-, rfl | ⟨m, hm, hmo, rfl⟩⟩
        · exact ⟨0, [], Or.inl ⟨rfl, rfl⟩, rfl⟩
        · exact ⟨1, [m], Or.inr ⟨rfl, m, rfl, hm, hmo⟩, rfl⟩
      · rintro ⟨j, fs, ⟨rfl, rfl⟩ | ⟨rfl, m, rfl, hm, hmo⟩, rfl⟩
        · exact ⟨empty_mem_omega, Or.inl rfl⟩
        · exact ⟨vsucc_mem_omega hmo, Or.inr ⟨m, hm, hmo, rfl⟩⟩)
    (fun _ => omega_mem_univ_succ 0)
    (fun _ x hx => (mem_natF.mp hx).1)
    (fun _ S _ hS => by
      intro n hn
      have hI : Inductive (sep (omega : V) fun x => x ∈ˢ S) := by
        refine ⟨mem_sep.mpr ⟨empty_mem_omega, hS _ (mem_natF.mpr ⟨empty_mem_omega, Or.inl rfl⟩)⟩,
          fun m hm => ?_⟩
        obtain ⟨hmo, hmS⟩ := mem_sep.mp hm
        exact mem_sep.mpr ⟨vsucc_mem_omega hmo,
          hS _ (mem_natF.mpr ⟨vsucc_mem_omega hmo, Or.inr ⟨m, hmS, hmo, rfl⟩⟩)⟩
      exact (mem_sep.mp (omega_subset_inductive hI n hn)).2)
    hleaf

/-! ## Recording a pinned block at its install -/

/-- **Record the lfp clause of a pinned one-member block at its former's
cons.**  The basis installs build the former's carrier as an existential
at the cons' leaf valuation (`declStep_preserves_of_basis_cons*`); this
adds the block's clause, whose leaf is the former's pinned leaf. -/
theorem nonempty_addLfp_of_exists {μ : ConLeche.CheckMode} {env : ConLeche.Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {c₀ : ConLeche.ConstantInfo}
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩, mp'.base2.acval = acval)
    (D : LfpDatum V) (hL : LfpClause acval D)
    (hst : ∀ mm, mm < D.k → ∃ cv caps,
      (⟨c₀ :: env.consts⟩ : ConLeche.Env).find? (D.member mm) = some (.indInfo cv caps)) :
    Nonempty (EnvModelM V μ ⟨c₀ :: env.consts⟩) := by
  obtain ⟨mp', hac⟩ := h
  exact ⟨mp'.addLfp D (by rw [hac]; exact hL) hst⟩

/-- A one-member block's member is the head former of the cons. -/
theorem lfp0_stored {env : ConLeche.Env} {cv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    {w : (Name → Nat) → Nat} {F : V → V} {fits : V → Nat → List V → Prop}
    {inj : Nat → List V → V} :
    ∀ mm, mm < (lfp0 cv.name w F fits inj).k → ∃ cv' caps',
      (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env).find?
        ((lfp0 cv.name w F fits inj).member mm) = some (.indInfo cv' caps') := by
  intro mm hmm
  obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
  exact ⟨cv, caps, by
    show (⟨.indInfo cv caps :: env.consts⟩ : ConLeche.Env).find? cv.name = _
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl⟩

/-! ## The field-free clauses in HOLE form (lane POSPROOF)

`ReadsHoles` (`Annot/BlockLfpMono.lean`) is the link HOLE2's clause must
carry: the fit relation IS the hole reading of the stored constructors.
The zero- and one-constructor field-free clauses above already have it
(no field, no result index; the index set is the unit set).  The pinned
`Nat`'s does NOT: its fit (`natFits`) asks `m ∈ ω` beside the hole
`m ∈ S`, a condition no field reading states — HOLE2 restates it (the
operator `{∅} ∪ {vsucc m ∣ m ∈ S}` has the same least fixed point `ω`). -/

/-- The hole reading of a one-member, unparameterized, unindexed block
with `n` field-free constructors. -/
@[expose] def holes0 (n : Nat) : HoleReading V where
  nctors := fun _ => n
  frame := fun _ ρp _ => ρp
  fields := fun _ _ _ => []
  resIdx := fun _ _ _ => []

theorem spineFit_nil_iff {ρ : Nat → V} {fs : List V} : SpineFit ρ [] fs ↔ fs = [] := by
  cases fs <;> simp [SpineFit]

/-- **`PUnit`'s recorded clause reads its constructor with holes.** -/
theorem punitLfp_readsHoles {nm : Name} {w : (Name → Nat) → Nat} :
    ReadsHoles (punitLfp (V := V) nm w) (holes0 1) := by
  intro ψ ρp _ X _ c _ t ht j fs
  have ht' : t ∈ˢ (unitSet : V) := by rw [← lfp0_idx ψ ρp c]; exact ht
  have ht := mem_unitSet_iff.mp ht'
  subst ht
  show (j = 0 ∧ fs = []) ↔ (j < 1 ∧ SpineFit ρp [] fs ∧ tupW 0 [] = pt)
  rw [spineFit_nil_iff, tupW_zero]
  exact ⟨fun ⟨hj, hf⟩ => ⟨by omega, hf, rfl⟩, fun ⟨hj, hf, _⟩ => ⟨by omega, hf⟩⟩

/-- **`Empty`'s and `False`'s recorded clauses read their (no)
constructors with holes.** -/
theorem emptyLfp_readsHoles {nm : Name} {w : Nat} :
    ReadsHoles (emptyLfp (V := V) nm w) (holes0 0) := by
  intro ψ ρp _ X _ c _ t _ j fs
  show False ↔ (j < 0 ∧ _)
  exact ⟨False.elim, fun h => absurd h.1 (Nat.not_lt_zero j)⟩

end ConLeche.Model
