module

public import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Semantics.Tower.BlockTower

public section

/-!
# The HOLE OPERATOR of an lfp datum

Charter item 2: a block's right-hand-side operator IS the interpretation
of its constructors' fields with holes.  `LfpDatum` records those fields
(`fields`, `resIdx`) and reads them at the hole frame (`frame`,
`HFits`).  This module spells the operator as a TERM — the block
operator of `BlockTower.lean` at its hole chains (`LfpDatum.holeOp`) — and proves that it is what
the clause says it is:

* **its fibre is the hole fit** (`LfpDatum.holeOp_fibre`): component
  `c`'s fibre at `(X, t)` is the injections of the spines `HFits`-fitting
  one of `c`'s constructors — with no field classification: the hole
  terms' frame IS the model's hole frame (`LfpDatum.holeTmFrame_frame`);
* **its chains are graded** at every tuple of the tuple space when the
  fields are graded at the hole frame (`LfpDatum.holeChains_ok`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (projS)

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## λ-towers of graphs, as terms and under lifts -/

/-- A graph-regime λ-tower term (every binder at a nonzero bit) reads as
the λ-tower of graphs of its body's readings. -/
theorem interp_mkLamsAV_pos {b : AnnotTerm} {v : Nat} (hv : v ≠ 0) :
    ∀ (Ts : List AnnotTerm) (ρ : Nat → V),
      interp V ρ (mkLamsAV (Ts.map (v, ·)) b) = holeFam ρ Ts fun vs => interp V (consList vs ρ) b
  | [], _ => rfl
  | T :: Ts, ρ => by
    show lamR v (interp V ρ T) (fun a => interp V (cons a ρ) (mkLamsAV (Ts.map (v, ·)) b)) = _
    unfold holeFam
    rw [lamR_pos hv, lamR_pos Nat.one_ne_zero]
    congr 1
    funext a
    exact interp_mkLamsAV_pos hv Ts (cons a ρ)

/-- `interp_mkLamsAV_pos` at the bit `1`. -/
theorem interp_mkLamsAV_one {b : AnnotTerm} (Ts : List AnnotTerm) (ρ : Nat → V) :
    interp V ρ (mkLamsAV (Ts.map (1, ·)) b) = holeFam ρ Ts fun vs => interp V (consList vs ρ) b :=
  interp_mkLamsAV_pos Nat.one_ne_zero Ts ρ

theorem holeFam_liftFields (n : Nat) :
    ∀ (Ts : List AnnotTerm) (k : Nat) (σ : Nat → V) (g : List V → V),
      holeFam σ (liftFields n k Ts) g = holeFam (shiftE n k σ) Ts g
  | [], _, _, _ => rfl
  | T :: Ts, k, σ, g => by
    simp only [liftFields_cons, holeFam, interp_liftN]
    congr 1
    funext a
    rw [holeFam_liftFields n Ts (k + 1) (cons a σ), cons_shiftE]

theorem holeFam_append :
    ∀ (A B : List AnnotTerm) (ρ : Nat → V) (g : List V → V),
      holeFam ρ (A ++ B) g = holeFam ρ A fun as => holeFam (consList as ρ) B fun bs => g (as ++ bs)
  | [], _, _, _ => rfl
  | T :: A, B, ρ, g => by
    show lamR 1 _ _ = lamR 1 _ _
    congr 1
    funext a
    exact holeFam_append A B (cons a ρ) fun vs => g (a :: vs)

theorem holeFam_congr :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {g g' : List V → V},
      (∀ vs, SpineFit ρ Ts vs → g vs = g' vs) → holeFam ρ Ts g = holeFam ρ Ts g'
  | _, [], _, _, h => h [] trivial
  | ρ, T :: Ts, g, g', h => by
    show lamR 1 _ _ = lamR 1 _ _
    exact lamR_congr fun a ha => holeFam_congr fun vs hvs => h (a :: vs) ⟨ha, hvs⟩

/-- A λ-tower of graphs applied to a fitting prefix is the λ-tower of the
rest at the extended frame. -/
theorem holeFam_foldl_prefix :
    ∀ {ρ : Nat → V} {A : List AnnotTerm} {ps : List V} (B : List AnnotTerm) (g : List V → V),
      SpineFit ρ A ps →
      ps.foldl app (holeFam ρ (A ++ B) g) = holeFam (consList ps ρ) B fun bs => g (ps ++ bs)
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim
  | ρ, T :: A, p :: ps, B, g, h => by
    show ps.foldl app (app (lamR 1 (interp V ρ T) _) p) = _
    rw [app_lamR_pos (by decide) h.1]
    exact holeFam_foldl_prefix B (fun vs => g (p :: vs)) h.2

/-! ## The hole operator of an lfp datum -/

namespace LfpDatum

variable (D : LfpDatum V)

/-- **Member `m`'s hole term** (`holeTmAV` at the member's index
telescope). -/
@[expose] def holeTm (ψ : Name → Nat) (m : Nat) : AnnotTerm :=
  holeTmAV (D.u m ψ) m (D.ids m ψ)

/-- **The hole chains**: every constructor's fields with holes and result
index readings, substituted by the hole terms. -/
@[expose] def holeChains (ψ : Name → Nat) : Nat → List (List AnnotTerm) :=
  holeChs D.k (D.holeTm ψ) (fun c => (D.ids c ψ).length)
    (fun c => (List.range (D.nctors c)).map (D.fields ψ c))
    (fun c => (List.range (D.nctors c)).map (D.resIdx ψ c))

/-- **The hole operator**: the block operator at the hole chains. -/
@[expose] noncomputable def holeOp (ψ : Name → Nat) (ρp : Nat → V) : (Nat → V) → Nat → V :=
  blockPhiG D.N (D.w ψ) ρp (fun c => D.u c ψ) (fun c => D.ids c ψ) (D.holeChains ψ)

/-- The frame the hole chains are read at: the parameter frame below the
hole terms' values at `(t, Y)`. -/
@[expose] noncomputable def holeTmFrame (ψ : Name → Nat) (ρp : Nat → V) (t Y : V) : Nat → V :=
  substE V (holeTau D.k (D.holeTm ψ)) 0 (cons t (cons Y ρp))

variable {D}

/-- **The hole term's value** is the model's hole value at `Y`'s
components: the λ-tower over the member's index telescope of `Y`'s
component at the index tuple. -/
theorem interp_holeTm {ψ : Name → Nat} {ρp : Nat → V} {m : Nat}
    (hbd : D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ)) (t Y : V) :
    interp V (cons t (cons Y ρp)) (D.holeTm ψ m)
      = holeFam ρp (D.ids m ψ) fun is => app (projS m Y) (tupW (D.u m ψ) is) := by
  have hsh : shiftE 2 0 (cons t (cons Y ρp)) = ρp := by
    rw [show (2 : Nat) = 1 + 1 by rfl, shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
  unfold holeTm holeTmAV
  rw [interp_mkLamsAV_one, holeFam_liftFields, hsh]
  refine holeFam_congr fun is his => ?_
  have hlenI : is.length = (D.ids m ψ).length := his.length_eq
  have hY' : consList is (cons t (cons Y ρp)) ((D.ids m ψ).length + 1) = Y := by
    have := Xframe_X ρp is t Y
    rwa [hlenI] at this
  have his' : SpineFit (cons t (cons Y ρp)) (liftFields 2 0 (D.ids m ψ)) is := by
    rw [spineFit_liftFields, hsh]; exact his
  have hbd' : D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) (cons t (cons Y ρp))
      (liftFields 2 0 (D.ids m ψ)) := fun hu => by
    rw [fieldsBound_liftFields, hsh]; exact hbd hu
  have htv := mkTowerGo_interp hbd' his'
  rw [interp_app, projAV_interp, interp_bvar, hY', htv]
  rfl

/-- The hole terms' frame is the parameter frame below the hole terms'
values. -/
theorem holeTmFrame_eq {ψ : Name → Nat} {ρp : Nat → V} (t Y : V) :
    D.holeTmFrame ψ ρp t Y
      = consList ((List.range D.k).map fun m => interp V (cons t (cons Y ρp)) (D.holeTm ψ m)) ρp :=
  substE_holeTau fun _ _ => rfl

/-- **The hole terms' frame IS the model's hole frame** at the tuple of
`Y`'s components. -/
theorem holeTmFrame_frame {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {t Y : V}
    (hXY : ∀ m, m < D.k → X m = projS m Y)
    (hbd : ∀ m, m < D.k → D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ)) :
    D.holeTmFrame ψ ρp t Y = D.frame ψ ρp X := by
  rw [holeTmFrame_eq]
  unfold frame
  congr 1
  refine List.map_congr_left fun m hm => ?_
  have hm' := List.mem_range.mp hm
  show interp V (cons t (cons Y ρp)) (D.holeTm ψ m) = D.holeVal ψ ρp X m
  rw [interp_holeTm (hbd m hm')]
  unfold holeVal
  rw [hXY m hm']

/-- The per-member facts the hole terms need at a parameter frame: each
member's index telescope is bounded. -/
@[expose] def HoleTmOk (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) : Prop :=
  ∀ m, m < D.k → D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ)

/-- **The hole operator's fibre is the hole fit** (see the module
docstring): at an index tuple of the component, the injections of the
spines fitting a constructor's fields with holes at the model's hole
frame, whose result index readings there are the index tuple's
components.  The tuple `X` is arbitrary. -/
theorem holeOp_fibre {ψ : Name → Nat} {ρp : Nat → V} (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (X : Nat → V) {c : Nat}
    (hres : ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length)
    {t : V} (ht : t ∈ˢ D.idx ψ ρp c) (x : V) :
    x ∈ˢ app (D.holeOp ψ ρp X c) t ↔
      ∃ j fs, D.HFits ψ ρp X t c j fs ∧
        x = (if D.w ψ = 0 then (pt : V) else ConLeche.SetTheory.Tower.inj j (ConLeche.SetTheory.Tower.mkTower (fs ++ [pt]))) := by
  have hag : substE V (holeTau D.k (D.holeTm ψ)) 0 (cons t (cons (ndMkTowerSet X 0 D.N) ρp))
      = D.frame ψ ρp X :=
    holeTmFrame_frame (fun m hm => (projS_ndMkTowerSet_zero (by omega)).symm) hok
  unfold holeOp
  rw [app_blockPhi (uf := fun c => D.u c ψ) (Idss := fun c => D.ids c ψ) ht]
  unfold holeChains
  rw [blockStepG_holeChs_mem_iff]
  simp only [List.length_map, List.length_range]
  have hgF : ∀ j, j < D.nctors c →
      ((List.range (D.nctors c)).map (D.fields ψ c)).getD j [] = D.fields ψ c j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
  have hgE : ∀ j, j < D.nctors c →
      ((List.range (D.nctors c)).map (D.resIdx ψ c)).getD j [] = D.resIdx ψ c j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
  refine exists_congr fun j => exists_congr fun fs => ?_
  constructor
  · rintro ⟨hj, hsp, hidx, rfl⟩
    rw [hgF j hj, hag] at hsp
    rw [hgE j hj, hag] at hidx
    refine ⟨⟨hj, hsp, fun l hl => ?_⟩, rfl⟩
    have hl' : l < (D.resIdx ψ c j).length := by rw [hres j hj]; exact hl
    refine ⟨(D.resIdx ψ c j)[l], List.getElem?_eq_getElem hl', ?_⟩
    have := hidx l hl
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some] at this
  · rintro ⟨⟨hj, hsp, hidx⟩, rfl⟩
    refine ⟨hj, ?_, fun l hl => ?_, rfl⟩
    · rw [hgF j hj, hag]; exact hsp
    · rw [hgE j hj, hag]
      obtain ⟨e, he, hev⟩ := hidx l hl
      rw [List.getD_eq_getElem?_getD, he, Option.getD_some]
      exact hev

/-- **The hole chains are graded** at every tuple of the family space
(`BlockChainsOkG`), when the fields with holes and the result index
readings are graded at the model's hole frame of every tuple of the
tuple space. -/
theorem holeChains_ok {ψ : Name → Nat} {ρp : Nat → V} (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (hIall : BlockIdxOk (V := V) D.N (fun c => D.u c ψ) ρp (fun c => D.ids c ψ))
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length)
    (hF : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N → ∀ j, j < D.nctors c →
      FieldsOkB (D.w ψ) (D.frame ψ ρp X) (D.fields ψ c j) ∧
      ∀ fs, SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs →
        ∀ e ∈ D.resIdx ψ c j, WellDenoted V (consList fs (D.frame ψ ρp X)) e) :
    BlockChainsOkG D.N (D.w ψ) ρp (fun c => D.u c ψ) (fun c => D.ids c ψ) (D.holeChains ψ) := by
  intro Y hY m hm t ht Fs hFs
  have hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) (fun c => projS c Y) := fun c hc => by
    rw [← lfpFamSpace_eq']; exact projS_mem_famsSpaceB hc hY
  have hag : substE V (holeTau D.k (D.holeTm ψ)) 0 (cons t (cons Y ρp))
      = D.frame ψ ρp fun c => projS c Y :=
    holeTmFrame_frame (fun _ _ => rfl) hok
  have hH : ∀ m', m' < D.k → WellDenoted V (cons t (cons Y ρp)) (D.holeTm ψ m') := fun m' hm' =>
    holeTmAV_wellDenoted hIall (by omega) hY t
  unfold holeChains holeChs at hFs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hFs
  simp only [List.length_map, List.length_range] at hj
  have hj' : j < D.nctors m := List.mem_range.mp hj
  have hgF : (((List.range (D.nctors m)).map (D.fields ψ m)).map
      (holeEntsAV D.k (D.holeTm ψ) 0)).getD j [] = holeEntsAV D.k (D.holeTm ψ) 0 (D.fields ψ m j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hj']
    rfl
  have hgE : ((List.range ((List.range (D.nctors m)).map (D.fields ψ m)).length).map fun j =>
      holeEqsAV D.k (D.holeTm ψ) (D.ids m ψ).length
        (((List.range (D.nctors m)).map (D.fields ψ m)).getD j []).length
        (((List.range (D.nctors m)).map (D.resIdx ψ m)).getD j [])).getD j []
      = holeEqsAV D.k (D.holeTm ψ) (D.ids m ψ).length (D.fields ψ m j).length (D.resIdx ψ m j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hj')]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj',
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj']
    rfl
  rw [hgF, hgE]
  obtain ⟨hFok, hEok⟩ := hF _ hX m hm j hj'
  refine FieldsOkB_append_idxEq ?_ fun bs hbs => ?_
  · have := (FieldsOkB_holeEntsAV (w := D.w ψ) hH (D.fields ψ m j) []).mpr
      (by simp only [consList_nil]; rw [hag]; exact hFok)
    simpa using this
  · have hbs' : SpineFit (substE V (holeTau D.k (D.holeTm ψ)) 0 (cons t (cons Y ρp)))
        (D.fields ψ m j) bs := by
      have := (spineFit_holeEntsAV D.k (D.holeTm ψ) (D.fields ψ m j) [] _ bs).mp (by simpa using hbs)
      exact this
    rw [hag] at hbs'
    have hlen : bs.length = (D.fields ψ m j).length := hbs'.length_eq
    exact holeEqsAV_ok (hIall m hm) ht hH hlen
      (fun e he => by rw [hag]; exact hEok bs hbs' e he) (hres m hm j hj')

end LfpDatum

end ConLeche.Model
