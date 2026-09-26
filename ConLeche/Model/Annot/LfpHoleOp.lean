module

public import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Semantics.Tower.BlockTower
public import ConLeche.Semantics.Inductives.HoleAppGrade

public section

/-!
# The HOLE OPERATOR of an lfp datum (lane HOLE2, checkpoint (d))

Charter item 2: a block's right-hand-side operator IS the interpretation
of its constructors' fields with holes.  `LfpDatum` records those fields
(`fields`, `resIdx`) and reads them at the hole frame (`frame`,
`HFits`).  This module spells the operator as a TERM — the block
operator of `BlockTower.lean` at the hole chains of
`BlockTower.lean` (`LfpDatum.holeOp`) — and proves that it is what
the clause says it is:

* **its fibre is the hole fit** (`LfpDatum.holeOp_fibre`): component
  `c`'s fibre at `(X, t)` is the injections of the spines `HFits`-fitting
  one of `c`'s constructors — with no field classification: the hole
  terms agree with the model's hole values applied to the parameters
  (`LfpDatum.holeAgreeW_frame`), which is how the fields read
  (`HolesApplied`, lane CONTSEM's M3);
* **its chains are graded** at every tuple of the tuple space when the
  fields are graded at the hole frame (`LfpDatum.holeChains_ok`) — the
  grading U2 gives, carried across by `wellDenoted_congr_holeApp`.
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

/-- A λ-tower of graphs applied to a strict prefix of a fitting spine is
a graph over the next binder's domain. -/
theorem holeFam_foldl_take :
    ∀ {ρ : Nat → V} {A : List AnnotTerm} {ps : List V} (g : List V → V) (j : Nat),
      SpineFit ρ A ps → j < A.length →
      ∃ D : AnnotTerm, ∃ G : V → V,
        (ps.take j).foldl app (holeFam ρ A g) = lamR 1 (interp V (consList (ps.take j) ρ) D) G ∧
        A[j]? = some D
  | _, [], _, _, _, _, hj => absurd hj (by simp)
  | _, _ :: _, [], _, _, h, _ => h.elim
  | ρ, T :: A, p :: ps, g, 0, _, _ => ⟨T, _, rfl, rfl⟩
  | ρ, T :: A, p :: ps, g, j + 1, h, hj => by
    obtain ⟨D, G, hG, hD⟩ := holeFam_foldl_take (fun vs => g (p :: vs)) j h.2 (by simpa using hj)
    refine ⟨D, G, ?_, by simpa using hD⟩
    show (ps.take j).foldl app (app (lamR 1 (interp V ρ T) _) p) = _
    rw [app_lamR_pos (by decide) h.1]
    exact hG

/-- **Graphs over the same domain accept the same arguments.** -/
theorem appOk_lamR {A a : V} {G G' : V → V} (h : AppOk (lamR 1 A G) a) : AppOk (lamR 1 A G') a := by
  obtain ⟨v, A', B, hf, ha, -⟩ := h
  have hmem : ∀ G'' : V → V, lamR 1 A G'' ∈ˢ piR 1 A fun x => sing (G'' x) :=
    fun G'' => lamR_mem fun x _ => mem_sing.mpr rfl
  have hA : A' = A := by
    by_cases hv : v = 0
    · subst hv
      have h1 := eq_pt_of_mem_piR_zero hf
      exact absurd h1 (mem_piR_pos (by decide) (hmem G)).2.2.2
    · exact (piR_dom_unique (by decide) hv (hmem G) hf).symm
  subst hA
  exact ⟨1, A', fun x => sing (G' x), hmem G', ha, fun h => absurd h (by decide)⟩

omit [SetTheory V] in
/-- The parameter positions of a frame whose `k` innermost positions are
holes read the parameter frame's own parameters. -/
theorem holeParamVals_consList (k nP : Nat) (L : List V) (hL : L.length = k) (ρp : Nat → V) :
    holeParamVals k nP 0 (consList L ρp) = frameIdx nP ρp := by
  unfold holeParamVals frameIdx
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  have := consList_apply_add L ρp (nP - 1 - p)
  rw [hL] at this
  rw [show 0 + k + nP - 1 - p = nP - 1 - p + k by omega, this]

/-! ## The hole operator of an lfp datum -/

namespace LfpDatum

variable (D : LfpDatum V)

/-- **Member `m`'s hole term** (`holeTmAV` at the member's own
telescopes). -/
@[expose] def holeTm (ψ : Name → Nat) (m : Nat) : AnnotTerm :=
  holeTmAV (D.u m ψ) m (D.pars m ψ) (D.ids m ψ)

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

/-- **The hole term's value**: a λ-tower over the member's parameter
telescope, blind in it, of the λ-tower over its index telescope AT THE
ACTUAL PARAMETERS of `Y`'s component at the index tuple. -/
theorem interp_holeTm {ψ : Name → Nat} {ρp : Nat → V} {m : Nat}
    (hbd : D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ)) (t Y : V) :
    interp V (cons t (cons Y ρp)) (D.holeTm ψ m)
      = holeFam (shiftE (D.pars m ψ).length 0 ρp) (D.pars m ψ) fun _ =>
          holeFam ρp (D.ids m ψ) fun is => app (projS m Y) (tupW (D.u m ψ) is) := by
  have hsh : shiftE ((D.pars m ψ).length + 2) 0 (cons t (cons Y ρp))
      = shiftE (D.pars m ψ).length 0 ρp := by
    rw [show (D.pars m ψ).length + 2 = (D.pars m ψ).length + 1 + 1 by omega, shiftE_succ_cons,
      shiftE_succ_cons]
  have hshI : ∀ ps : List V, ps.length = (D.pars m ψ).length →
      shiftE ((D.pars m ψ).length + 2) 0 (consList ps (cons t (cons Y ρp))) = ρp := by
    intro ps hps
    have := shiftE_consList_add ps 2 (cons t (cons Y ρp))
    rw [hps] at this
    rw [this, show (2 : Nat) = 1 + 1 by rfl, shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
  unfold holeTm holeTmAV
  rw [interp_mkLamsAV_one, holeFam_append, holeFam_liftFields, hsh]
  refine holeFam_congr fun ps hps => ?_
  have hlen : ps.length = (D.pars m ψ).length := hps.length_eq
  rw [holeFam_liftFields, hshI ps hlen]
  refine holeFam_congr fun is his => ?_
  have hlenI : is.length = (D.ids m ψ).length := his.length_eq
  have hY' : consList (ps ++ is) (cons t (cons Y ρp))
      ((D.pars m ψ).length + (D.ids m ψ).length + 1) = Y := by
    have := Xframe_X ρp (ps ++ is) t Y
    rwa [List.length_append, hlen, hlenI] at this
  have his' : SpineFit (consList ps (cons t (cons Y ρp)))
      (liftFields ((D.pars m ψ).length + 2) 0 (D.ids m ψ)) is := by
    rw [spineFit_liftFields, hshI ps hlen]; exact his
  have hbd' : D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) (consList ps (cons t (cons Y ρp)))
      (liftFields ((D.pars m ψ).length + 2) 0 (D.ids m ψ)) := fun hu => by
    rw [fieldsBound_liftFields, hshI ps hlen]; exact hbd hu
  have htv := mkTowerGo_interp hbd' his'
  rw [← consList_append] at htv
  rw [interp_app, projAV_interp, interp_bvar, hY', htv]
  rfl

/-- The hole terms' frame is the parameter frame below the hole terms'
values. -/
theorem holeTmFrame_eq {ψ : Name → Nat} {ρp : Nat → V} (t Y : V) :
    D.holeTmFrame ψ ρp t Y
      = consList ((List.range D.k).map fun m => interp V (cons t (cons Y ρp)) (D.holeTm ψ m)) ρp :=
  substE_holeTau fun _ _ => rfl

/-- **The hole terms agree with the model's hole values** — applied to
the parameters, and in what they accept at every prefix of them — at
the tuple `Y`'s components. -/
theorem holeAgreeW_frame {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {t Y : V}
    (hXY : ∀ m, m < D.k → X m = projS m Y)
    (hpars : ∀ m, m < D.k → (D.pars m ψ).length = (D.params ψ).length ∧
      Sat V (D.pars m ψ).reverse ρp)
    (hbd : ∀ m, m < D.k → D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ)) :
    HoleAgreeW D.k (D.params ψ).length 0 (D.frame ψ ρp X) (D.holeTmFrame ψ ρp t Y) := by
  have hlenL : ((List.range D.k).map (D.holeVal ψ ρp X)).length = D.k := by simp
  have hlenL' : ((List.range D.k).map fun m => interp V (cons t (cons Y ρp)) (D.holeTm ψ m)).length
      = D.k := by simp
  have hhpv : holeParamVals D.k (D.params ψ).length 0 (D.frame ψ ρp X)
      = frameIdx (D.params ψ).length ρp := holeParamVals_consList _ _ _ hlenL ρp
  -- the two holes at member `m`
  have hsides : ∀ h, h < D.k →
      D.frame ψ ρp X h = D.holeVal ψ ρp X (D.k - 1 - h) ∧
      D.holeTmFrame ψ ρp t Y h = interp V (cons t (cons Y ρp)) (D.holeTm ψ (D.k - 1 - h)) := by
    intro h hh
    refine ⟨?_, ?_⟩
    · have := frame_hole (D := D) (ψ := ψ) (ρp := ρp) (X := X) (t := D.k - 1 - h) (by omega)
      rwa [show D.k - 1 - (D.k - 1 - h) = h by omega] at this
    · rw [holeTmFrame_eq, consList_getD_of_lt _ _ _ (by rw [hlenL']; exact hh), hlenL',
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
  -- the parameter spine fits each member's own parameter telescope
  have hps : ∀ m, m < D.k →
      SpineFit (shiftE (D.pars m ψ).length 0 ρp) (D.pars m ψ) (frameIdx (D.params ψ).length ρp) := by
    intro m hm
    rw [← (hpars m hm).1]
    exact spineFit_frameIdx_of_sat (hpars m hm).2
  refine ⟨⟨fun i hi => ?_, fun h _ hh is => ?_⟩, fun h _ hh j hj a ha => ?_⟩
  · -- off the holes: the parameter frame at both
    have hi' : D.k ≤ i := by omega
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + D.k := ⟨i - D.k, by omega⟩
    show consList _ ρp (i + D.k) = D.holeTmFrame ψ ρp t Y (i + D.k)
    rw [holeTmFrame_eq]
    have h1 := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X)) ρp i
    have h2 := consList_apply_add ((List.range D.k).map fun m =>
      interp V (cons t (cons Y ρp)) (D.holeTm ψ m)) ρp i
    rw [hlenL] at h1
    rw [hlenL'] at h2
    rw [h1, h2]
  · -- at a hole, applied to the parameters and anything
    rw [Nat.zero_add] at hh
    obtain ⟨hL, hR⟩ := hsides h hh
    have hm : D.k - 1 - h < D.k := by omega
    rw [hhpv, hL, hR, interp_holeTm (hbd _ hm), List.foldl_append, List.foldl_append]
    have hsp := hps _ hm
    have hfr : consList (frameIdx (D.params ψ).length ρp) (shiftE (D.pars (D.k - 1 - h) ψ).length 0 ρp)
        = ρp := by
      rw [(hpars _ hm).1]; exact consList_frameIdx _ ρp
    unfold holeVal
    rw [holeFam_foldl_prefix _ _ hsp, holeFam_app _ hsp, hfr, hXY _ hm]
    congr 1
    refine holeFam_congr fun bs hbs => ?_
    rw [List.drop_left' (by rw [frameIdx, List.length_map, List.length_range, (hpars _ hm).1])]
  · -- at a strict prefix of the parameters: graphs over the same domain
    rw [Nat.zero_add] at hh
    obtain ⟨hL, hR⟩ := hsides h hh
    have hm : D.k - 1 - h < D.k := by omega
    rw [hhpv] at ha ⊢
    rw [hL] at ha
    rw [hR, interp_holeTm (hbd _ hm)]
    have hsp := hps _ hm
    have hjP : j < (D.pars (D.k - 1 - h) ψ).length := by rw [(hpars _ hm).1]; exact hj
    unfold holeVal at ha
    rw [holeFam_append] at ha
    obtain ⟨Dd, G, hG, hD⟩ := holeFam_foldl_take _ j hsp hjP
    obtain ⟨Dd', G', hG', hD'⟩ := holeFam_foldl_take
      (fun _ => holeFam ρp (D.ids (D.k - 1 - h) ψ) fun is =>
        app (projS (D.k - 1 - h) Y) (tupW (D.u (D.k - 1 - h) ψ) is)) j hsp hjP
    rw [hD] at hD'
    cases hD'
    rw [hG] at ha
    rw [hG']
    exact appOk_lamR ha

/-- The per-member facts the hole terms need at a parameter frame: each
member's own parameter telescope is the block's in length and satisfied,
and its index telescope is bounded. -/
@[expose] def HoleTmOk (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) : Prop :=
  ∀ m, m < D.k → ((D.pars m ψ).length = (D.params ψ).length ∧ Sat V (D.pars m ψ).reverse ρp) ∧
    (D.u m ψ ≠ 0 → FieldsBound (D.u m ψ) ρp (D.ids m ψ))

/-- **The hole operator's fibre is the hole fit** (see the module
docstring): at an index tuple of the component, the injections of the
spines fitting a constructor's fields with holes at the model's hole
frame, whose result index readings there are the index tuple's
components.  The tuple `X` is arbitrary. -/
theorem holeOp_fibre {ψ : Name → Nat} {ρp : Nat → V} (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (X : Nat → V) {c : Nat}
    (happ : ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length)
    {t : V} (ht : t ∈ˢ D.idx ψ ρp c) (x : V) :
    x ∈ˢ app (D.holeOp ψ ρp X c) t ↔
      ∃ j fs, D.HFits ψ ρp X t c j fs ∧
        x = (if D.w ψ = 0 then (pt : V) else ConLeche.SetTheory.Tower.inj j (ConLeche.SetTheory.Tower.mkTower (fs ++ [pt]))) := by
  have hag : HoleAgreeW D.k (D.params ψ).length 0 (D.frame ψ ρp X)
      (D.holeTmFrame ψ ρp t (ndMkTowerSet X 0 D.N)) :=
    holeAgreeW_frame (fun m hm => (projS_ndMkTowerSet_zero (by omega)).symm)
      (fun m hm => (hok m hm).1) (fun m hm => (hok m hm).2)
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
    rw [hgF j hj] at hsp
    rw [hgE j hj] at hidx
    have hsp' : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs :=
      (spineFit_congr_holeApp (D.fields ψ c j) (lo := 0)
        (fun l F hl => by simpa using (happ j hj).1 l F hl) hag.1 fs).mpr hsp
    have hlen : fs.length = (D.fields ψ c j).length := hsp'.length_eq
    refine ⟨⟨hj, hsp', fun l hl => ?_⟩, rfl⟩
    have hl' : l < (D.resIdx ψ c j).length := by rw [hres j hj]; exact hl
    refine ⟨(D.resIdx ψ c j)[l], List.getElem?_eq_getElem hl', ?_⟩
    have := hidx l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some] at this
    have hA := hag.1.consList fs
    rw [Nat.zero_add, hlen] at hA
    rw [interp_congr_holeApp ((happ j hj).2 _ (List.getElem_mem hl')) hA]
    exact this
  · rintro ⟨⟨hj, hsp, hidx⟩, rfl⟩
    have hlen : fs.length = (D.fields ψ c j).length := hsp.length_eq
    refine ⟨hj, ?_, fun l hl => ?_, rfl⟩
    · rw [hgF j hj]
      exact (spineFit_congr_holeApp (D.fields ψ c j) (lo := 0)
        (fun l F hl => by simpa using (happ j hj).1 l F hl) hag.1 fs).mp hsp
    · rw [hgE j hj]
      obtain ⟨e, he, hev⟩ := hidx l hl
      rw [List.getD_eq_getElem?_getD, he, Option.getD_some]
      have hA := hag.1.consList fs
      rw [Nat.zero_add, hlen] at hA
      have := interp_congr_holeApp ((happ j hj).2 _ (List.mem_of_getElem? he)) hA
      exact this ▸ hev

end LfpDatum

/-- **A telescope's grading crosses frames related at the holes.** -/
theorem fieldsOkB_congr_holeApp {k nP w : Nat} :
    ∀ (Fs : List AnnotTerm) {lo : Nat}, (∀ l F, Fs[l]? = some F → HoleApp k nP (lo + l) F) →
      ∀ {σ σ' : Nat → V}, HoleAgreeW k nP lo σ σ' → FieldsOkB w σ Fs → FieldsOkB w σ' Fs
  | [], _, _, _, _, _, _ => trivial
  | F :: Fs, lo, hF, σ, σ', h, hok => by
    have h0 : HoleApp k nP lo F := by simpa using hF 0 F rfl
    have ht : ∀ l F', Fs[l]? = some F' → HoleApp k nP (lo + 1 + l) F' := by
      intro l F' hl
      have := hF (l + 1) F' (by simpa using hl)
      rwa [show lo + (l + 1) = lo + 1 + l by omega] at this
    have he := interp_congr_holeApp h0 h.1
    refine ⟨wellDenoted_congr_holeApp h0 h hok.1, fun hw => he ▸ hok.2.1 hw, fun a ha => ?_⟩
    exact fieldsOkB_congr_holeApp Fs ht (h.cons a) (hok.2.2 a (he ▸ ha))

namespace LfpDatum

variable {D : LfpDatum V}

/-- **The hole chains are graded** at every tuple of the family space
(`BlockChainsOkG`), when the fields with holes and the result index
readings are graded at the model's hole frame of every tuple of the
tuple space — the grading U2's inference gives. -/
theorem holeChains_ok {ψ : Name → Nat} {ρp : Nat → V} (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (hIall : BlockIdxOk (V := V) D.N (fun c => D.u c ψ) ρp (fun c => D.ids c ψ))
    (hP : ∀ m, m < D.k → FieldsOkB 0 (shiftE (D.pars m ψ).length 0 ρp) (D.pars m ψ))
    (happ : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length)
    (hF : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N → ∀ j, j < D.nctors c →
      FieldsOkB (D.w ψ) (D.frame ψ ρp X) (D.fields ψ c j) ∧
      ∀ fs, SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs →
        ∀ e ∈ D.resIdx ψ c j, WellDenoted V (consList fs (D.frame ψ ρp X)) e) :
    BlockChainsOkG D.N (D.w ψ) ρp (fun c => D.u c ψ) (fun c => D.ids c ψ) (D.holeChains ψ) := by
  intro Y hY m hm t ht Fs hFs
  have hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) (fun c => projS c Y) := fun c hc => by
    rw [← lfpFamSpace_eq']; exact projS_mem_famsSpaceB hc hY
  have hag : HoleAgreeW D.k (D.params ψ).length 0 (D.frame ψ ρp fun c => projS c Y)
      (D.holeTmFrame ψ ρp t Y) :=
    holeAgreeW_frame (fun _ _ => rfl) (fun m hm => (hok m hm).1) (fun m hm => (hok m hm).2)
  have hH : ∀ m', m' < D.k → WellDenoted V (cons t (cons Y ρp)) (D.holeTm ψ m') := fun m' hm' =>
    holeTmAV_wellDenoted hIall (by omega) (hP m' hm') hY t
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
  have hFields : ∀ l F, (D.fields ψ m j)[l]? = some F → HoleApp D.k (D.params ψ).length (0 + l) F :=
    fun l F hl => by simpa using (happ m hm j hj').1 l F hl
  refine FieldsOkB_append_idxEq ?_ fun bs hbs => ?_
  · have := (FieldsOkB_holeEntsAV (w := D.w ψ) hH (D.fields ψ m j) []).mpr
      (fieldsOkB_congr_holeApp _ hFields hag hFok)
    simpa using this
  · have hbs' : SpineFit (D.holeTmFrame ψ ρp t Y) (D.fields ψ m j) bs := by
      have := (spineFit_holeEntsAV D.k (D.holeTm ψ) (D.fields ψ m j) [] _ bs).mp (by simpa using hbs)
      exact this
    have hbsF : SpineFit (D.frame ψ ρp fun c => projS c Y) (D.fields ψ m j) bs :=
      (spineFit_congr_holeApp (D.fields ψ m j) hFields hag.1 bs).mpr hbs'
    have hlen : bs.length = (D.fields ψ m j).length := hbsF.length_eq
    have hA := hag.consList bs
    rw [Nat.zero_add, hlen] at hA
    exact holeEqsAV_ok (hIall m hm) ht hH hlen
      (fun e he => wellDenoted_congr_holeApp ((happ m hm j hj').2 e he) hA (hEok bs hbsF e he))
      (hres m hm j hj')

end LfpDatum

end ConLeche.Model
