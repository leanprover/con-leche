module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Model.Inductives.SumKit

public section

/-!
# Bit validity of the hole chains

The P currency of a member's former leaf asks its chains to be
bit-valid (`SumFieldsValid`, `Model/Inductives/BlockLeafOk.lean`).  At
the hole chains (`LfpDatum.holeChains`, `Model/Annot/LfpHoleOp.lean`)
this is the fields' validity at the model's hole frame, carried across
the substitution (`AnnotValid_substAV`) — the hole terms' frame IS the
model's hole frame (`LfpDatum.holeTmFrame_frame`) — plus the hole terms'
own validity (`holeTmAV_validV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- **Bit validity crosses a parallel substitution**, given the
substituted terms' validity where they are read. -/
theorem AnnotValid_substAV (τ : Nat → AnnotTerm) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V), (∀ j, AnnotValid V (shiftE k 0 ρ) (τ j)) →
      (AnnotValid V ρ (AnnotTerm.substAV τ e k) ↔ AnnotValid V (substE V τ k ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ hτ
    by_cases hi : i < k
    · rw [AnnotTerm.substAV_bvar_lt τ hi]; simp
    · rw [AnnotTerm.substAV_bvar_ge τ (by omega), AnnotValid_liftN]
      simp only [AnnotValid_bvar, iff_true]
      exact hτ _
  | sort u => intro k ρ _; simp [AnnotTerm.substAV]
  | const c us => intro k ρ _; simp [AnnotTerm.substAV]
  | prf => intro k ρ _; simp [AnnotTerm.substAV]
  | app f a ihf iha =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_app, AnnotValid_app, AnnotValid_app, ihf k ρ hτ, iha k ρ hτ]
  | lam u A b ihA ihb =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, AnnotValid V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_lam, AnnotValid_lam, AnnotValid_lam, ihA k ρ hτ, interp_substAV]
    simp only [ihb (k + 1) _ (hτ' _), cons_substE]
  | pi u v A B ihA ihB =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, AnnotValid V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_pi, AnnotValid_pi, AnnotValid_pi, ihA k ρ hτ, interp_substAV]
    simp only [ihB (k + 1) _ (hτ' _), interp_substAV, cons_substE]
  | eqE a b iha ihb =>
    intro k ρ hτ
    show AnnotValid V ρ (.eqE _ _) ↔ AnnotValid V _ (.eqE _ _)
    rw [AnnotValid_eqE, AnnotValid_eqE, iha k ρ hτ, ihb k ρ hτ]
  | fst e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_fst, AnnotValid_fst, AnnotValid_fst, ih k ρ hτ]
  | snd e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_snd, AnnotValid_snd, AnnotValid_snd, ih k ρ hτ]

/-- The substituted entries are bit-valid exactly when the fields are, at
the frame the substitution produces. -/
theorem FieldsValid_holeEntsAV {k : Nat} {H : Nat → AnnotTerm} {σ : Nat → V}
    (hH : ∀ m, m < k → AnnotValid V σ (H m)) :
    ∀ (Fs : List AnnotTerm) (as : List V),
      FieldsValid (consList as σ) (holeEntsAV k H as.length Fs) ↔
        FieldsValid (consList as (substE V (holeTau k H) 0 σ)) Fs
  | [], _ => Iff.rfl
  | F :: Fs, as => by
    have hs : substE V (holeTau k H) as.length (consList as σ)
        = consList as (substE V (holeTau k H) 0 σ) := by
      have := substE_consList V (holeTau k H) as 0 σ
      rwa [Nat.add_zero] at this
    have hτ : ∀ j, AnnotValid V (shiftE as.length 0 (consList as σ)) (holeTau k H j) := by
      intro j
      rw [shiftE_consList]
      unfold holeTau
      split
      · exact hH _ (by omega)
      · simp
    show (AnnotValid V _ (AnnotTerm.substAV _ F _) ∧ _) ↔ (AnnotValid V _ F ∧ _)
    rw [AnnotValid_substAV (holeTau k H) F as.length _ hτ, interp_substAV, hs]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_)
    have := FieldsValid_holeEntsAV hH Fs (as ++ [a])
    rw [List.length_append, List.length_singleton, consList_append, consList_append] at this
    exact this

theorem FieldsValid_liftFields {n : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V},
      FieldsValid σ (liftFields n k Fs) ↔ FieldsValid (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsValid, AnnotValid_liftN, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_)
    rw [cons_shiftE]
    exact FieldsValid_liftFields

/-- A graph-regime λ-tower over a valid telescope with a body valid at
every fitting spine is valid. -/
theorem mkLamsAV_one_validV {b : AnnotTerm} :
    ∀ {Ts : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Ts →
      (∀ vs, SpineFit ρ Ts vs → AnnotValid V (consList vs ρ) b) →
      AnnotValid V ρ (mkLamsAV (Ts.map (1, ·)) b)
  | [], _, _, hb => hb [] trivial
  | T :: Ts, ρ, hT, hb => by
    show AnnotValid V ρ (.lam 1 T (mkLamsAV (Ts.map (1, ·)) b))
    rw [AnnotValid_lam]
    exact ⟨hT.1, fun x hx => mkLamsAV_one_validV (hT.2 x hx)
      (fun vs hvs => hb (x :: vs) ⟨hx, hvs⟩)⟩

/-- **The hole term is bit-valid** at the operator's frame. -/
theorem holeTmAV_validV {u m : Nat} {Is : List AnnotTerm} {ρp : Nat → V}
    (hI : FieldsValid ρp Is) (hb : u ≠ 0 → FieldsBound u ρp Is) (t Y : V) :
    AnnotValid V (cons t (cons Y ρp)) (holeTmAV u m Is) := by
  have hsh : shiftE 2 0 (cons t (cons Y ρp)) = ρp := by
    rw [show (2 : Nat) = 1 + 1 by rfl, shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
  unfold holeTmAV
  refine mkLamsAV_one_validV ?_ fun is his => ?_
  · rw [FieldsValid_liftFields, hsh]; exact hI
  · rw [AnnotValid_app]
    refine ⟨projAV_validV (by simp), mkTowerGo_validV ?_ (fun hu => ?_) his⟩
    · rw [FieldsValid_liftFields, hsh]; exact hI
    · rw [fieldsBound_liftFields, hsh]; exact hb hu

namespace LfpDatum

variable {D : LfpDatum V}

/-- **The hole chains are bit-valid** at every tuple of the family space
when the fields with holes and the result index readings are bit-valid at
the model's hole frame of every tuple of the tuple space, and the
members' index telescopes are valid. -/
theorem holeChains_valid {ψ : Name → Nat} {ρp : Nat → V} (hok : D.HoleTmOk ψ ρp)
    (hIV : ∀ m, m < D.k → FieldsValid ρp (D.ids m ψ))
    (hF : ∀ X : Nat → V, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ j, j < D.nctors c →
      FieldsValid (D.frame ψ ρp X) (D.fields ψ c j) ∧
      ∀ fs, SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs →
        ∀ e ∈ D.resIdx ψ c j, AnnotValid V (consList fs (D.frame ψ ρp X)) e)
    {Y : V} (hY : Y ∈ˢ famsSpaceB D.N (D.w ψ) ρp (fun c => D.u c ψ) (fun c => D.ids c ψ))
    (t : V) {m : Nat} (hm : m < D.N) :
    SumFieldsValid (cons t (cons Y ρp)) (D.holeChains ψ m) := by
  have hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) (fun c => SetTheory.Tower.projS c Y) :=
    fun c hc => by rw [← lfpFamSpace_eq']; exact projS_mem_famsSpaceB hc hY
  have hag : D.holeTmFrame ψ ρp t Y = D.frame ψ ρp fun c => SetTheory.Tower.projS c Y :=
    holeTmFrame_frame (fun _ _ => rfl) hok
  have hH : ∀ m', m' < D.k → AnnotValid V (cons t (cons Y ρp)) (D.holeTm ψ m') := fun m' hm' =>
    holeTmAV_validV (hIV m' hm') (hok m' hm') t Y
  intro Fs hFs
  unfold holeChains holeChs termChs at hFs
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
  obtain ⟨hFv, hEv⟩ := hF (fun c => SetTheory.Tower.projS c Y) hX m hm j hj'
  refine FieldsValid_append_one ?_ fun bs hbs => ?_
  · have := (FieldsValid_holeEntsAV hH (D.fields ψ m j) []).mpr
      (show FieldsValid (D.holeTmFrame ψ ρp t Y) _ by rw [hag]; exact hFv)
    simpa using this
  · have hbs' : SpineFit (D.holeTmFrame ψ ρp t Y) (D.fields ψ m j) bs :=
      (spineFit_holeEntsAV D.k (D.holeTm ψ) (D.fields ψ m j) [] _ bs).mp (by simpa using hbs)
    have hbsF : SpineFit (D.frame ψ ρp fun c => SetTheory.Tower.projS c Y) (D.fields ψ m j) bs :=
      hag ▸ hbs'
    have hlen : bs.length = (D.fields ψ m j).length := hbsF.length_eq
    have hs : substE V (holeTau D.k (D.holeTm ψ)) bs.length (consList bs (cons t (cons Y ρp)))
        = consList bs (D.holeTmFrame ψ ρp t Y) := by
      have := substE_consList V (holeTau D.k (D.holeTm ψ)) bs 0 (cons t (cons Y ρp))
      rwa [Nat.add_zero] at this
    have hτ : ∀ j, AnnotValid V (shiftE bs.length 0 (consList bs (cons t (cons Y ρp))))
        (holeTau D.k (D.holeTm ψ) j) := by
      intro j
      rw [shiftE_consList]
      unfold holeTau
      split
      · exact hH _ (by omega)
      · simp
    refine idxEqAV_validV fun e he => ?_
    unfold holeEqsAV at he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    refine ⟨?_, projAV_validV (by simp)⟩
    show AnnotValid V _ (AnnotTerm.substAV _ _ _)
    rw [← hlen, AnnotValid_substAV _ _ _ _ hτ, hs]
    have hl' := List.mem_range.mp hl
    by_cases hle : l < (D.resIdx ψ m j).length
    · have hmem : (D.resIdx ψ m j).getD l default ∈ D.resIdx ψ m j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle]
        exact List.getElem_mem hle
      rw [hag]; exact hEv bs hbsF _ hmem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
        show (default : AnnotTerm) = .bvar 0 from rfl, AnnotValid_bvar]
      trivial

end LfpDatum

end ConLeche.Model
