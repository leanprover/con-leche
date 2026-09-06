import Setlec.SetP.Direct.DirectRecReadP

/-!
# The recursor's frames (task #175 W4c, P3 module 6, part 13; S2)

`recFrames`: at every parameter valuation the recursor's post-parameter
phase facts hold — `RecBase`: the field chain graded, the motive
binder the Π over the carrier into the elimination sort, the minor
binder the minor space, the major binder the carrier.  Since task
#175 S2 the recursor type is the *generated* one, whose binder data
is `recDataAV`: its parameter entries are the type former's (so the
parameter frames coincide outright), and its three special entries are
spelled out, so every clause of `RecBase` is a **computation** on the
readings — `famSpine_val` for the carrier, `interp_minorSp_of_tele`
for the minor space, the constructor leaf's fold for its core.  The
gradings of the entries come from the opened type's record
(`OpenedP.okΓ`, the fabricated type's own inference run).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Frame arithmetic -/

/-- The recursor's reversed context above its three special binders is
its reversed parameter context. -/
theorem drop_three_rec {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3) :
    ((rds.map (·.2.2)).reverse).drop 3 = (((rds.take nP).map (·.2.2)).reverse) := by
  rw [reverse_map_take_drop rds nP, List.drop_left' (by simp [hlen])]

/-- An entry of the recursor's context by its binder position. -/
theorem rec_entry {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3) {i : Nat} (hi : i < nP + 3) :
    ((rds.map (·.2.2)).reverse).getD (nP + 3 - 1 - i) default
      = (rds.getD i default).2.2 := by
  have hq : rds[i]? = some (rds.getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  exact getD_reverse_of_peel hlen hi hq

/-! ## The generated data, by position -/

section Data
variable {m : EnvS2Core V env} {T C : Name} {ψ : Name → Nat} {nP nF : Nat} {ℓ : Level}
  {pps ds : List (Nat × Nat × AVExpr)}

theorem recDataAV_length (hlenP : pps.length = nP) :
    (recDataAV m T C ψ nP nF ℓ pps ds).length = nP + 3 := by
  simp [recDataAV, hlenP]

theorem recDataAV_take (hlenP : pps.length = nP) :
    (recDataAV m T C ψ nP nF ℓ pps ds).take nP = rebit (pwBit ψ (Level.zeronessOf ℓ)) pps := by
  unfold recDataAV
  rw [List.take_append_of_le_length (by simp [hlenP]), List.take_of_length_le (by simp [hlenP])]

theorem recDataAV_getD_motive (hlenP : pps.length = nP) :
    (recDataAV m T C ψ nP nF ℓ pps ds).getD nP default
      = (0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ) := by
  unfold recDataAV
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlenP]), rebit_length,
    hlenP, Nat.sub_self]
  rfl

theorem recDataAV_getD_minor (hlenP : pps.length = nP) :
    (recDataAV m T C ψ nP nF ℓ pps ds).getD (nP + 1) default
      = (0, pwBit ψ (Level.zeronessOf ℓ),
          minorAV m C ψ nP nF (pwBit ψ (Level.zeronessOf ℓ)) ds) := by
  unfold recDataAV
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlenP]), rebit_length,
    hlenP, show nP + 1 - nP = 1 from by omega]
  rfl

theorem recDataAV_getD_major (hlenP : pps.length = nP) :
    (recDataAV m T C ψ nP nF ℓ pps ds).getD (nP + 2) default
      = (0, pwBit ψ (Level.zeronessOf ℓ), majorAV m T ψ nP) := by
  unfold recDataAV
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlenP]), rebit_length,
    hlenP, show nP + 2 - nP = 2 from by omega]
  rfl

end Data

/-- The field chain's entry `j`. -/
theorem fields_getD {ds : List (Nat × Nat × AVExpr)} {nP j : Nat}
    (hj : j < (ds.drop nP).length) :
    (((ds.drop nP).map (·.2.2))).getD j default = ((ds.drop nP).getD j default).2.2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

/-! ## The frames -/

set_option maxHeartbeats 3200000 in
/-- **The recursor's frames, by computation.** -/
theorem recFrames {m : EnvS2Core V env}
    {p : DirectParts} {cvTa cvCa cvRa : ConstantVal}
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvTa p.nP p.resSort pps)
    (hCD : CtorData m p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hleafT : ∀ ψ, m.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hleafC : ∀ ψ, m.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false → FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))))
    (ψ : Name → Nat) {rds : List (Nat × Nat × AVExpr)}
    (hrds : rds = recDataAV m p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p) (pps ψ) (ds ψ))
    {fvsR : List Expr} {oR : Expr}
    (hR : OpenedP m ψ (p.nP + 3) cvRa.type fvsR oR ((rds.map (·.2.2)).reverse)
      (.app (.bvar 2) (.bvar 0))) :
    (∀ ρ : Nat → V,
      Sat2 V (((rds.take p.nP).map (·.2.2)).reverse) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ) ∧
    (∀ ρ : Nat → V,
      Sat2 V (((rds.take p.nP).map (·.2.2)).reverse) ρ →
        RecBase ((elimLevel p).eval ψ) (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))
          (rds.getD p.nP default) (rds.getD (p.nP + 1) default)
          (rds.getD (p.nP + 2) default)) := by
  have hlenR : rds.length = p.nP + 3 := by rw [hrds]; exact recDataAV_length (hFD.len ψ)
  have htake : (rds.take p.nP).map (·.2.2) = (pps ψ).map (·.2.2) := by
    rw [hrds, recDataAV_take (hFD.len ψ), rebit_map_dom]
  have hiffR : ∀ ρ : Nat → V,
      Sat2 V (((rds.take p.nP).map (·.2.2)).reverse) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ := by
    intro ρ; rw [htake]; exact hiff ψ ρ
  refine ⟨hiffR, fun ρp hρp => ?_⟩
  have hbz : (elimLevel p).eval ψ = 0 ↔ pwBit ψ (Level.zeronessOf (elimLevel p)) = 0 := by
    rw [pwBit_eq_zero_iff, Setlec.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hlenFs : (((ds ψ).drop p.nP).map (·.2.2)).length = p.nF := by simp [hCD.len ψ]
  have hlenFds : ((ds ψ).drop p.nP).length = p.nF := by simp [hCD.len ψ]
  have hsatC := (hiffR ρp).mp hρp
  have hsatP : Sat2 V ((pps ψ).map (·.2.2)).reverse ρp := (hiff ψ ρp).mpr hsatC
  have hdrop3 := drop_three_rec (rds := rds) hlenR
  have hρp3 : Sat2 V (((rds.map (·.2.2)).reverse).drop 3) ρp := by rw [hdrop3]; exact hρp
  -- the former's walks
  have hFsOk : ∀ (ψ' : Name → Nat) (ρ : Nat → V), Sat2 V ((pps ψ').map (·.2.2)).reverse ρ →
      FieldsOkB (p.resSort.eval ψ') ρ (((ds ψ').drop p.nP).map (·.2.2)) ∧
      FieldsValid ρ (((ds ψ').drop p.nP).map (·.2.2)) :=
    fun ψ' ρ h => ⟨(hfields ψ' ρ ((hiff ψ' ρ).mp h)).1, (hfields ψ' ρ ((hiff ψ' ρ).mp h)).2.1⟩
  have hok : ∀ ρ : Nat → V, ParamsOkT (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) (pps ψ) :=
    fun ρ => (formerWalks hFD hFsOk ψ ρ).1
  have hval : ∀ ρ : Nat → V, UnderTowerValid ρ (towerBodyAV (p.resSort.eval ψ) (((ds ψ).drop p.nP).map (·.2.2))) (pps ψ) :=
    fun ρ => (formerWalks hFD hFsOk ψ ρ).2
  have hcl : VExpr.bvarsBelow 0 (directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2))).erase := by
    have := m.cval_closedL p.cvT.name ψ
    rwa [hleafT] at this
  -- the family spine at any frame over the parameters
  have hfam : ∀ (e : Nat) (σ : Nat → V), (∀ j, σ (j + e) = ρp j) →
      AnnotOkP V σ (AVExpr.mkAppN (m.acval p.cvT.name ψ) (paramBvarsAt p.nP (p.nP + e))) ∧
      interp2 V σ (AVExpr.mkAppN (m.acval p.cvT.name ψ) (paramBvarsAt p.nP (p.nP + e)))
        = towerSet (p.resSort.eval ψ) (teleOfFields ρp (((ds ψ).drop p.nP).map (·.2.2))) := by
    intro e σ hσ
    rw [hleafT]
    exact famSpine_val (hFD.bits ψ) (hFD.below ψ) (hFD.len ψ) hok hval hcl hσ hsatP
  -- the entries
  have heM := recDataAV_getD_motive (m := m) (T := p.cvT.name) (C := p.cvC.name) (ψ := ψ)
    (nF := p.nF) (ℓ := elimLevel p) (ds := ds ψ) (hFD.len ψ)
  have hem := recDataAV_getD_minor (m := m) (T := p.cvT.name) (C := p.cvC.name) (ψ := ψ)
    (nF := p.nF) (ℓ := elimLevel p) (ds := ds ψ) (hFD.len ψ)
  have het := recDataAV_getD_major (m := m) (T := p.cvT.name) (C := p.cvC.name) (ψ := ψ)
    (nF := p.nF) (ℓ := elimLevel p) (ds := ds ψ) (hFD.len ψ)
  rw [← hrds] at heM hem het
  have hΓM : ((rds.map (·.2.2)).reverse).getD 2 default = (rds.getD p.nP default).2.2 := by
    have := rec_entry (rds := rds) hlenR (i := p.nP) (by omega)
    rwa [show p.nP + 3 - 1 - p.nP = 2 from by omega] at this
  have hΓm : ((rds.map (·.2.2)).reverse).getD 1 default = (rds.getD (p.nP + 1) default).2.2 := by
    have := rec_entry (rds := rds) hlenR (i := p.nP + 1) (by omega)
    rwa [show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega] at this
  have hΓt : ((rds.map (·.2.2)).reverse).getD 0 default = (rds.getD (p.nP + 2) default).2.2 := by
    have := rec_entry (rds := rds) hlenR (i := p.nP + 2) (by omega)
    rwa [show p.nP + 3 - 1 - (p.nP + 2) = 0 from by omega] at this
  have hlenΓ : ((rds.map (·.2.2)).reverse).length = p.nP + 3 := by simp [hlenR]
  have hdrop2 : ((rds.map (·.2.2)).reverse).drop 2
      = ((rds.map (·.2.2)).reverse).getD 2 default :: ((rds.map (·.2.2)).reverse).drop 3 := by
    have h := drop_succ_eq_getD_cons hlenΓ (i := p.nP) (by omega)
    rwa [show p.nP + 3 - (p.nP + 1) = 2 from by omega, show p.nP + 3 - 1 - p.nP = 2 from by omega,
      show p.nP + 3 - p.nP = 3 from by omega] at h
  have hdrop1 : ((rds.map (·.2.2)).reverse).drop 1
      = ((rds.map (·.2.2)).reverse).getD 1 default :: ((rds.map (·.2.2)).reverse).drop 2 := by
    have h := drop_succ_eq_getD_cons hlenΓ (i := p.nP + 1) (by omega)
    rwa [show p.nP + 3 - (p.nP + 1 + 1) = 1 from by omega,
      show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega,
      show p.nP + 3 - (p.nP + 1) = 2 from by omega] at h
  -- `RecBase`
  refine ⟨(hfields ψ ρp hsatC).1, ?_, ?_, ?_, ?_⟩
  · -- the squash bound at a large eliminator
    intro hw hl
    have hlarge : p.large = true := by
      cases hpl : p.large
      · exfalso
        apply hl
        simp [elimLevel, Setlec.directElimLevel, hpl, Level.eval]
      · rfl
    by_cases hnp : p.isProp = true
    · exact (hfields ψ ρp hsatC).2.2.2 hnp hlarge
    · have := (hfields ψ ρp hsatC).2.2.1 (by simpa using hnp)
      rwa [hw] at this
  · -- the motive's grading
    have h := (hR.okΓ p.nP (by omega) ρp
      (by rw [show p.nP + 3 - p.nP = 3 from by omega]; exact hρp3)).1
    rw [show p.nP + 3 - 1 - p.nP = 2 from by omega, hΓM] at h
    exact h
  · -- the motive's reading: the Π over the carrier into the elimination sort
    rw [heM]
    show interp2 V ρp (motiveAV m p.cvT.name ψ p.nP (elimLevel p)) = _
    unfold motiveAV
    rw [interp2_pi]
    have hfam0 := (hfam 0 ρp (fun j => rfl)).2
    rw [Nat.add_zero] at hfam0
    rw [hfam0, piR_congr_bit (v' := ((elimLevel p).eval ψ) + 1)
      ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ), fun h => absurd h (Nat.succ_ne_zero _)⟩]
    rfl
  · intro M hM
    have hρM : Sat2 V (((rds.map (·.2.2)).reverse).drop 2) (cons M ρp) := by
      rw [hdrop2, hΓM]; exact Sat2_cons V hρp3 hM
    refine ⟨?_, ?_, ?_⟩
    · -- the minor's grading
      have h := (hR.okΓ (p.nP + 1) (by omega) _
        (by rw [show p.nP + 3 - (p.nP + 1) = 2 from by omega]; exact hρM)).1
      rw [show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega, hΓm] at h
      exact h
    · -- the minor's reading: the minor space
      rw [hem]
      show interp2 V (cons M ρp) (minorAV m p.cvC.name ψ p.nP p.nF (pwBit ψ (Level.zeronessOf (elimLevel p))) (ds ψ)) = _
      unfold minorAV
      refine interp_minorSp_of_tele (by simp only [rebit_length, liftDoms_length, List.length_map]) ?_ ?_ ?_
      · intro d hd
        rw [mem_rebit hd]; exact hbz
      · -- the field domains agree along a fitting chain
        intro j as hj hsp
        rw [hlenFs] at hj
        have hlenAs : as.length = j := by
          rw [hsp.length_eq, List.length_take, hlenFs]; omega
        rw [rebit_getD _ _ _ (by rw [liftDoms_length]; omega)]
        show interp2 V (consList as (cons M ρp))
          ((liftDoms 1 0 ((ds ψ).drop p.nP)).getD j default).2.2 = _
        obtain ⟨q, hq⟩ : ∃ q, ((ds ψ).drop p.nP)[j]? = some q :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlenFds]; exact hj)⟩
        have hsh : shiftE 1 j (consList as (cons M ρp)) = consList as ρp := by
          rw [← hlenAs, shiftE_consList_len, shiftE_one_cons]
        rw [List.getD_eq_getElem?_getD, liftDoms_getElem?, hq, Option.map_some, Option.getD_some]
        show interp2 V (consList as (cons M ρp)) (q.2.2.liftN 1 (0 + j)) = _
        rw [interp2_liftN, Nat.zero_add, hsh, fields_getD (by rw [hlenFds]; exact hj),
          List.getD_eq_getElem?_getD, hq, Option.getD_some]
      · -- the core: the motive at the constructor leaf's fold
        intro as hsp
        have hlenAs : as.length = p.nF := by rw [hsp.length_eq, hlenFs]
        have hMval : consList as (cons M ρp) p.nF = M := by
          rw [← hlenAs, show as.length = 0 + as.length from by omega, consList_apply_add]
          rfl
        have hσ : ∀ j, consList as (cons M ρp) (j + (1 + p.nF)) = ρp j := by
          intro j
          rw [show j + (1 + p.nF) = (j + 1) + as.length from by omega, consList_apply_add]
          rfl
        have hleafC' : m.acval p.cvC.name ψ
            = directMkAV (p.resSort.eval ψ) ((ds ψ).take p.nP ++ (ds ψ).drop p.nP) (((ds ψ).drop p.nP).map (·.2.2)) := by
          rw [hleafC, List.take_append_drop]
        rw [interp2_app, interp2_bvar, hMval, interp2_mkAppN,
          ← List.foldl_map (f := interp2 V (consList as (cons M ρp))) (g := SetTheory.app),
          List.map_append, show p.nP + 1 + p.nF = p.nP + (1 + p.nF) from by omega,
          map_paramBvarsAt_interp hσ]
        show SetTheory.app M ((List.map ρp (List.range p.nP).reverse ++
            List.map (interp2 V (consList as (cons M ρp))) (fieldBvars p.nF)).foldl SetTheory.app
            (interp2 V (consList as (cons M ρp)) (m.acval p.cvC.name ψ))) = _
        rw [show fieldBvars p.nF = (List.range p.nF).map (fun k => AVExpr.bvar (p.nF - 1 - k)) from rfl,
          map_fieldBvars_interp hlenAs,
          interp2_closed (V := V) (m.cval_closedL p.cvC.name ψ) _ (fun j => ρp (j + p.nP)),
          hleafC']
        have hlenP : (((ds ψ).take p.nP).map (·.2.2)).length = p.nP := by simp [hCD.len ψ]
        have hsp₁ := spineFit_of_sat2 (Δ₀ := []) (Ds := ((ds ψ).take p.nP).map (·.2.2))
          (by rw [List.append_nil]; exact hsatC)
        rw [hlenP] at hsp₁
        rw [List.nil_append]
        rcases Nat.eq_zero_or_pos (p.resSort.eval ψ) with hw0 | hwpos
        · rw [hw0, directMkAV_zero, foldl_app_pt, if_pos rfl]
        · have hw : p.resSort.eval ψ ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
          rw [directMkAV_fold hw hsp₁ (by rw [consList_range_reverse]; exact hsp)
            (by rw [consList_range_reverse]; exact ((hfields ψ ρp hsatC).1).toBound hw), if_neg hw]
    · intro mv hm
      have hρm : Sat2 V (((rds.map (·.2.2)).reverse).drop 1) (cons mv (cons M ρp)) := by
        rw [hdrop1, hΓm]; exact Sat2_cons V hρM hm
      refine ⟨?_, ?_⟩
      · -- the major's grading
        have h := (hR.okΓ (p.nP + 2) (by omega) _
          (by rw [show p.nP + 3 - (p.nP + 2) = 1 from by omega]; exact hρm)).1
        rw [show p.nP + 3 - 1 - (p.nP + 2) = 0 from by omega, hΓt] at h
        exact h
      · -- the major's reading: the carrier
        rw [het]
        show interp2 V (cons mv (cons M ρp)) (majorAV m p.cvT.name ψ p.nP) = _
        unfold majorAV
        exact (hfam 2 (cons mv (cons M ρp)) (fun j => rfl)).2

end Setlec.SetP
