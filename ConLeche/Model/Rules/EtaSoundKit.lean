module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# Structure η's stuck side (task #342 L11b)

Structure η (`DefEq.structEta`) and the η rescue (`Red.rescueEta`) both
read a stuck term `b` inhabiting a stored η family `T` at the reduced
type `T targs`, and both need the same three facts about it: the
fabricated projections read and are graded, `b` is the η constructor
at the type's arguments and its own projections (the η law), and that
spine fits the η constructor's telescope (the coherence law,
`EtaCoherent`).  `etaSide` derives them once.

The parameter spine is NOT certified: the reduced type is a graded type
that is not the point ("not pt" source (1)), so its spine fits the
former's ∀-telescope in the graph regime (`teleFitPA_of_graded_ne_pt`).
The laws are read at that fit: a tower-backed family's through its
slot `0` entry (`TowerEntryLaw` (C)), a fieldless η family's through
`CapsOk`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

set_option maxHeartbeats 1600000 in
/-- **Structure η's stuck side.**  `b` reads as `ba`; the reduced type
`T targs` reads as the family's leaf at `tsa`.  The fabricated
projections (`etaProjs`) read to `ps`, framed; at a valuation where the
type is graded and not the point and `b` is a graded member of it, the
projections are graded, `b` is the η constructor at `tsa ++ ps`
(the η law), and that spine fits the constructor's type reading `TCa`
(the coherence law). -/
theorem etaSide (hin : RulesInputs V m φ) {d : Nat} {Δa : List Term}
    {T : Name} {cvT : ConstantVal} {caps : IndCaps} {us' : List Level}
    {cvC : ConstantVal} {nPc nFc : Nat}
    {targs : List Expr} {b : Expr} {tsa : List Term} {ba : Term}
    (hind : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresC : ConLeche.reservedBasisNames.contains caps.etaCtor = false)
    (hfC : env.find? caps.etaCtor = some (.ctorInfo cvC nPc nFc))
    (hlv : us'.length = cvT.levelParams.length)
    (htlen : targs.length = caps.etaParams)
    (htowS : ConLeche.towerSlotsAll env T caps.etaFields = true)
    (hfb : Frame d b) (hCb : CtxOkS m φ d Δa b)
    (hdb : denote m.acval env φ d b = some ba)
    (hspt : DenoteSpine m.acval env φ d targs tsa) :
    ∃ ps : List Term,
      DenoteSpine m.acval env φ d
        (ConLeche.etaProjs T b caps.etaFields) ps ∧
      (∀ x ∈ ConLeche.etaProjs T b caps.etaFields,
        Frame d x ∧ CtxOkS m φ d Δa x ∧
          ∀ l ∈ x.fvarLeaves, l ∈ b.fvarLeaves) ∧
      ∃ TCa : Term,
        denote m.acval env φ 0
          (cvC.type.instantiateLevelParams cvC.levelParams us') = some TCa ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d b ρ →
          (∀ x ∈ targs, LeavesGr m φ d x ρ) →
          WellDenoted V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ cvT.levelParams us')) tsa) →
          interp V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ cvT.levelParams us')) tsa) ≠ pt →
          WellDenoted V ρ ba →
          interp V ρ ba ∈ˢ interp V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ cvT.levelParams us')) tsa) →
          interp V ρ ba ≠ pt →
          (∀ x ∈ ConLeche.etaProjs T b caps.etaFields,
            LeavesGr m φ d x ρ) ∧
          (∀ x ∈ ps, WellDenoted V ρ x) ∧
          interp V ρ ba = ((tsa ++ ps).map (interp V ρ)).foldl SetTheory.app
            (interp V ρ (m.acval caps.etaCtor
              (Level.substFn φ cvT.levelParams us'))) ∧
          ∃ restC : V, TeleFit V ρ TCa ((tsa ++ ps).map (interp V ρ)) restC := by
  have hfold : ∀ (ρ : Nat → V) (l : List Term) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro ρ l x; rw [List.foldl_map]
  have hlenTs : ∀ ρ : Nat → V, (tsa.map (interp V ρ)).length = caps.etaParams := by
    intro ρ; rw [List.length_map, ← hspt.length, htlen]
  by_cases hkind : ConLeche.towerSlotsAll env T caps.etaFields = true ∧ 0 < caps.etaFields
  · -- TOWER-BACKED SLOTS: `.proj T j b` nodes, the slot-0 entry's laws
    obtain ⟨htow, h0⟩ := hkind
    obtain ⟨e0, hfe0⟩ := ConLeche.towerSlotsAll_slot htow 0 h0
    obtain ⟨-, -, -, ⟨cvT', capsT', hfT', hlpsT', himp'⟩,
      -, -, -, -, hetaL⟩ := hin.tower_ok T 0 e0 hfe0
    obtain ⟨rfl, rfl⟩ : cvT = cvT' ∧ caps = capsT' := by
      rw [hind] at hfT'
      exact ConstantInfo.indInfo.inj (Option.some.inj hfT')
    obtain ⟨hctr', hpar', hfld'⟩ := himp' heta
    obtain ⟨hlaw, hcoh⟩ :=
      hetaL cvT caps hind us' (by rw [← hlpsT']; exact hlv)
    obtain ⟨TCa, hTCa, hfitC⟩ :=
      hcoh heta cvC nPc nFc (by rw [← hctr']; exact hfC)
    have hslotE : ∀ j, j < caps.etaFields → ∃ entry : ProjEntry,
        env.findProj? T j = some entry := ConLeche.towerSlotsAll_slot htow
    refine ⟨(List.range caps.etaFields).map fun j => projNV (j + 1) ba,
      ?_, ?_, TCa, hTCa, fun ρ hρ hLb hLt hokW hneW hokB hmemB hneB => ?_⟩
    · rw [etaProjs_eq]
      refine DenoteSpine.map_list _ fun j hj => ?_
      obtain ⟨entry, hfe⟩ := hslotE j (List.mem_range.mp hj)
      exact denote_proj_tower hfe hdb
    · intro x hx
      rw [etaProjs_eq] at hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨⟨by simpa [Expr.WScoped] using hfb.1,
          by simpa [Expr.looseBVarsBounded] using hfb.2.1,
          fun l hl => hfb.2.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
        ⟨hCb.1, fun l hl => hCb.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
        fun l hl => by simpa [Expr.fvarLeaves] using hl⟩
    · have hfit : FamFit V ρ _ (tsa.map (interp V ρ)) := ⟨tsa, rfl, hokW, hneW⟩
      have hmemFam : interp V ρ ba
          ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
              (interp V ρ (m.acval T (Level.substFn φ e0.levelParams us'))) := by
        have h := hmemB
        rwa [interp_mkAppN, hfold, hlpsT'] at h
      have hlenP : (tsa.map (interp V ρ)).length = e0.numParams := by
        rw [hlenTs, hpar']
      have hb := hlaw ρ (tsa.map (interp V ρ)) (interp V ρ ba) hlenP
        (by rw [hlpsT'] at hfit; exact hfit) hmemFam
      obtain ⟨restC, hfC'⟩ := hfitC ρ (tsa.map (interp V ρ)) (interp V ρ ba)
        hlenP (by rw [hlpsT'] at hfit; exact hfit) hmemFam hneB
      have hps : ((List.range caps.etaFields).map fun j => projNV (j + 1) ba).map
            (interp V ρ)
          = (List.range e0.numFields).map fun j =>
              ConLeche.SetTheory.Tower.projS (j + 1) (interp V ρ ba) := by
        rw [List.map_map, hfld']
        refine List.map_congr_left fun j _ => ?_
        rw [Function.comp_apply, projNV_interp]
      refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, restC, ?_⟩
      · rw [etaProjs_eq] at hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
        exact fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl)
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        obtain ⟨entry, hfe⟩ := hslotE j (List.mem_range.mp hj)
        obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, hlpsTj, himpj⟩, cvCj,
          -, -, hlawj, -⟩ := hin.tower_ok T j entry hfe
        rw [hind] at hfTj
        obtain ⟨hcvTj, hcapsTj⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfTj)
        rw [← hcvTj] at hlpsTj
        rw [← hcapsTj] at himpj
        obtain ⟨-, hparj, -⟩ := himpj heta
        obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj us' (by rw [← hlpsTj]; exact hlv)
        obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
        have hlenVs : tsa.length = entry.numParams := by
          rw [← hspt.length, htlen, hparj]
        have hpc : PiChain (tsa ++ [ba]).length Ta := by
          rw [List.length_append, List.length_singleton, hlenVs]
          exact piChain_of_stripPis _
            (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
        obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
        rw [← hlpsTj] at hA
        exact (hA ρ tsa ba restj hlenVs hokW hneW hokB hmemB hpeel (Or.inr hneB)).1
      · rw [hb, List.map_append, hps, hctr', hlpsT']
      · rw [List.map_append, hps]; exact hfC'
  · -- NO FIELD: `CapsOk`'s law
    have h0 : caps.etaFields = 0 :=
      Nat.eq_zero_of_not_pos fun hpos => hkind ⟨htowS, hpos⟩
    have hetaP : ConLeche.etaProjs T b caps.etaFields = [] := by
      rw [etaProjs_eq, h0]; rfl
    have hfam : ConLeche.EtaFamilyStored env T caps := ⟨hresC, ⟨cvC, nPc, nFc, hfC⟩, h0⟩
    obtain ⟨hlaw, hcoh⟩ :=
      hin.caps_ok.1 T cvT caps hind heta hresT hfam φ us' hlv
    obtain ⟨TCa, hTCa, hfitC⟩ := hcoh cvC nPc nFc hfC
    refine ⟨[], ?_, ?_, TCa, hTCa, fun ρ _ _ _ hokW hneW _ hmemB hneB => ?_⟩
    · rw [hetaP]; exact DenoteSpine.nil
    · intro x hx
      rw [hetaP] at hx
      exact absurd hx List.not_mem_nil
    · have hfit : FamFit V ρ _ (tsa.map (interp V ρ)) := ⟨tsa, rfl, hokW, hneW⟩
      have hmemFam : interp V ρ ba
          ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
              (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
        have h := hmemB
        rwa [interp_mkAppN, hfold] at h
      have hb := hlaw ρ (tsa.map (interp V ρ)) (interp V ρ ba) (hlenTs ρ) hfit hmemFam
      obtain ⟨restC, hfC'⟩ := hfitC ρ (tsa.map (interp V ρ)) (interp V ρ ba)
        (hlenTs ρ) hfit hmemFam hneB
      refine ⟨fun x hx => ?_, fun x hx => absurd hx List.not_mem_nil, ?_, restC, ?_⟩
      · rw [hetaP] at hx
        exact absurd hx List.not_mem_nil
      · rw [List.append_nil]; exact hb
      · rw [List.append_nil]; exact hfC'

end ConLeche.Model.Rules
