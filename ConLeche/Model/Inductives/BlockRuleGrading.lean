module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.FixKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The rule frame's GRADING, at the run

Fits of a Π-tower reading from `SpineFit`, and the grading of a rule
frame's prefix and field segments at the run (`blockRuleHokPF_run`,
from `blockRuleHokA_of_run` in `BlockRecPreRun.lean`).  Every statement
is at the frame the segment quantifies: a prefix fitting the
recursor's prefix domains and fields fitting the constructor's field
domains.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Fits of a Π-tower reading, from `SpineFit` -/

section TowerFits

/-- **A `SpineFit` of a Π-tower's domains at the readings of a spine is
a `TeleFitPA` of the tower at the spine** — `spineFit_of_teleFitPA`'s
converse. -/
theorem teleFitPA_mkPisAV_of_spineFit {pds : List Term} {b : Term}
    {ρ : Nat → V} {ws : List Term} (hlen : ws.length = pds.length)
    (hsp : SpineFit ρ pds (ws.map (interp V ρ))) :
    ∃ rest, TeleFitPA V ρ (mkPisAV pds b) ws rest := by
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV pds b)
  refine ⟨_, teleFitPA_of_tower pds.length htele hlen fun n hn => ?_⟩
  have hm := FixKI.spineFit_getD_mem' hsp hn
  have hwn : n < ws.length := by omega
  have e1 : (ws.map (interp V ρ)).getD n pt = interp V ρ (ws.getD n default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hwn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwn]
    rfl
  have e2 : (ws.map (interp V ρ)).take n = (ws.take n).map (interp V ρ) := by
    rw [List.map_take]
  have e3 : pds.reverse.getD (pds.length - 1 - n) default
      = pds.getD n default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega),
      show pds.length - 1 - (pds.length - 1 - n) = n from by omega,
      ← List.getD_eq_getElem?_getD]
  rw [e1, e2] at hm
  rw [e3, chain, consN_eq_consList]
  exact hm

/-- **A telescope bounded at its own depths fits at every frame alike**:
entry `l` reads only the `l` values before it. -/
theorem spineFit_frame_of_bounded {Ds : List Term}
    (hb : ∀ l, l < Ds.length → Term.bvarsBelow l (Ds.getD l default))
    {σ σ' : Nat → V} {vs : List V} (h : SpineFit σ Ds vs) : SpineFit σ' Ds vs := by
  have hlen : vs.length = Ds.length := h.length_eq
  refine spineFit_of_getD hlen fun r hr => ?_
  have hm := FixKI.spineFit_getD_mem' h hr
  have htl : (vs.take r).length = r := by rw [List.length_take]; omega
  rw [interp_congr_below (V := V) (Ds.getD r default) r (consList (vs.take r) σ')
    (consList (vs.take r) σ) (hb r hr) fun i hi => by
      rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]]
  exact hm

end TowerFits

end ConLeche.Model
