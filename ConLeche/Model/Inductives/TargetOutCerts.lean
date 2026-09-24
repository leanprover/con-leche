module

public import ConLeche.Model.Inductives.TargetOutGrade
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.FixRuleData
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The rule certificates at an OUTSIDE class (lane NESTIND, session 7)

`graphRecPre_core`'s `hcerts` at a recursor whose major is an outside
container: `BlockRuleCerts` at the target check's rule data
(`tgtFdomsAV`, `tgtIhdomsAV`, `tgtRbAV`, `tgtCaAV`).  The member row is
`tgtRuleCertsW_run` (`TargetRowCertsW.lean`); the frame-level facts are
shared (`targetFrame_facts`, `targetRule_reads`, `targetIh_scope`, over
the major's parameters scoped at the prefix, `TgtDsOk`); what differs
at an outside class is

* `tgtOutDsOk` — the major's parameters are the arguments of the
  recursor type's major domain: scoped at the prefix, naming stored
  constants, drawing their leaves from the prefix openers;
* the fields' readings and grading — the instantiated constructor's
  (`tgtOutOpen`, `tgtOutCrestWd`);
* the conclusion `Ca` — its peel at the target spellings (`tgtOutCaAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Certs

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {outside nested : Bool} {block : List ConstantInfo}

/-- **An outside major's parameters are scoped at the prefix** (`TgtDsOk`):
the arguments of the recursor type's major domain, bounded below the
block's parameter count, naming stored constants, their leaves prefix
openers. -/
theorem tgtOutDsOk {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none) :
    TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds := by
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨hw0, -⟩ := recStage_tyClosed h hr
  obtain ⟨-, -, hTres, -, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound envC r.1.type := constsBound_of_constsResolve _ hTres
  have hsc := outsideDs_scoped E hMo hw0
  obtain ⟨-, -, -, -, -, -, hdsE, -, -, -, -⟩ := E.outside_of hMo
  -- the prefix openers are the major opening's first `rP`
  obtain ⟨o', hop'⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) r.1.type 0
    (by have := E.hle; omega) E.hopen
  have hPref : tgtPrefFvs pp.toBlockShape out j = E.fvs.take rc.rP := by
    rw [tgtPrefFvs, tgtRecTy_at hr, hRP, hop']; rfl
  rw [hRP, hPref]
  -- the major is an opener, so its type names stored constants
  have hcbMaj : ConstsBound envC E.maj.fvarTypeD := by
    obtain ⟨tyM, hmajE⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen rc.mI E.maj E.hmaj
    have hc := (openPisAtFvars_constsBound _ hTc E.hopen).1 E.maj (List.mem_of_getElem? E.hmaj)
    rw [hmajE] at hc ⊢
    simpa [ConstsBound, Expr.fvarTypeD] using hc
  intro a ha
  obtain ⟨hwa, hba, hla⟩ := hsc a ha
  have hroom := E.hroom
  refine ⟨Expr.WScoped.mono hroom hwa, hba, ?_, fun l hl => ?_⟩
  · rw [hdsE] at ha
    exact constsBound_getAppArgs _ hcbMaj a (List.mem_of_mem_take ha)
  · obtain ⟨hlt, hmem⟩ := hla l hl
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen k _ hk
    injection hty with hk1 _
    rw [Nat.zero_add] at hk1
    rw [List.mem_iff_getElem?]
    exact ⟨k, by rw [List.getElem?_take, if_pos (by omega)]; exact hk⟩

end Certs

end ConLeche.Model
