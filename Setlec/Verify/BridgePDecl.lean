import Setlec.Verify.BridgeSDecl
import Setlec.Verify.BridgeP
import Setlec.Verify.BracketB4

/-!
# The parsed-index step, bridged (V-free)

`checkDeclSPStep_run`: a successful parsed-index step is reproduced by
the pure fueled `checkDecl` on the *denoted* declaration, with the
interning residue (`ISOKF`) and the store extension (`Ext`) carried
alongside.  Shared tier because both soundness routes consume it and
neither may import the other (task #148 T6).
-/

namespace Setlec

open EStore Expr

variable {mode : CheckMode}

/-- A successful step validated its indices. -/
theorem checkDeclSPStep_inRange {n0 : Nat} {fe : FEnv}
    {pd : DeclP} {s₀ : IState} {fe' : FEnv} {s' : IState}
    (h : checkDeclSPStep mode n0 fe pd s₀ = .ok (fe', s')) :
    pd.inRangeB n0 = true := by
  unfold checkDeclSPStep at h
  by_cases hin : pd.inRangeB n0 = true
  · exact hin
  · rw [if_neg hin] at h
    exact absurd h (fun h => nomatch h)

/-- One step of the parsed fold: a successful run from a residue state
is reproduced by the pure fueled checker on the denoted declaration,
and the residue and arena extension thread to the next step. -/
theorem checkDeclSPStep_run {env : Env} (henv : EnvWF env) {pd : DeclP}
    {d : Declaration} {n0 : Nat} {s₀ : IState} (hres : ISOKF s₀)
    (hden : denoteDeclP s₀.store pd = some d)
    {fe' : FEnv} {s' : IState}
    (h : checkDeclSPStep mode n0 (mkFEnv env) pd s₀ = .ok (fe', s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env d = .ok fe'.env := by
  unfold checkDeclSPStep at h
  by_cases hin : pd.inRangeB n0 = true
  case neg =>
    rw [if_neg hin] at h
    exact absurd h (fun h => nomatch h)
  rw [if_pos hin] at h
  obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hisok : ISOK mode env s₀.flushed := flushS_isok hres
  have hden' : denoteDeclP s₀.flushed.store pd = some d := hden
  have main : (∀ block, pd ≠ .indDecl block) →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, checkDecl mode (fueledOps mode F) env d = .ok fe'.env := by
    intro hind
    obtain ⟨hs', hext, v, ⟨henvEq, hmk⟩, F, hF⟩ :=
      (checkDeclSP_sim henv hisok hres.wf.tier_off hden' hind) fe' s' h
    refine ⟨hs'.residue (tierOffE hext hres.wf.tier_off), hext, hmk,
      F, ?_⟩
    rw [← checkDecl_datF, henvEq]
    exact hF
  cases pd with
  | indDecl block =>
    obtain rfl : Declaration.indDecl block = d := by
      simpa [denoteDeclP] using hden'
    have hrun : (match directPartsF? (mkFEnv env) block with
        | some p => checkDirectStructS mode (mkFEnv env) p
        | none => checkIndDeclSF mode (mkFEnv env) block) s₀.flushed =
        .ok (fe', s') := h
    obtain ⟨hres', hext, hfe, F, hF⟩ :=
      checkIndOrDirectSF_run henv (hisok.residue hres.wf.tier_off) hrun
    exact ⟨hres', hext, hfe, F, hF⟩
  | defnDecl cv value hint => exact main (fun _ h => DeclP.noConfusion h)
  | thmDecl cv value => exact main (fun _ h => DeclP.noConfusion h)
  | opaqueDecl cv value => exact main (fun _ h => DeclP.noConfusion h)
  | axiomDecl cv => exact main (fun _ h => DeclP.noConfusion h)
  | basisDecl kind => exact main (fun _ h => DeclP.noConfusion h)

end Setlec
