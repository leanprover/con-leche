module

public import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Semantics.DeclRun
public import ConLeche.Cached.Justify
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.CheckerF
import ConLeche.Semantics.Bridge.DeclRun

/-!
# The justification route, as a pure run

`checkRecordC`'s justification route (a record offering a statement, a solution given) is, from a
canonical index of a well-formed environment: the statement justified (`justifyWhy`), its type's
front door as the pure checker runs it (`ConstantValRun`), the reserved names' check, and the
statement pushed as an axiom.  The model's step for a justified axiom starts here.
-/

public section

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics

variable {pins : List NatOpPinSet}

/-- **A justified record's check, run.** -/
theorem checkRecordC_justified_run {env : Env} (henv : EnvWF env) {J : Solution} {pd : Declaration}
    {cv : ConstantVal} (hj : justifiable pd = some cv) {s₀ : CState} (hres : CSOKF s₀)
    {fe' : FEnv} {s' : CState}
    (h : checkRecordC .verified pins (some J) (mkFEnv env) pd s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv ⟨.axiomInfo cv :: env.consts, env.tables⟩ ∧
      justifyWhy J (mkFEnv env) cv = none ∧ basisNamesOk pd = true ∧
      ∃ F, ConstantValRun F env cv cv.type := by
  unfold checkRecordC at h
  simp only [hj] at h
  obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcsok : CSOK .verified false env s₀.flushed := flushC_csok hres
  cases hw : justifyWhy J (mkFEnv env) cv with
  | some why =>
    rw [hw] at h
    simp [throw, throwThe, MonadExceptOf.throw, StateT.bind, bind] at h
    exact nomatch h
  | none =>
    rw [hw] at h
    obtain ⟨u₂, s₂, hcv, h⟩ := bindC_ok h
    obtain ⟨hs₂, ⟨F, hF⟩, -⟩ := triple_iff_run.mp (checkConstantValC_spec henv hcsok) u₂ s₂ hcv
    rw [checkConstantVal_datF] at hF
    obtain ⟨-, -, hrun⟩ := constantValRun_of hF
    have hb : basisNamesOk pd = true := by
      by_cases hb : basisNamesOk pd = true
      · exact hb
      · simp [hb, throw, throwThe, MonadExceptOf.throw, StateT.bind, bind] at h
        exact nomatch h
    simp only [hb, ↓reduceIte] at h
    obtain ⟨hfe, hst⟩ := pureC_ok h
    subst hst
    refine ⟨hs₂.residue, ?_, rfl, hb, F, hrun⟩
    rw [← hfe, push_mkFEnv]

end ConLeche.Cached
