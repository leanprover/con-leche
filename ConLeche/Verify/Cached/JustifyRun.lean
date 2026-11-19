module

public import ConLeche.Verify.Cached.DeclPushes
public import ConLeche.Verify.Cached.Justify
import ConLeche.Verify.Cached.DeclNames
import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF

/-!
# What an accepted fold with a sidecar says of its justified axioms

Every record the fold reads as a justified axiom (`justifiable`) took the justification route of
`checkRecordC`, so the sidecar stores a constant of its name whose statement is the record's up
to the names of the level parameters (`declsRun_justified`).  In particular a justified axiom of
type `False` is the statement of a sidecar constant of type `False` (`justified_false`), which
no accepted sidecar stores (`no_proof_of_False_cached`): no model is needed for that.
-/

public section

namespace ConLeche.Cached

open ConLeche

/-- **A justified record passed the justification.** -/
theorem checkRecordC_justified (mode : CheckMode) (pins : List NatOpPinSet) {J : Sidecar} {fe : FEnv}
    {pd : Declaration} {cv : ConstantVal} (hj : justifiable pd = some cv) :
    Yields (checkRecordC mode pins (some J) fe pd) (fun _ => justifyWhy J fe cv = none) := by
  unfold checkRecordC
  simp only [hj]
  refine Yields.bind fun _ => ?_
  cases justifyWhy J fe cv with
  | some why => exact Yields.ofThrowBind
  | none => exact Yields.const rfl

/-- **Along an accepting run, every justified record passed the justification**, at the index
the run had reached. -/
theorem declsRun_justified {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {J : Sidecar} {ds : List Declaration} {p q : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize (some J) ds p q) {pd : Declaration} {cv : ConstantVal}
    (hpd : pd ∈ ds) (hj : justifiable pd = some cv) : ∃ fe, justifyWhy J fe cv = none := by
  induction h with
  | nil p => exact absurd hpd List.not_mem_nil
  | @cons pd' ds p p₁ q hstep rest ih =>
    rcases List.mem_cons.mp hpd with rfl | hpd
    · obtain ⟨fe₁, s₁, -, hstepC⟩ := declStep_ok hstep
      exact ⟨p.2, checkRecordC_justified mode pins hj _ _ _ hstepC⟩
    · exact ih hpd

/-- **A justified statement is a sidecar constant's**, up to the names of its level
parameters. -/
theorem justifyWhy_none {J : Sidecar} {fe : FEnv} {cv : ConstantVal} (h : justifyWhy J fe cv = none) :
    ∃ cS, J.idx.find? cv.name = some cS ∧ sameCvUpToLevels cv cS.toConstantVal = true := by
  unfold justifyWhy at h
  split at h
  · exact nomatch h
  · next cS hf =>
    refine ⟨cS, hf, ?_⟩
    split at h
    · exact nomatch h
    · next hs => simpa using hs

/-- A type that reads as the constant `False` at other level names is that constant. -/
theorem instantiateLevelParams_false {ks : List Name} {us : List Level} {e : Expr}
    (h : e.instantiateLevelParams ks us = .const falseName []) : e = .const falseName [] := by
  cases e with
  | const n vs =>
    simp only [Expr.instantiateLevelParams, Expr.const.injEq, List.map_eq_nil_iff] at h
    rw [h.1, h.2]
  | _ => simp [Expr.instantiateLevelParams] at h

/-- **A statement of type `False`, the sidecar's up to level names, is of type `False`.** -/
theorem sameCvUpToLevels_false {cv cv' : ConstantVal} (h : sameCvUpToLevels cv cv' = true)
    (hty : cv.type = .const falseName []) : cv'.type = .const falseName [] := by
  unfold sameCvUpToLevels at h
  split at h
  · rw [← ConstantVal.eq_of_beqP h, hty]
  · simp only [Bool.and_eq_true] at h
    have he := ConstantVal.eq_of_beqP h.2
    rw [← ConstantVal.atLps_eq_atLpsC] at he
    have ht := congrArg ConstantVal.type he
    rw [hty] at ht
    exact instantiateLevelParams_false ht

/-- **A justified axiom of type `False` names a sidecar constant of type `False`**: in an
accepted fold with the sidecar `envS`, every record read as a justified axiom of type `False`
has a constant of its name in `envS`, of type `False`. -/
theorem justified_false {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {envS env : Env} {ds : Array Declaration}
    (h : checkDecls mode pins maxNatSize ds (some envS) = .ok env) {pd : Declaration}
    {cv : ConstantVal} (hpd : pd ∈ (sideRecords (some envS) ds).toList)
    (hj : justifiable pd = some cv) (hty : cv.type = .const falseName []) :
    ∃ cS ∈ envS.consts, cS.toConstantVal.type = .const falseName [] := by
  obtain ⟨n, fe, hrun, -⟩ := checkDecls_run mode h
  obtain ⟨fe', hw⟩ := declsRun_justified hrun hpd hj
  obtain ⟨cS, hf, hs⟩ := justifyWhy_none hw
  rw [ConLeche.mkFEnv_find?] at hf
  exact ⟨cS, Env.find?_mem hf, sameCvUpToLevels_false hs hty⟩

end ConLeche.Cached
