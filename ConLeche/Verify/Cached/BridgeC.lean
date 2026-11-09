module

import ConLeche.Verify.Cached.PinOverlay
import ConLeche.Verify.Cached.PinsC
import ConLeche.Cached.ParsedC
public import ConLeche.Verify.Cached.GenRecC

public section

/-!
# The cached parsed-declaration driver, bridged (task #163)

Each lemma relates a `ParsedC` driver function
(`ConLeche/Cached/ParsedC.lean`, `checkConstantValC` …) to the generic
declaration checker at the fueled families, as a `Std.WP` triple from
any invariant state, proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`).

* the syntactic guards are pure `Expr` walks —
  `Expr.looseBVarsBounded`/`Expr.hasFvar`/
  `Expr.allLevelParamsDefined`/`constsResolveFC` — and their agreement
  with the `Expr`-side guards is `ConLeche/Verify/Cached/GuardsC.lean`'s
  `*_spec` family;
* `opSIxC` has no level-readback wrapper (levels are trees): it is the
  shared operation `opS`;
* the pinned arms certify against a one-constant overlay of the index,
  which answers every reader as the fueled arm's consed environment.

`Declaration` is one type for both drivers (task #285): the two are
given the same record.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

section WalksP

variable {env : Env} {s₀ : CState}

/-! ## The knot's entry points at the checker's fuel

The knot's entry points at the checker's fuel, with the posts at the
fueled operations (`fueledOpsM`) the generic checker functions call:
the parsed driver calls the knot directly, not through `sharedOpsC`. -/

theorem inferK_spec (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified false (mkFEnv env) checkFuel).infer d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opE_infer_spec henv hs hw

theorem defeqK_spec (henv : EnvWF env) {d : Nat}
    {a b : Expr} (hs : CSOK .verified false env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified false (mkFEnv env) checkFuel).defeq d a b
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).isDefEq env d a b) v; ⊤⦄ :=
  opB_spec henv hs hwa hwb

/-! ## Parsed-index entry operations -/

/-- Parsed `ensureSort` is the shared operation `opS`. -/
theorem opSIxC_spec (henv : EnvWF env) {d : Nat} {i : Expr}
    (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ opSIxC .verified (mkFEnv env) d i
    ⦃fun u s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).ensureSort env d i) u; ⊤⦄ :=
  opS_spec henv hs hw

/-! ## The parsed-declaration checker functions -/

/-- `checkConstantValC` simulates the generic `checkConstantVal` at the
fueled families; the checked type is well scoped. -/
theorem checkConstantValC_spec (henv : EnvWF env)
    {cv : ConstantVal} {a : Bool} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkConstantValC .verified (mkFEnv env) cv a
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs (checkConstantVal (fueledOpsM .verified) env cv a) v ∧
      Expr.WScoped 0 cv.type; ⊤⦄ := by
  sym only [conleche_grind, checkConstantVal.eq_1,
      Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec, constsResolveF_eq,
      @wscoped_of_hasFvar_false 0 cv.type] =>
    vcgen [checkConstantValC, inferK_spec henv hs, opSIxC_spec henv] <;> finish

/-! ## The pinned arms' overlay

The pinned arms of `checkDeclC` certify against a one-constant overlay
of the index (`FEnv.overlay`); on `mkFEnv env` it answers every reader
as the pure arm's consed environment does (`find?_overlay_push`). -/

theorem find?_overlay_mkFEnv (env : Env) (ci : ConstantInfo) (n : Name) :
    ((mkFEnv env).overlay [ci]).find? n = Env.find? ⟨ci :: env.consts, env.tables⟩ n := by
  rw [find?_overlay_push (fe := mkFEnv env) rfl ci, push_mkFEnv, mkFEnv_find?]

theorem natOpGuardF_overlay (env : Env) (ci : ConstantInfo) (c : Name) :
    natOpGuardF ((mkFEnv env).overlay [ci]) c = natOpGuard ⟨ci :: env.consts, env.tables⟩ c := by
  rw [natOpGuardF_congr (find?_overlay_push (fe := mkFEnv env) rfl ci), push_mkFEnv,
    natOpGuardF_eq]

theorem natOpStoredOkF_overlay (env : Env) (ci : ConstantInfo) :
    natOpStoredOkF ((mkFEnv env).overlay [ci]) = natOpStoredOk ⟨ci :: env.consts, env.tables⟩ := by
  rw [natOpStoredOkF_congr (find?_overlay_push (fe := mkFEnv env) rfl ci), push_mkFEnv,
    natOpStoredOkF_eq_fun]

theorem checkReducePinF_overlay (ops : CheckerOps CheckCM) (env : Env) (ci : ConstantInfo)
    (c : Name) (value : Expr) :
    checkReducePinF ops (mkFEnv env) ((mkFEnv env).overlay [ci]) c value
      = checkReducePin ops env ⟨ci :: env.consts, env.tables⟩ c value := by
  rw [checkReducePinF_congr2 _ _ (find?_overlay_push (fe := mkFEnv env) rfl ci), push_mkFEnv,
    checkReducePinF_eq]

theorem checkDivModPinF_overlay (ops : CheckerOps CheckCM) (env : Env) (ci : ConstantInfo)
    (c : Name) :
    checkDivModPinF ops pins (mkFEnv env) ((mkFEnv env).overlay [ci]) c
      = checkDivModPin ops pins env ⟨ci :: env.consts, env.tables⟩ c := by
  rw [checkDivModPinF_congr2 _ _ _ (find?_overlay_push (fe := mkFEnv env) rfl ci), push_mkFEnv,
    checkDivModPinF_eq]

/-- The cached pin check at the arm's overlay (`checkDivModPinC_eq`, task #497). -/
theorem checkDivModPinC_overlay (ops : CheckerOps CheckCM) (env : Env) (ci : ConstantInfo)
    (c : Name) :
    checkDivModPinC ops pins (mkFEnv env) ((mkFEnv env).overlay [ci]) c
      = checkDivModPin ops pins env ⟨ci :: env.consts, env.tables⟩ c := by
  rw [checkDivModPinC_eq, checkDivModPinF_overlay]

/-- The structural-`Nat` recurrences at a closed stored value (at the
cached arm's `(mkFEnv env).env`). -/
theorem certifyNatOpEqsS_spec (henv : EnvWF env) {c : Name}
    {v : Expr} (hc : natOpNames.contains c = true) (hvf : v.hasFvar = false)
    (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ certifyNatEqs (sharedOpsC .verified (mkFEnv env)) (mkFEnv env).env
      ((natOpEquations 0 c).map fun eq => (Expr.substConst0 c v eq.1, Expr.substConst0 c v eq.2))
    ⦃fun r s' => CSOK .verified false env s' ∧ Runs (certifyNatEqs (fueledOpsM .verified) env
      ((natOpEquations 0 c).map fun eq =>
        (Expr.substConst0 c v eq.1, Expr.substConst0 c v eq.2))) r; ⊤⦄ := by
  refine certifyNatEqsS_spec henv (fun eq heq => ?_) hs
  obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
  obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB (by simpa using hc) eq₀ heq₀
  exact ⟨wscopedB_substConst0 hvf _ hs1, wscopedB_substConst0 hvf _ hs2⟩

/-- The `Nat.div`/`Nat.mod` pin at the consed environment, whose head
stores the closed value. -/
theorem checkDivModPinConsS_spec (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint} {ci : ConstantInfo}
    (hci : ci = .defnInfo cv value hint)
    (hc : natDivModNames.contains cv.name = true) (hvf : value.hasFvar = false)
    (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkDivModPin (sharedOpsC .verified (mkFEnv env)) pins env
      ⟨ci :: env.consts, env.tables⟩ cv.name
    ⦃fun r s' => CSOK .verified false env s' ∧ Runs (checkDivModPin (fueledOpsM .verified) pins env
      ⟨ci :: env.consts, env.tables⟩ cv.name) r; ⊤⦄ := by
  subst hci
  refine checkDivModPinS_spec henv (List.contains_iff_mem.mp hc) (fun cv' v' h' hf => ?_) hs
  have hself : Env.find? ⟨.defnInfo cv value hint :: env.consts, env.tables⟩ cv.name
      = some (.defnInfo cv value hint) := Env.find?_cons_self _ _
  rw [hself] at hf
  cases hf
  exact hvf

/-- `checkDefnValCI` simulates the generic `checkDefnVal`: the record it
returns is the definition the fueled side conses, its value closed. -/
theorem checkDefnValCI_spec (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (htf : Expr.WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkDefnValCI .verified (mkFEnv env) cv value hint
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkDefnVal (fueledOpsM .verified) env cv value hint) ⟨v :: env.consts, env.tables⟩ ∧
      v = .defnInfo cv value hint ∧ value.hasFvar = false; ⊤⦄ := by
  sym only [conleche_grind, checkDefnVal.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [checkDefnValCI, inferK_spec henv hs, defeqK_spec henv] <;> finish

/-- `checkThmValCI` simulates the generic `checkThmVal`: the record it returns is the statement the
fueled side conses. -/
theorem checkThmValCI_spec (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (htf : Expr.WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkThmValCI .verified (mkFEnv env) cv value
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkThmVal (fueledOpsM .verified) env cv value) ⟨v :: env.consts, env.tables⟩ ∧
      v = .thmInfo cv; ⊤⦄ := by
  sym only [conleche_grind, checkThmVal.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [checkThmValCI, inferK_spec henv, opSIxC_spec henv,
      liftFueled_spec (mode := .verified) (eager := false) (env := env), defeqK_spec henv] <;> finish

/-- `checkOpaqueValCI` simulates the generic `checkOpaqueVal`: the
record it returns is the axiom the fueled side conses, the value
closed. -/
theorem checkOpaqueValCI_spec (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (htf : Expr.WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkOpaqueValCI .verified (mkFEnv env) cv value
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkOpaqueVal (fueledOpsM .verified) env cv value) ⟨v :: env.consts, env.tables⟩ ∧
      v = .axiomInfo cv ∧ value.hasFvar = false; ⊤⦄ := by
  sym only [conleche_grind, checkOpaqueVal.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [checkOpaqueValCI, inferK_spec henv hs, defeqK_spec henv] <;> finish

/-! ## The converted declaration -/

/-- A quotient record's install simulates its generic twin: operation-free,
the state is unchanged and the environment is the generic twin's. -/
theorem checkQuotRecordC_spec (hs : CSOK mode false env s₀) (k : QuotKind) (cv : ConstantVal) :
    ⦃fun s => s = s₀⦄ checkQuotRecordC (mkFEnv env) k cv
    ⦃fun v s' => CSOK mode false env s' ∧
      Runs (checkQuotRecord (m := FueledM) env k cv) v.env ∧
      v = mkFEnv v.env; ⊤⦄ := by
  refine triple_iff_run.mpr fun v s' h => ?_
  unfold checkQuotRecordC at h
  rw [mkFEnv_find_fun] at h
  by_cases h1 : quotPinHit k cv = true
  · rw [ite_eq_left h1] at h
    by_cases h2 : quotPredsOk env.find? k = true
    · rw [ite_eq_left h2, installBasisDeclF_pushC] at h
      by_cases h3 : (env.find? (quotAt k cv).name).isNone = true
      · simp only [installBasisDecl, Option.isNone_iff_eq_none.mp h3] at h
        obtain ⟨rfl, rfl⟩ := pureC_ok h
        refine ⟨hs, ⟨0, ?_⟩, by simp only [mkFEnv_env]⟩
        rw [mkFEnv_env, checkQuotRecord_datF]
        unfold checkQuotRecord
        rw [ite_eq_left h1, ite_eq_left h2]
        simp [installBasisDecl, Option.isNone_iff_eq_none.mp h3]
        rfl
      · simp only [installBasisDecl, h3] at h
        exact nomatch h
    · rw [ite_eq_right h2] at h
      exact nomatch h
  · rw [ite_eq_right h1] at h
    exact nomatch h

/-- The non-inductive branches of a declaration's own checks, `checkDeclKindC`, simulate the
generic `checkDeclKind` at the fueled families on the same declaration. -/
theorem checkDeclKindC_spec (henv : EnvWF env)
    (hs : CSOK .verified false env s₀) {pd : Declaration}
    (hnotind : ∀ block nP, pd ≠ .indDecl block nP) :
    ⦃fun s => s = s₀⦄ checkDeclKindC .verified pins (mkFEnv env) pd
    ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkDeclKind (fueledOpsM .verified) pins env pd) v.env ∧
      v = mkFEnv v.env; ⊤⦄ := by
  cases pd with
  | indDecl block nP => exact absurd rfl (hnotind _ _)
  | quotDecl k cv =>
    sym only [conleche_grind, checkDeclKind, mkFEnv_env] =>
      vcgen [checkDeclKindC, checkQuotRecordC_spec hs] <;> finish
  | axiomDecl cv =>
    sym only [conleche_grind, checkDeclKind, stdAxiomOkF_eq, trustCompilerOkF_eq, ofReduceAxOkF_eq,
        push_mkFEnv, mkFEnv_env] =>
      vcgen [checkDeclKindC, checkConstantValC_spec henv hs, checkQuotRecordC_spec hs] <;> finish
  | thmDecl cv value =>
    sym only [conleche_grind, checkDeclKind, push_mkFEnv, mkFEnv_env] =>
      vcgen [checkDeclKindC, checkConstantValC_spec henv hs, checkThmValCI_spec henv] <;> finish
  | opaqueDecl cv value =>
    sym only [conleche_grind, checkDeclKind, push_mkFEnv, mkFEnv_env] =>
      vcgen [checkDeclKindC, checkConstantValC_spec henv hs, checkOpaqueValCI_spec henv,
        checkReducePinF_overlay, checkReducePinS_spec henv] <;> finish
  | defnDecl cv value hint =>
    sym only [conleche_grind, checkDeclKind, push_mkFEnv, mkFEnv_env, natOpGuardF_overlay,
        natOpStoredOkF_overlay, find?_overlay_mkFEnv, Env.find?_cons, ConstantInfo.name,
        ConstantInfo.toConstantVal] =>
      vcgen [checkDeclKindC, checkConstantValC_spec henv hs, checkDefnValCI_spec henv,
        checkDivModPinC_overlay, certifyNatOpEqsS_spec henv,
        checkDivModPinConsS_spec henv (cv := cv) (value := value) (hint := hint)] <;> finish

/-- One step of the converted-declaration fold: a successful run from a
residue state is reproduced by the pure fueled checker on the same
declaration, and the residue threads to the next step.  The cached
driver has no bracket and no index-range check, so the step is `flushC`
followed by `checkDeclC`: the declaration's own checks, then the reserved names'. -/
theorem checkDeclStepC_run {env : Env} (henv : EnvWF env) {pd : Declaration}
    {s₀ : CState} (hres : CSOKF s₀) {fe' : FEnv} {s' : CState}
    (h : checkDeclStepC .verified pins (mkFEnv env) pd s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl .verified (fueledOps .verified F) pins env pd = .ok fe'.env := by
  unfold checkDeclStepC at h
  obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcsok : CSOK .verified false env s₀.flushed := flushC_csok hres
  unfold checkDeclC at h
  obtain ⟨fe₂, s₂, hk, h⟩ := bindC_ok h
  have hb : basisNamesOk pd = true := by
    by_cases hb : basisNamesOk pd = true
    · exact hb
    · simp [hb, throw, throwThe, MonadExceptOf.throw, StateT.bind, bind] at h
      exact nomatch h
  simp only [hb, ↓reduceIte] at h
  obtain ⟨hfe, hst⟩ := pureC_ok h
  rw [← hfe, ← hst]
  suffices hkind : CSOKF s₂ ∧ fe₂ = mkFEnv fe₂.env ∧
      ∃ F, checkDeclKind (fueledOps .verified F) pins env pd = .ok fe₂.env by
    obtain ⟨h1, h2, F, hF⟩ := hkind
    exact ⟨h1, h2, F, checkDecl_of_kind hF hb⟩
  cases pd with
  | indDecl block nP =>
    -- the declared parameter count (task #228) is a guard whose `false`
    -- throws on both sides, so only the passing branch reaches the bridge
    have hd : (if indParamsOk nP block = true then
          (match readBlock nP block with
            | .ok p => checkBlockKS .verified (mkFEnv env) block p
            | .error e => throw e)
        else throw (CheckError.invalid "number of parameters mismatch"))
        s₀.flushed = .ok (fe₂, s₂) := hk
    by_cases hok : indParamsOk nP block = true
    · rw [ite_eq_left hok] at hd
      exact checkModeledOrNativeSF_run henv hok hres.flushed hd
    · rw [ite_eq_right hok] at hd
      exact nomatch hd
  | _ =>
    obtain ⟨hs', ⟨F, hF⟩, hmk⟩ := triple_iff_run.mp
      (checkDeclKindC_spec henv hcsok (fun _ _ h => Declaration.noConfusion h)) fe₂ s₂ hk
    refine ⟨hs'.residue, hmk, F, ?_⟩
    rw [← checkDeclKind_datF]
    exact hF

end WalksP

end ConLeche.Cached
