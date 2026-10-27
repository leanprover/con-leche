module

import ConLeche.Verify.Cached.PinOverlay
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

theorem inferK_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) checkFuel).infer d e
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opE_infer_spec hμ henv hs hw

theorem defeqK_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {a b : Expr} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) checkFuel).defeq d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).isDefEq env d a b) v; ⊤⦄ :=
  opB_spec hμ henv hs hwa hwb

/-! ## Parsed-index entry operations -/

/-- Parsed `ensureSort` is the shared operation `opS`. -/
theorem opSIxC_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ opSIxC mode (mkFEnv env) d i
    ⦃fun u s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).ensureSort env d i) u; ⊤⦄ :=
  opS_spec hμ henv hs hw

/-! ## The parsed-declaration checker functions -/

/-- `checkConstantValC` simulates the generic `checkConstantVal` at the
fueled families; the checked type is well scoped. -/
theorem checkConstantValC_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkConstantValC mode (mkFEnv env) cv
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkConstantVal (fueledOpsM mode) env cv) v ∧
      Expr.WScoped 0 cv.type; ⊤⦄ := by
  sym only [conleche_grind, checkConstantVal.eq_1,
      Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec, constsResolveF_eq,
      @wscoped_of_hasFvar_false 0 cv.type] =>
    vcgen [checkConstantValC, inferK_spec hμ henv hs, opSIxC_spec hμ henv] <;> finish

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

/-- The structural-`Nat` recurrences at a closed stored value (at the
cached arm's `(mkFEnv env).env`). -/
theorem certifyNatOpEqsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {c : Name}
    {v : Expr} (hc : natOpNames.contains c = true) (hvf : v.hasFvar = false)
    (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ certifyNatEqs (sharedOpsC mode (mkFEnv env)) (mkFEnv env).env
      ((natOpEquations 0 c).map fun eq => (Expr.substConst0 c v eq.1, Expr.substConst0 c v eq.2))
    ⦃fun r s' => CSOK mode env s' ∧ Runs (certifyNatEqs (fueledOpsM mode) env
      ((natOpEquations 0 c).map fun eq =>
        (Expr.substConst0 c v eq.1, Expr.substConst0 c v eq.2))) r; ⊤⦄ := by
  refine certifyNatEqsS_spec hμ henv (fun eq heq => ?_) hs
  obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
  obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB (by simpa using hc) eq₀ heq₀
  exact ⟨wscopedB_substConst0 hvf _ hs1, wscopedB_substConst0 hvf _ hs2⟩

/-- The `Nat.div`/`Nat.mod` pin at the consed environment, whose head
stores the closed value. -/
theorem checkDivModPinConsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint} {ci : ConstantInfo}
    (hci : ci = .defnInfo cv value hint)
    (hc : natDivModNames.contains cv.name = true) (hvf : value.hasFvar = false)
    (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkDivModPin (sharedOpsC mode (mkFEnv env)) pins env
      ⟨ci :: env.consts, env.tables⟩ cv.name
    ⦃fun r s' => CSOK mode env s' ∧ Runs (checkDivModPin (fueledOpsM mode) pins env
      ⟨ci :: env.consts, env.tables⟩ cv.name) r; ⊤⦄ := by
  subst hci
  refine checkDivModPinS_spec hμ henv (List.contains_iff_mem.mp hc) (fun cv' v' h' hf => ?_) hs
  have hself : Env.find? ⟨.defnInfo cv value hint :: env.consts, env.tables⟩ cv.name
      = some (.defnInfo cv value hint) := Env.find?_cons_self _ _
  rw [hself] at hf
  cases hf
  exact hvf

/-- `checkDefnValCI` simulates the generic `checkDefnVal`: the record it
returns is the definition the fueled side conses, its value closed. -/
theorem checkDefnValCI_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (htf : Expr.WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkDefnValCI mode (mkFEnv env) cv value hint
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (checkDefnVal (fueledOpsM mode) env cv value hint) ⟨v :: env.consts, env.tables⟩ ∧
      v = .defnInfo cv value hint ∧ value.hasFvar = false; ⊤⦄ := by
  sym only [conleche_grind, checkDefnVal.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [checkDefnValCI, inferK_spec hμ henv hs, defeqK_spec hμ henv] <;> finish

/-- `checkOpaqueValCI` simulates the generic `checkOpaqueVal`: the
record it returns is the axiom the fueled side conses, the value
closed. -/
theorem checkOpaqueValCI_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (htf : Expr.WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkOpaqueValCI mode (mkFEnv env) cv value
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (checkOpaqueVal (fueledOpsM mode) env cv value) ⟨v :: env.consts, env.tables⟩ ∧
      v = .axiomInfo cv ∧ value.hasFvar = false; ⊤⦄ := by
  sym only [conleche_grind, checkOpaqueVal.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [checkOpaqueValCI, inferK_spec hμ henv hs, defeqK_spec hμ henv] <;> finish

/-! ## The converted declaration -/

/-- The pinned-block install simulates its generic twin (task #293:
three of `checkDeclC`'s arms share this body). -/
theorem checkBasisDeclC_spec (hs : CSOK mode env s₀) (kind : BasisKind) :
    ⦃fun s => s = s₀⦄ checkBasisDeclC (mkFEnv env) kind
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkBasisDecl (m := FueledM) env kind) v.env ∧
      v = mkFEnv v.env; ⊤⦄ := by
  sym only [conleche_grind, checkBasisDecl.eq_1, mkFEnv_env] =>
    vcgen [checkBasisDeclC, installBasisFoldF_pushC, installBasisFoldS_spec (mode := mode) (env := env)] <;> finish

/-- The non-inductive branches of the converted-declaration driver
`checkDeclC` simulate the generic `checkDecl` at the fueled families
on the same declaration.  (There is no bracket in the cached driver:
`checkDeclC` *is* the plain path.) -/
theorem checkDeclC_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    (hs : CSOK mode env s₀) {pd : Declaration}
    (hnotind : ∀ block nP, pd ≠ .indDecl block nP) :
    ⦃fun s => s = s₀⦄ checkDeclC mode pins (mkFEnv env) pd
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkDecl mode (fueledOpsM mode) pins env pd) v.env ∧
      v = mkFEnv v.env; ⊤⦄ := by
  cases pd with
  | indDecl block nP => exact absurd rfl (hnotind _ _)
  | basisDecl kind =>
    sym only [conleche_grind, checkDecl] => vcgen [checkDeclC, checkBasisDeclC_spec hs] <;> finish
  | quotDecl k cv =>
    cases k <;>
      sym only [conleche_grind, checkDecl, mkFEnv_env] =>
        vcgen [checkDeclC, checkBasisDeclC_spec hs] <;> finish
  | axiomDecl cv =>
    sym only [conleche_grind, checkDecl, stdAxiomOkF_eq, trustCompilerOkF_eq, ofReduceAxOkF_eq,
        bvStubOkF_eq, push_mkFEnv, mkFEnv_env] =>
      vcgen [checkDeclC, checkConstantValC_spec hμ henv] <;> finish
  | thmDecl cv value =>
    sym only [conleche_grind] => vcgen [checkDeclC] <;> finish
  | opaqueDecl cv value =>
    sym only [conleche_grind, checkDecl, push_mkFEnv, mkFEnv_env] =>
      vcgen [checkDeclC, checkConstantValC_spec hμ henv hs, checkOpaqueValCI_spec hμ henv,
        checkReducePinF_overlay, checkReducePinS_spec hμ henv] <;> finish
  | defnDecl cv value hint =>
    sym only [conleche_grind, checkDecl, push_mkFEnv, mkFEnv_env, natOpGuardF_overlay,
        natOpStoredOkF_overlay, find?_overlay_mkFEnv, Env.find?_cons, ConstantInfo.name,
        ConstantInfo.toConstantVal] =>
      vcgen [checkDeclC, checkConstantValC_spec hμ henv hs, checkDefnValCI_spec hμ henv,
        checkDivModPinF_overlay, certifyNatOpEqsS_spec hμ henv,
        checkDivModPinConsS_spec hμ henv (cv := cv) (value := value) (hint := hint)] <;> finish

/-- One step of the converted-declaration fold: a successful run from a
residue state is reproduced by the pure fueled checker on the same
declaration, and the residue threads to the next step.  The cached
driver has no bracket and no index-range check, so the step is `flushC`
followed by `checkDeclC`. -/
theorem checkDeclStepC_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env) {pd : Declaration}
    {s₀ : CState} (hres : CSOKF s₀) {fe' : FEnv} {s' : CState}
    (h : checkDeclStepC mode pins (mkFEnv env) pd s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env pd = .ok fe'.env := by
  unfold checkDeclStepC at h
  obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcsok : CSOK mode env s₀.flushed := flushC_csok hres
  have main : (∀ block nP, pd ≠ .indDecl block nP) →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, checkDecl mode (fueledOps mode F) pins env pd = .ok fe'.env := by
    intro hind
    obtain ⟨hs', ⟨F, hF⟩, hmk⟩ := triple_iff_run.mp (checkDeclC_spec hμ henv hcsok hind) fe' s' h
    refine ⟨hs'.residue, hmk, F, ?_⟩
    rw [← checkDecl_datF]
    exact hF
  cases pd with
  | indDecl block nP =>
    -- task #293: a block the fold recognises as one of the five pinned
    -- ones installs the pin, on both sides; the declared parameter
    -- count (task #228) below it is a guard whose `false` throws on
    -- both sides, so only the passing branch reaches the bridge
    have hd : (match basisPinHit block with
        | some kind => checkBasisDeclC (mkFEnv env) kind
        | none =>
          if indParamsOk nP block = true then
            (match blockParts? nP block with
              | some p => checkBlockKS mode (mkFEnv env) block p
              | none => checkShapelessS mode (mkFEnv env) block)
          else throw (CheckError.invalid "number of parameters mismatch"))
        s₀.flushed = .ok (fe', s') := h
    cases hpin : basisPinHit block with
    | some kind =>
      rw [hpin] at hd
      obtain ⟨hs', ⟨F, hF⟩, hmk⟩ := triple_iff_run.mp (checkBasisDeclC_spec hcsok kind) fe' s' hd
      refine ⟨hs'.residue, hmk, F, ?_⟩
      show checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) = _
      simp only [checkDecl, hpin]
      rw [← checkBasisDecl_datF]
      exact hF
    | none =>
      rw [hpin] at hd
      by_cases hok : indParamsOk nP block = true
      · rw [ite_eq_left hok] at hd
        obtain ⟨hres', hfe, F, hF⟩ :=
          checkModeledOrNativeSF_run hμ henv hpin hok hres.flushed hd
        exact ⟨hres', hfe, F, hF⟩
      · rw [ite_eq_right hok] at hd
        exact nomatch hd
  | defnDecl cv value hint => exact main (fun _ _ h => Declaration.noConfusion h)
  | thmDecl cv value => exact main (fun _ _ h => Declaration.noConfusion h)
  | opaqueDecl cv value => exact main (fun _ _ h => Declaration.noConfusion h)
  | axiomDecl cv => exact main (fun _ _ h => Declaration.noConfusion h)
  | basisDecl kind => exact main (fun _ _ h => Declaration.noConfusion h)
  | quotDecl k cv => exact main (fun _ _ h => Declaration.noConfusion h)

end WalksP

end ConLeche.Cached
