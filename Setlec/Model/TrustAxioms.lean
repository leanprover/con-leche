import Setlec.Model.StdAxioms
import Setlec.Model.DivModCert

/-!
# The compiler-trust axiom family in the model (task #95)

* `Lean.trustCompiler : True` is valued by the stored `True.intro`'s
  interpretation — its pinned type is the stored `True`, and the
  stored constructor's membership fact is exactly the required
  inhabitation.  No new meta-axiom.
* `Lean.ofReduceNat` / `Lean.ofReduceBool` are valued by the proof
  point: their pinned types interpret to `Prop`-level `pi`-towers, and
  with the stored reduce opaque interpreted as the identity
  (`EnvModel.reduce_ops`, established at the opaque's install from the
  identity certificate), the hypothesis set *is* the conclusion set —
  `pt_mem_pi_zero` closes.  No `Eq` semantics is consumed: the
  equality applications stay abstract.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}

open SetTheory Expr

/-! ## `Lean.trustCompiler` -/

/-- What `trustCompilerOk` checked. -/
theorem trustCompilerOk_inv {cvA : ConstantVal}
    (h : trustCompilerOk env cvA = true) :
    (∃ cvT caps, env.find? trueName = some (.indInfo cvT caps) ∧
      ConstantVal.matchesPin cvT trueCvA = true) ∧
    (∃ cvTi, env.find? trueIntroName = some (.ctorInfo cvTi 0 0) ∧
      ConstantVal.matchesPin cvTi trueIntroCvA = true) ∧
    ConstantVal.matchesPin cvA trustCompilerA = true := by
  unfold trustCompilerOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hT, hTi⟩, hpin⟩ := h
  refine ⟨?_, ?_, hpin⟩
  · revert hT; split
    · next cvT caps hf => exact fun hp => ⟨cvT, caps, hf, hp⟩
    · exact fun hc => nomatch hc
  · revert hTi; split
    · next cvTi hf => exact fun hp => ⟨cvTi, hf, hp⟩
    · exact fun hc => nomatch hc

/-- The interpretation of `.const True []` over a pinned stored
`True`. -/
theorem interp_true_const {cval : ConstVal V}
    {cvT : ConstantVal} {caps : IndCaps}
    (hT : env.find? trueName = some (.indInfo cvT caps))
    (hlpT : cvT.levelParams = []) :
    interpClosed V cval env ψ (Expr.const trueName []) =
      some (cval trueName ψ) := by
  simp only [interpClosed, interpExpr, hT, ConstantInfo.toConstantVal,
    hlpT, List.length_nil, reduceIte, Level.substFn_nil]

/-- The `Lean.trustCompiler` inhabitation: the stored `True.intro`'s
interpretation is a member of the interpreted pinned type (which is
the stored `True`'s value). -/
theorem trustCompiler_key (m : EnvModel V env)
    {cvT : ConstantVal} {capsT : IndCaps}
    (hT : env.find? trueName = some (.indInfo cvT capsT))
    (hTp : ConstantVal.matchesPin cvT trueCvA = true)
    {cvTi : ConstantVal}
    (hTi : env.find? trueIntroName = some (.ctorInfo cvTi 0 0))
    (hTip : ConstantVal.matchesPin cvTi trueIntroCvA = true)
    (ψ' : Name → Nat) :
    ∃ T, interpClosed V m.val env ψ' trustCompilerA.type = some T ∧
      m.val trueIntroName ψ' ∈ˢ T := by
  have hlpT : cvT.levelParams = [] := (ConstantVal.matchesPin_inv hTp).2
  refine ⟨m.val trueName ψ', ?_, ?_⟩
  · show interpClosed V m.val env ψ' (Expr.const trueName []) = _
    exact interp_true_const hT hlpT
  · obtain ⟨T, hTt, hmem⟩ := m.mem_type _ (find?_mem hTi) ψ'
    rw [show (ConstantInfo.ctorInfo cvTi 0 0).toConstantVal = cvTi
      from rfl] at hTt
    rw [interpClosed_matchesPin hTip] at hTt
    rw [show trueIntroCvA.type = Expr.const trueName [] from rfl,
      interp_true_const hT hlpT] at hTt
    obtain rfl := Option.some.inj hTt
    have hname : cvTi.name = trueIntroName :=
      (ConstantVal.matchesPin_inv hTip).1
    rw [show (ConstantInfo.ctorInfo cvTi 0 0).name = cvTi.name from rfl,
      hname] at hmem
    exact hmem

/-! ## The `ofReduce*` axioms -/

/-- What `ofReduceAxOk` checked. -/
theorem ofReduceAxOk_inv {cvA : ConstantVal}
    (h : ofReduceAxOk env cvA = true) :
    decide (env.find? eqName = some eqA) = true ∧
    reduceElemOk env (ofReduceOp cvA.name) = true ∧
    (∃ cvR, env.find? (ofReduceOp cvA.name) = some (.axiomInfo cvR) ∧
      ConstantVal.matchesPin cvR (reduceOpCvA (ofReduceOp cvA.name))
        = true) ∧
    ConstantVal.matchesPin cvA (ofReducePinA cvA.name) = true := by
  unfold ofReduceAxOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hE, hel⟩, hst⟩, hpin⟩ := h
  refine ⟨hE, hel, ?_, hpin⟩
  unfold reduceStoredOk at hst
  revert hst; split
  · next cvR hf => exact fun hp => ⟨cvR, hf, hp⟩
  · exact fun hc => nomatch hc

/-- Interpretation of `Lean.ofReduceNat`'s pinned type, computed (the
`Eq` applications stay abstract — no `Eq` semantics is consumed). -/
theorem interp_ofReduceNat_type {cval : ConstVal V}
    (hN : env.find? natName = some natA)
    (hE : env.find? eqName = some eqA)
    {cvR : ConstantVal}
    (hR : env.find? reduceNatName = some (.axiomInfo cvR))
    (hlpR : cvR.levelParams = []) :
    interpClosed V cval env ψ ofReduceNatA.type =
      some (pi 0 (cval natName ψ) fun a =>
        pi 0 (cval natName ψ) fun b =>
          pi 0 (SetTheory.app (SetTheory.app (SetTheory.app
              (cval eqName (pxψ ψ)) (cval natName ψ))
              (SetTheory.app (cval reduceNatName ψ) a)) b) fun _ =>
            SetTheory.app (SetTheory.app (SetTheory.app
              (cval eqName (pxψ ψ)) (cval natName ψ)) a) b) := by
  have hN' : env.find? (Name.anonymous.str "Nat") = some natA := hN
  have hE' : env.find? (Name.anonymous.str "Eq") = some eqA := hE
  have hR' : env.find? ((Name.anonymous.str "Lean").str "reduceNat") =
      some (.axiomInfo cvR) := hR
  simp only [interpClosed, ofReduceNatA, interpExpr, Expr.instantiate1,
    updV, Level.eval, Option.getD, hN', hE', hR', eqA, natA,
    ConstantInfo.toConstantVal, hlpR, List.length_cons, List.length_nil,
    reduceIte, Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, uN, pxψ, natName, eqName,
    reduceNatName, Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- Interpretation of `Lean.ofReduceBool`'s pinned type, computed. -/
theorem interp_ofReduceBool_type {cval : ConstVal V}
    {cvB : ConstantVal} {capsB : IndCaps}
    (hB : env.find? boolName = some (.indInfo cvB capsB))
    (hlpB : cvB.levelParams = [])
    (hE : env.find? eqName = some eqA)
    {cvR : ConstantVal}
    (hR : env.find? reduceBoolName = some (.axiomInfo cvR))
    (hlpR : cvR.levelParams = []) :
    interpClosed V cval env ψ ofReduceBoolA.type =
      some (pi 0 (cval boolName ψ) fun a =>
        pi 0 (cval boolName ψ) fun b =>
          pi 0 (SetTheory.app (SetTheory.app (SetTheory.app
              (cval eqName (pxψ ψ)) (cval boolName ψ))
              (SetTheory.app (cval reduceBoolName ψ) a)) b) fun _ =>
            SetTheory.app (SetTheory.app (SetTheory.app
              (cval eqName (pxψ ψ)) (cval boolName ψ)) a) b) := by
  have hB' : env.find? (Name.anonymous.str "Bool") =
      some (.indInfo cvB capsB) := hB
  have hE' : env.find? (Name.anonymous.str "Eq") = some eqA := hE
  have hR' : env.find? ((Name.anonymous.str "Lean").str "reduceBool") =
      some (.axiomInfo cvR) := hR
  simp only [interpClosed, ofReduceBoolA, interpExpr, Expr.instantiate1,
    updV, Level.eval, Option.getD, hB', hE', hR', eqA,
    ConstantInfo.toConstantVal, hlpB, hlpR, List.length_cons,
    List.length_nil, reduceIte, Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, uN, pxψ, boolName, eqName,
    reduceBoolName, Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-! ## The identity certificate (`checkReducePin`), in the model -/

/-- Interpretation of `.const Nat []` over the pinned basis (any depth
and valuation — the constant clause reads neither). -/
theorem interp_natC {cval : ConstVal V} {d : Nat} {ρ : Nat → V}
    (hN : env.find? natName = some natA) :
    interpExpr V cval env ψ d ρ (Expr.const natName []) =
      some (cval natName ψ) := by
  simp only [interpExpr, hN, natA, ConstantInfo.toConstantVal,
    List.length_nil, reduceIte, Level.substFn_nil]

/-- Interpretation of `.const Bool []` over a pinned stored `Bool`. -/
theorem interp_boolC {cval : ConstVal V} {d : Nat} {ρ : Nat → V}
    {cvB : ConstantVal} {capsB : IndCaps}
    (hB : env.find? boolName = some (.indInfo cvB capsB))
    (hlpB : cvB.levelParams = []) :
    interpExpr V cval env ψ d ρ (Expr.const boolName []) =
      some (cval boolName ψ) := by
  simp only [interpExpr, hB, ConstantInfo.toConstantVal, hlpB,
    List.length_nil, reduceIte, Level.substFn_nil]

/-- What `reduceElemOk` checked, per operation: interpretation and
universe membership of the element type. -/
theorem reduceElem_facts (m : EnvModel V env) {c : Name}
    (hcmem : c ∈ reduceOpNames) (hel : reduceElemOk env c = true)
    (ψ' : Name → Nat) :
    (∀ (d : Nat) (ρ : Nat → V),
      interpExpr V m.val env ψ' d ρ (reduceElemTy c) =
        some (m.val (reduceElemName c) ψ')) ∧
    m.val (reduceElemName c) ψ' ∈ˢ univ 1 := by
  have hsort : ∀ (T : V),
      interpClosed V m.val env ψ' (Expr.sort (.succ .zero)) = some T →
      T = univ 1 := by
    intro T hT
    simp only [interpClosed, interpExpr, Level.eval] at hT
    exact (Option.some.inj hT).symm
  rcases (by simpa [reduceOpNames] using hcmem :
      c = reduceNatName ∨ c = reduceBoolName) with rfl | rfl
  · have hN : env.find? natName = some natA := by
      unfold reduceElemOk at hel
      rw [if_pos rfl] at hel
      exact of_decide_eq_true hel
    refine ⟨?_, ?_⟩
    · intro d ρ
      show interpExpr V m.val env ψ' d ρ (Expr.const natName []) = _
      rw [interp_natC hN]
      rfl
    · obtain ⟨T, hT, hmem⟩ := m.mem_type _ (find?_mem hN) ψ'
      rw [show (natA).toConstantVal.type = Expr.sort (.succ .zero)
        from rfl] at hT
      rw [hsort T hT] at hmem
      show m.val natName ψ' ∈ˢ univ 1
      exact hmem
  · obtain ⟨cvB, capsB, hBf, hBp⟩ : ∃ cvB capsB,
        env.find? boolName = some (.indInfo cvB capsB) ∧
        ConstantVal.matchesPin cvB boolCvA = true := by
      unfold reduceElemOk at hel
      rw [if_neg (by decide)] at hel
      revert hel
      split
      · next cvB capsB hf => exact fun hp => ⟨cvB, capsB, hf, hp⟩
      · exact fun hc => nomatch hc
    have hlpB : cvB.levelParams = [] := (ConstantVal.matchesPin_inv hBp).2
    refine ⟨?_, ?_⟩
    · intro d ρ
      show interpExpr V m.val env ψ' d ρ (Expr.const boolName []) = _
      rw [interp_boolC hBf hlpB]
      rfl
    · obtain ⟨T, hT, hmem⟩ := m.mem_type _ (find?_mem hBf) ψ'
      rw [show (ConstantInfo.indInfo cvB capsB).toConstantVal = cvB
        from rfl, interpClosed_matchesPin hBp,
        show boolCvA.type = Expr.sort (.succ .zero) from rfl] at hT
      rw [hsort T hT] at hmem
      have hname : cvB.name = boolName := (ConstantVal.matchesPin_inv hBp).1
      rw [show (ConstantInfo.indInfo cvB capsB).name = cvB.name from rfl,
        hname] at hmem
      show m.val boolName ψ' ∈ˢ univ 1
      exact hmem

/-- Interpretation of `Lean.reduceNat`'s pinned type, computed. -/
theorem interp_reduceNatTy {cval : ConstVal V}
    (hN : env.find? natName = some natA) :
    interpClosed V cval env ψ reduceNatCvA.type =
      some (pi 1 (cval natName ψ) fun _ => cval natName ψ) := by
  have hN' : env.find? (Name.anonymous.str "Nat") = some natA := hN
  simp only [interpClosed, reduceNatCvA, interpExpr, Expr.instantiate1,
    updV, Level.eval, Option.getD, hN', natA,
    ConstantInfo.toConstantVal, List.length_nil, reduceIte,
    Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, natName, Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- Interpretation of `Lean.reduceBool`'s pinned type, computed. -/
theorem interp_reduceBoolTy {cval : ConstVal V}
    {cvB : ConstantVal} {capsB : IndCaps}
    (hB : env.find? boolName = some (.indInfo cvB capsB))
    (hlpB : cvB.levelParams = []) :
    interpClosed V cval env ψ reduceBoolCvA.type =
      some (pi 1 (cval boolName ψ) fun _ => cval boolName ψ) := by
  have hB' : env.find? (Name.anonymous.str "Bool") =
      some (.indInfo cvB capsB) := hB
  simp only [interpClosed, reduceBoolCvA, interpExpr, Expr.instantiate1,
    updV, Level.eval, Option.getD, hB', ConstantInfo.toConstantVal,
    hlpB, List.length_nil, reduceIte, Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, boolName, Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `reduceElemOk` stores the element inductive. -/
theorem reduceElemOk_isSome {c : Name} (hel : reduceElemOk env c = true) :
    (env.find? (reduceElemName c)).isSome = true := by
  unfold reduceElemOk at hel
  unfold reduceElemName
  by_cases hc : c = reduceNatName
  · rw [if_pos hc] at hel
    rw [if_pos hc, decide_eq_true_eq.mp hel]
    rfl
  · rw [if_neg hc] at hel
    rw [if_neg hc]
    revert hel
    split
    · next hf => intro _; rw [hf]; rfl
    · exact fun hc => nomatch hc

/-- Interpretation of the pinned reduce-operation type, computed
(dispatch over the two operations from `reduceElemOk`). -/
theorem interp_reduceOpTy {c : Name} (m : EnvModel V env)
    (hcmem : c ∈ reduceOpNames) (hel : reduceElemOk env c = true) :
    interpClosed V m.val env ψ (reduceOpCvA c).type =
      some (pi 1 (m.val (reduceElemName c) ψ) fun _ =>
        m.val (reduceElemName c) ψ) := by
  rcases (by simpa [reduceOpNames] using hcmem :
      c = reduceNatName ∨ c = reduceBoolName) with rfl | rfl
  · have hN : env.find? natName = some natA := by
      unfold reduceElemOk at hel
      rw [if_pos rfl] at hel
      exact of_decide_eq_true hel
    rw [show reduceOpCvA reduceNatName = reduceNatCvA from by
      unfold reduceOpCvA; rw [if_pos rfl],
      show reduceElemName reduceNatName = natName from by
      unfold reduceElemName; rw [if_pos rfl]]
    exact interp_reduceNatTy hN
  · obtain ⟨cvB, capsB, hBf, hBp⟩ : ∃ cvB capsB,
        env.find? boolName = some (.indInfo cvB capsB) ∧
        ConstantVal.matchesPin cvB boolCvA = true := by
      unfold reduceElemOk at hel
      rw [if_neg (by decide)] at hel
      revert hel
      split
      · next cvB capsB hf => exact fun hp => ⟨cvB, capsB, hf, hp⟩
      · exact fun hc => nomatch hc
    rw [show reduceOpCvA reduceBoolName = reduceBoolCvA from by
      unfold reduceOpCvA; rw [if_neg (by decide)],
      show reduceElemName reduceBoolName = boolName from by
      unfold reduceElemName; rw [if_neg (by decide)]]
    exact interp_reduceBoolTy hBf (ConstantVal.matchesPin_inv hBp).2

/-- Soundness of the identity certificate (`checkReducePin`'s depth-1
definitional equality `value' x ≡ x`): the checked opaque witness's
interpretation is the identity on the element type. -/
theorem reduceCert_sound (m : EnvModel V env) {c : Name} {F : Nat}
    (hcmem : c ∈ reduceOpNames)
    (hel : reduceElemOk env c = true)
    {value' : Expr}
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    (hAval : AnnotOk V m.val env ψ 0 (rho0 V) value')
    (hkeyv : ∃ v T, interpClosed V m.val env ψ value' = some v ∧
      interpClosed V m.val env ψ (reduceOpCvA c).type = some T ∧ v ∈ˢ T)
    (hde : isDefEqCore env F 1 (.app value' (reduceCertVar c))
      (reduceCertVar c) = .ok true)
    {x : V} (hx : x ∈ˢ m.val (reduceElemName c) ψ)
    {v : V} (hv : interpClosed V m.val env ψ value' = some v) :
    SetTheory.app v x = x := by
  obtain ⟨helI, helU⟩ := reduceElem_facts m hcmem hel ψ
  obtain ⟨v₀, T, hv₀, hT, hmemT⟩ := hkeyv
  have hveq : v = v₀ := by rw [hv] at hv₀; exact Option.some.inj hv₀
  rw [← hveq] at hmemT
  rw [interp_reduceOpTy m hcmem hel] at hT
  obtain rfl := Option.some.inj hT
  -- the valuation: the certificate variable at `x`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Nat → V, ρ = updV V (rho0 V) 0 x := ⟨_, rfl⟩
  have hρ0 : ρ 0 = x := by rw [hρ]; simp [updV]
  -- side facts
  have hvW : WScoped 1 value' := WScoped.of_not_hasFvar hvf
  have hxW : WScoped 1 (reduceCertVar c) := by
    unfold reduceCertVar
    simp only [WScoped]
    refine ⟨Nat.zero_lt_one, ?_⟩
    unfold reduceElemTy
    split <;> simp only [WScoped]
  have happW : WScoped 1 (Expr.app value' (reduceCertVar c)) := by
    simp only [WScoped]
    exact ⟨hvW, hxW⟩
  have hiv : interpExpr V m.val env ψ 1 ρ value' = some v := by
    rw [interp_closed_invariant hvf 1 ρ]
    exact hv
  have hix : interpExpr V m.val env ψ 1 ρ (reduceCertVar c) = some x := by
    unfold reduceCertVar
    simp only [interpExpr]
    rw [hρ0]
  have hAty : AnnotOk V m.val env ψ 1 ρ (reduceElemTy c) := by
    unfold reduceElemTy
    split <;> simp [AnnotOk]
  have hFx : FvarsOk V m.val env ψ 1 ρ (reduceCertVar c) := by
    unfold reduceCertVar
    refine FvarsOk.fvar_intro (T := m.val (reduceElemName c) ψ)
      Nat.zero_lt_one ?_ ?_ ?_ ?_
    · show AnnotOk V m.val env ψ 1 ρ (reduceElemTy c)
      exact hAty
    · show interpExpr V m.val env ψ 1 ρ (reduceElemTy c) = _
      rw [helI 1 ρ]
    · rw [hρ0]
      exact hx
    · show FvarsOk V m.val env ψ 1 ρ (reduceElemTy c)
      unfold reduceElemTy
      split <;> exact FvarsOk.of_not_hasFvar rfl
  have hLx : Expr.LeavesBounded (reduceCertVar c) := by
    unfold reduceCertVar
    refine LeavesBounded.fvar_intro ?_ ?_
    · unfold reduceElemTy
      split <;> rfl
    · unfold reduceElemTy
      split <;> exact Expr.LeavesBounded.of_not_hasFvar rfl
  have hxB : (reduceCertVar c).looseBVarsBounded 0 = true := by
    unfold reduceCertVar reduceElemTy
    split <;> rfl
  have hAx : AnnotOk V m.val env ψ 1 ρ (reduceCertVar c) := by
    unfold reduceCertVar
    simp [AnnotOk]
  have hAv : AnnotOk V m.val env ψ 1 ρ value' :=
    AnnotOk.closed_invariant hvf 1 ρ hAval
  have hiapp : interpExpr V m.val env ψ 1 ρ
      (.app value' (reduceCertVar c)) = some (SetTheory.app v x) := by
    simp only [interpExpr, hiv, hix]
  have hAapp : AnnotOk V m.val env ψ 1 ρ
      (.app value' (reduceCertVar c)) := by
    simp only [AnnotOk]
    refine ⟨hAv, hAx, v, x, 1, m.val (reduceElemName c) ψ,
      fun _ => m.val (reduceElemName c) ψ, hiv, hix, hmemT, ?_, ?_⟩
    · exact hx
    · intro y hy
      exact helU
  have hres := isDefEqCore_sound (φ := ψ) m F hde
    happW hxW
    (by simp [Expr.looseBVarsBounded, hvb, hxB]) hxB
    (LeavesBounded.app_intro (Expr.LeavesBounded.of_not_hasFvar hvf) hLx)
    hLx
    (FvarsOk.app_intro (FvarsOk.of_not_hasFvar hvf) hFx) hFx
    hAapp hAx hiapp hix
  exact hres

/-- The `ofReduce*` inhabitation: with the stored reduce opaque
interpreted as the identity on its element type
(`EnvModel.reduce_ops`), the hypothesis set is the conclusion set, so
the proof point inhabits the interpreted pinned type. -/
theorem ofReduce_key (m : EnvModel V env) {cvA : ConstantVal}
    (hor : cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName)
    (hok : ofReduceAxOk env cvA = true)
    (ψ' : Name → Nat) :
    ∃ T, interpClosed V m.val env ψ' (ofReducePinA cvA.name).type
        = some T ∧ SetTheory.pt ∈ˢ T := by
  obtain ⟨hE, hel, ⟨cvR, hR, hRp⟩, -⟩ := ofReduceAxOk_inv hok
  rw [decide_eq_true_eq] at hE
  have hmem : ofReduceOp cvA.name ∈ reduceOpNames := by
    rcases hor with hn | hn <;> rw [hn] <;> decide
  have hid := (m.reduce_ops (ofReduceOp cvA.name) hmem cvR hR hRp).2
  have hlpR : cvR.levelParams = [] := by
    rw [(ConstantVal.matchesPin_inv hRp).2]
    unfold reduceOpCvA
    split <;> rfl
  rcases hor with hn | hn
  · -- ofReduceNat
    rw [hn, (by decide : ofReduceOp ofReduceNatName = reduceNatName)]
      at hR hid hel
    have helN : env.find? natName = some natA := by
      unfold reduceElemOk at hel
      rw [if_pos rfl] at hel
      exact of_decide_eq_true hel
    have hidN : ∀ x : V, x ∈ˢ m.val natName ψ' →
        SetTheory.app (m.val reduceNatName ψ') x = x := by
      have := hid ψ'
      unfold reduceElemName at this
      rw [if_pos rfl] at this
      exact this
    rw [hn]
    refine ⟨_, interp_ofReduceNat_type helN hE hR hlpR, ?_⟩
    refine pt_mem_pi_zero fun a ha => ?_
    refine pt_mem_pi_zero fun b hb => ?_
    refine pt_mem_pi_zero fun w hw => ?_
    rw [hidN a ha] at hw
    have hab := mem_eqv hw
    exact hab ▸ pt_mem_eqv_self _
  · -- ofReduceBool
    rw [hn, (by decide : ofReduceOp ofReduceBoolName = reduceBoolName)]
      at hR hid hel
    have helB : ∃ cvB capsB,
        env.find? boolName = some (.indInfo cvB capsB) ∧
        cvB.levelParams = [] := by
      unfold reduceElemOk at hel
      rw [if_neg (by decide)] at hel
      revert hel
      split
      · next cvB capsB hf =>
        intro hp
        exact ⟨cvB, capsB, hf, (ConstantVal.matchesPin_inv hp).2⟩
      · exact fun hc => nomatch hc
    obtain ⟨cvB, capsB, hBf, hlpB⟩ := helB
    have hidB : ∀ x : V, x ∈ˢ m.val boolName ψ' →
        SetTheory.app (m.val reduceBoolName ψ') x = x := by
      have := hid ψ'
      unfold reduceElemName at this
      rw [if_neg (by decide)] at this
      exact this
    rw [hn]
    refine ⟨_, interp_ofReduceBool_type hBf hlpB hE hR hlpR, ?_⟩
    refine pt_mem_pi_zero fun a ha => ?_
    refine pt_mem_pi_zero fun b hb => ?_
    refine pt_mem_pi_zero fun w hw => ?_
    rw [hidB a ha] at hw
    have hab := mem_eqv hw
    exact hab ▸ pt_mem_eqv_self _

end Setlec
