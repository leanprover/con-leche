import Setlec.Verify.Cached.BridgeCS2

/-!
# Cached shared-state walks, part 3: the direct simple-structure install

Port of `Setlec/Verify/BridgeS3.lean` for the cached tier.  The
single-environment functions of the direct-install path
(`checkDirectFieldSorts`, `checkDirectDomsAt`, `checkDirectInd`,
`checkDirectCtor`, `checkDirectRec`,
`checkDirectProj`), as `SimC`s between the `sharedOpsC` and
`(fueledOpsM mode)` instantiations.  The per-site scoping facts mirror
`Setlec/Verify/BridgeWfImp.lean`'s `_wfimp` walks one for one; the
`FEnv`-to-`Env` step is `Setlec/Verify/CheckerF.lean`'s `_eq`/`_push`
family and happens in `Setlec/Verify/Cached/BridgeCS4.lean`, so
everything here is stated over the generic functions.

The *subjects* are the very same `Expr`-level checker functions as in
the interned original — only the operations record differs — so the
walks transpose by the recipe's substitutions alone (`SimAt → SimC`,
`ISOK → CSOK`, no `Ext` binder, state-free value relations).  The pure
comparand side of every statement is byte-identical to the interned
original's.
-/

namespace Setlec.Cached

open Setlec
open Setlec.Cached.ExprC
open Expr

variable {mode : CheckMode}

section Walks3

variable {env : Env} {s₀ : CState}

/-- The per-frame binder-domain pins at the shared operations. -/
theorem checkDirectDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j)
        (checkDirectDomsAt (fueledOpsM mode) env off fvs doms j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectDomsAt
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ a a' hs₁ hP => ?_)
    obtain ⟨rfl, hae⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ b b' hs₂ hQ => ?_)
    obtain ⟨rfl, hbe⟩ := hQ
    refine SimC.bind (opB_sim hμ henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDirectDomsAtS_sim hμ henv hc ht hs₃

/-- The per-field sort walk at the shared operations (task #175
W4c/O4: the universe bound has the official `Prop` escape hatch). -/
theorem checkDirectFieldSortsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {isProp large : Bool}
    {s : Level} {nP : Nat} {fvs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectFieldSorts (sharedOpsC mode (mkFEnv env)) env isProp large
          s nP fvs j)
        (checkDirectFieldSorts (fueledOpsM mode) env isProp large s nP fvs j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectFieldSorts
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ fv fv' hs₁ hP => ?_)
    obtain ⟨rfl, hfe⟩ := hP
    refine SimC.bind (opE_infer_sim hμ henv hs₁ (hfvs j fv hfe))
      (fun s₂ ty ty' hs₂ hP₂ => ?_)
    obtain ⟨rfl, htyW⟩ := hP₂
    refine SimC.bind (opS_sim hμ henv hs₂ htyW)
      (fun s₃ u u' hs₃ hP₃ => ?_)
    obtain rfl : u = u' := hP₃
    by_cases hnp : (!isProp) = true
    · simp only [if_pos hnp]
      refine SimC.bind (SimC.liftFueled _ _ hs₃)
        (fun s₃ c c' hs₃ hC => ?_)
      obtain rfl : c = c' := hC
      cases c with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind (checkDirectFieldSortsS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl
    · simp only [if_neg hnp]
      by_cases hl : large = true
      · simp only [if_pos hl]
        by_cases hz : (Level.isEquiv u .zero == some true) = true
        · simp only [if_pos hz]
          refine SimC.bind (checkDirectFieldSortsS_sim hμ henv hfvs hs₃)
            (fun s₄ rest rest' hs₄ hR => ?_)
          obtain rfl : rest = rest' := hR
          exact SimC.pure hs₄ rfl
        · simp only [if_neg hz]
          exact SimC.throw_bind
      · simp only [if_neg hl]
        refine SimC.bind (checkDirectFieldSortsS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl

/-- Stage 1 (the type former) at the shared operations. -/
theorem checkDirectIndS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : DirectParts}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectInd (sharedOpsC mode (mkFEnv env)) env p)
      (checkDirectInd (fueledOpsM mode) env p) := by
  unfold checkDirectInd
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvTa cvTa' hs₁ hP => ?_)
  obtain ⟨rfl, hTw⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort p.resSort) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  exact SimC.pure hs₂ ⟨rfl, hTw⟩

/-- Stage 2 (the constructor) at the shared operations. -/
theorem checkDirectCtorS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {p : DirectParts} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.snd v).1.type)
      (checkDirectCtor (sharedOpsC mode (mkFEnv env)) env₀ env p cvTa)
      (checkDirectCtor (fueledOpsM mode) env₀ env p cvTa) := by
  unfold checkDirectCtor
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvCa cvCa' hs₁ hP => ?_)
  obtain ⟨rfl, hCw⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨cbs, cbody⟩ := q
  dsimp only
  by_cases h1 : (cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF)
      = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ cq cq' hs₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, crest⟩ := cq
  dsimp only
  obtain ⟨hfvsW0, hcrW0⟩ := openPisAtFvars_WScoped p.nP cvCa.type 0 hop hCw
  have hcrW : WScoped p.nP crest := by rwa [Nat.zero_add] at hcrW0
  refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ tq tq' hs₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨tfvs, trest⟩ := tq
  dsimp only
  obtain ⟨htfvsW0, -⟩ := openPisAtFvars_WScoped p.nP cvTa.type 0 hci
    (WScoped.of_not_hasFvar hTf)
  refine SimC.bind (checkDirectDomsAtS_sim hμ (off := 0) henv
      (fun i x hx => by
        obtain ⟨nm, ty, rfl⟩ :=
          openPisAtFvars_index p.nP cvCa.type 0 hop i x hx
        have hw := hfvsW0 _ (List.mem_of_getElem? hx)
        simp only [WScoped] at hw
        exact hw.2)
      (fun i x hx => by
        rw [List.getElem?_map] at hx
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨nm, ty, rfl⟩ :=
          openPisAtFvars_index p.nP cvTa.type 0 hci i y hy
        have hw := htfvsW0 _ (List.mem_of_getElem? hy)
        simp only [WScoped] at hw
        exact hw.2)
      hs₄)
    (fun s₅ u1 u1' hs₅ hU1 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ xq xq' hs₆ hT => ?_)
  obtain ⟨rfl, hox⟩ := hT
  obtain ⟨xFvs, cresid⟩ := xq
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF crest p.nP hox hcrW
  have hxPos : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (p.nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index p.nF crest p.nP hox i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  by_cases h2 : (cresid == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  refine SimC.bind (checkDirectFieldSortsS_sim hμ henv hxPos hs₆)
    (fun s₇ sorts sorts' hs₇ hS => ?_)
  obtain rfl : sorts = sorts' := hS
  exact SimC.pure hs₇ ⟨rfl, hCw⟩

/-- Stage 3 (the recursor, generated and compared; task #175 S2) at
the shared operations: every operation runs at depth `0` on a closed
term. -/
theorem checkDirectRecS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : DirectParts}
    {cvTa cvCa : ConstantVal} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectRec (sharedOpsC mode (mkFEnv env)) env p cvTa cvCa)
      (checkDirectRec (fueledOpsM mode) env p cvTa cvCa) := by
  unfold checkDirectRec
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ cvRi cvRi' hs₁ hP => ?_)
  obtain ⟨rfl, hwI⟩ := hP
  try dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ recTy recTy' hs₂ hR => ?_)
  obtain ⟨rfl, -⟩ := hR
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ rhs rhs' hs₃ hH => ?_)
  obtain ⟨rfl, -⟩ := hH
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  by_cases h2 : (Expr.allLevelParamsDefined p.cvR.levelParams rhs &&
      Expr.constsResolve env rhs && Expr.looseBVarsBounded 0 rhs &&
      !rhs.hasFvar) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  have hRf : recTy.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  have hrf : rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact h2.2
  have hwR : WScoped 0 recTy := WScoped.of_not_hasFvar hRf
  have hwr : WScoped 0 rhs := WScoped.of_not_hasFvar hrf
  refine SimC.bind (opE_infer_sim hμ henv hs₃ hwR) (fun s₄ sty sty' hs₄ hS => ?_)
  obtain ⟨rfl, hwsty⟩ := hS
  refine SimC.bind (opS_sim hμ henv hs₄ hwsty) (fun s₅ u u' hs₅ hU => ?_)
  refine SimC.bind (opB_sim hμ henv hs₅ hwI hwR) (fun s₆ b b' hs₆ hB => ?_)
  obtain rfl : b = b' := hB
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (opE_infer_sim hμ henv hs₆ hwr) (fun s₇ rty rty' hs₇ hT => ?_)
  exact SimC.pure hs₇ rfl

/-! ## The direct sum install (task #175 sum-types, indexed)

The same three stages over a constructor *list*: the former, one
constructor stage per constructor — all at the environment holding the
type former alone — and the recursor, generated and compared, whose
rules loop runs `inferType` on closed generated right-hand sides.
Task #175 indexed: the stages carry `nIdx` and the field-sort walk is
`checkDirectFieldSortsI` (`checkDirectFieldSortsIS_sim`). -/

/-- The per-field sort walk of the sum route at the shared operations
(task #175 indexed: the large-eliminator escape admits a field that is
one of the residual's index expressions). -/
theorem checkDirectFieldSortsIS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {isProp large : Bool}
    {s : Level} {nP : Nat} {fvs idxArgs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectFieldSortsI (sharedOpsC mode (mkFEnv env)) env isProp large
          s nP fvs idxArgs j)
        (checkDirectFieldSortsI (fueledOpsM mode) env isProp large s nP fvs idxArgs j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectFieldSortsI
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ fv fv' hs₁ hP => ?_)
    obtain ⟨rfl, hfe⟩ := hP
    refine SimC.bind (opE_infer_sim hμ henv hs₁ (hfvs j fv hfe))
      (fun s₂ ty ty' hs₂ hP₂ => ?_)
    obtain ⟨rfl, htyW⟩ := hP₂
    refine SimC.bind (opS_sim hμ henv hs₂ htyW)
      (fun s₃ u u' hs₃ hP₃ => ?_)
    obtain rfl : u = u' := hP₃
    by_cases hnp : (!isProp) = true
    · simp only [if_pos hnp]
      refine SimC.bind (SimC.liftFueled _ _ hs₃)
        (fun s₃ c c' hs₃ hC => ?_)
      obtain rfl : c = c' := hC
      cases c with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind (checkDirectFieldSortsIS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl
    · simp only [if_neg hnp]
      by_cases hl : large = true
      · simp only [if_pos hl]
        by_cases hz : (Level.isEquiv u .zero == some true || idxArgs.contains fv) = true
        · simp only [if_pos hz]
          refine SimC.bind (checkDirectFieldSortsIS_sim hμ henv hfvs hs₃)
            (fun s₄ rest rest' hs₄ hR => ?_)
          obtain rfl : rest = rest' := hR
          exact SimC.pure hs₄ rfl
        · simp only [if_neg hz]
          exact SimC.throw_bind
      · simp only [if_neg hl]
        refine SimC.bind (checkDirectFieldSortsIS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl

/-- Stage 1 (the type former) of the sum route at the shared
operations. -/
theorem checkDirectSumIndS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : DirectSumParts}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectSumInd (sharedOpsC mode (mkFEnv env)) env p)
      (checkDirectSumInd (fueledOpsM mode) env p) := by
  unfold checkDirectSumInd
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvTa cvTa' hs₁ hP => ?_)
  obtain ⟨rfl, hTw⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort p.resSort) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  exact SimC.pure hs₂ ⟨rfl, hTw⟩

/-- Stage 2 (one constructor, the constructor and its field count
explicit) at the shared operations. -/
theorem checkDirectSumCtorS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC : ConstantVal} {nF : Nat} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectSumCtor (sharedOpsC mode (mkFEnv env)) env₀ env T lps nP
        nIdx resSort isProp large cvC nF cvTa)
      (checkDirectSumCtor (fueledOpsM mode) env₀ env T lps nP nIdx resSort isProp large
        cvC nF cvTa) := by
  unfold checkDirectSumCtor
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvCa cvCa' hs₁ hP => ?_)
  obtain ⟨rfl, hCw⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨cbs, cbody⟩ := q
  dsimp only
  by_cases h1 : directCtorResidOk T lps nP nF nIdx cbody = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ cq cq' hs₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, crest⟩ := cq
  dsimp only
  obtain ⟨hfvsW0, hcrW0⟩ := openPisAtFvars_WScoped nP cvCa.type 0 hop hCw
  have hcrW : WScoped nP crest := by rwa [Nat.zero_add] at hcrW0
  refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ tq tq' hs₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨tfvs, trest⟩ := tq
  dsimp only
  obtain ⟨htfvsW0, -⟩ := openPisAtFvars_WScoped nP cvTa.type 0 hci
    (WScoped.of_not_hasFvar hTf)
  refine SimC.bind (checkDirectDomsAtS_sim hμ (off := 0) henv
      (fun i x hx => by
        obtain ⟨nm, ty, rfl⟩ :=
          openPisAtFvars_index nP cvCa.type 0 hop i x hx
        have hw := hfvsW0 _ (List.mem_of_getElem? hx)
        simp only [WScoped] at hw
        exact hw.2)
      (fun i x hx => by
        rw [List.getElem?_map] at hx
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨nm, ty, rfl⟩ :=
          openPisAtFvars_index nP cvTa.type 0 hci i y hy
        have hw := htfvsW0 _ (List.mem_of_getElem? hy)
        simp only [WScoped] at hw
        exact hw.2)
      hs₄)
    (fun s₅ u1 u1' hs₅ hU1 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ xq xq' hs₆ hT => ?_)
  obtain ⟨rfl, hox⟩ := hT
  obtain ⟨xFvs, cresid⟩ := xq
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped nF crest nP hox hcrW
  have hxPos : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index nF crest nP hox i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  by_cases h2 : (cresid.getAppFn == Expr.const T (lps.map .param) &&
      cresid.getAppArgs.take nP == fvsP && cresid.getAppArgs.length == nP + nIdx) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : ((cresid.getAppArgs.drop nP).all fun e => Expr.constsResolve env₀ e) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (checkDirectFieldSortsIS_sim hμ henv hxPos hs₆)
    (fun s₇ sorts sorts' hs₇ hS => ?_)
  obtain rfl : sorts = sorts' := hS
  exact SimC.pure hs₇ rfl

/-- Stage 2, the whole constructor list: every constructor is checked
at the *same* environment (the one holding the type former alone), so
the walk is a plain induction on the list. -/
theorem checkDirectSumCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvTa : ConstantVal} (hTf : cvTa.type.hasFvar = false) :
    ∀ {cs : List (ConstantVal × Nat)} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectSumCtors (sharedOpsC mode (mkFEnv env)) env₀ env T lps
          nP nIdx resSort isProp large cvTa cs)
        (checkDirectSumCtors (fueledOpsM mode) env₀ env T lps nP nIdx resSort isProp
          large cvTa cs)
  | [], s₀, hs => SimC.pure hs rfl
  | c :: cs, s₀, hs => by
    unfold checkDirectSumCtors
    dsimp only [sharedOpsC]
    refine SimC.bind (checkDirectSumCtorS_sim hμ henv hTf hs)
      (fun s₁ cvCa cvCa' hs₁ hP => ?_)
    obtain rfl : cvCa = cvCa' := hP
    refine SimC.bind (checkDirectSumCtorsS_sim hμ henv hTf hs₁)
      (fun s₂ rest rest' hs₂ hR => ?_)
    obtain rfl : rest = rest' := hR
    exact SimC.pure hs₂ rfl

/-- The generated rules loop at the shared operations: each right-hand
side is closed by its own scoping guard, so `inferType` runs at depth
`0` on a well-scoped term. -/
theorem checkDirectSumRulesS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {rlps : List Name}
    {T : Name} {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat}
    {tty : Expr} {ctors : List (Name × Nat × Expr)} :
    ∀ {k j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectSumRules (sharedOpsC mode (mkFEnv env)) env rlps T lps
          elim large nP nIdx tty ctors k j)
        (checkDirectSumRules (fueledOpsM mode) env rlps T lps elim large nP nIdx tty
          ctors k j)
  | 0, _, s₀, hs => SimC.pure hs rfl
  | k + 1, j, s₀, hs => by
    unfold checkDirectSumRules
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ rhs rhs' hs₁ hP => ?_)
    obtain ⟨rfl, -⟩ := hP
    by_cases h1 : (Expr.allLevelParamsDefined rlps rhs &&
        Expr.constsResolve env rhs && Expr.looseBVarsBounded 0 rhs &&
        !rhs.hasFvar) = true
    case neg => simp only [if_neg h1]; exact SimC.throw_bind
    simp only [if_pos h1]
    have hrf : rhs.hasFvar = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
      exact h1.2
    have hwr : WScoped 0 rhs := WScoped.of_not_hasFvar hrf
    refine SimC.bind (opE_infer_sim hμ henv hs₁ hwr) (fun s₂ rty rty' hs₂ hT => ?_)
    refine SimC.bind (checkDirectSumRulesS_sim hμ henv hs₂)
      (fun s₃ rest rest' hs₃ hR => ?_)
    obtain rfl : rest = rest' := hR
    exact SimC.pure hs₃ rfl

/-- Stage 3 (the recursor, generated and compared) of the sum route at
the shared operations. -/
theorem checkDirectSumRecS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : DirectSumParts}
    {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectSumRec (sharedOpsC mode (mkFEnv env)) env p cvTa ctorsA)
      (checkDirectSumRec (fueledOpsM mode) env p cvTa ctorsA) := by
  unfold checkDirectSumRec
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ cvRi cvRi' hs₁ hP => ?_)
  obtain ⟨rfl, hwI⟩ := hP
  try dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ recTy recTy' hs₂ hR => ?_)
  obtain ⟨rfl, -⟩ := hR
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  have hRf : recTy.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  have hwR : WScoped 0 recTy := WScoped.of_not_hasFvar hRf
  refine SimC.bind (opE_infer_sim hμ henv hs₂ hwR) (fun s₃ sty sty' hs₃ hS => ?_)
  obtain ⟨rfl, hwsty⟩ := hS
  refine SimC.bind (opS_sim hμ henv hs₃ hwsty) (fun s₄ u u' hs₄ hU => ?_)
  refine SimC.bind (opB_sim hμ henv hs₄ hwI hwR) (fun s₅ b b' hs₅ hB => ?_)
  obtain rfl : b = b' := hB
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (checkDirectSumRulesS_sim hμ henv hs₅)
    (fun s₆ rhss rhss' hs₆ hRs => ?_)
  obtain rfl : rhss = rhss' := hRs
  exact SimC.pure hs₆ rfl

end Walks3

end Setlec.Cached
