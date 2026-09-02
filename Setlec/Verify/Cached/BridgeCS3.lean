import Setlec.Verify.Cached.BridgeCS2

/-!
# Cached shared-state walks, part 3: the direct simple-structure install

Port of `Setlec/Verify/BridgeS3.lean` for the cached tier.  The
single-environment functions of the direct-install path
(`checkDirectFieldUniv`, `checkDirectDomsAt`, `checkDirectInd`,
`checkDirectCtor`, `checkDirectRecTy`, `checkDirectRule`,
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
theorem checkDirectDomsAtS_sim (henv : EnvWF env) {off : Nat}
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
    refine SimC.bind (opB_sim henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDirectDomsAtS_sim henv hc ht hs₃

/-- The per-field universe bound at the shared operations. -/
theorem checkDirectFieldUnivS_sim (henv : EnvWF env) {s : Level} {nP : Nat}
    {fvs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDirectFieldUniv (sharedOpsC mode (mkFEnv env)) env s nP fvs j)
        (checkDirectFieldUniv (fueledOpsM mode) env s nP fvs j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectFieldUniv
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ fv fv' hs₁ hP => ?_)
    obtain ⟨rfl, hfe⟩ := hP
    refine SimC.bind (opE_infer_sim henv hs₁ (hfvs j fv hfe))
      (fun s₂ ty ty' hs₂ hP₂ => ?_)
    obtain ⟨rfl, htyW⟩ := hP₂
    refine SimC.bind (opS_sim henv hs₂ htyW)
      (fun s₃ u u' hs₃ hP₃ => ?_)
    obtain rfl : u = u' := hP₃
    refine SimC.bind (SimC.liftFueled _ _ hs₃)
      (fun s₄ c c' hs₄ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDirectFieldUnivS_sim henv hfvs hs₄

/-- Stage 1 (the type former) at the shared operations. -/
theorem checkDirectIndS_sim (henv : EnvWF env) {p : DirectParts}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectInd (sharedOpsC mode (mkFEnv env)) env p)
      (checkDirectInd (fueledOpsM mode) env p) := by
  unfold checkDirectInd
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim henv hs)
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
theorem checkDirectCtorS_sim (henv : EnvWF env) {env₀ : Env}
    {p : DirectParts} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectCtor (sharedOpsC mode (mkFEnv env)) env₀ env p cvTa)
      (checkDirectCtor (fueledOpsM mode) env₀ env p cvTa) := by
  unfold checkDirectCtor
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim henv hs)
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
  refine SimC.bind (checkDirectDomsAtS_sim (off := 0) henv
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
  refine SimC.bind (checkDirectFieldUnivS_sim henv hxPos hs₆)
    (fun s₇ u0 u0' hs₇ hU0 => ?_)
  exact SimC.pure hs₇ ⟨rfl, hCw⟩

/-- Stage 3 (the recursor's type) at the shared operations. -/
theorem checkDirectRecTyS_sim (henv : EnvWF env) {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectRecTy (sharedOpsC mode (mkFEnv env)) env p cvTa cvCa cvRa)
      (checkDirectRecTy (fueledOpsM mode) env p cvTa cvCa cvRa) := by
  unfold checkDirectRecTy
  dsimp only [sharedOpsC]
  by_cases h0 : directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim
      p.nP p.nF cvTa.type cvCa.type cvRa.type = true
  case neg => simp only [if_neg h0]; exact SimC.throw_bind
  simp only [if_pos h0]
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ q q' hs₁ hP => ?_)
  obtain ⟨rfl, hop⟩ := hP
  obtain ⟨fvsP, rest⟩ := q
  dsimp only
  have hopW := openPisAtFvars_WScoped (p.nP + 2) cvRa.type 0 hop
    (WScoped.of_not_hasFvar hRf)
  rw [Nat.zero_add] at hopW
  obtain ⟨hfvsW0, hrestW0⟩ := hopW
  have hfvsW : ∀ x ∈ fvsP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => (hfvsW0 x hx).mono (by omega)
  have hpsW : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => hfvsW x (List.mem_of_mem_take hx)
  have hpsWn : ∀ x ∈ fvsP.take p.nP, WScoped p.nP x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hi
    split at hi
    · next hlt =>
      obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop i x hi
      have hw := hfvsW0 _ (List.mem_of_getElem? hi)
      simp only [WScoped] at hw ⊢
      exact ⟨by omega, hw.2⟩
    · exact nomatch hi
  have hfamWn : WScoped p.nP
      (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hpsWn
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q2 q2' hs₂ hQ => ?_)
  obtain ⟨rfl, hci⟩ := hQ
  obtain ⟨cdomsP, crest⟩ := q2
  dsimp only
  obtain ⟨hcdW, hcrW⟩ := instPisAt_WScoped (d := p.nP + 2 + p.nF) _ _ hci
    (WScoped.of_not_hasFvar hCf) hpsW
  obtain ⟨-, hcrWn⟩ := instPisAt_WScoped (d := p.nP) _ _ hci
    (WScoped.of_not_hasFvar hCf) hpsWn
  have hpsIdx : ∀ (i : Nat) (x : Expr), (fvsP.take p.nP)[i]? = some x →
      WScoped (0 + i) (Expr.fvarTypeD x) := by
    intro i x hx
    rw [List.getElem?_take] at hx
    split at hx
    · obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop i x hx
      have hw := hfvsW0 _ (List.mem_of_getElem? hx)
      simp only [WScoped] at hw
      exact hw.2
    · exact nomatch hx
  have hcdIdx : ∀ (i : Nat) (x : Expr), cdomsP[i]? = some x →
      WScoped (0 + i) x := by
    intro i x hx
    refine instPisAt_index_WScoped (fvsP.take p.nP) (d := 0) hci
      (WScoped.of_not_hasFvar hCf) ?_ i x hx
    intro k a hk
    rw [List.getElem?_take] at hk
    split at hk
    · obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop k a hk
      have hw := hfvsW0 _ (List.mem_of_getElem? hk)
      simp only [WScoped] at hw
      simp only [WScoped]
      exact ⟨by omega, hw.2⟩
    · exact nomatch hk
  refine SimC.bind (checkDirectDomsAtS_sim (off := 0) henv hpsIdx hcdIdx hs₂)
    (fun s₃ u1 u1' hs₃ hU1 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ mfv mfv' hs₄ hM => ?_)
  obtain ⟨rfl, hmf⟩ := hM
  have hmftWn : WScoped p.nP mfv.fvarTypeD := by
    obtain ⟨nm, ty, hmfv⟩ :=
      openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop p.nP mfv hmf
    have hw := hfvsW0 _ (List.mem_of_getElem? hmf)
    rw [hmfv] at hw ⊢
    simp only [WScoped] at hw
    show WScoped p.nP ty
    simpa using hw.2
  refine SimC.bind (SimC.unwrapOr' hs₄) (fun s₅ q3 q3' hs₅ hN => ?_)
  obtain ⟨rfl, hms⟩ := hN
  obtain ⟨mbs, mbody⟩ := q3
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ mdom mdom' hs₆ hD => ?_)
  obtain ⟨rfl, hmd⟩ := hD
  have hmdWn : WScoped p.nP mdom :=
    stripPis_head_WScoped hms hmftWn hmd
  refine SimC.bind (opB_sim henv hs₆ hmdWn hfamWn)
    (fun s₇ b1 b1' hs₇ hB1 => ?_)
  obtain rfl : b1 = b1' := hB1
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h2 : (mbody == Expr.sort (.param p.elim)) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  refine SimC.bind (SimC.unwrapOr' hs₇) (fun s₈ minfv mi' hs₈ hI => ?_)
  obtain ⟨rfl, hmi⟩ := hI
  have hmitW : WScoped (p.nP + 2) minfv.fvarTypeD :=
    fvarTypeD_WScoped (hfvsW0 minfv (List.mem_of_getElem? hmi))
  refine SimC.bind (SimC.unwrapOr' hs₈) (fun s₉ q4 q4' hs₉ hX => ?_)
  obtain ⟨rfl, hox⟩ := hX
  obtain ⟨xFvs, minBody⟩ := q4
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF minfv.fvarTypeD (p.nP + 2)
    hox hmitW
  refine SimC.bind (SimC.unwrapOr' hs₉) (fun s₁₀ q5 q5' hs₁₀ hF => ?_)
  obtain ⟨rfl, hcf⟩ := hF
  obtain ⟨cdomsF, crest2⟩ := q5
  dsimp only
  have hxIdx : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (p.nP + 2 + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨nm, ty, rfl⟩ :=
      openPisAtFvars_index p.nF minfv.fvarTypeD (p.nP + 2) hox i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  have hcdFIdx : ∀ (i : Nat) (x : Expr), cdomsF[i]? = some x →
      WScoped (p.nP + 2 + i) x := by
    intro i x hx
    refine instPisAt_index_WScoped xFvs (d := p.nP + 2) hcf
      (hcrWn.mono (by omega)) ?_ i x hx
    intro k a hk
    obtain ⟨nm, ty, rfl⟩ :=
      openPisAtFvars_index p.nF minfv.fvarTypeD (p.nP + 2) hox k a hk
    have hw := hxW _ (List.mem_of_getElem? hk)
    simp only [WScoped] at hw ⊢
    exact ⟨by omega, hw.2⟩
  refine SimC.bind
    (checkDirectDomsAtS_sim (off := p.nP + 2) henv hxIdx hcdFIdx hs₁₀)
    (fun s₁₁ u2 u2' hs₁₁ hU2 => ?_)
  by_cases h3 : (crest2 ==
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : (minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP ++ xFvs))) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (SimC.unwrapOr' hs₁₁)
    (fun s₁₂ q6 q6' hs₁₂ hJ => ?_)
  obtain ⟨rfl, hjs⟩ := hJ
  obtain ⟨jbs, jbody⟩ := q6
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₁₂)
    (fun s₁₃ jdom jdom' hs₁₃ hJD => ?_)
  obtain ⟨rfl, hjd⟩ := hJD
  have hjdW : WScoped (p.nP + 2) jdom :=
    stripPis_head_WScoped hjs hrestW0 hjd
  refine SimC.bind (opB_sim henv hs₁₃ hjdW (hfamWn.mono (by omega)))
    (fun s₁₄ b2 b2' hs₁₄ hB2 => ?_)
  obtain rfl : b2 = b2' := hB2
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h5 : (jbody == Expr.app mfv (.bvar 0)) = true
  case neg => simp only [if_neg h5]; exact SimC.throw
  simp only [if_pos h5]
  exact SimC.pure hs₁₄ rfl

/-- Stage 4 (the recursor's single rule) at the shared operations. -/
theorem checkDirectRuleS_sim (henv : EnvWF env) {p : DirectParts}
    {cvCa cvRa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectRule (sharedOpsC mode (mkFEnv env)) env p cvCa cvRa)
      (checkDirectRule (fueledOpsM mode) env p cvCa cvRa) := by
  unfold checkDirectRule
  dsimp only [sharedOpsC]
  by_cases h0 : (!p.rhs.hasFvar && Expr.looseBVarsBounded 0 p.rhs) = true
  case neg => simp only [if_neg h0]; exact SimC.throw_bind
  simp only [if_pos h0]
  have hrawf : p.rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  refine SimC.bind (opE_annotate_sim henv hs (WScoped.of_not_hasFvar hrawf))
    (fun s₁ rhsA rhsA' hs₁ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  by_cases h1 : (Expr.allLevelParamsDefined cvRa.levelParams rhsA &&
      Expr.constsResolve env rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  have hfv : rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨rbs, rbody⟩ := q
  dsimp only
  by_cases h2 : (rbody == directRuleBody p.nF) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ q2 q2' hs₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, rrest⟩ := q2
  dsimp only
  have hopW := openPisAtFvars_WScoped (p.nP + 2) cvRa.type 0 hop
    (WScoped.of_not_hasFvar hRf)
  rw [Nat.zero_add] at hopW
  obtain ⟨hfvsW0, -⟩ := hopW
  have hfvsW : ∀ x ∈ fvsP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => (hfvsW0 x hx).mono (by omega)
  refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ q3 q3' hs₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨cdomsP, crest⟩ := q3
  dsimp only
  have hpsW2 : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2) x :=
    fun x hx => hfvsW0 x (List.mem_of_mem_take hx)
  obtain ⟨-, hcrW2⟩ := instPisAt_WScoped (d := p.nP + 2) _ _ hci
    (WScoped.of_not_hasFvar hCf) hpsW2
  refine SimC.bind (SimC.unwrapOr' hs₄) (fun s₅ q4 q4' hs₅ hT => ?_)
  obtain ⟨rfl, hox⟩ := hT
  obtain ⟨xFvs, xrest⟩ := q4
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF crest (p.nP + 2) hox hcrW2
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ q6 q6' hs₆ hL => ?_)
  obtain ⟨rfl, hli⟩ := hL
  obtain ⟨ldoms, lrest⟩ := q6
  dsimp only
  have hspineW : ∀ a ∈ fvsP ++ xFvs, WScoped (p.nP + 2 + p.nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsW a ha
    · exact hxW a ha
  obtain ⟨hldW, -⟩ := instLamsAt_WScoped (fvsP ++ xFvs) rhsA hli
    (WScoped.of_not_hasFvar hfv) hspineW
  refine SimC.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hspineW x hx))
      hldW hs₆)
    (fun s₇ u1 u1' hs₇ hU1 => ?_)
  refine SimC.bind (opE_infer_sim henv hs₇ (WScoped.of_not_hasFvar hfv))
    (fun s₈ rhsTy rhsTy' hs₈ hI => ?_)
  exact SimC.pure hs₈ rfl

/-- The projection-function install of the direct path at the shared
operations. -/
theorem checkDirectProjS_sim (henv : EnvWF env) {T C : Name}
    {lps : List Name} {nP nF i : Nat} {cvTa cvCa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDirectProj (sharedOpsC mode (mkFEnv env)) T C lps nP nF cvTa cvCa env i)
      (checkDirectProj (fueledOpsM mode) T C lps nP nF cvTa cvCa env i) := by
  unfold checkDirectProj
  dsimp only [sharedOpsC]
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ pty pty' hs₁ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  by_cases h0 : (!pty.hasFvar && Expr.looseBVarsBounded 0 pty) = true
  case neg => simp only [if_neg h0]; exact SimC.throw_bind
  simp only [if_pos h0]
  have hptyf : pty.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  refine SimC.bind (opE_annotate_sim henv hs₁ (WScoped.of_not_hasFvar hptyf))
    (fun s₂ ptyA ptyA' hs₂ hA => ?_)
  obtain ⟨rfl, -⟩ := hA
  by_cases h1 : (Expr.allLevelParamsDefined lps ptyA &&
      Expr.constsResolve env ptyA && Expr.looseBVarsBounded 0 ptyA &&
      !ptyA.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  have hAf : ptyA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  by_cases h2 : (ptyA.stripPis (nP + 1)).isSome = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  refine SimC.bind (opE_infer_sim henv hs₂ (WScoped.of_not_hasFvar hAf))
    (fun s₃ sty sty' hs₃ hI => ?_)
  obtain ⟨rfl, hstyW⟩ := hI
  refine SimC.bind (opS_sim henv hs₃ hstyW)
    (fun s₄ u u' hs₄ hU => ?_)
  obtain rfl : u = u' := hU
  by_cases h3 : (env.find? (projFnName T i)).isNone = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  refine SimC.bind (checkProjShapeS_sim hs₄)
    (fun s₅ u0 u0' hs₅ hU0 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ q1 q1' hs₆ hQ => ?_)
  obtain ⟨rfl, hop⟩ := hQ
  obtain ⟨fvsP, prest⟩ := q1
  dsimp only
  obtain ⟨hfvsW, hprestW⟩ :=
    openPisAtFvars_WScoped nP ptyA 0 hop (WScoped.of_not_hasFvar hAf)
  rw [Nat.zero_add] at hfvsW hprestW
  have hfamW : WScoped nP (Expr.mkAppN (.const T (lps.map .param)) fvsP) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hfvsW
  refine SimC.bind (SimC.unwrapOr' hs₆) (fun s₇ q2 q2' hs₇ hR => ?_)
  obtain ⟨rfl, hsb⟩ := hR
  obtain ⟨sbs, sbody⟩ := q2
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₇) (fun s₈ sdom sdom' hs₈ hD => ?_)
  obtain ⟨rfl, hsd⟩ := hD
  have hsdW : WScoped nP sdom := stripPis_head_WScoped hsb hprestW hsd
  refine SimC.bind (opB_sim henv hs₈ hsdW hfamW)
    (fun s₉ b1 b1' hs₉ hB1 => ?_)
  obtain rfl : b1 = b1' := hB1
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (SimC.unwrapOr' hs₉) (fun s₁₀ q3 q3' hs₁₀ hT => ?_)
  obtain ⟨rfl, hot⟩ := hT
  obtain ⟨tFvs, resid⟩ := q3
  dsimp only
  obtain ⟨htfW, hresidW⟩ := openPisAtFvars_WScoped 1 prest nP hot hprestW
  refine SimC.bind (SimC.unwrapOr' hs₁₀)
    (fun s₁₁ tfv tfv' hs₁₁ hTf => ?_)
  obtain ⟨rfl, htf⟩ := hTf
  have htfvW : WScoped (nP + 1) tfv := htfW tfv (List.mem_of_getElem? htf)
  have hargsW : ∀ x ∈ fvsP ++ (List.range i).map (fun j =>
      Expr.mkAppN (.const (projFnName T j) (lps.map .param))
        (fvsP ++ [tfv])), WScoped (nP + 1) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hfvsW x hx).mono (by omega)
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      refine Expr.WScoped.mkAppN (by simp [WScoped]) (fun y hy => ?_)
      rcases List.mem_append.mp hy with hy | hy
      · exact (hfvsW y hy).mono (by omega)
      · rcases List.mem_singleton.mp hy with rfl
        exact htfvW
  refine SimC.bind (SimC.unwrapOr' hs₁₁) (fun s₁₂ q4 q4' hs₁₂ hC => ?_)
  obtain ⟨rfl, hci⟩ := hC
  obtain ⟨cdoms, cresid⟩ := q4
  dsimp only
  obtain ⟨-, hcresW⟩ := instPisAt_WScoped (d := nP + 1) _ _ hci
    (WScoped.of_not_hasFvar hCf) hargsW
  refine SimC.bind (SimC.unwrapOr' hs₁₂) (fun s₁₃ fdom fdom' hs₁₃ hFd => ?_)
  obtain ⟨rfl, hfd⟩ := hFd
  obtain ⟨nmC, bodyC, mbC, hcres⟩ :
      ∃ nmC bodyC mbC, cresid = .forallE nmC fdom bodyC mbC := by
    match cresid, hfd with
    | .forallE nmC d bodyC mbC, hfd =>
      obtain rfl : d = fdom := by simpa using hfd
      exact ⟨nmC, bodyC, mbC, rfl⟩
    | .bvar _, hfd | .fvar _ _ _, hfd | .sort _, hfd | .const _ _, hfd
    | .app _ _, hfd | .lam _ _ _ _, hfd | .letE _ _ _ _, hfd
    | .lit _, hfd | .proj _ _ _, hfd => exact nomatch hfd
  have hfdW : WScoped (nP + 1) fdom := by
    rw [hcres] at hcresW
    simp only [WScoped] at hcresW
    exact hcresW.1
  refine SimC.bind (opB_sim henv hs₁₃ hresidW hfdW)
    (fun s₁₄ b2 b2' hs₁₄ hB2 => ?_)
  obtain rfl : b2 = b2' := hB2
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (checkProjRuleS_sim henv hAf hCf hs₁₄)
    (fun s₁₅ rhsA rhsA' hs₁₅ hRu => ?_)
  obtain rfl : rhsA = rhsA' := hRu
  exact SimC.pure hs₁₅ rfl

end Walks3

end Setlec.Cached
