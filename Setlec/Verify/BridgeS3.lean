import Setlec.Verify.BridgeS2

/-!
# Shared-state walks, part 3: the direct simple-structure install (task #82)

The single-environment functions of the direct-install path
(`checkDirectFieldUniv`, `checkDirectDomsAt`, `checkDirectInd`,
`checkDirectCtor`, `checkDirectRecTy`, `checkDirectRule`,
`checkDirectProj`), as `SimAt`s between the `sharedOps` and
`fueledOpsM` instantiations.  The per-site scoping facts mirror
`Setlec/Verify/BridgeWfImp.lean`'s `_wfimp` walks one for one; the
`FEnv`-to-`Env` step is `Setlec/Verify/CheckerF.lean`'s `_eq`/`_push`
family and happens in `Setlec/Model/BridgeS.lean`, so everything here
is stated over the generic functions.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

section Walks3

variable {env : Env} {s₀ : IState}

/-- The per-frame binder-domain pins at the shared operations. -/
theorem checkDirectDomsAtS_sim (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : IState}, ISOK env s₀ →
      SimAt env s₀ RelV
        (checkDirectDomsAt (sharedOps (mkFEnv env)) env off fvs doms j)
        (checkDirectDomsAt fueledOpsM env off fvs doms j)
  | 0, s₀, hs => SimAt.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectDomsAt
    dsimp only [sharedOps]
    refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ a a' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hae⟩ := hP
    refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ b b' hs₂ hext₂ hQ => ?_)
    obtain ⟨rfl, hbe⟩ := hQ
    refine SimAt.bind (opB_sim henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hext₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDirectDomsAtS_sim henv hc ht hs₃

/-- The per-field universe bound at the shared operations. -/
theorem checkDirectFieldUnivS_sim (henv : EnvWF env) {s : Level} {nP : Nat}
    {fvs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {s₀ : IState}, ISOK env s₀ →
      SimAt env s₀ RelV
        (checkDirectFieldUniv (sharedOps (mkFEnv env)) env s nP fvs j)
        (checkDirectFieldUniv fueledOpsM env s nP fvs j)
  | 0, s₀, hs => SimAt.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkDirectFieldUniv
    dsimp only [sharedOps]
    refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ fv fv' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hfe⟩ := hP
    refine SimAt.bind (opE_infer_sim henv hs₁ (hfvs j fv hfe))
      (fun s₂ ty ty' hs₂ hext₂ hP₂ => ?_)
    obtain ⟨rfl, htyW⟩ := hP₂
    refine SimAt.bind (opS_sim henv hs₂ htyW)
      (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
    obtain rfl : u = u' := hP₃
    refine SimAt.bind (SimAt.liftFueled _ _ hs₃)
      (fun s₄ c c' hs₄ hext₄ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDirectFieldUnivS_sim henv hfvs hs₄

/-- Stage 1 (the type former) at the shared operations. -/
theorem checkDirectIndS_sim (henv : EnvWF env) {p : DirectParts}
    (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectInd (sharedOps (mkFEnv env)) env p)
      (checkDirectInd fueledOpsM env p) := by
  unfold checkDirectInd
  dsimp only [sharedOps]
  refine SimAt.bind (checkConstantValS_sim henv hs)
    (fun s₁ cvTa cvTa' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hTw⟩ := hP
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q q' hs₂ hext₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort p.resSort) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  exact SimAt.pure hs₂ ⟨rfl, hTw⟩

/-- Stage 2 (the constructor) at the shared operations. -/
theorem checkDirectCtorS_sim (henv : EnvWF env) {env₀ : Env}
    {p : DirectParts} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v = w ∧ WScoped 0 (Prod.snd v).type)
      (checkDirectCtor (sharedOps (mkFEnv env)) env₀ env p cvTa)
      (checkDirectCtor fueledOpsM env₀ env p cvTa) := by
  unfold checkDirectCtor
  dsimp only [sharedOps]
  refine SimAt.bind (checkConstantValS_sim henv hs)
    (fun s₁ cvCa cvCa' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hCw⟩ := hP
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q q' hs₂ hext₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨cbs, cbody⟩ := q
  dsimp only
  by_cases h1 : (cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF)
      = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.bind (SimAt.unwrapOr' hs₂) (fun s₃ cq cq' hs₃ hext₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, crest⟩ := cq
  dsimp only
  obtain ⟨hfvsW0, hcrW0⟩ := openPisAtFvars_WScoped p.nP cvCa.type 0 hop hCw
  have hcrW : WScoped p.nP crest := by rwa [Nat.zero_add] at hcrW0
  refine SimAt.bind (SimAt.unwrapOr' hs₃) (fun s₄ tq tq' hs₄ hext₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨tfvs, trest⟩ := tq
  dsimp only
  obtain ⟨htfvsW0, -⟩ := openPisAtFvars_WScoped p.nP cvTa.type 0 hci
    (WScoped.of_not_hasFvar hTf)
  refine SimAt.bind (checkDirectDomsAtS_sim (off := 0) henv
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
    (fun s₅ u1 u1' hs₅ hext₅ hU1 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ xq xq' hs₆ hext₆ hT => ?_)
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
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  refine SimAt.bind (checkDirectFieldUnivS_sim henv hxPos hs₆)
    (fun s₇ u0 u0' hs₇ hext₇ hU0 => ?_)
  exact SimAt.pure hs₇ ⟨rfl, hCw⟩

set_option maxHeartbeats 1600000 in
/-- Stage 3 (the recursor's type) at the shared operations. -/
theorem checkDirectRecTyS_sim (henv : EnvWF env) {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkDirectRecTy (sharedOps (mkFEnv env)) env p cvTa cvCa cvRa)
      (checkDirectRecTy fueledOpsM env p cvTa cvCa cvRa) := by
  unfold checkDirectRecTy
  dsimp only [sharedOps]
  by_cases h0 : directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim
      p.nP p.nF cvTa.type cvCa.type cvRa.type = true
  case neg => simp only [if_neg h0]; exact SimAt.throw_bind
  simp only [if_pos h0]
  refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ q q' hs₁ hext₁ hP => ?_)
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
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q2 q2' hs₂ hext₂ hQ => ?_)
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
  refine SimAt.bind (checkDirectDomsAtS_sim (off := 0) henv hpsIdx hcdIdx hs₂)
    (fun s₃ u1 u1' hs₃ hext₃ hU1 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₃) (fun s₄ mfv mfv' hs₄ hext₄ hM => ?_)
  obtain ⟨rfl, hmf⟩ := hM
  have hmftWn : WScoped p.nP mfv.fvarTypeD := by
    obtain ⟨nm, ty, hmfv⟩ :=
      openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop p.nP mfv hmf
    have hw := hfvsW0 _ (List.mem_of_getElem? hmf)
    rw [hmfv] at hw ⊢
    simp only [WScoped] at hw
    show WScoped p.nP ty
    simpa using hw.2
  refine SimAt.bind (SimAt.unwrapOr' hs₄) (fun s₅ q3 q3' hs₅ hext₅ hN => ?_)
  obtain ⟨rfl, hms⟩ := hN
  obtain ⟨mbs, mbody⟩ := q3
  dsimp only
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ mdom mdom' hs₆ hext₆ hD => ?_)
  obtain ⟨rfl, hmd⟩ := hD
  have hmdWn : WScoped p.nP mdom :=
    stripPis_head_WScoped hms hmftWn hmd
  refine SimAt.bind (opB_sim henv hs₆ hmdWn hfamWn)
    (fun s₇ b1 b1' hs₇ hext₇ hB1 => ?_)
  obtain rfl : b1 = b1' := hB1
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h2 : (mbody == Expr.sort (.param p.elim)) = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  refine SimAt.bind (SimAt.unwrapOr' hs₇) (fun s₈ minfv mi' hs₈ hext₈ hI => ?_)
  obtain ⟨rfl, hmi⟩ := hI
  have hmitW : WScoped (p.nP + 2) minfv.fvarTypeD :=
    fvarTypeD_WScoped (hfvsW0 minfv (List.mem_of_getElem? hmi))
  refine SimAt.bind (SimAt.unwrapOr' hs₈) (fun s₉ q4 q4' hs₉ hext₉ hX => ?_)
  obtain ⟨rfl, hox⟩ := hX
  obtain ⟨xFvs, minBody⟩ := q4
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF minfv.fvarTypeD (p.nP + 2)
    hox hmitW
  refine SimAt.bind (SimAt.unwrapOr' hs₉) (fun s₁₀ q5 q5' hs₁₀ hext₁₀ hF => ?_)
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
  refine SimAt.bind
    (checkDirectDomsAtS_sim (off := p.nP + 2) henv hxIdx hcdFIdx hs₁₀)
    (fun s₁₁ u2 u2' hs₁₁ hext₁₁ hU2 => ?_)
  by_cases h3 : (crest2 ==
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : (minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP ++ xFvs))) = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind (SimAt.unwrapOr' hs₁₁)
    (fun s₁₂ q6 q6' hs₁₂ hext₁₂ hJ => ?_)
  obtain ⟨rfl, hjs⟩ := hJ
  obtain ⟨jbs, jbody⟩ := q6
  dsimp only
  refine SimAt.bind (SimAt.unwrapOr' hs₁₂)
    (fun s₁₃ jdom jdom' hs₁₃ hext₁₃ hJD => ?_)
  obtain ⟨rfl, hjd⟩ := hJD
  have hjdW : WScoped (p.nP + 2) jdom :=
    stripPis_head_WScoped hjs hrestW0 hjd
  refine SimAt.bind (opB_sim henv hs₁₃ hjdW (hfamWn.mono (by omega)))
    (fun s₁₄ b2 b2' hs₁₄ hext₁₄ hB2 => ?_)
  obtain rfl : b2 = b2' := hB2
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h5 : (jbody == Expr.app mfv (.bvar 0)) = true
  case neg => simp only [if_neg h5]; exact SimAt.throw
  simp only [if_pos h5]
  exact SimAt.pure hs₁₄ rfl

set_option maxHeartbeats 1600000 in
/-- Stage 4 (the recursor's single rule) at the shared operations. -/
theorem checkDirectRuleS_sim (henv : EnvWF env) {p : DirectParts}
    {cvCa cvRa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkDirectRule (sharedOps (mkFEnv env)) env p cvCa cvRa)
      (checkDirectRule fueledOpsM env p cvCa cvRa) := by
  unfold checkDirectRule
  dsimp only [sharedOps]
  by_cases h0 : (!p.rhs.hasFvar && Expr.looseBVarsBounded 0 p.rhs) = true
  case neg => simp only [if_neg h0]; exact SimAt.throw_bind
  simp only [if_pos h0]
  have hrawf : p.rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  refine SimAt.bind (opE_annotate_sim henv hs (WScoped.of_not_hasFvar hrawf))
    (fun s₁ rhsA rhsA' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  by_cases h1 : (Expr.allLevelParamsDefined cvRa.levelParams rhsA &&
      Expr.constsResolve env rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  have hfv : rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q q' hs₂ hext₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨rbs, rbody⟩ := q
  dsimp only
  by_cases h2 : (rbody == directRuleBody p.nF) = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  refine SimAt.bind (SimAt.unwrapOr' hs₂) (fun s₃ q2 q2' hs₃ hext₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, rrest⟩ := q2
  dsimp only
  have hopW := openPisAtFvars_WScoped (p.nP + 2) cvRa.type 0 hop
    (WScoped.of_not_hasFvar hRf)
  rw [Nat.zero_add] at hopW
  obtain ⟨hfvsW0, -⟩ := hopW
  have hfvsW : ∀ x ∈ fvsP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => (hfvsW0 x hx).mono (by omega)
  refine SimAt.bind (SimAt.unwrapOr' hs₃) (fun s₄ q3 q3' hs₄ hext₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨cdomsP, crest⟩ := q3
  dsimp only
  have hpsW2 : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2) x :=
    fun x hx => hfvsW0 x (List.mem_of_mem_take hx)
  obtain ⟨-, hcrW2⟩ := instPisAt_WScoped (d := p.nP + 2) _ _ hci
    (WScoped.of_not_hasFvar hCf) hpsW2
  refine SimAt.bind (SimAt.unwrapOr' hs₄) (fun s₅ q4 q4' hs₅ hext₅ hT => ?_)
  obtain ⟨rfl, hox⟩ := hT
  obtain ⟨xFvs, xrest⟩ := q4
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF crest (p.nP + 2) hox hcrW2
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ q6 q6' hs₆ hext₆ hL => ?_)
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
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hspineW x hx))
      hldW hs₆)
    (fun s₇ u1 u1' hs₇ hext₇ hU1 => ?_)
  refine SimAt.bind (opE_infer_sim henv hs₇ (WScoped.of_not_hasFvar hfv))
    (fun s₈ rhsTy rhsTy' hs₈ hext₈ hI => ?_)
  exact SimAt.pure hs₈ rfl

set_option maxHeartbeats 1600000 in
/-- The projection-function install of the direct path at the shared
operations. -/
theorem checkDirectProjS_sim (henv : EnvWF env) {T C : Name}
    {lps : List Name} {nP nF i : Nat} {cvTa cvCa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false) (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkDirectProj (sharedOps (mkFEnv env)) T C lps nP nF cvTa cvCa env i)
      (checkDirectProj fueledOpsM T C lps nP nF cvTa cvCa env i) := by
  unfold checkDirectProj
  dsimp only [sharedOps]
  refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ pty pty' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  by_cases h0 : (!pty.hasFvar && Expr.looseBVarsBounded 0 pty) = true
  case neg => simp only [if_neg h0]; exact SimAt.throw_bind
  simp only [if_pos h0]
  have hptyf : pty.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  refine SimAt.bind (opE_annotate_sim henv hs₁ (WScoped.of_not_hasFvar hptyf))
    (fun s₂ ptyA ptyA' hs₂ hext₂ hA => ?_)
  obtain ⟨rfl, -⟩ := hA
  by_cases h1 : (Expr.allLevelParamsDefined lps ptyA &&
      Expr.constsResolve env ptyA && Expr.looseBVarsBounded 0 ptyA &&
      !ptyA.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  have hAf : ptyA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  by_cases h2 : (ptyA.stripPis (nP + 1)).isSome = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  refine SimAt.bind (opE_infer_sim henv hs₂ (WScoped.of_not_hasFvar hAf))
    (fun s₃ sty sty' hs₃ hext₃ hI => ?_)
  obtain ⟨rfl, hstyW⟩ := hI
  refine SimAt.bind (opS_sim henv hs₃ hstyW)
    (fun s₄ u u' hs₄ hext₄ hU => ?_)
  obtain rfl : u = u' := hU
  by_cases h3 : (env.find? (projFnName T i)).isNone = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  refine SimAt.bind (checkProjShapeS_sim hs₄)
    (fun s₅ u0 u0' hs₅ hext₅ hU0 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ q1 q1' hs₆ hext₆ hQ => ?_)
  obtain ⟨rfl, hop⟩ := hQ
  obtain ⟨fvsP, prest⟩ := q1
  dsimp only
  obtain ⟨hfvsW, hprestW⟩ :=
    openPisAtFvars_WScoped nP ptyA 0 hop (WScoped.of_not_hasFvar hAf)
  rw [Nat.zero_add] at hfvsW hprestW
  have hfamW : WScoped nP (Expr.mkAppN (.const T (lps.map .param)) fvsP) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hfvsW
  refine SimAt.bind (SimAt.unwrapOr' hs₆) (fun s₇ q2 q2' hs₇ hext₇ hR => ?_)
  obtain ⟨rfl, hsb⟩ := hR
  obtain ⟨sbs, sbody⟩ := q2
  dsimp only
  refine SimAt.bind (SimAt.unwrapOr' hs₇) (fun s₈ sdom sdom' hs₈ hext₈ hD => ?_)
  obtain ⟨rfl, hsd⟩ := hD
  have hsdW : WScoped nP sdom := stripPis_head_WScoped hsb hprestW hsd
  refine SimAt.bind (opB_sim henv hs₈ hsdW hfamW)
    (fun s₉ b1 b1' hs₉ hext₉ hB1 => ?_)
  obtain rfl : b1 = b1' := hB1
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimAt.bind (SimAt.unwrapOr' hs₉) (fun s₁₀ q3 q3' hs₁₀ hext₁₀ hT => ?_)
  obtain ⟨rfl, hot⟩ := hT
  obtain ⟨tFvs, resid⟩ := q3
  dsimp only
  obtain ⟨htfW, hresidW⟩ := openPisAtFvars_WScoped 1 prest nP hot hprestW
  refine SimAt.bind (SimAt.unwrapOr' hs₁₀)
    (fun s₁₁ tfv tfv' hs₁₁ hext₁₁ hTf => ?_)
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
  refine SimAt.bind (SimAt.unwrapOr' hs₁₁) (fun s₁₂ q4 q4' hs₁₂ hext₁₂ hC => ?_)
  obtain ⟨rfl, hci⟩ := hC
  obtain ⟨cdoms, cresid⟩ := q4
  dsimp only
  obtain ⟨-, hcresW⟩ := instPisAt_WScoped (d := nP + 1) _ _ hci
    (WScoped.of_not_hasFvar hCf) hargsW
  refine SimAt.bind (SimAt.unwrapOr' hs₁₂) (fun s₁₃ fdom fdom' hs₁₃ hx hFd => ?_)
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
  refine SimAt.bind (opB_sim henv hs₁₃ hresidW hfdW)
    (fun s₁₄ b2 b2' hs₁₄ hext₁₄ hB2 => ?_)
  obtain rfl : b2 = b2' := hB2
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimAt.bind (checkProjRuleS_sim henv hAf hCf hs₁₄)
    (fun s₁₅ rhsA rhsA' hs₁₅ hext₁₅ hRu => ?_)
  obtain rfl : rhsA = rhsA' := hRu
  exact SimAt.pure hs₁₅ rfl

end Walks3

end Setlec
