import Setlec.Model.TypeChecker

/-!
# Fold facts for a modeled recursor

`modeled_rule_fold` derives one recursor rule's `RecRulesOk` fold
obligation from the checked `R._model.iota_j` theorem: the certified
telescope fits are transferred onto the statement's telescope, the
theorem's inhabitant is eliminated into a member of the interpreted
equation, the `Eq` collapse turns that into a value equality between
the model recursor's spine fold and the rule body's interpretation,
and the λ-tower fold identifies the latter with the rule's own
interpretation applied along the spine.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {φ' : Name → Nat}

open SetTheory Expr

/-- A fit's argument spine interprets pointwise to its value spine. -/
theorem TeleFitI.toInterpSpine {V : Type u} [SetTheory V]
    {cval : ConstVal V} {env : Env} {φ : Name → Nat} {d : Nat}
    {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      InterpSpine cval env φ d ρ args vs := by
  intro ty args vs rest h
  induction h with
  | nil => trivial
  | cons hity hiarg hx hfb hwa hba hAa _ ih => exact ⟨hiarg, ih⟩

set_option maxHeartbeats 1600000 in
theorem modeled_rule_fold
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name}
    (hro : RenameOk val' env₁ f)
    (hcvp : ConstValParams val' env₁)
    -- the block members and their models
    {R : Name} {lps : List Name} {tyA : Expr} {nP nm ni cnF : Nat}
    {ctor : Name} {cvj : ConstantVal}
    (hfj : env₁.find? ctor = some (.ctorInfo cvj nP cnF))
    {cim : ConstantInfo}
    (hfRm : env₁.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    (hClps : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) → val' ctor ψ₁ = val' ctor ψ₂)
    -- the pinned equality former
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    -- the iota theorem (value and statement facts)
    {thmName : Name} {cvt : ConstantVal}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V val' env₁ ψ'' cvt.type = some P ∧
      val' thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    -- syntactic pins (kernel checks)
    {rhsA rbody tybody cbody sbody : Expr}
    {rbinders tbinders cbinders sbinders : List (Name × Expr × BinderMeta)}
    {ℓA : Level}
    (hstripR : rhsA.stripLams (nP + 1 + nm + cnF) = some (rbinders, rbody))
    (hR_strip : tyA.stripPis (nP + 1 + nm + ni + 1) = some (tbinders, tybody))
    (hC_strip : cvj.type.stripPis (nP + cnF) = some (cbinders, cbody))
    (_hC_len : cbody.getAppArgs.length = nP + ni)
    (hS_strip : cvt.type.stripPis ((nP + (1 + nm)) + cnF) =
      some (sbinders, sbody))
    (hdomsPre : ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      i < nP + 1 + nm →
      rbinders[i]? = some b → tbinders[i]? = some b' → b.2.1 = b'.2.1)
    (hdomsF : ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[(nP + (1 + nm)) + i]? = some b →
      cbinders[nP + i]? = some b' →
      b.2.1 = (b'.2.1).liftLooseBVars (1 + nm) i)
    (hsdoms : ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[i]? = some b → rbinders[i]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [Expr.mkAppN (.bvar (cnF + nm))
        (((cbody.getAppArgs.drop nP).map fun e =>
            (e.liftLooseBVars (1 + nm) cnF).renameConsts f) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (((List.range nP).map fun k =>
              Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
           ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
       Expr.mkAppN (.const (f R) (lps.map .param))
        (((((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
          ((List.range (1 + nm)).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))) ++
          ((cbody.getAppArgs.drop nP).map fun e =>
            (e.liftLooseBVars (1 + nm) cnF).renameConsts f)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
            ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
       rbody.renameConsts f])
    -- rule right-hand-side facts
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) rhsA)
    -- member type wf
    (htyw : tyA.hasFvar = false)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    -- the fold clause's inputs
    {us usj : List Level} {args margs : List V} {tv : V}
    (hlena : args.length = nP + 1 + nm + ni)
    (hlenm : margs.length = nP + cnF)
    (htv : tv = SpineFold V (val' ctor
      (Level.substFn φ' cvj.levelParams usj)) margs)
    (hparameq : margs.take nP = (args ++ [tv]).take nP)
    (hleveq : ∀ p ∈ cvj.levelParams,
      Level.substFn φ' cvj.levelParams usj p = Level.substFn φ' lps us p)
    {d : Nat} {ρ : Nat → V} {d₁ : Nat} {ρ₁ : Nat → V} {rest₁ : Expr}
    {d₂ : Nat} {ρ₂ : Nat → V} {rest₂ : Expr}
    (hfit1 : TeleFit V val' env₁ φ' d ρ
      (tyA.instantiateLevelParams lps us) (args ++ [tv]) d₁ ρ₁ rest₁)
    (hfit2 : TeleFit V val' env₁ φ' d₁ ρ₁
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs
      d₂ ρ₂ rest₂)
    (hidx : (rest₂.getAppArgs.drop nP).mapM
      (interpExpr V val' env₁ φ' d₂ ρ₂) =
      some (args.drop (nP + 1 + nm))) :
    ∃ Rv, interpClosed V val' env₁ (Level.substFn φ' lps us) rhsA =
        some Rv ∧
      SpineFold V (val' R (Level.substFn φ' lps us)) (args ++ [tv]) =
        SpineFold V Rv (args.take (nP + 1 + nm) ++ margs.drop nP) ∧
      ChainSlots V Rv (args.take (nP + 1 + nm) ++ margs.drop nP) := by
  -- S0/S1: sanitized fvar-argument fits on the *raw* telescopes at ψ,
  -- in the final frame
  have hTw : ∀ D, WScoped D (tyA.instantiateLevelParams lps us) := fun D =>
    WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact htyw)
  have hCwI : ∀ D, WScoped D
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := fun D =>
    WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hCw)
  obtain ⟨hd₁, hagr₁, argsR0, hfitL1, hfvR0⟩ :=
    TeleFit.toTeleFitI hfit1 (hTw d)
  obtain ⟨hd₂, hagr₂, argsC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfit2 (hCwI d₁)
  have hlenR0 : argsR0.length = nP + 1 + nm + ni + 1 := by
    have h1 := TeleFitI.vs_length hfitL1
    simp [hlena] at h1
    omega
  have hlenC0 : argsC0.length = nP + cnF := by
    have h1 := TeleFitI.vs_length hfitL2
    simp [hlenm] at h1
    omega
  obtain ⟨restR1, hfitS1⟩ := TeleFitI.sanitize hfitL1
    (by rw [hlenR0]
        exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
          (by rw [hR_strip]; rfl)) hfvR0
  obtain ⟨restC1, hfitS2⟩ := TeleFitI.sanitize hfitL2
    (by rw [hlenC0]
        exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
          (by rw [hC_strip]; rfl)) hfvC0
  have hshR : ∀ a ∈ argsR0.map sanitizeArg, ∃ i n,
      a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvR0 a₀ ha₀
    exact ⟨i, n, rfl⟩
  have hshC : ∀ a ∈ argsC0.map sanitizeArg, ∃ i n,
      a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨i, n, rfl⟩
  -- uninstantiate the levels: raw telescopes at ψ / ψj, then move the
  -- constructor fit to ψ
  obtain ⟨restR2, hfitRaw1⟩ := TeleFitI.instLev_down hcvp hfitS1 hshR
    (WScoped.of_not_hasFvar htyw (d := d₁)).fvarsBelow
  obtain ⟨restC2', hfitRaw2⟩ := TeleFitI.instLev_down hcvp hfitS2 hshC
    (WScoped.of_not_hasFvar hCw (d := d₂)).fvarsBelow
  obtain ⟨restC3, hfitRaw2'⟩ := TeleFitI.params_ext hleveq hcvp hfitRaw2
    hCps hshC
  -- lift the recursor fit to the final frame
  have hfitR : TeleFitI V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      tyA (argsR0.map sanitizeArg) (args ++ [tv]) restR2 :=
    TeleFitI.lift hfitRaw1 (WScoped.of_not_hasFvar htyw) hd₂ hagr₂
  obtain ⟨argsR, hargsRdef⟩ : ∃ x, x = argsR0.map sanitizeArg := ⟨_, rfl⟩
  obtain ⟨argsC, hargsCdef⟩ : ∃ x, x = argsC0.map sanitizeArg := ⟨_, rfl⟩
  rw [← hargsRdef] at hfitR
  rw [← hargsCdef] at hfitRaw2'
  have hlenR : argsR.length = nP + 1 + nm + ni + 1 := by
    simp [hargsRdef, hlenR0]
  have hlenC : argsC.length = nP + cnF := by
    simp [hargsCdef, hlenC0]
  have hshR' : ∀ a ∈ argsR, ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    rw [hargsRdef]; exact hshR
  have hshC' : ∀ a ∈ argsC, ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    rw [hargsCdef]; exact hshC
  -- S2: swap the constructor fit's parameter arguments for the
  -- recursor fit's (equal values by the kernel's parameter check)
  have hrel : ArgsRel (fun a₁ a₂ =>
      interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₂ =
        interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₁ ∧
      WScoped d₂ a₂ ∧ a₂.looseBVarsBounded 0 = true ∧
      AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₂)
      (argsC.take nP) (argsR.take nP) := by
    refine ArgsRel.of_pointwise (by simp [hlenC, hlenR]; omega) ?_
    intro i a₁ a₂ ha₁ ha₂
    have hi : i < nP := by
      rcases Nat.lt_or_ge i nP with h | h
      · exact h
      · rw [List.getElem?_take_eq_none h] at ha₁
        exact nomatch ha₁
    rw [List.getElem?_take_of_lt hi] at ha₁ ha₂
    obtain ⟨v, hv⟩ : ∃ v, margs[i]? = some v :=
      ⟨margs[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hint₁ := TeleFitI.arg_facts hfitRaw2' i a₁ v ha₁ hv
    have hveq : (args ++ [tv])[i]? = some v := by
      have h1 : (margs.take nP)[i]? = some v := by
        rw [List.getElem?_take_of_lt hi]; exact hv
      rw [hparameq] at h1
      rwa [List.getElem?_take_of_lt hi] at h1
    have hint₂ := TeleFitI.arg_facts hfitR i a₂ v ha₂ hveq
    obtain ⟨hw₂, hb₂, hA₂⟩ := TeleFitI.arg_wf hfitR i a₂ ha₂
    exact ⟨hint₂.trans hint₁.symm, hw₂, hb₂, hA₂⟩
  have hfitC' : TeleFitI V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      cvj.type (argsC.take nP ++ argsC.drop nP) margs restC3 := by
    rw [List.take_append_drop]
    exact hfitRaw2'
  obtain ⟨restC4, hfitC4⟩ := TeleFitI.swap_prefix hfitC'
    (by rw [show (argsC.take nP ++ argsC.drop nP).length = nP + cnF from
        by simp [hlenC]]
        rw [hC_strip]; rfl) hrel
  -- S3: the raw prefix relation and the statement prefix fit
  obtain ⟨tyPreBody, hTpre⟩ := Expr.stripPis_prefix (nP + 1 + nm) (ni + 1)
    (by rw [show nP + 1 + nm + (ni + 1) = nP + 1 + nm + ni + 1 from by omega]
        exact hR_strip)
  obtain ⟨stPreBody, hSpre⟩ := Expr.stripPis_prefix (nP + (1 + nm)) cnF
    hS_strip
  have hpiRel : PiDomsRenEq f (nP + 1 + nm) tyA cvt.type := by
    refine PiDomsRenEq.of_pointwise (nP + 1 + nm) hTpre
      (by rw [show nP + 1 + nm = nP + (1 + nm) from by omega]
          exact hSpre) ?_
    intro i b₁ b₂ hb₁ hb₂
    have htlen : tbinders.length = nP + 1 + nm + ni + 1 :=
      Expr.stripPis_length _ hR_strip
    have hslen : sbinders.length = (nP + (1 + nm)) + cnF :=
      Expr.stripPis_length _ hS_strip
    have hrlen : rbinders.length = nP + 1 + nm + cnF :=
      Expr.stripLams_length _ hstripR
    have hi : i < nP + 1 + nm := by
      rcases Nat.lt_or_ge i (nP + 1 + nm) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by simp [htlen]; omega)] at hb₁
        exact nomatch hb₁
    have hb₁' : tbinders[i]? = some b₁ := by
      rwa [List.getElem?_take_of_lt hi] at hb₁
    have hb₂' : sbinders[i]? = some b₂ := by
      rwa [List.getElem?_take_of_lt (by omega)] at hb₂
    obtain ⟨rb, hrb⟩ : ∃ rb, rbinders[i]? = some rb :=
      ⟨rbinders[i]'(by omega), List.getElem?_eq_getElem _⟩
    have h1 : rb.2.1 = b₁.2.1 := hdomsPre i rb b₁ hi hrb hb₁'
    have h2 : b₂.2.1 = rb.2.1.renameConsts f := hsdoms i b₂ rb hb₂' hrb
    show RenEq f b₁.2.1 b₂.2.1
    rw [h2, h1]
    exact Expr.ErasedEq.rfl _
  -- the recursor fit's prefix
  have hfitR' : TeleFitI V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      tyA (argsR.take (nP + 1 + nm) ++ argsR.drop (nP + 1 + nm))
      (args ++ [tv]) restR2 := by
    rw [List.take_append_drop]
    exact hfitR
  obtain ⟨midR, hpreR⟩ := TeleFitI.take_prefix hfitR'
  have hpreRlen : (argsR.take (nP + 1 + nm)).length = nP + 1 + nm := by
    simp [hlenR]
    omega
  have hpreRvs : (args ++ [tv]).take (argsR.take (nP + 1 + nm)).length =
      args.take (nP + 1 + nm) := by
    rw [hpreRlen, List.take_append_of_le_length (by omega)]
  rw [hpreRvs] at hpreR
  have hargsSelf : ArgsRel (fun a₁ a₂ => RenEq f a₁ a₂ ∧ WScoped d₂ a₂ ∧
      a₂.looseBVarsBounded 0 = true ∧
      AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₂)
      (argsR.take (nP + 1 + nm)) (argsR.take (nP + 1 + nm)) := by
    refine ArgsRel.of_pointwise rfl ?_
    intro i a₁ a₂ ha₁ ha₂
    obtain rfl : a₁ = a₂ := by
      rw [ha₁] at ha₂
      exact Option.some.inj ha₂
    have hi : i < nP + 1 + nm := by
      rcases Nat.lt_or_ge i (nP + 1 + nm) with h | h
      · exact h
      · rw [List.getElem?_take_eq_none h] at ha₁
        exact nomatch ha₁
    have ha₁' : argsR[i]? = some a₁ := by
      rwa [List.getElem?_take_of_lt hi] at ha₁
    obtain ⟨j, n, rfl⟩ := hshR' a₁ (List.mem_of_getElem? ha₁')
    obtain ⟨hw, hb, hA⟩ := TeleFitI.arg_wf hfitR i _ ha₁'
    exact ⟨RenEq.fvar_self, hw, hb, hA⟩
  have hSfb : Expr.fvarsBelow d₂ cvt.type :=
    (WScoped.of_not_hasFvar hSw).fvarsBelow
  obtain ⟨midSE, hpreS⟩ := TeleFitI.ren_transfer hro hpreR
    (by rw [hpreRlen]; exact hpiRel) hSfb hargsSelf
  -- S4: the constructor field fit transfers onto the statement's
  -- residual
  obtain ⟨midCE, vsF, hpeelC, hfieldC, hvsF, hvsFlen⟩ :=
    TeleFitI.drop_prefix (pre := argsR.take nP) (post := argsC.drop nP)
      hfitC4
  have hlenRnP : (argsR.take nP).length = nP := by
    simp [hlenR]
    omega
  have hvsFeq : vsF = margs.drop nP := by
    rw [hlenRnP] at hvsF
    exact List.append_cancel_left
      (hvsF.symm.trans (List.take_append_drop nP margs).symm)
  subst hvsFeq
  -- the fields relation between the two residuals
  have hfieldsRel : PiDomsRenEq f cnF midCE midSE := by
    refine fields_relation (f := f) (nP := nP) (nmM := 1 + nm)
      (cnF := cnF) (params := argsR.take nP)
      (extras := (argsR.take (nP + 1 + nm)).drop nP)
      (by omega) hC_strip hS_strip ?_ hlenRnP
      (by simp only [List.length_drop, List.length_take, hlenR]; omega)
      ?_ ?_ hpeelC ?_
    · intro i cb sb hcb hsb
      obtain ⟨rb, hrb⟩ : ∃ rb, rbinders[(nP + (1 + nm)) + i]? = some rb := by
        have hrlen : rbinders.length = nP + 1 + nm + cnF :=
          Expr.stripLams_length _ hstripR
        have hilt : (nP + (1 + nm)) + i < rbinders.length := by
          have hslen : sbinders.length = (nP + (1 + nm)) + cnF :=
            Expr.stripPis_length _ hS_strip
          rcases Nat.lt_or_ge ((nP + (1 + nm)) + i) sbinders.length
            with h | h
          · omega
          · rw [List.getElem?_eq_none (by omega)] at hsb
            exact nomatch hsb
        exact ⟨rbinders[(nP + (1 + nm)) + i]'hilt,
          List.getElem?_eq_getElem _⟩
      have e3 : sb.2.1 = rb.2.1.renameConsts f :=
        hsdoms _ sb rb hsb hrb
      have e4 : rb.2.1 = cb.2.1.liftLooseBVars (1 + nm) i :=
        hdomsF i rb cb hrb hcb
      rw [e3, e4]
    · intro a ha
      obtain ⟨j, n, rfl⟩ := hshR' a
        (List.mem_of_mem_take ha)
      rfl
    · intro a ha
      obtain ⟨j, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
      exact rfl
    · -- the statement mid is the prefix walk's residual
      have hpe := TeleFitI.rest_eq hpreS
      rw [show argsR.take nP ++ (argsR.take (nP + 1 + nm)).drop nP =
          argsR.take (nP + 1 + nm) from by
        rw [show argsR.take nP = (argsR.take (nP + 1 + nm)).take nP from by
          rw [List.take_take]
          congr 1
          omega]
        exact List.take_append_drop nP (argsR.take (nP + 1 + nm))]
      exact hpe
  have hCfb : ∀ a ∈ argsC.drop nP, Expr.fvarsBelow d₂ a := by
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshC' a (List.mem_of_mem_drop ha)
    obtain ⟨i0, hi0⟩ : ∃ i0, (argsC.drop nP)[i0]? = some (Expr.fvar j n
      (.sort .zero)) := List.getElem?_of_mem ha
    have hci : argsC[nP + i0]? = some (Expr.fvar j n (.sort .zero)) := by
      rwa [List.getElem?_drop] at hi0
    have := (TeleFitI.arg_wf hfitRaw2' (nP + i0) _ hci).1
    exact this.fvarsBelow
  have hargsSelfC : ArgsRel (fun a₁ a₂ => RenEq f a₁ a₂ ∧ WScoped d₂ a₂ ∧
      a₂.looseBVarsBounded 0 = true ∧
      AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₂)
      (argsC.drop nP) (argsC.drop nP) := by
    refine ArgsRel.of_pointwise rfl ?_
    intro i a₁ a₂ ha₁ ha₂
    obtain rfl : a₁ = a₂ := by
      rw [ha₁] at ha₂
      exact Option.some.inj ha₂
    have ha₁' : argsC[nP + i]? = some a₁ := by
      rwa [List.getElem?_drop] at ha₁
    obtain ⟨j, n, rfl⟩ := hshC' a₁ (List.mem_of_getElem? ha₁')
    obtain ⟨hw, hb, hA⟩ := TeleFitI.arg_wf hfitRaw2' (nP + i) _ ha₁'
    exact ⟨RenEq.fvar_self, hw, hb, hA⟩
  have hmidSfb : Expr.fvarsBelow d₂ midSE := by
    refine telescopeInst_fvarsBelow _ hSfb ?_ (TeleFitI.rest_eq hpreS)
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
    obtain ⟨i0, hi0⟩ := List.getElem?_of_mem ha
    have hci : argsR[i0]? = some (Expr.fvar j n (.sort .zero)) := by
      have hi : i0 < nP + 1 + nm := by
        rcases Nat.lt_or_ge i0 (nP + 1 + nm) with h | h
        · exact h
        · rw [List.getElem?_take_eq_none h] at hi0
          exact nomatch hi0
      rwa [List.getElem?_take_of_lt hi] at hi0
    exact ((TeleFitI.arg_wf hfitR i0 _ hci).1).fvarsBelow
  obtain ⟨restF, hfieldS⟩ := TeleFitI.ren_transfer hro hfieldC
    (by rw [show (argsC.drop nP).length = cnF from by simp [hlenC]]
        exact hfieldsRel) hmidSfb hargsSelfC
  -- S5: the full statement fit
  have hstmtFit := TeleFitI.append hpreS hfieldS
  -- S6: eliminate the theorem's inhabitant through the statement fit
  obtain ⟨P, hPi, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPi' : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      cvt.type = some P := by
    rw [interp_closed_invariant hSw d₂ ρ₂]
    exact hPi
  have hSA : AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      cvt.type :=
    AnnotOk.closed_invariant hSw d₂ ρ₂ (hthm_annot _)
  obtain ⟨Q, hQi, hQmem, hQA⟩ := TeleFitI.elim hstmtFit hSA hPi' hPmem
  -- the elimination residual is the instantiated equation body
  have hallLen : (argsR.take (nP + 1 + nm) ++ argsC.drop nP).length =
      (nP + (1 + nm)) + cnF := by
    simp only [List.length_append, List.length_take, List.length_drop,
      hlenR, hlenC]
    omega
  obtain ⟨restT, hrestT, bs0, body0, hstrip0, hbody0, -⟩ :=
    telescopeInst_stripPis ((nP + (1 + nm)) + cnF)
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP) 0 hallLen hS_strip
  have hrest_id : restT = body0 := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip0
    exact hstrip0.2
  have hrestF : telescopeInst cvt.type
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP) =
      some (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
        ((nP + (1 + nm)) + cnF - 1) sbody) := by
    rw [hrestT, hrest_id, hbody0,
      show nP + (1 + nm) + cnF + 0 - 1 = nP + (1 + nm) + cnF - 1 from by
        omega]
  have hfitrest := TeleFitI.rest_eq hstmtFit
  rw [hrestF] at hfitrest
  obtain rfl := Option.some.inj hfitrest
  -- S7: resolve the equation's components along the argument spine
  have hbounded : ∀ a ∈ argsR.take (nP + 1 + nm) ++ argsC.drop nP,
      a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
      rfl
    · obtain ⟨i, n, rfl⟩ := hshC' a (List.mem_of_mem_drop ha)
      rfl
  have hresolve : ∀ (k : Nat), k < (nP + (1 + nm)) + cnF →
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)[k]? =
      some (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
        ((nP + (1 + nm)) + cnF - 1)
        (.bvar ((nP + (1 + nm)) + cnF - 1 - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
      ((nP + (1 + nm)) + cnF - 1) ((nP + (1 + nm)) + cnF - 1 - k)
      hbounded (by omega) (by rw [hallLen]; omega)
    rwa [show (nP + (1 + nm)) + cnF - 1 - ((nP + (1 + nm)) + cnF - 1 - k)
      = k from by omega] at h1
  -- the three bvar-spine resolutions (parameters+motive+minors, and
  -- fields), as list identities
  have hres_pm : (((List.range nP).map fun k =>
        Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
      ((List.range (1 + nm)).map fun k =>
        Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))).map
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) ·) =
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP).take (nP + 1 + nm) := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k (nP + 1 + nm) with hk | hk
    · rw [List.getElem?_take_of_lt hk, List.getElem?_map]
      rcases Nat.lt_or_ge k nP with hk2 | hk2
      · rw [List.getElem?_append_left (by simpa using hk2),
          List.getElem?_map, List.getElem?_range hk2]
        rw [hresolve k (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        congr 2
        omega
      · rw [List.getElem?_append_right (by simpa using hk2),
          List.getElem?_map]
        rw [show k - (((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k))).length = k - nP from
          by simp]
        rw [List.getElem?_range (by omega)]
        rw [hresolve k (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        congr 2
        omega
    · rw [List.getElem?_take_eq_none hk, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega)]
      rfl
  have hres_x : (((List.range cnF).map fun k =>
        Expr.bvar (cnF - 1 - k))).map
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) ·) =
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop (nP + 1 + nm) := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k cnF with hk | hk
    · rw [List.getElem?_drop, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hk]
      rw [show (nP + 1 + nm) + k = k + (nP + 1 + nm) from by omega]
      rw [show (argsR.take (nP + 1 + nm) ++ argsC.drop nP)[k +
          (nP + 1 + nm)]? = some (Expr.instSeq
            (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
            ((nP + (1 + nm)) + cnF - 1)
            (.bvar ((nP + (1 + nm)) + cnF - 1 - (k + (nP + 1 + nm)))))
          from hresolve (k + (nP + 1 + nm)) (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      congr 2
      omega
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by
          rw [List.length_drop, hallLen]
          omega)]
      rfl
  have hres_p : (((List.range nP).map fun k =>
        Expr.bvar (nP + 1 + nm + cnF - 1 - k))).map
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) ·) =
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_take_of_lt hk, List.getElem?_map,
        List.getElem?_map, List.getElem?_range hk,
        hresolve k (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      congr 2
      omega
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_take_eq_none hk]
      rfl
  -- resolve the constructor application
  have hctorRes : Expr.instSeq
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
      ((nP + (1 + nm)) + cnF - 1)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
         ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
         (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
           (nP + 1 + nm)) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p
      | exact hres_x
  -- resolve the index expressions: the middle collapse onto the
  -- parameter+field spine
  have hBlen : ((argsR.take (nP + 1 + nm)).drop nP).length = 1 + nm := by
    simp [hlenR]
    omega
  have hClen2 : (argsC.drop nP).length = cnF := by
    simp [hlenC]
  have hAlen : (argsR.take nP).length = nP := by
    simp [hlenR]
    omega
  have hidxRes : ∀ e : Expr,
      Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
        ((nP + (1 + nm)) + cnF - 1)
        ((e.liftLooseBVars (1 + nm) cnF).renameConsts f) =
      Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
        (e.renameConsts f) := by
    intro e
    rw [Expr.renameConsts_liftLooseBVars]
    rw [show argsR.take (nP + 1 + nm) =
        argsR.take nP ++ (argsR.take (nP + 1 + nm)).drop nP from by
      rw [show argsR.take nP = (argsR.take (nP + 1 + nm)).take nP from by
        rw [List.take_take]
        congr 1
        omega]
      exact (List.take_append_drop nP _).symm]
    have hcoll := Expr.instSeq_mid_collapse (argsR.take nP)
      ((argsR.take (nP + 1 + nm)).drop nP) (argsC.drop nP)
      (X := e.renameConsts f)
      (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
        rfl)
    rw [hAlen, hBlen, hClen2] at hcoll
    exact hcoll
  have hres_idx : (((cbody.getAppArgs.drop nP).map fun e =>
        (e.liftLooseBVars (1 + nm) cnF).renameConsts f).map
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) ·)) =
      (cbody.getAppArgs.drop nP).map fun e =>
        Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
          (e.renameConsts f) := by
    rw [List.map_map]
    exact List.map_congr_left (fun e _ => hidxRes e)
  -- resolve the recursor application
  have hlhsRes : Expr.instSeq
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
      ((nP + (1 + nm)) + cnF - 1)
      (Expr.mkAppN (.const (f R) (lps.map .param))
        (((((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
          ((List.range (1 + nm)).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))) ++
          ((cbody.getAppArgs.drop nP).map fun e =>
            (e.liftLooseBVars (1 + nm) cnF).renameConsts f)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
            ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))])) =
      Expr.mkAppN (.const (f R) (lps.map .param))
        (((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take (nP + 1 + nm) ++
          ((cbody.getAppArgs.drop nP).map fun e =>
            Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
              (e.renameConsts f))) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
            (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
              (nP + 1 + nm))]) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl),
      List.map_append, List.map_append, hres_pm, hres_idx]
    simp only [List.map_cons, List.map_nil]
    rw [hctorRes]
  -- resolve the motive application
  have hmotRes : (argsR.take (nP + 1 + nm) ++ argsC.drop nP)[nP]? =
      some (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
        ((nP + (1 + nm)) + cnF - 1) (.bvar (cnF + nm))) := by
    have h1 := hresolve nP (by omega)
    rwa [show (nP + (1 + nm)) + cnF - 1 - nP = cnF + nm from by omega]
      at h1
  -- the resolved residual
  have hresidual : Expr.instSeq
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
      ((nP + (1 + nm)) + cnF - 1) sbody =
      Expr.mkAppN (.const eqName [ℓA])
        [Expr.mkAppN (Expr.instSeq
            (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
            ((nP + (1 + nm)) + cnF - 1) (.bvar (cnF + nm)))
          (((cbody.getAppArgs.drop nP).map fun e =>
            Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
              (e.renameConsts f)) ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
            ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
             (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
               (nP + 1 + nm))]),
         Expr.mkAppN (.const (f R) (lps.map .param))
          (((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take (nP + 1 + nm)
            ++
            ((cbody.getAppArgs.drop nP).map fun e =>
              Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
                (e.renameConsts f))) ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
              (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
                (nP + 1 + nm))]),
         Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
           ((nP + (1 + nm)) + cnF - 1) (rbody.renameConsts f)] := by
    rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    simp only [List.map_cons, List.map_nil]
    rw [hlhsRes]
    rw [Expr.instSeq_mkAppN, List.map_append, hres_idx]
    simp only [List.map_cons, List.map_nil]
    rw [hctorRes]
  rw [hresidual] at hQi hQA
  -- S8: compute the components' values
  have hAllSpine : InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
      (args.take (nP + 1 + nm) ++ margs.drop nP) :=
    TeleFitI.toInterpSpine hstmtFit
  -- value lists along the two sub-spines
  have hVlen : (args.take (nP + 1 + nm)).length = nP + 1 + nm := by
    simp [hlena]
    try omega
  have hVtake : (args.take (nP + 1 + nm) ++ margs.drop nP).take nP =
      margs.take nP := by
    rw [List.take_append_of_le_length (by rw [hVlen]; omega),
      List.take_take, show min nP (nP + 1 + nm) = nP from by omega,
      show args.take nP = (args ++ [tv]).take nP from
        (List.take_append_of_le_length (by omega)).symm, ← hparameq]
  have hVdrop : (args.take (nP + 1 + nm) ++ margs.drop nP).drop
      (nP + 1 + nm) = margs.drop nP := by
    have h0 := List.drop_left (l₁ := args.take (nP + 1 + nm))
      (l₂ := margs.drop nP)
    rwa [hVlen] at h0
  have hVpre : (args.take (nP + 1 + nm) ++ margs.drop nP).take
      (nP + 1 + nm) = args.take (nP + 1 + nm) := by
    have h0 := List.take_left (l₁ := args.take (nP + 1 + nm))
      (l₂ := margs.drop nP)
    rwa [hVlen] at h0
  -- the constructor's value
  obtain ⟨cimC, hfCm, hlpCm⟩ := hro.1 ctor _ hfj
  have hcCval : val' (f ctor) (Level.substFn (Level.substFn φ' lps us)
      cvj.levelParams (cvj.levelParams.map .param)) =
      val' ctor (Level.substFn φ' cvj.levelParams usj) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) cvj.levelParams
        (cvj.levelParams.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 ctor]
    exact hClps _ _ (fun p hp => (hleveq p hp).symm)
  have hcCi : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (.const (f ctor) (cvj.levelParams.map .param)) =
      some (val' ctor (Level.substFn φ' cvj.levelParams usj)) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hlpCm]; simp [ConstantInfo.toConstantVal])]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from by
      rw [hlpCm]; rfl]
    rw [hcCval]
  -- the resolved constructor application's value is the major
  have hctorVal : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
         (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
           (nP + 1 + nm))) = some tv := by
    rw [interp_mkAppN _ _ hcCi
      (InterpSpine.append (InterpSpine.take nP hAllSpine)
        (InterpSpine.drop (nP + 1 + nm) hAllSpine))]
    congr 1
    rw [hVtake, hVdrop, htv]
    congr 1
    exact List.take_append_drop nP margs
  -- the recursor's resolved application: the fold's left-hand side
  have hRvalEq : val' (f R) (Level.substFn (Level.substFn φ' lps us) lps
      (lps.map .param)) = val' R (Level.substFn φ' lps us) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 R]
  have hcRi : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (.const (f R) (lps.map .param)) =
      some (val' R (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    rw [hRvalEq]
  -- S8b: the index values — the walk residual's slice values are the
  -- resolved statement slots' values
  have hcbodyNF : cbody.hasFvar = false :=
    Expr.stripPis_body_hasFvar _ hC_strip hCw
  have hcbodyBnd : cbody.looseBVarsBounded (nP + cnF) = true := by
    have h0 := Expr.stripPis_body_bounded _ hC_strip hCb
    simpa using h0
  have hcbodyLPD : cbody.allLevelParamsDefined cvj.levelParams = true :=
    Expr.allLevelParamsDefined_stripPis_body _ hC_strip hCps
  have hstripCIsome := Expr.stripPis_instantiateLevelParams_isSome
    cvj.levelParams usj (nP + cnF) (e := cvj.type) (by rw [hC_strip]; rfl)
  obtain ⟨⟨bsI, bodyI⟩, hstripCI⟩ :=
    Option.isSome_iff_exists.mp hstripCIsome
  obtain ⟨hbodyIeq, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams usj _ hC_strip hstripCI
  have hrest2eq : rest₂ = Expr.instSeq argsC0 (nP + cnF - 1)
      (cbody.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨mid, hmid, bs', body', hstripMid, hbodyMid, -⟩ :=
      telescopeInst_stripPis (nP + cnF) argsC0 0 hlenC0
        (by rw [Nat.add_zero]; exact hstripCI)
    rw [TeleFitI.rest_eq hfitL2] at hmid
    obtain rfl : rest₂ = mid := Option.some.inj hmid
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripMid
    rw [hstripMid.2, hbodyMid, hbodyIeq]
    simp
  have hrest2Args : rest₂.getAppArgs =
      cbody.getAppArgs.map (fun e => Expr.instSeq argsC0 (nP + cnF - 1)
        (e.instantiateLevelParams cvj.levelParams usj)) := by
    rw [hrest2eq]
    calc (Expr.instSeq argsC0 (nP + cnF - 1)
          (cbody.instantiateLevelParams cvj.levelParams usj)).getAppArgs
        = (Expr.instSeq argsC0 (nP + cnF - 1)
            (Expr.mkAppN (cbody.instantiateLevelParams cvj.levelParams
              usj).getAppFn (cbody.instantiateLevelParams cvj.levelParams
              usj).getAppArgs)).getAppArgs := by
          rw [Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (Expr.instSeq argsC0 (nP + cnF - 1)
            (cbody.instantiateLevelParams cvj.levelParams usj).getAppFn)
            ((cbody.instantiateLevelParams cvj.levelParams
              usj).getAppArgs.map
              (Expr.instSeq argsC0 (nP + cnF - 1) ·))).getAppArgs := by
          rw [Expr.instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app argsC0 _ hfvC0
                (getAppFn_not_app _)),
            Expr.getAppArgs_instantiateLevelParams, List.map_map]
          simp [Function.comp]
  have hidxSp0 : InterpSpine val' env₁ φ' d₂ ρ₂
      ((cbody.getAppArgs.drop nP).map (fun e =>
        Expr.instSeq argsC0 (nP + cnF - 1)
          (e.instantiateLevelParams cvj.levelParams usj)))
      (args.drop (nP + 1 + nm)) := by
    have h0 := InterpSpine.of_mapM hidx
    rw [hrest2Args, ← List.map_drop] at h0
    exact h0
  have hPFfv0 : ∀ a ∈ argsR.take nP ++ argsC.drop nP,
      ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hshR' a (List.mem_of_mem_take ha)
    · exact hshC' a (List.mem_of_mem_drop ha)
  have hPFfv : ∀ a ∈ argsR.take nP ++ argsC.drop nP,
      ∃ i n ty, a = Expr.fvar i n ty := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hPFfv0 a ha
    exact ⟨i, n, _, rfl⟩
  have hPFlen : (argsR.take nP ++ argsC.drop nP).length = nP + cnF := by
    rw [List.length_append, hAlen, hClen2]
  have hPFinstid : (argsR.take nP ++ argsC.drop nP).map
      (·.instantiateLevelParams cvj.levelParams usj) =
      argsR.take nP ++ argsC.drop nP := by
    have h0 : (argsR.take nP ++ argsC.drop nP).map
        (·.instantiateLevelParams cvj.levelParams usj) =
        (argsR.take nP ++ argsC.drop nP).map id :=
      List.map_congr_left (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hPFfv0 a ha
        rfl)
    rw [h0, List.map_id]
  have hIA_C0 : InstArgs val' env₁ φ' d₂ ρ₂ argsC0 margs :=
    TeleFitI.toInstArgs hfitL2
  have hIA_PF : InstArgs val' env₁ φ' d₂ ρ₂
      (argsR.take nP ++ argsC.drop nP) margs :=
    InstArgs.of_fvars_ext hPFfv (TeleFitI.toInstArgs hfitC4)
  have hIdxSpine : InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      ((cbody.getAppArgs.drop nP).map fun e =>
        Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
          (e.renameConsts f))
      (args.drop (nP + 1 + nm)) := by
    have hconv : ∀ (l : List Expr) (vs0 : List V),
        (∀ x ∈ l, x ∈ cbody.getAppArgs) →
        InterpSpine val' env₁ φ' d₂ ρ₂
          (l.map (fun e => Expr.instSeq argsC0 (nP + cnF - 1)
            (e.instantiateLevelParams cvj.levelParams usj))) vs0 →
        InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
          (l.map (fun e => Expr.instSeq
            (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
            (e.renameConsts f))) vs0 := by
      intro l
      induction l with
      | nil =>
        intro vs0 _ hs
        match vs0, hs with
        | [], _ => trivial
      | cons x l ihl =>
        intro vs0 hmem hs
        match vs0, hs with
        | v :: vs0, ⟨hix, hrest⟩ =>
          refine ⟨?_, ihl vs0
            (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) hrest⟩
          have hxmem := hmem x List.mem_cons_self
          have hxNF : x.hasFvar = false :=
            hasFvar_getAppArgs hcbodyNF _ hxmem
          have hxBnd : x.looseBVarsBounded (nP + cnF) = true :=
            looseBVarsBounded_getAppArgs hcbodyBnd _ hxmem
          have hxLPD : x.allLevelParamsDefined cvj.levelParams = true :=
            Expr.allLevelParamsDefined_getAppArgs hcbodyLPD _ hxmem
          have hxINF : (x.instantiateLevelParams cvj.levelParams
              usj).hasFvar = false := by
            rw [hasFvar_instantiateLevelParams]
            exact hxNF
          have hxIBnd : (x.instantiateLevelParams cvj.levelParams
              usj).looseBVarsBounded (nP + cnF) = true := by
            rw [looseBVarsBounded_instantiateLevelParams]
            exact hxBnd
          have hswap := interp_instSeq_congr (cval := val') hIA_PF hIA_C0
            (WScoped.of_not_hasFvar hxINF (d := d₂)).fvarsBelow
            (by rw [hPFlen]; exact hxIBnd)
          rw [show (argsR.take nP ++ argsC.drop nP).length - 1 =
              nP + cnF - 1 from by rw [hPFlen],
            show argsC0.length - 1 = nP + cnF - 1 from by rw [hlenC0]]
            at hswap
          rw [← hswap] at hix
          rw [show Expr.instSeq (argsR.take nP ++ argsC.drop nP)
              (nP + cnF - 1) (x.instantiateLevelParams cvj.levelParams
                usj) =
              (Expr.instSeq (argsR.take nP ++ argsC.drop nP)
                (nP + cnF - 1) x).instantiateLevelParams cvj.levelParams
                usj from by
            rw [Expr.instSeq_instantiateLevelParams_fvars _ _ _ _ _ hPFfv,
              hPFinstid]] at hix
          rw [interp_instLevels hcvp] at hix
          rw [interp_params_ext hcvp hleveq _ _ _
            (Expr.allLevelParamsDefined_instSeq_fvars _ _
              (fun a ha => ⟨by
                obtain ⟨i, n, rfl⟩ := hPFfv0 a ha
                rfl, hPFfv a ha⟩)
              hxLPD)] at hix
          have hren : interpExpr V val' env₁ (Level.substFn φ' lps us)
              d₂ ρ₂ (Expr.instSeq (argsR.take nP ++ argsC.drop nP)
                (nP + cnF - 1) (x.renameConsts f)) =
              interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
                (Expr.instSeq (argsR.take nP ++ argsC.drop nP)
                  (nP + cnF - 1) x) := by
            rw [← interp_erasedEq (Expr.instSeq_renameConsts _ _
              (fun a ha => by
                obtain ⟨i, n, rfl⟩ := hPFfv0 a ha
                exact rfl)) d₂ ρ₂]
            exact interp_renameConsts hro _ d₂ ρ₂
          rw [hren]
          exact hix
    exact hconv (cbody.getAppArgs.drop nP) (args.drop (nP + 1 + nm))
      (fun x hx => List.mem_of_mem_drop hx) hidxSp0
  have hlhsVal : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (Expr.mkAppN (.const (f R) (lps.map .param))
        (((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take (nP + 1 + nm)
          ++
          ((cbody.getAppArgs.drop nP).map fun e =>
            Expr.instSeq (argsR.take nP ++ argsC.drop nP) (nP + cnF - 1)
              (e.renameConsts f))) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((argsR.take (nP + 1 + nm) ++ argsC.drop nP).take nP ++
            (argsR.take (nP + 1 + nm) ++ argsC.drop nP).drop
              (nP + 1 + nm))])) =
      some (SpineFold V (val' R (Level.substFn φ' lps us))
        (args ++ [tv])) := by
    rw [interp_mkAppN _ _ hcRi
      (InterpSpine.append (InterpSpine.append
        (InterpSpine.take (nP + 1 + nm) hAllSpine) hIdxSpine)
        (show InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
          [_] [tv] from ⟨hctorVal, trivial⟩))]
    congr 1
    rw [hVpre, List.take_append_drop]
  -- S8: destructure the equation's annotation chain and extract the
  -- value equality through the Eq collapse
  obtain ⟨-, hcomps, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hQA
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  -- identify the middle component with the fold's left-hand side
  have hvl : vl = SpineFold V (val' R (Level.substFn φ' lps us))
      (args ++ [tv]) := by
    rw [hlhsVal] at hil
    exact (Option.some.inj hil).symm
  -- the equality former's value
  have hveq : veq = eqVal V (Level.substFn (Level.substFn φ' lps us)
      [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  -- canonical memberships through the (never-collapsed) Eq value
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn (Level.substFn φ' lps us) [uN]
      [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  -- the interpreted equation is the equality truth value
  have hQeqv : Q = eqv vl vr := by
    rw [hfoldQ] at hQi
    rw [← Option.some.inj hQi, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn
        (Level.substFn φ' lps us) [uN] [ℓA])) [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn (Level.substFn φ' lps us) [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  -- the theorem's inhabitant collapses the equation
  have hveq_final : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- S9: the λ-tower fold on the rule's right-hand side
  have hlamRel : LamPiDomsRenEq f ((nP + (1 + nm)) + cnF) rhsA
      cvt.type := by
    have hstripR' : rhsA.stripLams ((nP + (1 + nm)) + cnF) =
        some (rbinders, rbody) := by
      rw [show (nP + (1 + nm)) + cnF = nP + 1 + nm + cnF from by omega]
      exact hstripR
    refine LamPiDomsRenEq.of_pointwise _ hstripR' hS_strip ?_
    intro i b₁ b₂ hb₁ hb₂
    have h2 : b₂.2.1 = b₁.2.1.renameConsts f := hsdoms i b₂ b₁ hb₂ hb₁
    show RenEq f b₁.2.1 b₂.2.1
    rw [h2]
    exact Expr.ErasedEq.rfl _
  have hargsRen : ∀ a ∈ argsR.take (nP + 1 + nm) ++ argsC.drop nP,
      RenEq f a a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
      exact RenEq.fvar_self
    · obtain ⟨i, n, rfl⟩ := hshC' a (List.mem_of_mem_drop ha)
      exact RenEq.fvar_self
  obtain ⟨restL, hlamFit⟩ := TeleFitI.toLamRen hro hstmtFit
    (by rw [hallLen]; exact hlamRel)
    (WScoped.of_not_hasFvar hrhsw (d := d₂)).fvarsBelow hargsRen
  have hArhs' : AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      rhsA :=
    AnnotOk.closed_invariant hrhsw d₂ ρ₂ (hArhs _)
  -- interpretation existence for the λ-tower's head
  obtain ⟨L, hLi⟩ : ∃ L, interpExpr V val' env₁ (Level.substFn φ' lps us)
      d₂ ρ₂ rhsA = some L := by
    obtain ⟨n₀, ty₀, b₀, m₀, heq⟩ :
        ∃ n₀ ty₀ b₀ m₀, rhsA = .lam n₀ ty₀ b₀ m₀ := by
      have hstripR' : rhsA.stripLams ((nP + nm + cnF) + 1) =
          some (rbinders, rbody) := by
        rw [show (nP + nm + cnF) + 1 = nP + 1 + nm + cnF from by omega]
        exact hstripR
      match rhsA, hstripR' with
      | .lam n₀ ty₀ b₀ m₀, _ => exact ⟨n₀, ty₀, b₀, m₀, rfl⟩
    subst heq
    have hA' := hArhs'
    simp only [AnnotOk] at hA'
    obtain ⟨-, ⟨cod, hcod⟩, -⟩ := hA'
    -- the domain interprets: it is the first binder of the fit
    obtain ⟨a₀, allrest, hallEq⟩ : ∃ a₀ allrest,
        argsR.take (nP + 1 + nm) ++ argsC.drop nP = a₀ :: allrest := by
      match h : argsR.take (nP + 1 + nm) ++ argsC.drop nP, hallLen with
      | a₀ :: allrest, _ => exact ⟨a₀, allrest, rfl⟩
      | [], hl => simp at hl; omega
    obtain ⟨v₀, vrest, hvEq⟩ : ∃ v₀ vrest,
        args.take (nP + 1 + nm) ++ margs.drop nP = v₀ :: vrest := by
      match h : args.take (nP + 1 + nm) ++ margs.drop nP with
      | v₀ :: vrest => exact ⟨v₀, vrest, rfl⟩
      | [] =>
        have h0 : (args.take (nP + 1 + nm) ++
            margs.drop nP).length = 0 := by rw [h]; rfl
        rw [List.length_append, hVlen] at h0
        omega
    have hlf := hlamFit
    rw [hallEq, hvEq] at hlf
    cases hlf with
    | cons hity hiarg hx hfb hwa hba hAa hsub =>
      simp only [interpExpr, hcod, hity]
      exact ⟨_, rfl⟩
  obtain ⟨B, hBi, hfoldB, hchainB⟩ := TeleFitLam.fold hlamFit hArhs' hLi
  -- the fold's residual is the instantiated rule body
  have hlamRest : telescopeInstLam rhsA
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP) =
      some (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
        ((nP + (1 + nm)) + cnF - 1) rbody) := by
    have h1 := telescopeInstLam_body ((nP + (1 + nm)) + cnF)
      (argsR.take (nP + 1 + nm) ++ argsC.drop nP) hallLen
      (by rw [show (nP + (1 + nm)) + cnF = nP + 1 + nm + cnF from by
        omega]; exact hstripR)
    exact h1
  have hrest_id2 := TeleFitLam.rest_eq hlamFit
  rw [hlamRest] at hrest_id2
  obtain rfl := Option.some.inj hrest_id2
  -- identify the equation's right value with the fold's result
  have hvrB : vr = B := by
    have hren1 : Expr.ErasedEq
        ((Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) rbody).renameConsts f)
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) (rbody.renameConsts f)) := by
      refine Expr.instSeq_renameConsts _ _ ?_
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, n, rfl⟩ := hshR' a (List.mem_of_mem_take ha)
        exact Expr.ErasedEq.rfl _
      · obtain ⟨i, n, rfl⟩ := hshC' a (List.mem_of_mem_drop ha)
        exact Expr.ErasedEq.rfl _
    have h2 : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
        (Expr.instSeq (argsR.take (nP + 1 + nm) ++ argsC.drop nP)
          ((nP + (1 + nm)) + cnF - 1) (rbody.renameConsts f)) =
        some B := by
      rw [← interp_erasedEq hren1 d₂ ρ₂,
        interp_renameConsts hro _ d₂ ρ₂]
      exact hBi
    rw [h2] at hir
    exact Option.some.inj hir |>.symm
  -- S10: assemble the conclusion
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [show interpClosed V val' env₁ (Level.substFn φ' lps us) rhsA =
        interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ rhsA from
      (interp_closed_invariant hrhsw d₂ ρ₂).symm]
    exact hLi
  · rw [← hvl, hveq_final, hvrB]
    exact hfoldB.symm
  · exact hchainB

end Setlec
