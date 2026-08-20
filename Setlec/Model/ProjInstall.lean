import Setlec.Model.IndInstall

/-!
# Fold facts for an installed projection function

`proj_rule_fold` derives the single rule's `RecRulesOk` fold
obligation for a projection function (a degenerate recursor installed
against the structure model's `proj_i` definition) from the checked
`T._model.proj_i.iota` theorem.  The pipeline mirrors
`modeled_rule_fold`, radically simplified: the statement's telescope
is the constructor's telescope (renamed), so the constructor fit
transfers onto it in one step, and the equality's sides are the
projection redex and the projected field.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {φ' : Name → Nat}

open SetTheory Expr

set_option maxHeartbeats 1600000 in
theorem proj_rule_fold
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name}
    (hro : RenameOk val' env₁ f)
    (hcvp : ConstValParams val' env₁)
    {P : Name} {lps : List Name} {nP nF i : Nat}
    (hi : i < nF)
    {ctor : Name} {cvj : ConstantVal}
    (hfj : env₁.find? ctor = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env₁.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = lps)
    (hClps : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
      val' ctor ψ₁ = val' ctor ψ₂)
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    {thmName : Name} {cvt : ConstantVal}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val' env₁ ψ'' cvt.type = some Pv ∧
      val' thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    {rhsA rbody cbody sbody tySlot : Expr}
    {rbinders cbinders sbinders : List (Name × Expr × BinderMeta)}
    {ℓA : Level}
    (hstripR : rhsA.stripLams (nP + nF) = some (rbinders, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    (hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = b'.2.1)
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f P) (lps.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) rhsA)
    (hCw : cvj.type.hasFvar = false)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    {us usj : List Level} {args margs : List V} {tv : V}
    (hlena : args.length = nP)
    (hlenm : margs.length = nP + nF)
    (htv : tv = SpineFold V (val' ctor
      (Level.substFn φ' cvj.levelParams usj)) margs)
    (hparameq : margs.take nP = (args ++ [tv]).take nP)
    (hleveq : ∀ p ∈ cvj.levelParams,
      Level.substFn φ' cvj.levelParams usj p =
      Level.substFn φ' lps us p)
    {d₁ : Nat} {ρ₁ : Nat → V} {d₂ : Nat} {ρ₂ : Nat → V} {rest₂ : Expr}
    (hfit2 : TeleFit V val' env₁ φ' d₁ ρ₁
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs
      d₂ ρ₂ rest₂) :
    ∃ Rv, interpClosed V val' env₁ (Level.substFn φ' lps us) rhsA =
        some Rv ∧
      SpineFold V (val' P (Level.substFn φ' lps us)) (args ++ [tv]) =
        SpineFold V Rv (args.take nP ++ margs.drop nP) ∧
      ChainSlots V Rv (args.take nP ++ margs.drop nP) := by
  -- the argument lists coincide with the constructor's value spine
  have hargsEq : args = margs.take nP := by
    rw [hparameq, List.take_append_of_le_length (by omega), ← hlena,
      List.take_length]
  have hvalsEq : args.take nP ++ margs.drop nP = margs := by
    rw [hargsEq, List.take_take, Nat.min_self, List.take_append_drop]
  -- the sanitized raw fit for the constructor telescope at ψ
  have hCwI : ∀ D, WScoped D
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := fun D =>
    WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hCw)
  obtain ⟨hd₂, hagr₂, argsC0, restC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfit2 (hCwI d₁)
  have hlenC0 : argsC0.length = nP + nF := by
    have h1 := TeleFitI.vs_length hfitL2
    simp [hlenm] at h1
    omega
  obtain ⟨restC1, hfitS2⟩ := TeleFitI.sanitize hfitL2
    (by rw [hlenC0]
        exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
          (by rw [hC_strip]; rfl)) hfvC0
  have hshC : ∀ a ∈ argsC0.map sanitizeArg, ∃ j n,
      a = Expr.fvar j n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨j, n, rfl⟩
  obtain ⟨restC2', hfitRaw2⟩ := TeleFitI.instLev_down hcvp hfitS2 hshC
    (WScoped.of_not_hasFvar hCw (d := d₂)).fvarsBelow
  obtain ⟨restC3, hfitRaw2'⟩ := TeleFitI.params_ext hleveq hcvp hfitRaw2
    hCps hshC
  obtain ⟨argsC, hargsCdef⟩ : ∃ x, x = argsC0.map sanitizeArg := ⟨_, rfl⟩
  rw [← hargsCdef] at hfitRaw2' hshC
  have hlenC : argsC.length = nP + nF := by
    rw [hargsCdef]; simp [hlenC0]
  have hshC' : ∀ a ∈ argsC, ∃ j n, a = Expr.fvar j n (.sort .zero) := hshC
  -- the statement telescope is the constructor's, renamed
  have hpiRel : PiDomsRenEq f (nP + nF) cvj.type cvt.type := by
    refine PiDomsRenEq.of_pointwise (nP + nF) hC_strip hS_strip ?_
    intro k b₁ b₂ hb₁ hb₂
    have h2 : b₂.2.1 = b₁.2.1.renameConsts f := hsdoms k b₂ b₁ hb₂ hb₁
    show RenEq f b₁.2.1 b₂.2.1
    rw [h2]
    exact Expr.ErasedEq.rfl _
  have hargsSelf : ArgsRel (fun a₁ a₂ => RenEq f a₁ a₂ ∧ WScoped d₂ a₂ ∧
      a₂.looseBVarsBounded 0 = true ∧
      AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ a₂)
      argsC argsC := by
    refine ArgsRel.of_pointwise rfl ?_
    intro k a₁ a₂ ha₁ ha₂
    obtain rfl : a₁ = a₂ := by
      rw [ha₁] at ha₂
      exact Option.some.inj ha₂
    obtain ⟨j, n, rfl⟩ := hshC' a₁ (List.mem_of_getElem? ha₁)
    obtain ⟨hw, hb, hA⟩ := TeleFitI.arg_wf hfitRaw2' k _ ha₁
    exact ⟨RenEq.fvar_self, hw, hb, hA⟩
  have hSfb : Expr.fvarsBelow d₂ cvt.type :=
    (WScoped.of_not_hasFvar hSw).fvarsBelow
  obtain ⟨midSE, hstmtFit⟩ := TeleFitI.ren_transfer hro hfitRaw2'
    (by rw [hlenC]; exact hpiRel) hSfb hargsSelf
  -- eliminate the theorem's inhabitant through the statement fit
  obtain ⟨Pv, hPi, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPi' : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      cvt.type = some Pv := by
    rw [interp_closed_invariant hSw d₂ ρ₂]
    exact hPi
  have hSA : AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      cvt.type :=
    AnnotOk.closed_invariant hSw d₂ ρ₂ (hthm_annot _)
  obtain ⟨Q, hQi, hQmem, hQA⟩ := TeleFitI.elim hstmtFit hSA hPi' hPmem
  -- the elimination residual is the instantiated equation body
  obtain ⟨restT, hrestT, bs0, body0, hstrip0, hbody0, -⟩ :=
    telescopeInst_stripPis (nP + nF) argsC 0 hlenC hS_strip
  have hrest_id : restT = body0 := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip0
    exact hstrip0.2
  have hrestF : telescopeInst cvt.type argsC =
      some (Expr.instSeq argsC (nP + nF - 1) sbody) := by
    rw [hrestT, hrest_id, hbody0,
      show nP + nF + 0 - 1 = nP + nF - 1 from by omega]
  have hfitrest := TeleFitI.rest_eq hstmtFit
  rw [hrestF] at hfitrest
  obtain rfl := Option.some.inj hfitrest
  -- resolve the equation's components along the argument spine
  have hbounded : ∀ a ∈ argsC, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshC' a ha
    rfl
  have hresolve : ∀ (k : Nat), k < nP + nF →
      argsC[k]? = some (Expr.instSeq argsC (nP + nF - 1)
        (.bvar (nP + nF - 1 - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar argsC (nP + nF - 1)
      (nP + nF - 1 - k) hbounded (by omega) (by rw [hlenC]; omega)
    rwa [show nP + nF - 1 - (nP + nF - 1 - k) = k from by omega] at h1
  have hres_p : (((List.range nP).map fun k =>
        Expr.bvar (nP + nF - 1 - k))).map
        (Expr.instSeq argsC (nP + nF - 1) ·) = argsC.take nP := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_take_of_lt hk, List.getElem?_map,
        List.getElem?_map, List.getElem?_range hk,
        hresolve k (by omega)]
      rfl
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_take_eq_none hk]
      rfl
  have hres_x : (((List.range nF).map fun k =>
        Expr.bvar (nF - 1 - k))).map
        (Expr.instSeq argsC (nP + nF - 1) ·) = argsC.drop nP := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nF with hk | hk
    · rw [List.getElem?_drop, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hk,
        show argsC[nP + k]? = some (Expr.instSeq argsC (nP + nF - 1)
          (.bvar (nP + nF - 1 - (nP + k)))) from
          hresolve (nP + k) (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      congr 2
      omega
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by
          rw [List.length_drop, hlenC]
          omega)]
      rfl
  have hctorRes : Expr.instSeq argsC (nP + nF - 1)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (argsC.take nP ++ argsC.drop nP) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p
      | exact hres_x
  have hlhsRes : Expr.instSeq argsC (nP + nF - 1)
      (Expr.mkAppN (.const (f P) (lps.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])) =
      Expr.mkAppN (.const (f P) (lps.map .param))
        (argsC.take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (argsC.take nP ++ argsC.drop nP)]) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p
      | (simp only [List.map_cons, List.map_nil]; rw [hctorRes])
  have hresidual : Expr.instSeq argsC (nP + nF - 1) sbody =
      Expr.mkAppN (.const eqName [ℓA])
        [Expr.instSeq argsC (nP + nF - 1) tySlot,
         Expr.mkAppN (.const (f P) (lps.map .param))
          (argsC.take nP ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             (argsC.take nP ++ argsC.drop nP)]),
         Expr.instSeq argsC (nP + nF - 1) (.bvar (nF - 1 - i))] := by
    rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    simp only [List.map_cons, List.map_nil]
    rw [hlhsRes]
  rw [hresidual] at hQi hQA
  -- compute the components' values
  have hAllSpine : InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      argsC margs :=
    TeleFitI.toInterpSpine hstmtFit
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
  have hctorVal : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (argsC.take nP ++ argsC.drop nP)) = some tv := by
    rw [interp_mkAppN _ _ hcCi
      (InterpSpine.append (InterpSpine.take nP hAllSpine)
        (InterpSpine.drop nP hAllSpine))]
    congr 1
    rw [htv]
    congr 1
    exact List.take_append_drop nP margs
  have hPvalEq : val' (f P) (Level.substFn (Level.substFn φ' lps us) lps
      (lps.map .param)) = val' P (Level.substFn φ' lps us) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 P]
  have hcPi : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (.const (f P) (lps.map .param)) =
      some (val' P (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfPm]
    rw [if_pos (by rw [hPmlps]; simp)]
    rw [show cimP.toConstantVal.levelParams = lps from hPmlps]
    rw [hPvalEq]
  have hlhsVal : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (Expr.mkAppN (.const (f P) (lps.map .param))
        (argsC.take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (argsC.take nP ++ argsC.drop nP)])) =
      some (SpineFold V (val' P (Level.substFn φ' lps us))
        (args ++ [tv])) := by
    rw [interp_mkAppN _ _ hcPi
      (InterpSpine.append (InterpSpine.take nP hAllSpine)
        (show InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
          [_] [tv] from ⟨hctorVal, trivial⟩))]
    congr 1
    rw [hargsEq]
  -- destructure the equation's chain and extract the value equality
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
  have hvl : vl = SpineFold V (val' P (Level.substFn φ' lps us))
      (args ++ [tv]) := by
    rw [hlhsVal] at hil
    exact (Option.some.inj hil).symm
  have hveq : veq = eqVal V (Level.substFn (Level.substFn φ' lps us)
      [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
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
  have hveq_final : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- the λ-tower fold on the rule's right-hand side
  have hlamRel : LamPiDomsRenEq f (nP + nF) rhsA cvt.type := by
    refine LamPiDomsRenEq.of_pointwise _ hstripR hS_strip ?_
    intro k b₁ b₂ hb₁ hb₂
    obtain ⟨cb, hcb⟩ : ∃ cb, cbinders[k]? = some cb := by
      have hclen : cbinders.length = nP + nF :=
        Expr.stripPis_length _ hC_strip
      have hslen : sbinders.length = nP + nF :=
        Expr.stripPis_length _ hS_strip
      have hk : k < nP + nF := by
        rcases Nat.lt_or_ge k (nP + nF) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hb₂
          exact nomatch hb₂
      exact ⟨cbinders[k]'(by omega), List.getElem?_eq_getElem _⟩
    have h1 : b₁.2.1 = cb.2.1 := hdoms k b₁ cb hb₁ hcb
    have h2 : b₂.2.1 = cb.2.1.renameConsts f := hsdoms k b₂ cb hb₂ hcb
    show RenEq f b₁.2.1 b₂.2.1
    rw [h1, h2]
    exact Expr.ErasedEq.rfl _
  have hargsRen : ∀ a ∈ argsC, RenEq f a a := by
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshC' a ha
    exact RenEq.fvar_self
  obtain ⟨restL, hlamFit⟩ := TeleFitI.toLamRen hro hstmtFit
    (by rw [hlenC]; exact hlamRel)
    (WScoped.of_not_hasFvar hrhsw (d := d₂)).fvarsBelow hargsRen
  have hArhs' : AnnotOk V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      rhsA :=
    AnnotOk.closed_invariant hrhsw d₂ ρ₂ (hArhs _)
  obtain ⟨L, hLi⟩ : ∃ L, interpExpr V val' env₁ (Level.substFn φ' lps us)
      d₂ ρ₂ rhsA = some L := by
    obtain ⟨n₀, ty₀, b₀, m₀, heq⟩ :
        ∃ n₀ ty₀ b₀ m₀, rhsA = .lam n₀ ty₀ b₀ m₀ := by
      have hstripR' : rhsA.stripLams ((nP + nF - 1) + 1) =
          some (rbinders, rbody) := by
        rw [show (nP + nF - 1) + 1 = nP + nF from by omega]
        exact hstripR
      match rhsA, hstripR' with
      | .lam n₀ ty₀ b₀ m₀, _ => exact ⟨n₀, ty₀, b₀, m₀, rfl⟩
    subst heq
    have hA' := hArhs'
    simp only [AnnotOk] at hA'
    obtain ⟨-, ⟨cod, hcod⟩, -⟩ := hA'
    obtain ⟨a₀, allrest, hallEq⟩ : ∃ a₀ allrest,
        argsC = a₀ :: allrest := by
      match h : argsC, hlenC with
      | a₀ :: allrest, _ => exact ⟨a₀, allrest, rfl⟩
      | [], hl => simp at hl; omega
    obtain ⟨v₀, vrest, hvEq⟩ : ∃ v₀ vrest, margs = v₀ :: vrest := by
      match h : margs with
      | v₀ :: vrest => exact ⟨v₀, vrest, rfl⟩
      | [] =>
        simp at hlenm
        omega
    have hlf := hlamFit
    rw [hallEq, hvEq] at hlf
    cases hlf with
    | cons hity hiarg hx hfb hwa hba hAa hsub =>
      simp only [interpExpr, hcod, hity]
      exact ⟨_, rfl⟩
  obtain ⟨B, hBi, hfoldB, hchainB⟩ := TeleFitLam.fold hlamFit hArhs' hLi
  have hlamRest : telescopeInstLam rhsA argsC =
      some (Expr.instSeq argsC (nP + nF - 1) rbody) := by
    have h1 := telescopeInstLam_body (nP + nF) argsC hlenC hstripR
    exact h1
  have hrest_id2 := TeleFitLam.rest_eq hlamFit
  rw [hlamRest] at hrest_id2
  obtain rfl := Option.some.inj hrest_id2
  have hvrB : vr = B := by
    rw [hrbody] at hBi
    rw [hBi] at hir
    exact Option.some.inj hir |>.symm
  have hargsTake : args.take nP = args := by
    rw [← hlena]
    exact List.take_length
  rw [hargsTake]
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [show interpClosed V val' env₁ (Level.substFn φ' lps us) rhsA =
        interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂ rhsA from
      (interp_closed_invariant hrhsw d₂ ρ₂).symm]
    exact hLi
  · rw [← hvl, hveq_final, hvrB,
      show args ++ margs.drop nP = margs from by
        rw [hargsEq, List.take_append_drop]]
    exact hfoldB.symm
  · rw [show args ++ margs.drop nP = margs from by
      rw [hargsEq, List.take_append_drop]]
    exact hchainB

end Setlec
