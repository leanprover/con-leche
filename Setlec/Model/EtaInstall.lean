import Setlec.Model.IndInstall

/-!
# The eta law of a modeled structure, from its checked `_model.eta`

`eta_rule_fold` derives the semantic eta law — every member of the
interpreted structure type is the constructor-model value applied to
its projection-model values — from the checked `T._model.eta` theorem.
The pipeline mirrors `proj_rule_fold`: the use site's fit of the
public type former's parameter telescope transfers onto the statement
telescope (whose domains are the parameters', renamed), the subject
binder is fitted with the member itself, the theorem's inhabitant is
eliminated through the statement, and the equality collapses to the
value identity.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {φ' : Name → Nat}

open SetTheory Expr

set_option maxHeartbeats 3200000 in
theorem eta_rule_fold
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name}
    (hro : RenameOk val' env₁ f)
    (hcvp : ConstValParams val' env₁)
    {T ctor : Name} {lps ctorLps : List Name} {nP nF : Nat}
    {cvTty : Expr}
    -- model-side stored constants (for the pinned constants' interps)
    {cimT : ConstantInfo}
    (hfTm : env₁.find? (T.str "_model") = some cimT)
    (hTmlps : cimT.toConstantVal.levelParams = lps)
    {cimC : ConstantInfo}
    (hfCm : env₁.find? (ctor.str "_model") = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = ctorLps)
    (hprojf : ∀ j, j < nF → ∃ cimj : ConstantInfo,
      env₁.find? (projModelName T j) = some cimj ∧
      cimj.toConstantVal.levelParams = lps)
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    -- the checked eta theorem
    {thmName : Name} {cvt : ConstantVal}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val' env₁ ψ'' cvt.type = some Pv ∧
      val' thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    -- statement pins
    {sbinders : List (Name × Expr × BinderMeta)}
    {sbody tySlot : Expr} {ℓA : Level}
    (hS_strip : cvt.type.stripPis (nP + 1) = some (sbinders, sbody))
    {tbinders : List (Name × Expr × BinderMeta)} {tbody : Expr}
    (hT_strip : cvTty.stripPis nP = some (tbinders, tbody))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbinders[k]? = some b' →
      RenEq f b'.2.1 b.2.1)
    (hxdom : ∃ nx mx, sbinders[nP]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx))
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot, .bvar 0,
       Expr.mkAppN (.const (ctor.str "_model") (ctorLps.map .param))
        (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
         (List.range nF).map fun j => Expr.mkAppN
           (.const (projModelName T j) (lps.map .param))
           (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
            [Expr.bvar 0]))])
    -- wellformedness of the public type former's type
    (hTw : cvTty.hasFvar = false)
    -- the use-site data
    {us : List Level} {ps : List V} {x : V}
    (hlen : ps.length = nP)
    (hx : x ∈ˢ SpineFold V (val' (T.str "_model")
      (Level.substFn φ' lps us)) ps)
    {d₁ : Nat} {ρ₁ : Nat → V} {d₂ : Nat} {ρ₂ : Nat → V} {rest : Expr}
    (hfitT : TeleFit V val' env₁ φ' d₁ ρ₁
      (cvTty.instantiateLevelParams lps us) ps d₂ ρ₂ rest) :
    x = SpineFold V (val' (ctor.str "_model") (Level.substFn φ' lps us))
      (ps ++ (List.range nF).map fun j =>
        SpineFold V (val' (projModelName T j) (Level.substFn φ' lps us))
          (ps ++ [x])) := by
  -- fit the parameter values through the raw public type former
  have hTwI : ∀ D, WScoped D (cvTty.instantiateLevelParams lps us) :=
    fun D => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hTw)
  obtain ⟨hd₂, hagr₂, argsC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfitT (hTwI d₁)
  have hlenC0 : argsC0.length = nP := by
    have h1 := TeleFitI.vs_length hfitL2
    simp [hlen] at h1
    omega
  obtain ⟨restC1, hfitS2⟩ := TeleFitI.sanitize hfitL2
    (by rw [hlenC0]
        exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
          (by rw [hT_strip]; rfl)) hfvC0
  have hshC : ∀ a ∈ argsC0.map sanitizeArg, ∃ j n,
      a = Expr.fvar j n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨j, n, rfl⟩
  obtain ⟨restC2', hfitRaw⟩ := TeleFitI.instLev_down hcvp hfitS2 hshC
    (WScoped.of_not_hasFvar hTw (d := d₂)).fvarsBelow
  obtain ⟨argsC, hargsCdef⟩ : ∃ a, a = argsC0.map sanitizeArg := ⟨_, rfl⟩
  rw [← hargsCdef] at hfitRaw hshC
  have hlenC : argsC.length = nP := by
    rw [hargsCdef]; simp [hlenC0]
  have hshC' : ∀ a ∈ argsC, ∃ j n, a = Expr.fvar j n (.sort .zero) := hshC
  -- transfer onto the statement's parameter prefix
  obtain ⟨nx, mx, hxdom'⟩ := hxdom
  have hslen : sbinders.length = nP + 1 := Expr.stripPis_length _ hS_strip
  have htlen : tbinders.length = nP := Expr.stripPis_length _ hT_strip
  obtain ⟨sbodyN, hS_stripP⟩ := stripPis_prefix nP 1 hS_strip
  have hpiRel : PiDomsRenEq f nP cvTty cvt.type := by
    refine PiDomsRenEq.of_pointwise nP hT_strip hS_stripP ?_
    intro k b₁ b₂ hb₁ hb₂
    have hk : k < nP := by
      rcases Nat.lt_or_ge k nP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hb₁
        exact nomatch hb₁
    have hb₂' : sbinders[k]? = some b₂ := by
      rw [← List.getElem?_take_of_lt hk]
      exact hb₂
    exact hsdoms k b₂ b₁ hk hb₂' hb₁
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
    obtain ⟨hw, hb, hA⟩ := TeleFitI.arg_wf hfitRaw k _ ha₁
    exact ⟨RenEq.fvar_self, hw, hb, hA⟩
  have hSfb : Expr.fvarsBelow d₂ cvt.type :=
    (WScoped.of_not_hasFvar hSw).fvarsBelow
  obtain ⟨midS, hstmtFitP⟩ := TeleFitI.ren_transfer hro hfitRaw
    (by rw [hlenC]; exact hpiRel) hSfb hargsSelf
  -- the residual is the subject binder over the instantiated model type
  obtain ⟨mid2, hmid2, bs', body', hstrip1, hbody', hbind'⟩ :=
    telescopeInst_stripPis nP argsC 1 hlenC hS_strip
  obtain rfl : midS = mid2 := by
    have h1 := TeleFitI.rest_eq hstmtFitP
    rw [hmid2] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨nb, domb, bodyb, mb, rfl⟩ : ∃ nb domb bodyb mb,
      midS = .forallE nb domb bodyb mb := by
    match midS, hstrip1 with
    | .forallE nb domb bodyb mb, _ => exact ⟨nb, domb, bodyb, mb, rfl⟩
  simp only [Expr.stripPis, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hstrip1
  obtain ⟨rfl, rfl⟩ := hstrip1
  have hdombEq : domb = Expr.instSeq argsC (nP + 0 - 1)
      (Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))) := by
    have h1 := hbind' 0 _ _ (by simpa using hxdom') (by rfl)
    exact h1
  -- resolve the subject domain along the parameter arguments
  have hbounded : ∀ a ∈ argsC, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshC' a ha
    rfl
  have hresolveP : ∀ (k : Nat), k < nP →
      argsC[k]? = some (Expr.instSeq argsC (nP - 1)
        (.bvar (nP - 1 - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar argsC (nP - 1)
      (nP - 1 - k) hbounded (by omega) (by rw [hlenC]; omega)
    rwa [show nP - 1 - (nP - 1 - k) = k from by omega] at h1
  have hres_pP : (((List.range nP).map fun k =>
        Expr.bvar (nP - 1 - k))).map
        (Expr.instSeq argsC (nP - 1) ·) = argsC := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hk]
      simp only [Option.map_some]
      exact (hresolveP k hk).symm
    · rw [List.getElem?_map, List.getElem?_map]
      rw [List.getElem?_eq_none (l := List.range nP) (by simp; omega)]
      rw [List.getElem?_eq_none (l := argsC) (by rw [hlenC]; omega)]
      all_goals rfl
  have hdomRes : domb =
      Expr.mkAppN (.const (T.str "_model") (lps.map .param)) argsC := by
    rw [hdombEq, show nP + 0 - 1 = nP - 1 from by omega,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    all_goals congr 1
    all_goals exact hres_pP
  -- interpret the subject domain: the model type at the parameters
  have hAllSpineP : InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      argsC ps :=
    TeleFitI.toInterpSpine hstmtFitP
  have hTvalEq : val' (T.str "_model") (Level.substFn
      (Level.substFn φ' lps us) lps (lps.map .param)) =
      val' (T.str "_model") (Level.substFn φ' lps us) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1]
  have hcTi : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (.const (T.str "_model") (lps.map .param)) =
      some (val' (T.str "_model") (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfTm]
    rw [if_pos (by rw [hTmlps]; simp)]
    rw [show cimT.toConstantVal.levelParams = lps from hTmlps]
    rw [hTvalEq]
  have hdomI : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      domb = some (SpineFold V
        (val' (T.str "_model") (Level.substFn φ' lps us)) ps) := by
    rw [hdomRes]
    exact interp_mkAppN _ _ hcTi hAllSpineP
  -- extend the fit with the subject itself, one fresh level up
  obtain ⟨ρ₃, hρ₃⟩ : ∃ ρ₃, ρ₃ = updV V ρ₂ d₂ x := ⟨_, rfl⟩
  have hρagree : ∀ i, i < d₂ → ρ₃ i = ρ₂ i := by
    intro i hi
    rw [hρ₃]
    simp [updV, Nat.ne_of_lt hi]
  have hfitLift : TeleFitI V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ cvt.type argsC ps
      (.forallE nb domb bodyb mb) :=
    TeleFitI.lift hstmtFitP (WScoped.of_not_hasFvar hSw)
      (Nat.le_succ d₂) hρagree
  obtain ⟨xArg, hxArg⟩ : ∃ a, a = Expr.fvar d₂ nb (.sort .zero) :=
    ⟨_, rfl⟩
  have hxItp : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ xArg = some x := by
    rw [hxArg, hρ₃]
    simp [interpExpr, updV]
  have hdomI' : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ domb = some (SpineFold V
        (val' (T.str "_model") (Level.substFn φ' lps us)) ps) := by
    have hwdom : WScoped d₂ domb := by
      rw [hdomRes]
      refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      · intro a ha
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
        obtain ⟨hw, -, -⟩ := TeleFitI.arg_wf hstmtFitP k _ hk
        exact hw
    rw [interp_lift hwdom (d₂ + 1) (Nat.le_succ d₂) ρ₂ ρ₃
      (fun i hi => hρagree i hi)]
    exact hdomI
  have hxfit : TeleFitI V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ (.forallE nb domb bodyb mb) [xArg] [x]
      (bodyb.instantiate1 xArg) := by
    refine TeleFitI.cons hdomI' hxItp hx ?_ ?_ ?_ ?_ TeleFitI.nil
    · have hres_fb : Expr.fvarsBelow d₂
          (Expr.forallE nb domb bodyb mb) := by
        refine telescopeInst_fvarsBelow argsC
          (WScoped.of_not_hasFvar hSw).fvarsBelow ?_ hmid2
        intro a ha
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
        obtain ⟨hw, -, -⟩ := TeleFitI.arg_wf hstmtFitP k _ hk
        exact hw.fvarsBelow
      have hb2 : Expr.fvarsBelow d₂ bodyb := by
        have := hres_fb
        simp only [Expr.fvarsBelow] at this
        exact this.2
      exact fvarsBelow_mono (Nat.le_succ d₂) hb2
    · rw [hxArg]
      simp only [WScoped]
      exact ⟨Nat.lt_succ_self d₂, trivial⟩
    · rw [hxArg]; rfl
    · rw [hxArg]; simp [AnnotOk]
  have hfitFull := TeleFitI.append hfitLift hxfit
  -- eliminate the theorem's inhabitant through the extended fit
  obtain ⟨Pv, hPi, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPi' : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ cvt.type = some Pv := by
    rw [interp_closed_invariant hSw (d₂ + 1) ρ₃]
    exact hPi
  have hSA : AnnotOk V val' env₁ (Level.substFn φ' lps us) (d₂ + 1) ρ₃
      cvt.type :=
    AnnotOk.closed_invariant hSw (d₂ + 1) ρ₃ (hthm_annot _)
  obtain ⟨Q, hQi, hQmem, hQA⟩ := TeleFitI.elim hfitFull hSA hPi' hPmem
  -- identify the residual with the instantiated equation body
  have hlen' : (argsC ++ [xArg]).length = nP + 1 := by
    simp [hlenC]
  obtain ⟨midF, hmidF, bsF, bodyF, hstripF, hbodyF, -⟩ :=
    telescopeInst_stripPis (nP + 1) (argsC ++ [xArg]) 0 hlen'
      (by rw [show nP + 1 + 0 = nP + 1 from rfl]; exact hS_strip)
  have hmidF_id : midF = bodyF := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripF
    exact hstripF.2
  have hresidEq : bodyb.instantiate1 xArg =
      Expr.instSeq (argsC ++ [xArg]) (nP + 1 + 0 - 1) sbody := by
    have h1 := TeleFitI.rest_eq hfitFull
    rw [hmidF] at h1
    rw [← hbodyF, ← hmidF_id]
    exact (Option.some.inj h1).symm
  -- resolve the equation's components along the extended spine
  have hbounded' : ∀ a ∈ argsC ++ [xArg], a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hbounded a h
    · rw [List.mem_singleton.mp h, hxArg]
      rfl
  have hresolve' : ∀ (k : Nat), k < nP + 1 →
      (argsC ++ [xArg])[k]? = some (Expr.instSeq (argsC ++ [xArg]) nP
        (.bvar (nP - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar (argsC ++ [xArg]) nP (nP - k) hbounded'
      (by omega) (by simp [hlenC]; omega)
    rwa [show nP - (nP - k) = k from by omega] at h1
  have hres_p' : (((List.range nP).map fun k =>
        Expr.bvar (nP - k))).map
        (Expr.instSeq (argsC ++ [xArg]) nP ·) = argsC := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hk]
      simp only [Option.map_some]
      have h1 := (hresolve' k (by omega)).symm
      rw [List.getElem?_append_left (by rw [hlenC]; omega)] at h1
      exact h1
    · rw [List.getElem?_map, List.getElem?_map]
      rw [List.getElem?_eq_none (l := List.range nP) (by simp; omega)]
      rw [List.getElem?_eq_none (l := argsC) (by rw [hlenC]; omega)]
      all_goals rfl
  have hres_x' : Expr.instSeq (argsC ++ [xArg]) nP (.bvar 0) = xArg := by
    have h1 := hresolve' nP (by omega)
    rw [show nP - nP = 0 from by omega] at h1
    have h2 : (argsC ++ [xArg])[nP]? = some xArg := by
      rw [List.getElem?_append_right (by rw [hlenC]; omega)]
      simp [hlenC]
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hrhsRes : Expr.instSeq (argsC ++ [xArg]) nP
      (Expr.mkAppN (.const (ctor.str "_model") (ctorLps.map .param))
        (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
         (List.range nF).map fun j => Expr.mkAppN
           (.const (projModelName T j) (lps.map .param))
           (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
            [Expr.bvar 0]))) =
      Expr.mkAppN (.const (ctor.str "_model") (ctorLps.map .param))
        (argsC ++ (List.range nF).map fun j => Expr.mkAppN
          (.const (projModelName T j) (lps.map .param))
          (argsC ++ [xArg])) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p'
      | (refine List.ext_getElem? ?_
         intro j
         rcases Nat.lt_or_ge j nF with hj | hj
         · rw [List.getElem?_map, List.getElem?_map, List.getElem?_map,
             List.getElem?_range hj]
           simp only [Option.map_some, Option.some.injEq]
           rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
           congr 1
           rw [List.map_append]
           congr 1
           all_goals first
             | exact hres_p'
             | (simp only [List.map_cons, List.map_nil]
                rw [hres_x'])
         · rw [List.getElem?_map, List.getElem?_map]
           rw [List.getElem?_eq_none (l := List.range nF)
             (by simp; omega)]
           rw [List.getElem?_eq_none
             (l := (List.range nF).map _) (by simp; omega)]
           all_goals rfl)
  have hresidual : Expr.instSeq (argsC ++ [xArg]) nP sbody =
      Expr.mkAppN (.const eqName [ℓA])
        [Expr.instSeq (argsC ++ [xArg]) nP tySlot,
         xArg,
         Expr.mkAppN (.const (ctor.str "_model") (ctorLps.map .param))
          (argsC ++ (List.range nF).map fun j => Expr.mkAppN
            (.const (projModelName T j) (lps.map .param))
            (argsC ++ [xArg]))] := by
    rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    simp only [List.map_cons, List.map_nil]
    rw [hres_x', hrhsRes]
  rw [hresidEq, show nP + 1 + 0 - 1 = nP from by omega, hresidual]
    at hQi hQA
  -- compute the equation components' values
  have hSpineFull : InterpSpine val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ (argsC ++ [xArg]) (ps ++ [x]) :=
    TeleFitI.toInterpSpine hfitFull
  have hSpineP' : InterpSpine val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ argsC ps := by
    have h1 := InterpSpine.take nP hSpineFull
    rwa [List.take_append_of_le_length (by omega), ← hlenC,
      List.take_length,
      show (ps ++ [x]).take argsC.length = ps from by
        rw [hlenC, List.take_append_of_le_length (by omega), ← hlen,
          List.take_length]] at h1
  have hCvalEq : val' (ctor.str "_model") (Level.substFn
      (Level.substFn φ' lps us) ctorLps (ctorLps.map .param)) =
      val' (ctor.str "_model") (Level.substFn φ' lps us) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) ctorLps
        (ctorLps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1]
  have hcCi : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃ (.const (ctor.str "_model") (ctorLps.map .param)) =
      some (val' (ctor.str "_model") (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hCmlps]; simp)]
    rw [show cimC.toConstantVal.levelParams = ctorLps from hCmlps]
    rw [hCvalEq]
  have hprojVal : ∀ j, j < nF →
      interpExpr V val' env₁ (Level.substFn φ' lps us) (d₂ + 1) ρ₃
        (Expr.mkAppN (.const (projModelName T j) (lps.map .param))
          (argsC ++ [xArg])) =
      some (SpineFold V
        (val' (projModelName T j) (Level.substFn φ' lps us))
        (ps ++ [x])) := by
    intro j hj
    obtain ⟨cimj, hfj, hjlps⟩ := hprojf j hj
    have hcji : interpExpr V val' env₁ (Level.substFn φ' lps us)
        (d₂ + 1) ρ₃ (.const (projModelName T j) (lps.map .param)) =
        some (val' (projModelName T j) (Level.substFn φ' lps us)) := by
      have hjval : val' (projModelName T j) (Level.substFn
          (Level.substFn φ' lps us) lps (lps.map .param)) =
          val' (projModelName T j) (Level.substFn φ' lps us) := by
        have h1 : Level.substFn (Level.substFn φ' lps us) lps
            (lps.map .param) = Level.substFn φ' lps us :=
          funext (fun p => Level.substFn_map_param)
        rw [h1]
      simp only [interpExpr, hfj]
      rw [if_pos (by rw [hjlps]; simp)]
      rw [show cimj.toConstantVal.levelParams = lps from hjlps]
      rw [hjval]
    exact interp_mkAppN _ _ hcji hSpineFull
  have hprojSpine : InterpSpine val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃
      ((List.range nF).map fun j => Expr.mkAppN
        (.const (projModelName T j) (lps.map .param))
        (argsC ++ [xArg]))
      ((List.range nF).map fun j => SpineFold V
        (val' (projModelName T j) (Level.substFn φ' lps us))
        (ps ++ [x])) := by
    have hgen : ∀ (l : List Nat), (∀ j ∈ l, j < nF) →
        InterpSpine val' env₁ (Level.substFn φ' lps us) (d₂ + 1) ρ₃
          (l.map fun j => Expr.mkAppN
            (.const (projModelName T j) (lps.map .param))
            (argsC ++ [xArg]))
          (l.map fun j => SpineFold V
            (val' (projModelName T j) (Level.substFn φ' lps us))
            (ps ++ [x])) := by
      intro l
      induction l with
      | nil => intro _; exact trivial
      | cons j l ih =>
        intro hl
        exact ⟨hprojVal j (hl j List.mem_cons_self),
          ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))⟩
    exact hgen (List.range nF) (fun j hj => List.mem_range.mp hj)
  have hrhsVal : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 1) ρ₃
      (Expr.mkAppN (.const (ctor.str "_model") (ctorLps.map .param))
        (argsC ++ (List.range nF).map fun j => Expr.mkAppN
          (.const (projModelName T j) (lps.map .param))
          (argsC ++ [xArg]))) =
      some (SpineFold V
        (val' (ctor.str "_model") (Level.substFn φ' lps us))
        (ps ++ (List.range nF).map fun j =>
          SpineFold V (val' (projModelName T j) (Level.substFn φ' lps us))
            (ps ++ [x]))) :=
    interp_mkAppN _ _ hcCi (InterpSpine.append hSpineP' hprojSpine)
  -- destructure the equation's chain and extract the value identity
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
  have hvl : vl = x := by
    rw [hxItp] at hil
    exact (Option.some.inj hil).symm
  have hvr : vr = SpineFold V
      (val' (ctor.str "_model") (Level.substFn φ' lps us))
      (ps ++ (List.range nF).map fun j =>
        SpineFold V (val' (projModelName T j) (Level.substFn φ' lps us))
          (ps ++ [x])) := by
    rw [hrhsVal] at hir
    exact (Option.some.inj hir).symm
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
  have hxr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  rw [hvl] at hxr
  rw [hvr] at hxr
  exact hxr

set_option maxHeartbeats 3200000 in
/-- The semantic unit-like law from the checked `T._model.unitlike`
theorem: any two members of the interpreted family are equal.  Same
pipeline as `eta_rule_fold`, with two subject binders and no
constructor spine. -/
theorem unit_rule_fold
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name}
    (hro : RenameOk val' env₁ f)
    (hcvp : ConstValParams val' env₁)
    {T : Name} {lps : List Name} {nP : Nat}
    {cvTty : Expr}
    {cimT : ConstantInfo}
    (hfTm : env₁.find? (T.str "_model") = some cimT)
    (hTmlps : cimT.toConstantVal.levelParams = lps)
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    {thmName : Name} {cvt : ConstantVal}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val' env₁ ψ'' cvt.type = some Pv ∧
      val' thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    {sbinders : List (Name × Expr × BinderMeta)}
    {sbody tySlot : Expr} {ℓA : Level}
    (hS_strip : cvt.type.stripPis (nP + 2) = some (sbinders, sbody))
    {tbinders : List (Name × Expr × BinderMeta)} {tbody : Expr}
    (hT_strip : cvTty.stripPis nP = some (tbinders, tbody))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbinders[k]? = some b' →
      RenEq f b'.2.1 b.2.1)
    (hxdom : ∃ nx mx, sbinders[nP]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx))
    (hydom : ∃ ny my, sbinders[nP + 1]? = some (ny,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - k)), my))
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot, .bvar 1, .bvar 0])
    (hTw : cvTty.hasFvar = false)
    {us : List Level} {ps : List V} {x y : V}
    (hlen : ps.length = nP)
    (hx : x ∈ˢ SpineFold V (val' (T.str "_model")
      (Level.substFn φ' lps us)) ps)
    (hy : y ∈ˢ SpineFold V (val' (T.str "_model")
      (Level.substFn φ' lps us)) ps)
    {d₁ : Nat} {ρ₁ : Nat → V} {d₂ : Nat} {ρ₂ : Nat → V} {rest : Expr}
    (hfitT : TeleFit V val' env₁ φ' d₁ ρ₁
      (cvTty.instantiateLevelParams lps us) ps d₂ ρ₂ rest) :
    x = y := by
  -- fit the parameter values through the raw public type former
  have hTwI : ∀ D, WScoped D (cvTty.instantiateLevelParams lps us) :=
    fun D => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hTw)
  obtain ⟨hd₂, hagr₂, argsC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfitT (hTwI d₁)
  have hlenC0 : argsC0.length = nP := by
    have h1 := TeleFitI.vs_length hfitL2
    simp [hlen] at h1
    omega
  obtain ⟨restC1, hfitS2⟩ := TeleFitI.sanitize hfitL2
    (by rw [hlenC0]
        exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
          (by rw [hT_strip]; rfl)) hfvC0
  have hshC : ∀ a ∈ argsC0.map sanitizeArg, ∃ j n,
      a = Expr.fvar j n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨j, n, rfl⟩
  obtain ⟨restC2', hfitRaw⟩ := TeleFitI.instLev_down hcvp hfitS2 hshC
    (WScoped.of_not_hasFvar hTw (d := d₂)).fvarsBelow
  obtain ⟨argsC, hargsCdef⟩ : ∃ a, a = argsC0.map sanitizeArg := ⟨_, rfl⟩
  rw [← hargsCdef] at hfitRaw hshC
  have hlenC : argsC.length = nP := by
    rw [hargsCdef]; simp [hlenC0]
  have hshC' : ∀ a ∈ argsC, ∃ j n, a = Expr.fvar j n (.sort .zero) := hshC
  -- transfer onto the statement's parameter prefix
  obtain ⟨nx, mx, hxdom'⟩ := hxdom
  obtain ⟨ny, my, hydom'⟩ := hydom
  have hslen : sbinders.length = nP + 2 := Expr.stripPis_length _ hS_strip
  have htlen : tbinders.length = nP := Expr.stripPis_length _ hT_strip
  obtain ⟨sbodyN, hS_stripP⟩ := stripPis_prefix nP 2 hS_strip
  have hpiRel : PiDomsRenEq f nP cvTty cvt.type := by
    refine PiDomsRenEq.of_pointwise nP hT_strip hS_stripP ?_
    intro k b₁ b₂ hb₁ hb₂
    have hk : k < nP := by
      rcases Nat.lt_or_ge k nP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hb₁
        exact nomatch hb₁
    have hb₂' : sbinders[k]? = some b₂ := by
      rw [← List.getElem?_take_of_lt hk]
      exact hb₂
    exact hsdoms k b₂ b₁ hk hb₂' hb₁
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
    obtain ⟨hw, hb, hA⟩ := TeleFitI.arg_wf hfitRaw k _ ha₁
    exact ⟨RenEq.fvar_self, hw, hb, hA⟩
  have hSfb : Expr.fvarsBelow d₂ cvt.type :=
    (WScoped.of_not_hasFvar hSw).fvarsBelow
  obtain ⟨midS, hstmtFitP⟩ := TeleFitI.ren_transfer hro hfitRaw
    (by rw [hlenC]; exact hpiRel) hSfb hargsSelf
  -- the residual: two subject binders over the instantiated model type
  obtain ⟨mid2, hmid2, bs', body', hstrip2, hbody', hbind'⟩ :=
    telescopeInst_stripPis nP argsC 2 hlenC hS_strip
  obtain rfl : midS = mid2 := by
    have h1 := TeleFitI.rest_eq hstmtFitP
    rw [hmid2] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨nb, domb, midY, mb, rfl⟩ : ∃ nb domb midY mb,
      midS = .forallE nb domb midY mb := by
    match midS, hstrip2 with
    | .forallE nb domb midY mb, _ => exact ⟨nb, domb, midY, mb, rfl⟩
  obtain ⟨nb2, domy, bodyb, mb2, rfl⟩ : ∃ nb2 domy bodyb mb2,
      midY = .forallE nb2 domy bodyb mb2 := by
    simp only [Expr.stripPis] at hstrip2
    match midY, hstrip2 with
    | .forallE nb2 domy bodyb mb2, _ =>
      exact ⟨nb2, domy, bodyb, mb2, rfl⟩
  simp only [Expr.stripPis, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hstrip2
  obtain ⟨rfl, rfl⟩ := hstrip2
  have hdombEq : domb = Expr.instSeq argsC (nP + 0 - 1)
      (Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))) := by
    exact hbind' 0 _ _ (by simpa using hxdom') (by rfl)
  have hdomyEq : domy = Expr.instSeq argsC (nP + 1 - 1)
      (Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - k))) := by
    exact hbind' 1 _ _ (by simpa using hydom') (by rfl)
  -- resolve the subject domains along the parameter arguments
  have hbounded : ∀ a ∈ argsC, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, n, rfl⟩ := hshC' a ha
    rfl
  have hresolveP : ∀ (k : Nat), k < nP →
      argsC[k]? = some (Expr.instSeq argsC (nP - 1)
        (.bvar (nP - 1 - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar argsC (nP - 1)
      (nP - 1 - k) hbounded (by omega) (by rw [hlenC]; omega)
    rwa [show nP - 1 - (nP - 1 - k) = k from by omega] at h1
  have hresolveP1 : ∀ (k : Nat), k < nP →
      argsC[k]? = some (Expr.instSeq argsC nP (.bvar (nP - k))) := by
    intro k hk
    have h1 := Expr.instSeq_bvar argsC nP
      (nP - k) hbounded (by omega) (by rw [hlenC]; omega)
    rwa [show nP - (nP - k) = k from by omega] at h1
  have hres_pP : (((List.range nP).map fun k =>
        Expr.bvar (nP - 1 - k))).map
        (Expr.instSeq argsC (nP - 1) ·) = argsC := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hk]
      simp only [Option.map_some]
      exact (hresolveP k hk).symm
    · rw [List.getElem?_map, List.getElem?_map]
      rw [List.getElem?_eq_none (l := List.range nP) (by simp; omega)]
      rw [List.getElem?_eq_none (l := argsC) (by rw [hlenC]; omega)]
      all_goals rfl
  have hres_pP1 : (((List.range nP).map fun k =>
        Expr.bvar (nP - k))).map
        (Expr.instSeq argsC nP ·) = argsC := by
    refine List.ext_getElem? ?_
    intro k
    rcases Nat.lt_or_ge k nP with hk | hk
    · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hk]
      simp only [Option.map_some]
      exact (hresolveP1 k hk).symm
    · rw [List.getElem?_map, List.getElem?_map]
      rw [List.getElem?_eq_none (l := List.range nP) (by simp; omega)]
      rw [List.getElem?_eq_none (l := argsC) (by rw [hlenC]; omega)]
      all_goals rfl
  have hdomRes : domb =
      Expr.mkAppN (.const (T.str "_model") (lps.map .param)) argsC := by
    rw [hdombEq, show nP + 0 - 1 = nP - 1 from by omega,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    all_goals congr 1
    all_goals exact hres_pP
  have hdomyRes : domy =
      Expr.mkAppN (.const (T.str "_model") (lps.map .param)) argsC := by
    rw [hdomyEq, show nP + 1 - 1 = nP from by omega,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    all_goals congr 1
    all_goals exact hres_pP1
  -- interpret the subject domains
  have hAllSpineP : InterpSpine val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      argsC ps :=
    TeleFitI.toInterpSpine hstmtFitP
  have hTvalEq : val' (T.str "_model") (Level.substFn
      (Level.substFn φ' lps us) lps (lps.map .param)) =
      val' (T.str "_model") (Level.substFn φ' lps us) := by
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1]
  have hcTi : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      (.const (T.str "_model") (lps.map .param)) =
      some (val' (T.str "_model") (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfTm]
    rw [if_pos (by rw [hTmlps]; simp)]
    rw [show cimT.toConstantVal.levelParams = lps from hTmlps]
    rw [hTvalEq]
  have hdomI : interpExpr V val' env₁ (Level.substFn φ' lps us) d₂ ρ₂
      domb = some (SpineFold V
        (val' (T.str "_model") (Level.substFn φ' lps us)) ps) := by
    rw [hdomRes]
    exact interp_mkAppN _ _ hcTi hAllSpineP
  -- extend the fit with both subjects, two fresh levels up
  obtain ⟨ρ₃, hρ₃⟩ : ∃ ρ₃, ρ₃ = updV V ρ₂ d₂ x := ⟨_, rfl⟩
  obtain ⟨ρ₄, hρ₄⟩ : ∃ ρ₄, ρ₄ = updV V ρ₃ (d₂ + 1) y := ⟨_, rfl⟩
  have hρ34 : ∀ i, i < d₂ + 1 → ρ₄ i = ρ₃ i := by
    intro i hi
    rw [hρ₄]
    simp [updV, Nat.ne_of_lt hi]
  have hρ23 : ∀ i, i < d₂ → ρ₃ i = ρ₂ i := by
    intro i hi
    rw [hρ₃]
    simp [updV, Nat.ne_of_lt hi]
  have hρ24 : ∀ i, i < d₂ → ρ₄ i = ρ₂ i := by
    intro i hi
    rw [hρ34 i (by omega), hρ23 i hi]
  have hfitLift : TeleFitI V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ cvt.type argsC ps
      (.forallE nb domb (.forallE nb2 domy bodyb mb2) mb) :=
    TeleFitI.lift hstmtFitP (WScoped.of_not_hasFvar hSw)
      (by omega) hρ24
  obtain ⟨xArg, hxArg⟩ : ∃ a, a = Expr.fvar d₂ nb (.sort .zero) :=
    ⟨_, rfl⟩
  obtain ⟨yArg, hyArg⟩ : ∃ a, a = Expr.fvar (d₂ + 1) nb2 (.sort .zero) :=
    ⟨_, rfl⟩
  have hxItp : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ xArg = some x := by
    rw [hxArg, hρ₄, hρ₃]
    simp [interpExpr, updV]
  have hyItp : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ yArg = some y := by
    rw [hyArg, hρ₄]
    simp [interpExpr, updV]
  have hargswtb : ∀ a ∈ argsC, WScoped d₂ a := by
    intro a ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
    obtain ⟨hw, -, -⟩ := TeleFitI.arg_wf hstmtFitP k _ hk
    exact hw
  have hwdom : WScoped d₂ domb := by
    rw [hdomRes]
    exact Expr.WScoped.mkAppN (by simp [WScoped]) hargswtb
  have hwdomy : WScoped d₂ domy := by
    rw [hdomyRes]
    exact Expr.WScoped.mkAppN (by simp [WScoped]) hargswtb
  have hdomI' : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ domb = some (SpineFold V
        (val' (T.str "_model") (Level.substFn φ' lps us)) ps) := by
    rw [interp_lift hwdom (d₂ + 2) (by omega) ρ₂ ρ₄
      (fun i hi => hρ24 i hi)]
    exact hdomI
  have hdomyI' : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ domy = some (SpineFold V
        (val' (T.str "_model") (Level.substFn φ' lps us)) ps) := by
    rw [interp_lift hwdomy (d₂ + 2) (by omega) ρ₂ ρ₄
      (fun i hi => hρ24 i hi)]
    rw [hdomyRes]
    exact interp_mkAppN _ _ hcTi hAllSpineP
  have hres_fb : Expr.fvarsBelow d₂
      (Expr.forallE nb domb (.forallE nb2 domy bodyb mb2) mb) := by
    refine telescopeInst_fvarsBelow argsC
      (WScoped.of_not_hasFvar hSw).fvarsBelow ?_ hmid2
    intro a ha
    exact (hargswtb a ha).fvarsBelow
  have hfb_parts : Expr.fvarsBelow d₂ domy ∧
      Expr.fvarsBelow d₂ bodyb := by
    have h1 := hres_fb
    simp only [Expr.fvarsBelow] at h1
    exact ⟨h1.2.1, h1.2.2⟩
  have hdomyClosed : domy.looseBVarsBounded 0 = true := by
    rw [hdomyRes]
    refine looseBVarsBounded_mkAppN (by rfl) ?_
    intro a ha
    exact hbounded a ha
  obtain ⟨restXY, hxyfit⟩ : ∃ restXY, TeleFitI V val' env₁
      (Level.substFn φ' lps us) (d₂ + 2) ρ₄
      (.forallE nb domb (.forallE nb2 domy bodyb mb2) mb)
      [xArg, yArg] [x, y] restXY := by
    refine ⟨(bodyb.instantiate1 xArg 1).instantiate1 yArg,
      TeleFitI.cons hdomI' hxItp hx ?_ ?_ ?_ ?_ ?_⟩
    · have h1 : Expr.fvarsBelow d₂
          (Expr.forallE nb2 domy bodyb mb2) := by
        have h2 := hres_fb
        simp only [Expr.fvarsBelow] at h2 ⊢
        exact h2.2
      exact fvarsBelow_mono (by omega) h1
    · rw [hxArg]
      simp only [WScoped]
      exact ⟨by omega, trivial⟩
    · rw [hxArg]; rfl
    · rw [hxArg]; simp [AnnotOk]
    · rw [show (Expr.forallE nb2 domy bodyb mb2).instantiate1 xArg =
        .forallE nb2 (domy.instantiate1 xArg)
          (bodyb.instantiate1 xArg 1) mb2 from rfl,
        instantiate1_eq_self hdomyClosed]
      refine TeleFitI.cons hdomyI' hyItp hy ?_ ?_ ?_ ?_ TeleFitI.nil
      · refine fvarsBelow_instantiate1_gen ?_ 1
          (fvarsBelow_mono (by omega) hfb_parts.2)
        rw [hxArg]
        exact (show WScoped (d₂ + 2) (Expr.fvar d₂ nb (.sort .zero))
          from by
            simp only [WScoped]
            exact ⟨by omega, trivial⟩).fvarsBelow
      · rw [hyArg]
        simp only [WScoped]
        exact ⟨by omega, trivial⟩
      · rw [hyArg]; rfl
      · rw [hyArg]; simp [AnnotOk]
  have hfitFull := TeleFitI.append hfitLift hxyfit
  -- eliminate the theorem's inhabitant
  obtain ⟨Pv, hPi, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPi' : interpExpr V val' env₁ (Level.substFn φ' lps us)
      (d₂ + 2) ρ₄ cvt.type = some Pv := by
    rw [interp_closed_invariant hSw (d₂ + 2) ρ₄]
    exact hPi
  have hSA : AnnotOk V val' env₁ (Level.substFn φ' lps us) (d₂ + 2) ρ₄
      cvt.type :=
    AnnotOk.closed_invariant hSw (d₂ + 2) ρ₄ (hthm_annot _)
  obtain ⟨Q, hQi, hQmem, hQA⟩ := TeleFitI.elim hfitFull hSA hPi' hPmem
  -- the residual is the instantiated equation
  have hlen' : (argsC ++ [xArg, yArg]).length = nP + 2 := by
    simp [hlenC]
  obtain ⟨midF, hmidF, bsF, bodyF, hstripF, hbodyF, -⟩ :=
    telescopeInst_stripPis (nP + 2) (argsC ++ [xArg, yArg]) 0 hlen'
      (by rw [show nP + 2 + 0 = nP + 2 from rfl]; exact hS_strip)
  have hmidF_id : midF = bodyF := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripF
    exact hstripF.2
  have hresidEq : restXY =
      Expr.instSeq (argsC ++ [xArg, yArg]) (nP + 2 + 0 - 1) sbody := by
    have h1 := TeleFitI.rest_eq hfitFull
    rw [hmidF] at h1
    rw [← hbodyF, ← hmidF_id]
    exact (Option.some.inj h1).symm
  have hbounded' : ∀ a ∈ argsC ++ [xArg, yArg],
      a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hbounded a h
    · rcases List.mem_cons.mp h with rfl | h
      · rw [hxArg]; rfl
      · rw [List.mem_singleton.mp h, hyArg]; rfl
  have hres_x : Expr.instSeq (argsC ++ [xArg, yArg]) (nP + 1)
      (.bvar 1) = xArg := by
    have h1 := Expr.instSeq_bvar (argsC ++ [xArg, yArg]) (nP + 1) 1
      hbounded' (by omega) (by simp [hlenC])
    rw [show nP + 1 - 1 = nP from by omega] at h1
    have h2 : (argsC ++ [xArg, yArg])[nP]? = some xArg := by
      rw [List.getElem?_append_right (by rw [hlenC]; omega)]
      simp [hlenC]
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hres_y : Expr.instSeq (argsC ++ [xArg, yArg]) (nP + 1)
      (.bvar 0) = yArg := by
    have h1 := Expr.instSeq_bvar (argsC ++ [xArg, yArg]) (nP + 1) 0
      hbounded' (by omega) (by simp [hlenC])
    rw [show nP + 1 - 0 = nP + 1 from by omega] at h1
    have h2 : (argsC ++ [xArg, yArg])[nP + 1]? = some yArg := by
      rw [List.getElem?_append_right (by rw [hlenC]; omega)]
      simp [hlenC]
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hresidual : Expr.instSeq (argsC ++ [xArg, yArg]) (nP + 1) sbody =
      Expr.mkAppN (.const eqName [ℓA])
        [Expr.instSeq (argsC ++ [xArg, yArg]) (nP + 1) tySlot,
         xArg, yArg] := by
    rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    simp only [List.map_cons, List.map_nil]
    rw [hres_x, hres_y]
  rw [hresidEq, show nP + 2 + 0 - 1 = nP + 1 from by omega, hresidual]
    at hQi hQA
  -- destructure and collapse the equation
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
  have hvl : vl = x := by
    rw [hxItp] at hil
    exact (Option.some.inj hil).symm
  have hvr : vr = y := by
    rw [hyItp] at hir
    exact (Option.some.inj hir).symm
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
  have hxr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  rw [hvl] at hxr
  rw [hvr] at hxr
  exact hxr
