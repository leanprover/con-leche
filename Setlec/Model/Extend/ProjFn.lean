import Setlec.Model.Extend.Modeled
import Setlec.Model.Extend.Transport

/-!
# ProjFn — split out of `Setlec.Model.Extend`

`extend_proj_fn`: extend a model by an installed projection
function, a degenerate recursor whose single rule's total λ-equality
obligation is discharged by the checked `proj_i.iota` theorem.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by an installed projection function: a degenerate
recursor (no motive, no minors) whose value is its `_model.proj_i`
counterpart's and whose single rule's total λ-equality obligation is
discharged by the checked `proj_i.iota` theorem (`proj_rule_eq`). -/
theorem extend_proj_fn {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nF i : Nat) (rule : RecRule)
    (f : Name → Name) (mnameP : Name)
    {cvm : ConstantVal} {mval : Expr} {cvj : ConstantVal}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA nP nP [rule] :: env.consts⟩
      (.recInfo cvA nP nP [rule]))
    (htyres0 : cvA.type.constsResolve env = true)
    (hmodel : env.find? mnameP = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = cvA.levelParams)
    (hren : cvA.type.renameConsts f = cvm.type)
    (f₀ : Name → Name) (hro : RenameOk m.val env f₀)
    (hff₀ : ∀ n, n ≠ cvA.name → f n = f₀ n)
    (hfself : f cvA.name = mnameP)
    (hfnot : ∀ n, f n ≠ cvA.name)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'')
    (hi : i < nF)
    (hfire : ∀ lvls pins, rule.fire ≠ .nested lvls pins)
    (hctor : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    (_hnf : rule.nfields = nF)
    (hcp : rule.ctorParams = nP)
    {raw : Expr}
    (hann : annotateCore env F 0 raw = .ok (RecRule.rhs rule))
    (hrawf : raw.hasFvar = false)
    (hrawb : raw.looseBVarsBounded 0 = true)
    (hrhsres : (RecRule.rhs rule).constsResolve env = true)
    {rbinders cbinders sbinders : List (Name × Expr × BinderMeta)}
    {rbody cbody sbody tySlot : Expr} {ℓA : Level}
    {thmName : Name} {cvt : ConstantVal} {tval : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) =
      some (rbinders, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    {dN : Name} {dus : List Level} {dargs : List Expr}
    (hcbody : cbody = Expr.mkAppN (.const dN dus) dargs)
    (hdargs : dargs.length = nP)
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f (RecRule.ctor rule))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    {fvsO : List Expr} {sbodyO : Expr}
    (hopenO : openPisAtFvars (nP + nF) cvt.type 0 = some (fvsO, sbodyO))
    (hrhsTyC : ∃ tr, inferTypeCore env F (nP + nF)
        (sbodyO.getAppArgs.getD 2 (.bvar 0)) = .ok tr ∧
      isDefEqCore env F (nP + nF) tr
        (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok true)
    (hthm : env.find? thmName = some (.thmInfo cvt tval))
    (_hlpt : cvt.levelParams = cvA.levelParams)
    -- the kernel's frame walks and definitional pins (task #58)
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvs : List Expr} {crest2X : Expr}
    {ldoms : List Expr} {lrestL : Expr}
    (hopenP : openPisAtFvars nP cvA.type 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt fvsP cvj.type = some (cdomsP, crestP))
    (hdeParsP : DefEqListOk F env (nP + nF)
      (fvsP.map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars nF crestP nP = some (xFvs, crest2X))
    (hlinstP : Expr.instLamsAt (fvsP ++ xFvs) (RecRule.rhs rule) =
      some (ldoms, lrestL))
    (hdeLamP : DefEqListOk F env (nP + nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms)
    (hrhsw : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    {rhsTy : Expr}
    (hity : inferTypeCore env F 0 (RecRule.rhs rule) = .ok rhsTy)
    -- the eta head obligation, forwarded: only the caller (the
    -- projection phase, with its `ProjPhaseInv` identification in
    -- scope) knows whether this projection function completes its
    -- former's eta family
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨.recInfo cvA nP nP [] :: env.consts⟩ : Env).find? T =
        some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored (⟨.recInfo cvA nP nP [] :: env.consts⟩ : Env)
        T capsT →
      (∃ j, j < capsT.etaFields ∧ projFnName T j = cvA.name) →
      ∀ val₁ : ConstVal V,
        (∀ (n : Name) (ψ : Name → Nat), n ≠ cvA.name →
          val₁ n ψ = m.val n ψ) →
        (∀ ψ : Name → Nat, val₁ cvA.name ψ = m.val mnameP ψ) →
        EtaLaw V (⟨.recInfo cvA nP nP [] :: env.consts⟩ : Env) val₁
          T cvT capsT) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP nP [rule] :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val mnameP ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hwf₀ : ConstWF (⟨.recInfo cvA nP nP [] :: env.consts⟩ : Env)
      (.recInfo cvA nP nP []) := ConstWF.recRules_head_empty hwf
  have hren₀ : cvA.type.renameConsts f₀ = cvm.type := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => hff₀ n (fun he => by
        rw [he, hfind'] at hn; exact nomatch hn))
      cvA.type htyres0]
    exact hren
  -- the projection type is the model's renamed back verbatim, so its
  -- annotation truthfulness transports from the model's
  have hannT : ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) cvA.type := by
    intro ψ
    obtain ⟨hA, -⟩ := m.annot_ok _ (find?_mem hmodel) ψ
    have hA' : AnnotOk V m.val env ψ 0 (rho0 V)
        (cvA.type.renameConsts f₀) := by
      rw [hren₀]; exact hA
    exact AnnotOk_renameConsts hro _ 0 (rho0 V) hA'
  obtain ⟨m₀, hval₀, hpres₀⟩ := extend_modeled_one m
    (.recInfo cvA nP nP []) f₀ (mnameP)
    hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, nP, rfl⟩)) hmodel hlps
    (by show Expr.eqUpToNames (cvA.type.renameConsts f₀) cvm.type = true
        rw [hren₀]
        exact Expr.eqUpToNames_rfl _) hannT hro
    (fun val₁ hv₁ he₁ => by
      refine ⟨?_, fun cv2 caps2 hcon => nomatch hcon⟩
      intro T cvT capsT hfT hcape hresT hfam hpart
      rcases hpart with rfl | hC | hPart
      · rw [Env.find?_cons, if_pos rfl] at hfT
        exact nomatch (Option.some.inj hfT)
      · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [hC, Env.find?_cons, if_pos rfl] at hfC
        exact nomatch (Option.some.inj hfC)
      · exact hheadEta T cvT capsT hfT hcape hresT hfam hPart val₁
          he₁ hv₁)
  -- transports from the base model into the final environment
  have hagreeM : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      m₀.val n ψ = m.val n ψ := by
    intro n hn ψ
    refine hpres₀ n ψ ?_
    intro h
    have h2 : n = cvA.name := h
    rw [h2, hfind'] at hn
    exact nomatch hn
  have htransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      interpClosed V m₀.val
        (⟨.recInfo cvA nP nP [rule] :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e :=
    fun e hres ψ => interpClosed_extend_fresh
      (c₀ := .recInfo cvA nP nP [rule]) hfind' hagreeM hres ψ
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP nP [rule] :: env.consts⟩ : Env) ψ 0
        (rho0 V) e :=
    fun e hres ψ ha => AnnotOk.extend_fresh
      (c₀ := .recInfo cvA nP nP [rule]) hfind' hagreeM hres ψ ha
  -- the head's stored-constructor fact and single fold obligation
  have hctors : ∀ r ∈ [rule], ∃ cvj' cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj' cnP cnF) := by
    intro r hr
    obtain rfl : rule = r := by
      rcases List.mem_cons.mp hr with h | h
      · exact h.symm
      · cases h
    exact ⟨cvj, nP, nF, hctor⟩
  have hrecm : RecMemberOk (V := V)
      ⟨.recInfo cvA nP nP [rule] :: env.consts⟩ m₀.val
      (.recInfo cvA nP nP [rule]) := by
      intro cvR mI' rP' rules hceq r hr
      injection hceq with e1 e2 e3 e4
      subst e1 e2 e3 e4
      obtain rfl : rule = r := by
        rcases List.mem_cons.mp hr with h | h
        · exact h.symm
        · cases h
      have hncc : RecRule.ctor rule ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hctor)
        have h3 : (ConstantInfo.ctorInfo cvj nP nF).name =
            RecRule.ctor rule := by
          have h4 := List.find?_some hctor
          simpa using h4
        exact h2 (by rw [h3, h])
      have hArhs₁ : ∀ ψ : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP nP [rule] :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs rule) := by
        intro ψ
        exact hAtransM _ hrhsres ψ
          (annotate_sound m raw hann (WScoped.of_not_hasFvar hrawf)
            hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
            (FvarsOk.of_not_hasFvar hrawf))
      refine ⟨hArhs₁, fun _ => Nat.le_refl _, fun _ => Nat.le_of_eq hcp,
        fun lvls pins hn => absurd hn (hfire lvls pins), ?_⟩
      intro cvj' cnP' cnF' hfj hnotinert
      have hfr : RecRule.fire rule = .plain := by
        rcases h : RecRule.fire rule with _ | _ | ⟨lvls, pins⟩
        · exact absurd h hnotinert
        · rfl
        · exact absurd h (hfire lvls pins)
      have hctor₁ : (⟨.recInfo cvA nP nP [rule] ::
          env.consts⟩ : Env).find? (RecRule.ctor rule) =
          some (.ctorInfo cvj nP nF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP nP
            [rule]).name = RecRule.ctor rule from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP nP [rule] :: env.consts⟩ : Env) f := by
        refine ⟨?_, ?_, ?_⟩
        · intro n₂ ci₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain rfl := Option.some.inj hf₂
            refine ⟨.defnInfo cvm mval hmcvm, ?_, ?_⟩
            · rw [show f n₂ = mnameP from by
                rw [← (show cvA.name = n₂ from hh)]
                exact hfself]
              rw [Env.find?_cons,
                if_neg (show ¬(ConstantInfo.recInfo cvA nP nP
                  [rule]).name = mnameP from
                  fun h => hfnot cvA.name (hfself.trans h.symm))]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP nP
                  [rule]).toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP nP
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP nP
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = mnameP from hfself]
            rw [hpres₀ _ ψ₂
              (fun h => hfnot cvA.name (hfself.trans h))]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hff₀ n₂ hh,
                hro.2.2 n₂]
      have heqval₁ : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'' :=
        fun ψ'' => by
          rw [hagreeM eqName (by rw [heqfind]; rfl) ψ'', heqval ψ'']
      have hfP₁ : (⟨.recInfo cvA nP nP [rule] ::
          env.consts⟩ : Env).find? cvA.name =
          some (.recInfo cvA nP nP [rule]) := by
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP nP
            [rule]).name = cvA.name from rfl)]
      -- the base-model facts the new glue consumes
      have hffRes : ∀ n, (env.find? n).isSome = true → f n = f₀ n := by
        intro n hn
        refine hff₀ n ?_
        intro he
        rw [he, hfind'] at hn
        exact nomatch hn
      obtain ⟨hSw, -, hSres, hSb, -, -⟩ := m.wf _ (find?_mem hthm)
      have hthm_memL : ∀ ψ'' : Name → Nat, ∃ Pv,
          interpClosed V m.val env ψ'' cvt.type = some Pv ∧
          m.val thmName ψ'' ∈ˢ Pv := by
        intro ψ''
        obtain ⟨Pv, hPv, hmm⟩ := m.mem_type _ (find?_mem hthm) ψ''
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          simpa using List.find?_some hthm
        exact ⟨Pv, hPv, by rw [← h3]; exact hmm⟩
      have hthm_annotL : ∀ ψ'' : Name → Nat,
          AnnotOk V m.val env ψ'' 0 (rho0 V) cvt.type :=
        fun ψ'' => (m.annot_ok _ (find?_mem hthm) ψ'').1
      obtain ⟨hCtf, -, hCtres, hCtb, -, -⟩ := m.wf _ (find?_mem hctor)
      have hACtyL : ∀ ψ'' : Name → Nat,
          AnnotOk V m.val env ψ'' 0 (rho0 V) cvj.type :=
        fun ψ'' => (m.annot_ok _ (find?_mem hctor) ψ'').1
      have hICtyL : ∀ ψ'' : Name → Nat, ∃ T,
          interpClosed V m.val env ψ'' cvj.type = some T := by
        intro ψ''
        obtain ⟨t, ht, -⟩ := m.mem_type _ (find?_mem hctor) ψ''
        exact ⟨t, ht⟩
      have hItyL : ∀ ψ'' : Name → Nat, ∃ T,
          interpClosed V m.val env ψ'' cvA.type = some T := by
        intro ψ''
        obtain ⟨t, ht, -⟩ := m.mem_type _ (find?_mem hmodel) ψ''
        refine ⟨t, ?_⟩
        have h0 : interpClosed V m.val env ψ''
            (cvA.type.renameConsts f₀) = some t := by
          rw [hren₀]
          exact ht
        unfold interpClosed at h0 ⊢
        rw [← interp_renameConsts hro cvA.type 0 (rho0 V)]
        exact h0
      have hArhsL : ∀ ψ'' : Name → Nat,
          AnnotOk V m.val env ψ'' 0 (rho0 V) (RecRule.rhs rule) :=
        fun ψ'' => annotate_sound m raw hann
          (WScoped.of_not_hasFvar hrawf) hrawb
          (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
          (FvarsOk.of_not_hasFvar hrawf)
      have hIrhsL : ∀ ψ'' : Name → Nat, ∃ L,
          interpClosed V m.val env ψ'' (RecRule.rhs rule) = some L := by
        intro ψ''
        obtain ⟨⟨v, tv', hiv, -, -⟩, -, -⟩ :=
          inferTypeCore_sound (φ := ψ'') m F hity
            (WScoped.of_not_hasFvar hrhsw) hrhsb
            (Expr.LeavesBounded.of_not_hasFvar hrhsw)
            (FvarsOk.of_not_hasFvar hrhsw) (hArhsL ψ'')
        exact ⟨v, hiv⟩
      have hfPmE : env.find? (f cvA.name) =
          some (.defnInfo cvm mval hmcvm) := by
        rw [hfself]
        exact hmodel
      exact proj_rule_eq (P := cvA.name) (i := i)
        (c₀ := .recInfo cvA nP nP [rule]) m F hfind' hagreeM
        hffRes hro hro₁ hi hfP₁ rfl hctor hfPmE
        (show (ConstantInfo.defnInfo cvm
          mval hmcvm).toConstantVal.levelParams = cvA.levelParams from
          hlps)
        heqfind heqval₁ hthm_memL hthm_annotL hSw hSb hSres hfr hcp _hnf
        hstripR hrbody hC_strip hS_strip hsdoms hsbody hopenO hrhsTyC
        hcbody
        hdargs
        hopenP hcinstP hdeParsP hopenX hlinstP hdeLamP
        hwf.1 hwf.2.2.2.1 hCtf hCtb htyres0 hCtres hrhsres hrhsw hrhsb
        hannT hItyL hACtyL hICtyL hArhsL hIrhsL
  obtain ⟨m', hveq⟩ := extend_rec_swap m₀ hfind' hnres hwf hctors hrecm
  exact ⟨m', fun ψ => (hveq _ ψ).trans (hval₀ ψ),
    fun n ψ hne => (hveq n ψ).trans (hpres₀ n ψ hne)⟩
end Setlec
