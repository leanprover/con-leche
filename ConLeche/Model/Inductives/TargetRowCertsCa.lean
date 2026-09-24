module

public import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.FixAssemblyKit

public section

/-!
# The rule's conclusion read at ANY depth past the fields (lane RECLIB)

`blockRuleCaAV_run` (`BlockRuleCaRun.lean`) at an arbitrary width `nR`
of the block between the fields and the conclusion: the target check's
`ih` block (`tgtCaAV`) is read at its own width, not the frame's `nR`.
The proof is `blockRuleCaAV_run`'s, which uses `nR` only as a depth.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section CaRun

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **The conclusion at any depth `nR`**: `blockRuleCaAV_run` with the
frame's `nR` replaced by an arbitrary width — (i) every `concl` of the
run reads there to the reading of `blockRuleConclExpr`, (ii) that
reading is the recursor type's peel along the rule's spine lifted past
the `nR` binders. -/
theorem blockRuleCaAt_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List ConLeche.RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcd : BlockCtorDataI mpC.base2 env₀ T Tof nIdxOf lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {ci : ConstantInfo} (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (nR : Nat) :
    (∀ concl : Expr,
      ConLeche.Expr.instPisAtLift
          (blockRulePrefFvs p.toBlockShape rs c
            ++ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP
            ++ [Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
                ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
                  ++ blockRuleFieldFvs p.toBlockShape rs c i)]) r.1.type = some concl →
      denoteMeta mpC.base2.acval envC ψ
          (p.toBlockShape.rulePrefixAt c + cA.2 + nR) concl
        = some ((denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
          (blockRuleConclExpr p rs c i)).getD default)) ∧
    BlockRuleConclAt (p.toBlockShape.rulePrefixAt c) cA.2 nR
      (blockRecTyAV mpC.base2.acval envC rs ψ c)
      ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (·.liftN nR 0))
      ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).liftN
        nR 0)
      ((denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
          (blockRuleConclExpr p rs c i)).getD default) := by
  have hacl := mpC.base2.acval_closed
  have hct : blockRuleCtorOf rs c i = cA := blockRuleCtorOf_eq hr hcA
  have hrd : rs.getD c default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hty : blockRuleRecTy rs c = r.1.type := by rw [blockRuleRecTy, hrd]
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, hopPref, hinst, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  obtain ⟨-, -, concl0, -, -, -, -, -, hpr, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨hw₁, hb₁⟩ := checkBlockRecK_tyClosed h hr
  have hf₁ : r.1.type.hasFvar = false :=
    (ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr)).1
  -- names for the frame's depths
  have hlenPref : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := openPisAtFvars_length _ hopPref
  have hlenF : (blockRuleFieldFvs p.toBlockShape rs c i).length = cA.2 :=
    openPisAtFvars_length _ hopF
  have hidxPref := ConLeche.openPisAtFvars_index _ _ _ hopPref
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hopF
  -- scoping of the openers and of the constructor's body
  have hwPref := (ConLeche.openPisAtFvars_WScoped _ _ 0 hopPref hw₁).1
  rw [Nat.zero_add] at hwPref
  have hw₂ : Expr.WScoped (p.toBlockShape.rulePrefixAt c) (blockRuleCrest p.toBlockShape rs c i) :=
    blockRuleHw2_of hopPref hw₁ hCf hinst
  obtain ⟨hwF, hwCb⟩ := ConLeche.openPisAtFvars_WScoped _ _ _ hopF hw₂
  have hb₂ : (blockRuleCrest p.toBlockShape rs c i).looseBVarsBounded 0 = true :=
    (instPisAt_bounded _ hinst hCb
      (fun a ha => openPisAtFvars_fvars_closed hopPref a (List.mem_of_mem_take ha))).2
  have hbCb : (blockRuleCbody p.toBlockShape rs c i).looseBVarsBounded 0 = true :=
    (openPisAtFvars_bounded cA.2 hopF hb₂).1
  -- the constructor's body READS at the rule frame (`blockRuleEsAV_eq`'s first half)
  obtain ⟨crest, hopP, hopX⟩ := hcd.opens
  obtain ⟨pps₀, b₀, hst₀, hb₀, -, -⟩ := denoteMeta_openPis p.nP hopP (hcd.read ψ)
  have hstTake := stripPisAV_mkPisAV_take p.nP (ds ψ)
    (ctorBodyAVI mpC.base2 T p.nP cA.2 ψ (Es ψ)) (by rw [hcd.len ψ]; omega)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst₀.symm.trans hstTake))
  rw [Nat.zero_add] at hb₀
  have hwC : Expr.WScoped p.nP crest := by
    have := (ConLeche.openPisAtFvars_WScoped p.nP cA.1.type 0 hopP
      (Expr.WScoped.of_not_hasFvar hCf)).2
    rwa [Nat.zero_add] at this
  have hargsR : ∀ (k : Nat) (a a' : Expr), fvsP[k]? = some a →
      ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]? = some a' →
      ConLeche.Verify.RenEqT (fun n => n) a a' := by
    intro k a a' ha ha'
    obtain ⟨ty, rfl⟩ := hcd.pIdx k a ha
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha'
      rw [List.length_take] at hlt
      omega
    have ha'' : (blockRulePrefFvs p.toBlockShape rs c)[k]? = some a' := by
      have ht : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]?
          = (blockRulePrefFvs p.toBlockShape rs c)[k]? := by
        rw [List.getElem?_take, if_pos hk]
      rw [← ht]; exact ha'
    obtain ⟨ty', rfl⟩ := hidxPref k a' ha''
    rw [Nat.zero_add]
    exact ConLeche.Verify.RenEqT.fvar
  obtain ⟨-, hrenC⟩ := ConLeche.Verify.instPisAt_renEq (f := fun n => n) fvsP
    ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)
    (ConLeche.Verify.openPisAtFvars_instPisAt _ hopP) hinst
    (by show Expr.ErasedEq _ _; rw [renameConsts_id]; exact Expr.ErasedEq.rfl _)
    hargsR
    (by rw [hcd.pLen, List.length_take, hlenPref]; omega)
  have heq : Expr.ErasedEq crest (blockRuleCrest p.toBlockShape rs c i) := by
    have := hrenC
    rwa [ConLeche.Verify.RenEqT, renameConsts_id] at this
  have hsh := readOpenedDoms_shift (m := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt c - p.nP) hb₀ hwC (hcd.len ψ) heq
    (by rw [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
          = p.toBlockShape.rulePrefixAt c from by omega]
        exact hopF)
  have hcb : ∃ v, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2)
      (blockRuleCbody p.toBlockShape rs c i) = some v := by
    have := hsh.2.1
    rw [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
        = p.toBlockShape.rulePrefixAt c from by omega] at this
    exact ⟨_, this⟩
  obtain ⟨vcb, hvcb⟩ := hcb
  obtain ⟨vsA, hspA⟩ := denoteMetaSpine_getAppArgs hvcb
  have hspEs := hspA.drop p.nP
  -- `es0` IS that spine's reading
  have hesE : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i = vsA.drop p.nP := by
    rw [blockRuleEsAV, hct]
    exact denoteMetaSpine_map_getD hspEs
  have hesK0 : blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i
      = blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i := by
    rw [blockRecEsK]
    exact (List.map_congr_left fun e _ => AnnotTerm.liftN_zero e _).trans (List.map_id _)
  -- the fired spine READS at the rule frame (`blockRuleMkAV_eq`'s head and openers)
  have hconst : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2)
      (.const cA.1.name (p.toBlockShape.lps.map Level.param))
      = some (mpC.base2.acval cA.1.name
          (Level.substFn ψ p.lps (p.lps.map Level.param))) := by
    rw [denoteMeta]
    simp only [hfind, hlps]
    rw [if_pos (by rw [List.length_map])]
  have hlenTake : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP).length = p.nP := by
    rw [List.length_take, hlenPref]; omega
  have hidxTake : ∀ (k : Nat) (x : Expr),
      ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
      rw [hlenTake] at hlt
      exact hlt
    have hx' : (blockRulePrefFvs p.toBlockShape rs c)[k]? = some x := by
      have ht : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]?
          = (blockRulePrefFvs p.toBlockShape rs c)[k]? := by
        rw [List.getElem?_take, if_pos hk]
      rw [← ht]; exact hx
    obtain ⟨ty, hty'⟩ := hidxPref k x hx'
    exact ⟨ty, by rw [hty', Nat.zero_add]⟩
  have hspP := denoteMetaSpine_params (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.rulePrefixAt c + cA.2) hlenTake hidxTake
  have hspF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.rulePrefixAt c + cA.2) (blockRuleFieldFvs p.toBlockShape rs c i)
    (p.toBlockShape.rulePrefixAt c) hidxF
  have hmk0 := denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hspP hspF)
  have hmkE : blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = AnnotTerm.mkAppN (mpC.base2.acval cA.1.name
          (Level.substFn ψ p.lps (p.lps.map Level.param)))
          (paramBvarsAt p.nP (p.toBlockShape.rulePrefixAt c + cA.2)
            ++ (List.range (blockRuleFieldFvs p.toBlockShape rs c i).length).map
              fun k => .bvar (p.toBlockShape.rulePrefixAt c + cA.2 - 1
                - (p.toBlockShape.rulePrefixAt c + k))) := by
    rw [blockRuleMkAV, hct]
    exact congrArg (·.getD default) hmk0
  rw [← hmkE] at hmk0
  have hmkK0 : blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i
      = blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i := by
    rw [blockRecMkK]; exact AnnotTerm.liftN_zero _ _
  -- the spine's scoping at the rule frame
  have hwMk : Expr.WScoped (p.toBlockShape.rulePrefixAt c + cA.2)
      (Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
        ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
          ++ blockRuleFieldFvs p.toBlockShape rs c i)) := by
    refine Expr.WScoped.mkAppN (by simp [Expr.WScoped]) fun x hx => ?_
    rcases List.mem_append.mp hx with hx' | hx'
    · exact Expr.WScoped.mono (Nat.le_add_right _ _) (hwPref x (List.mem_of_mem_take hx'))
    · exact hwF x hx'
  have hwEs : ∀ a ∈ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP,
      Expr.WScoped (p.toBlockShape.rulePrefixAt c + cA.2) a :=
    fun a ha => Expr.WScoped.getAppArgs hwCb a (List.mem_of_mem_drop ha)
  -- the whole spine, one frame deeper
  have hsp : DenoteMetaSpine mpC.base2.acval envC ψ
      (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
      (blockRulePrefFvs p.toBlockShape rs c
        ++ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP
        ++ [Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
            ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
              ++ blockRuleFieldFvs p.toBlockShape rs c i)])
      (paramBvarsAt (p.toBlockShape.rulePrefixAt c) (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
        ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).map (·.liftN nR 0)
        ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).liftN nR 0]) := by
    refine DenoteMetaSpine.append (DenoteMetaSpine.append
      (denoteMetaSpine_prefFvs hopPref hlenPref) ?_) ?_
    · rw [hesK0, hesE]
      exact DenoteMetaSpine.liftDepth hacl nR hspEs hwEs
    · rw [hmkK0]
      exact DenoteMetaSpine.liftDepth hacl nR (.cons hmk0 .nil)
        (fun a ha => by rw [List.mem_singleton.mp ha]; exact hwMk)
  -- the scoping and closedness of the arguments
  have ha : ∀ a ∈ blockRulePrefFvs p.toBlockShape rs c
        ++ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP
        ++ [Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
            ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
              ++ blockRuleFieldFvs p.toBlockShape rs c i)],
      Expr.WScoped (p.toBlockShape.rulePrefixAt c + cA.2 + nR) a
        ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ⟨Expr.WScoped.mono (by omega) (hwPref a ha''),
          openPisAtFvars_fvars_closed hopPref a ha''⟩
      · exact ⟨Expr.WScoped.mono (Nat.le_add_right _ _) (hwEs a ha''),
          ConLeche.looseBVarsBounded_getAppArgs hbCb a (List.mem_of_mem_drop ha'')⟩
    · rw [List.mem_singleton] at ha'
      subst ha'
      refine ⟨Expr.WScoped.mono (Nat.le_add_right _ _) hwMk,
        ConLeche.looseBVarsBounded_mkAppN rfl (fun x hx => ?_)⟩
      rcases List.mem_append.mp hx with hx' | hx'
      · exact openPisAtFvars_fvars_closed hopPref x (List.mem_of_mem_take hx')
      · exact openPisAtFvars_fvars_closed hopF x hx'
  -- the recursor type, read at the deep frame
  obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  have htyD : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
      r.1.type = some (blockRecTyAV mpC.base2.acval envC rs ψ c) :=
    denoteMeta_depth_of_closed hacl hf₁
      (fun k => denoteMeta_closed mpC.base2.acval_erase mpC.base2.cval_closed hf₁ hb₁ hread 1 k)
      hread _
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAtLift_peel hacl (acval_inst_self mpC.base2)
    _ hpr (Expr.WScoped.mono (Nat.zero_le _) hw₁) ha htyD hsp
  have hE : blockRuleConclExpr p rs c i = concl0 := by
    rw [blockRuleConclExpr, hct, hty, hpr]; rfl
  have hCa : (denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + nR)
      (blockRuleConclExpr p rs c i)).getD default = restA := by
    rw [hE, hrest]; rfl
  refine ⟨fun concl hpr' => ?_, by rw [hCa]; exact hpeel⟩
  obtain rfl : concl = concl0 := Option.some.inj (hpr'.symm.trans hpr)
  rw [hrest, ← hCa]

end CaRun

end ConLeche.Model
