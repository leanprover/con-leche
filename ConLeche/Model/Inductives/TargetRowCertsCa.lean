module

public import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockLfpHoles

public section

/-!
# The rule's conclusion read at ANY depth past the fields (lane RECLIB)

`blockRuleCaAV_run` (`BlockRuleCaRun.lean`) at an arbitrary width `nR`
of the block between the fields and the conclusion: the target check's
`ih` block (`tgtCaAV`) is read at its own width, not the frame's `nR`.
The proof is `blockRuleCaAV_run`'s, which uses `nR` only as a depth.

Likewise `blockRuleConclFit_run`/`blockRuleConclArgs_run`
(`BlockRuleCertsRun.lean`, `hokC`'s fit and arguments) at an arbitrary
`ih` block `I`: they read today's `ih` domains only through their
length.
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

section ConclW

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **The rule's conclusion FITS the recursor's tower** at every frame
satisfying the rule's context: the peel's arguments — the prefix
bvars, the constructor's result index readings and the fired spine,
each lifted past the `ih` block — read along the recursor type's
Π-tower.  It is `blockRuleCerts_of_run`'s `hfit`, at the peel's own argument
list. -/
theorem blockRuleConclFitW_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c)
    (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∃ rest, TeleFitPA V σ (blockRecTyAV mpC.base2.acval envC rs ψ c)
        (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + I.length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN I.length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              I.length 0]) rest := by
  intro σ hsat
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hfl : fs.length = (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length :=
    hfs.length_eq
  have hwl : ws.length = I.length :=
    hws.length_eq
  -- the kit's fired-spine fit, at `K = 0`
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  have hfire := blockKitRule_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ 0 (fun _ => pt) σ₀
    c hc j hj xs fs hxl hsp0
  rw [chainFrame_zero] at hfire
  -- the recursor's tower, and its binder data's bounds
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  obtain ⟨hbndR, -⟩ := checkBlockRecK_tyBounds hμ mpC h hr ψ
  -- the argument list reads to the fired spine's values
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hpb : (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + I.length)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀)) = xs := by
    have hLlen : (xs ++ fs ++ ws).length
        = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + I.length := by
      rw [List.length_append, List.length_append, hxl, hfl, hwl]
    rw [map_bvarAt_take (nP := (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
      hLlen.symm (by rw [hLlen]; omega), List.append_assoc, List.take_left' hxl]
  have hes : ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (·.liftN I.length 0)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀))
      = (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (interp V (consList (xs ++ fs) σ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show interp V (consList (xs ++ fs ++ ws) σ₀)
      (e.liftN I.length 0) = _
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals e
  have hmk : interp V (consList (xs ++ fs ++ ws) σ₀)
        ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
          I.length 0)
      = interp V (consList (xs ++ fs) σ₀)
          (blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) := by
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals _
  -- the tower's binder data is closed below its own entries, so the fit
  -- moves from the base frame to the context's
  have hbnd : ∀ l, l < ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (fun b : Nat × Nat × AnnotTerm => b.2.2)).length →
      Term.bvarsBelow l ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (fun b : Nat × Nat × AnnotTerm => b.2.2)).getD l default).erase) := by
    intro l hl
    rw [List.length_map] at hl
    have hq := hbndR l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hq
    exact hq
  have hfitσ := spineFit_frame_of_bounded (σ' := consList (xs ++ fs ++ ws) σ₀) hbnd hfire
  rw [hTyE]
  refine teleFitPA_mkPisAV_of_spineFit ?_ ?_
  · have hq := hfire.length_eq
    simp only [List.length_map, List.length_append, List.length_singleton] at hq
    simp only [List.length_append, List.length_map, paramBvarsAt_length, List.length_singleton]
    omega
  · rw [List.map_append, List.map_append, hpb, hes, List.map_cons, List.map_nil, hmk]
    rw [← List.append_assoc] at hfitσ
    exact hfitσ




/-- **The rule conclusion's peel arguments are graded** at every frame
satisfying the rule's context — `blockRuleCerts_of_run`'s `hargs`, at
the argument list `blockRuleConclFit_run` fits.  The prefix entries are
bound variables; an index reading is the constructor's own
(`blockRuleSpine_peel`'s `es0`), graded at the constructor's field frame
(`blockCtorEs_wdV`) and lifted twice; the fired spine is graded at the
rule's base frame (`blockRuleMkAV_wdV`).  The `ih` block is lifted over
(`WellDenotedV_liftN`, `shiftE_consList_ih`). -/
theorem blockRuleConclArgsW_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c)
    (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∀ a ∈ paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + I.length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN I.length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              I.length 0],
        WellDenotedV V σ a := by
  intro σ hsat
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, -⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hwl : ws.length = I.length :=
    hws.length_eq
  -- the rule's own spine, peeled to the constructor's datum (at `K = 0`)
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, -, hpre, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxl hsp0
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 :=
    blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ
  -- the constructor's parameter fit (the hop through the member's former)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hcvTa := TE.hcvTa
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk j cA hcj).1 ψ
  have hcd := hcf.2.2
  have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.len ψ) hframes (spineFit_take_any hpre p.nP)
  -- the frame, with the `ih` block on top
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hdrop : ∀ e : AnnotTerm,
      WellDenotedV V (consList (xs ++ fs ++ ws) σ₀)
          (e.liftN I.length 0)
        ↔ WellDenotedV V (consList (xs ++ fs) σ₀) e := by
    intro e
    rw [WellDenotedV_liftN, hframe, ← hwl,
      show consList ws (consList (xs ++ fs) σ₀)
        = consList ([] : List V) (consList ws (consList (xs ++ fs) σ₀)) from rfl,
      shiftE_consList_ih (d := 0) (locals := ([] : List V)) (ihvals := ws) rfl rfl]
    rfl
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · -- a prefix variable
      simp only [paramBvarsAt, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      exact ⟨trivial, trivial⟩
    · -- an index reading, lifted past the fields' cutoff and the `ih` block
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [hdrop]
      rw [blockRecEsK] at he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      rw [hes] at he'
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he'
      rw [hpl, hfl]
      exact (wellDenotedV_liftN_rule (K := 0) (a := fun _ => (pt : V)) hxs' hfsl E).mpr
        (blockCtorEs_wdV hcf hcj hpc hfb E hE)
  · -- the fired constructor application
    rw [List.mem_singleton] at ha
    rw [ha, hdrop, blockRecMkK, AnnotTerm.liftN_zero]
    exact blockRuleMkAV_wdV h hr hcA hrhs hcf hcj rfl hnP hxs' hfsl hpc hfb

end ConclW

end ConLeche.Model
