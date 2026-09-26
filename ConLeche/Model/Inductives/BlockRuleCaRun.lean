module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Annot.BitInst

public section

/-!
# The rule's CONCLUSION `Ca`, pinned — and the graph kit's `hCaB`

`BlockRuleCerts` carries the rule's conclusion `Ca` as the reading of
an EXISTENTIAL `concl` (`denoteMeta … concl = some Ca`), and every
consumer that evaluates `Ca` — the graph kit's `hCaB`, through
`blockIndCaE_of_run` — needs it as
`BlockRuleConclAt`: the recursor type's reading peeled along the rule's
spine.  So one `Ca` per rule has to be chosen, and both sides stated
at it.

`checkBlockRule` DOES compute it: the conclusion the residue is
compared against is `instPisAtLift` of the recursor's stored type at
the prefix openers, the constructor's result index arguments and the
fired major (`blockRuleResidueData_runP`'s `concl`), and every input is
a §A.9b definition of the run.  So `Ca` is DEFINED here
(`blockRuleCaAV`, the reading of that `concl` at the whole rule frame),
and the run proves:

* `blockRuleCaAV_reads` — the reading exists and IS the definition:
  exactly `blockRuleCerts_of_run`'s `hCa` premise, so the certificate
  bundle is stated at this `Ca`;
* `blockRuleCaAV_conclAt` — `BlockRuleConclAt` at the run's own
  components (`hcon`/`hmkL`/`hesL` of `blockIndCaE_of_run`): the index
  arguments and the fired spine read,
  at the deeper frame, to the rule-frame readings lifted past the `ih`
  block (`denoteMeta_lift`).

**`hCaB` is narrowed to `i ∈ d.idx …`**: a `ChainFit` at the fixpoint
for an ARBITRARY `i : V` is not enough.  Evaluating `Ca`
needs the fired spine's value (`blockRecMkK_value`) and the index
readings' values (`blockRecEsK_eq_is`), and both need the FIELD fit
`SpineFit … Fss fs`, which a `ChainFit` gives only through the slot
agreement (`blockSlot_agree`) — whose witness is `i ∈ d.idx …`.  The
kit's typing (`blockGraphKit`'s `hst`) has it (the decoding's `i`, off
`blockRecIs_pos`), exactly as for `hspF`.  The producers below are
stated at the narrowed row.
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

/-! ## 1. `Ca`, pinned -/

section CaDef

variable (pp : ConLeche.BlockParts)
  (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))

/-- The checker's rule CONCLUSION: the recursor's stored type
instantiated at the prefix openers, the constructor's result index
arguments and the fired major (`checkBlockRule`'s `instPisAtLift`). -/
@[expose] def blockRuleConclExpr (c i : Nat) : Expr :=
  (ConLeche.Expr.instPisAtLift
    (blockRulePrefFvs pp.toBlockShape rs c
      ++ (blockRuleCbody pp.toBlockShape rs c i).getAppArgs.drop pp.nP
      ++ [Expr.mkAppN (.const (blockRuleCtorOf rs c i).1.name (pp.toBlockShape.lps.map .param))
          ((blockRulePrefFvs pp.toBlockShape rs c).take pp.nP
            ++ blockRuleFieldFvs pp.toBlockShape rs c i)])
    (blockRuleRecTy rs c)).getD default

variable (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ψ : Name → Nat)

end CaDef

/-! ## 2. The conclusion's spine, read -/

section Spine

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

omit [SetTheory V] in
/-- An application spine's arguments read wherever the application
does. -/
theorem denoteMetaSpine_getAppArgs {d : Nat} :
    ∀ {e : Expr} {v : AnnotTerm}, denoteMeta acval env φ d e = some v →
      ∃ vs, DenoteMetaSpine acval env φ d e.getAppArgs vs
  | .app f a, v, h => by
    obtain ⟨fa, aa, hf, ha, -⟩ := denoteMeta_app_inv h
    obtain ⟨vs, hvs⟩ := denoteMetaSpine_getAppArgs hf
    exact ⟨vs ++ [aa], hvs.append (.cons ha .nil)⟩
  | .bvar _, _, _ => ⟨[], .nil⟩
  | .fvar _ _, _, _ => ⟨[], .nil⟩
  | .sort _, _, _ => ⟨[], .nil⟩
  | .const _ _, _, _ => ⟨[], .nil⟩
  | .lam _ _ _, _, _ => ⟨[], .nil⟩
  | .forallE _ _ _, _, _ => ⟨[], .nil⟩
  | .letE _ _ _, _, _ => ⟨[], .nil⟩
  | .lit _, _, _ => ⟨[], .nil⟩
  | .proj _ _ _, _, _ => ⟨[], .nil⟩

omit [SetTheory V] in
/-- A read spine of expressions scoped at `D₀` reads, `n` binders
deeper, to its readings lifted by `n` at cutoff `0` (`denoteMeta_lift`,
entry by entry). -/
theorem DenoteMetaSpine.liftDepth
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {D₀ : Nat} (n : Nat) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ D₀ as vs →
      (∀ a ∈ as, Expr.WScoped D₀ a) →
      DenoteMetaSpine acval env φ (D₀ + n) as (vs.map (AnnotTerm.liftN n · 0))
  | _, _, .nil, _ => .nil
  | a :: _, _, .cons ha htl, hw => by
    refine .cons ?_ (DenoteMetaSpine.liftDepth hacl n htl fun x hx =>
      hw x (List.mem_cons_of_mem _ hx))
    rw [denoteMeta_lift hacl (hw a List.mem_cons_self) (D₀ + n) (Nat.le_add_right _ _), ha,
      Nat.add_sub_cancel_left]
    rfl

end Spine

/-! ## 3. `Ca` at the run: its reading, and its peel -/

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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
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
    blockRuleData_run (hm := hm) h hr hcA hrhs
  obtain ⟨concl0, hpr⟩ := blockRuleConcl_run (hm := hm) h hr hcA hrhs
  obtain ⟨hw₁, hb₁⟩ := recStage_tyClosed h hr
  have hf₁ : r.1.type.hasFvar = false :=
    (ConLeche.recStage_facts h _ (List.mem_of_getElem? hr)).1
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
  -- the constructor's body READS at the rule frame (`blockRuleCtorShift`)
  have hvcb := (blockRuleCtorShift h hm hr hcA hrhs hcd hCf hnP ψ).2.1
  obtain ⟨vsA, hspA⟩ := denoteMetaSpine_getAppArgs hvcb
  have hspEs := hspA.drop p.nP
  -- `es0` IS that spine's reading
  have hesE : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i = vsA.drop p.nP := by
    rw [blockRuleEsAV, hct]
    exact DenoteMetaSpine.getD_eq hspEs
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
  obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
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

/-! ## 4. The per-pair data, at the block datum

The graph kit's `hCaB` reads the per-(recursor, constructor) facts: the rule's constructor
IS the member's `j`-th (the counting stage's `hctM`), its record, and the
pinned `Ca`'s peel, named once here. -/

variable {d : BlockData V}

/-- **One pair's data**, at the run and the block datum: every per-rule
input of `blockIndCaE_of_run` at the pinned `Ca` (`blockRuleCaAV`), the
pinned `ih` domains (`blockRecIhdomsK`) and the frame's `nR`, the rule
index being the constructor's own, plus the two facts `hCaB` also needs
(the member is a component, the recursor's binder data is as long as
its prefix, indices and major). -/
theorem blockRuleCaAV_pair (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      memR c → rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) {c : Nat} (hm : memR c) (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
      (cA : ConstantVal × Nat) (rhs : Expr) (ci : ConstantInfo),
      rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs ∧
      envC.find? cA.1.name = some ci ∧ ci.toConstantVal.levelParams = p.lps ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt c ∧
      (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA ∧
      j < (d.ctorsM (p.toBlockShape.recTgtAt c)).length ∧
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
            (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) ∧
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        = p.toBlockShape.rulePrefixAt c ∧
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 ∧
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 ∧
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        = p.toBlockShape.rulePrefixAt c + (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length + 1 ∧
      p.toBlockShape.recTgtAt c < d.N := by
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  have hcj : (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    rw [hctM c _ hm hr]; exact hcA
  obtain ⟨hnPle, hmemk, hmI, hlenRds, -⟩ := blockRecMajor_run (hm := hm) (V := V) hμ mpC h hmr hr ψ
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c := by rw [← hdnP]; exact hnPle
  have hcdP := hcd
  rw [hdnP] at hcdP
  -- the lengths
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run (hm := hm) h hr hcA hrhs
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ hopF]
  have hFssLen : ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 := by
    have hFssD : (d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []
        = ((d.dsF (p.toBlockShape.recTgtAt c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    omega
  have hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) := by
    rw [blockRuleEsAV_eq (hm := hm) h hr hcA hrhs hcdP hCf hnP ψ, hdnP, BlockData.Ess, BlockData.cds,
      essOfR_fixCtorDataList_getD hcj]
  refine ⟨rs[c], cA, rhs, _, hr, hcA, hrhs, hfindC, hlpsC, hnP, hcj,
    (List.getElem?_eq_some_iff.mp hcj).1, hes, blockRulePdomsAV_length hμ mpC h hr ψ,
    hfl, hFssLen, ?_, Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)⟩
  rw [hlenRds, hmI, blockMembers_IdsM_length hmr hmemk ψ]

/-! ## 5. The graph kit's `hCaB`, at the NARROWED row

The row asks, at a prefix `x⃗` fitting the parameters and the rule's
prefix and a field spine `f⃗` whose `ChainFit` at the fixpoint carries
the tuple `i`, that the rule's conclusion read at the rule's frame (the
`ih` values whatever they are, as long as there are `nR` of them) be
the kit's motive at the constructed element.  With `i` in the member's
index set (the narrowing), `i` IS the tuple of an index spine `ı⃗`
(`mem_idxSet_elim`), the field spine fits the constructor's own field
domains (`blockRecSpF_base`, through the slot agreement), and §29b's
`blockIndCaE_of_run` evaluates `Ca`; the motive decodes `ı⃗` back out of
its tuple (`isOfW_tupW`). -/

end CaRun

end ConLeche.Model
