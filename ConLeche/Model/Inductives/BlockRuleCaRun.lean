module

import ConLeche.Model.Inductives.BlockRuleFit
public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.FixAssemblyKit

public section

/-!
# The rule's CONCLUSION `Ca`, pinned — and the kit arms' `hCaB`

`BlockRuleCerts` carries the rule's conclusion `Ca` as the reading of
an EXISTENTIAL `concl` (`denoteMeta … concl = some Ca`), and every
consumer that evaluates `Ca` — the kit arms' `hCaB`, the IND arm's
`hCaE` through `blockIndCaE_of_run` (`blockIndRuleRows_run`) — needs it as
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
kit's step (`blockWfKit`'s `hst`, and the SQ kit's) has it (`hi`, off
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

/-- **`Ca`, PINNED** — the conclusion read at the whole rule frame
(the prefix, the fields and the `ih` openers). -/
@[expose] def blockRuleCaAV (c i : Nat) : AnnotTerm :=
  (denoteMeta acval envC ψ
    (pp.toBlockShape.rulePrefixAt c + (blockRuleCtorOf rs c i).2
      + (blockRuleFrameAt pp rs c i).nR)
    (blockRuleConclExpr pp rs c i)).getD default

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

/-- **The pinned `Ca` at the run.**  (i) Whatever `concl` the rule's
check produced (`blockRuleResidueData_runP`'s `instPisAtLift` row), it
reads at the whole rule frame to `blockRuleCaAV` — the `hCa` premise of
`blockRuleCerts_of_run`, verbatim.  (ii) `blockRuleCaAV` is the peel of
the recursor type's reading along the rule's spine, the index arguments
and the fired spine being the rule-frame readings (`blockRecEsK 0`,
`blockRecMkK 0`) lifted past the `ih` block — the `hcon`/`hmkL`/`hesL`
triple of `blockIndCaE_of_run`.

The inputs are the run and the constructor's reading record (`hcd`,
out of `BlockCtorsCore`), the constructor's stored level parameters and
its type's closedness — the same inputs as `blockRuleEsAV_eq` /
`blockRuleMkAV_eq`, whose readings these are one frame deeper. -/
theorem blockRuleCaAV_run (hμ : μ.verifiedChecks = true)
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
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    (∀ concl : Expr,
      ConLeche.Expr.instPisAtLift
          (blockRulePrefFvs p.toBlockShape rs c
            ++ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP
            ++ [Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
                ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
                  ++ blockRuleFieldFvs p.toBlockShape rs c i)]) r.1.type = some concl →
      denoteMeta mpC.base2.acval envC ψ
          (p.toBlockShape.rulePrefixAt c + cA.2 + (blockRuleFrameAt p rs c i).nR) concl
        = some (blockRuleCaAV p rs mpC.base2.acval envC ψ c i)) ∧
    BlockRuleConclAt (p.toBlockShape.rulePrefixAt c) cA.2 (blockRuleFrameAt p rs c i).nR
      (blockRecTyAV mpC.base2.acval envC rs ψ c)
      ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (·.liftN (blockRuleFrameAt p rs c i).nR 0))
      ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).liftN
        (blockRuleFrameAt p rs c i).nR 0)
      (blockRuleCaAV p rs mpC.base2.acval envC ψ c i) := by
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
  generalize hnR : (blockRuleFrameAt p rs c i).nR = nR
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
  have hCa : blockRuleCaAV p rs mpC.base2.acval envC ψ c i = restA := by
    rw [blockRuleCaAV, hct, hnR, hE, hrest]; rfl
  refine ⟨fun concl hpr' => ?_, by rw [hCa]; exact hpeel⟩
  obtain rfl : concl = concl0 := Option.some.inj (hpr'.symm.trans hpr)
  rw [hrest, hCa]

/-! ## 4. The per-pair data, at the block datum

The IND arm's `hCaE` (`blockIndRuleRows_run`) and the kit arms' `hCaB`
read the same per-(recursor, constructor) facts: the rule's constructor
IS the member's `j`-th (the counting stage's `hctM`), its record, and the
pinned `Ca`'s peel.  They are named once here. -/

variable {d : BlockData V}

/-- **One pair's data**, at the run and the block datum: every per-rule
input of `blockIndCaE_of_run` at the pinned `Ca` (`blockRuleCaAV`), the
pinned `ih` domains (`blockRecIhdomsK`) and the frame's `nR`, the rule
index being the constructor's own, plus the two facts `hCaB` also needs
(the member is a component, the recursor's binder data is as long as
its prefix, indices and major). -/
theorem blockRuleCaAV_pair (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
      (cA : ConstantVal × Nat) (rhs : Expr) (ci : ConstantInfo),
      rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs ∧
      envC.find? cA.1.name = some ci ∧ ci.toConstantVal.levelParams = p.lps ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt c ∧
      (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA ∧
      j < (d.ctorsM (p.toBlockShape.recTgtAt c)).length ∧
      BlockRuleConclAt (p.toBlockShape.rulePrefixAt c) cA.2 (blockRuleFrameAt p rs c j).nR
        (blockRecTyAV mpC.base2.acval envC rs ψ c)
        ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
          (·.liftN (blockRuleFrameAt p rs c j).nR 0))
        ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
          (blockRuleFrameAt p rs c j).nR 0)
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j) ∧
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
            (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) ∧
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        = p.toBlockShape.rulePrefixAt c ∧
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 ∧
      (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
        = (blockRuleFrameAt p rs c j).nR ∧
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 ∧
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        = p.toBlockShape.rulePrefixAt c + (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length + 1 ∧
      p.toBlockShape.recTgtAt c < d.N := by
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hcj : (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    rw [hctM c _ hr]; exact hcA
  obtain ⟨hnPle, hmemk, hmI, hlenRds, -⟩ := blockRecMajor_run (V := V) hμ mpC h hmr hr ψ
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c := by rw [← hdnP]; exact hnPle
  have hcdP := hcd
  rw [hdnP] at hcdP
  obtain ⟨-, hcon⟩ := blockRuleCaAV_run hμ h hr hcA hrhs hcdP hCf hCb hfindC hlpsC hnP ψ
  -- the lengths
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ hopF]
  obtain ⟨-, -, -, -, -, -, hopIh, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  have hih : (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRecIhdomsK, liftDomsK_length, blockRuleIhdomsAV, readOpenedDoms_length_eq,
      blockRuleFvsIhAt]
    have := openPisAtFvars_length _ hopIh
    rw [blockRuleIhOpenAt, hct, hopIh]
    exact this
  have hFssLen : ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 := by
    have hFssD : (d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []
        = ((d.dsF (p.toBlockShape.recTgtAt c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    omega
  have hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) := by
    rw [blockRuleEsAV_eq h hr hcA hrhs hcdP hCf hnP ψ, hdnP, BlockData.Ess, BlockData.cds,
      essOfR_fixCtorDataList_getD hcj]
  refine ⟨rs[c], cA, rhs, _, hr, hcA, hrhs, hfindC, hlpsC, hnP, hcj,
    (List.getElem?_eq_some_iff.mp hcj).1, hcon, hes, blockRulePdomsAV_length hμ mpC h hr ψ,
    hfl, hih, hFssLen, ?_, Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)⟩
  rw [hlenRds, hmI, blockMembers_IdsM_length hmr hmemk ψ]

/-! ## 5. The kit arms' `hCaB`, at the NARROWED row

The row asks, at a prefix `x⃗` fitting the parameters and the rule's
prefix and a field spine `f⃗` whose `ChainFit` at the fixpoint carries
the tuple `i`, that the rule's conclusion read at the rule's frame (the
`ih` values whatever they are, as long as there are `nR` of them) be
the kit's motive at the constructed element.  With `i` in the member's
index set (the narrowing), `i` IS the tuple of an index spine `ı⃗`
(`mem_idxSet_elim`), the field spine fits the constructor's own field
domains (`blockRecSpF_base`, through the slot agreement), and §29b's
`blockIndCaE_of_run` evaluates `Ca`; the motive decodes `ı⃗` back out of
its tuple (`isOfW_tupW`).  The generic form is at any class count `K`
with `c < K` (WF: `K = rs.length`; SQ: `K = 1`). -/

/-- **`hCaB`, generic in the class count.** -/
theorem blockKitCaB_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {names : List Name} (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (ρ : Nat → V) {ihv : List V → Nat → Nat → List V → V → List V}
    (hihl : ∀ xs c j fs g, (ihv xs c j fs g).length = (blockRuleFrameAt p rs c j).nR)
    {K : Nat} :
    ∀ xs : List V, ∀ c, c < K → c < rs.length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      ∀ j, j < blockRecNCt rs c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (p.toBlockShape.recTgtAt c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ))
          (blockRuleCaAV p rs mpC.base2.acval envC ψ c j)
        = blockRecMot K (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
            (fun c' => d.uM (p.toBlockShape.recTgtAt c') ψ)
            (fun c' => d.nIdxAt (p.toBlockShape.recTgtAt c')) ρ xs
            (tagged c i (d.inj ψ (p.toBlockShape.recTgtAt c) j fs)) := by
  intro xs c hcK hc hps hpref j hj i fs hi hfit g
  obtain ⟨r, cA, rhs, ci, hr, hcA, hrhs, hfind, hlps, hnP, hcj, hjc, hcon, hes, hpl, hfl, -,
    -, hrds, hmemN⟩ := blockRuleCaAV_pair hμ h hkLen hcore hmr hdnP hctM ψ hc hj
  obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run (V := V) hμ mpC h hmr hr ψ
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ j cA hcj
  -- the tuple is an index spine's
  obtain ⟨is, hIs, rfl⟩ := mem_idxSet_elim hi
  -- the field spine fits the constructor's own field domains
  have hxs : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hasLen : (xs.take d.nP).length = d.nP := by
    rw [List.length_take, hxs, hdnP]; omega
  have hfd := blockRuleFdomsAV_datum h hr hcA hrhs hcore hmemk hcj hnP hdnP ψ
  have hq := blockRecSpF_base (mem := p.toBlockShape.recTgtAt) hM hμ h hr hcj
    ⟨hfindC, hlpsC, hcd⟩ hfd hasLen hps (fun l _ => by rw [← hN.2.2.2]; exact hN.2.1 _ j l)
    hmemN hjc hi (lfpTuple_mem _ _ _ _) hxs hpref hfit
  obtain ⟨xs', fs', heq, hxs', hfs'⟩ := spineFit_append_inv hq
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hxs'.length_eq, hpref.length_eq])
  have hod : (xs.drop d.nP).length = p.toBlockShape.rulePrefixAt c - d.nP := by
    rw [List.length_drop, hxs]
  have hsf : SpineFit (consList (xs.take d.nP) ρ)
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) fs := by
    have hq' := (spineFit_liftDomsK_insert (us := xs.drop d.nP)
      (ρ := consList (xs.take d.nP) ρ) ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) [] fs)
    rw [List.length_nil, hod, consList_nil, consList_nil, ← consList_append,
      List.take_append_drop, ← hfd] at hq'
    exact hq'.mp hfs'
  have hfsl : fs.length = cA.2 := by rw [hfs'.length_eq, hfl]
  -- the conclusion, evaluated (§29b)
  have hCaE := blockIndCaE_of_run hμ hM h hr hcA hrhs hfind hlps hnP hdnP hmemN hcj hjc ψ
    hcon rfl rfl hes hpl hfl hrds rfl hxs hfsl (hihl xs c j fs g) hps hsf hIs hfit rfl
  rw [hCaE, blockRecMot_tagged hcK]
  have hIdx := hM.idxOk ψ _ (d.satOfSpine hps) _ hmemN
  have hret : isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ) (d.nIdxAt (p.toBlockShape.recTgtAt c))
      (tupW (d.uM (p.toBlockShape.recTgtAt c) ψ) is) = is := by
    rw [← blockMembers_IdsM_length hmr hmemk ψ]
    exact isOfW_tupW hIdx hIs
  rw [hret, List.append_assoc]

/-- **REGIME WF's `hCaB`, PRODUCED** — `BlockWfOwed`'s row at the
pinned `Ca`, narrowed by the class index `i ∈ d.idx …`. -/
theorem blockWfCaB_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {names : List Name} (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (ρ : Nat → V) {ihv : List V → Nat → Nat → List V → V → List V}
    (hihl : ∀ xs c j fs g, (ihv xs c j fs g).length = (blockRuleFrameAt p rs c j).nR) :
    ∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) ((p.toBlockShape.recTgtAt) c) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ))
            ((fun c j => blockRuleCaAV p rs mpC.base2.acval envC ψ c j) c j)
          = blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt
            ((p.toBlockShape.recTgtAt) c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) :=
  fun xs c hc => blockKitCaB_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ ρ hihl xs c hc hc

/-- **REGIME SQ's `hCaB`, PRODUCED** — `BlockSqOwed`'s row (`c < 1`,
`K = 1`) at the pinned `Ca`, narrowed by the class index. -/
theorem blockSqCaB_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {names : List Name} (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (hpos : 0 < rs.length)
    (ψ : Name → Nat) (ρ : Nat → V) {ihv : List V → Nat → Nat → List V → V → List V}
    (hihl : ∀ xs c j fs g, (ihv xs c j fs g).length = (blockRuleFrameAt p rs c j).nR) :
    ∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) ((p.toBlockShape.recTgtAt) c) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ))
            ((fun c j => blockRuleCaAV p rs mpC.base2.acval envC ψ c j) c j)
          = blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun c' =>
            d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt)
            c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) :=
  fun xs c hc => blockKitCaB_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ ρ hihl xs c hc
    (by omega)

end CaRun

end ConLeche.Model
