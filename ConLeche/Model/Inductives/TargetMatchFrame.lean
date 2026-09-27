module

public import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetDefeqTie
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.ClassMatchRun

public section

/-!
# A class match's frame at the recursor's prefix

The class tie at a node (`tgtNodeTie`) reads an outside class's frame —
its major's parameters read at the rule prefix — as the node's.  The
recursor check matched the class against the node's key read back per
component (`ClassMatches`); this module turns that run into the frame
equation (`NodeFrameTie`): at any prefix spine the class is guarded at,
the recursor's prefix walk context (`tgtPrefix_walk`, the prefix alone,
no constructor fields) with the members' own values at the holes makes
every matched parameter pair read alike (`params_read_eq`).

* `tgtPrefix_walk` — a recursor's prefix walk context at a spine
  fitting its prefix domains;
* `tgtMatch_frame` — a matched class reads its parameters as the
  matched instantiation's;
* `nodeFrameTie_of` — the frame half of the node tie, at every listed
  node.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape NestCtx PosTree)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A major's parameter openers are its recursor's prefix openers.** -/
theorem tyEntry_pfvs {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    M.pfvs = E.fvs.take rc.rP := by
  obtain ⟨_, fvs, concl, _, _, maj, _, _, _, hroom, hle, hopen, _, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  cases major <;> rfl

section Prefix

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- **A recursor's PREFIX walk context** at any spine fitting its prefix
domains (`tgtFrame_walk` with no constructor fields). -/
theorem tgtPrefix_walk (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    (ψ : Name → Nat) {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars (pp.toBlockShape.rulePrefixAt c) r.1.type 0 = some (fvs, o))
    {ρ : Nat → V} {xs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c) xs) :
    FvarList fvs.length fvs.reverse ∧
      WalkCtx V mpC.base2 ψ fvs.length (consList xs ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c).reverse fvs.reverse := by
  have hlen : fvs.length = pp.toBlockShape.rulePrefixAt c :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨hTf, -, hTres, hTb, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound envC r.1.type := constsBound_of_constsResolve _ hTres
  have hcr : ConLeche.instPisWith [] (Expr.sort .zero) = some (Expr.sort .zero) := rfl
  have h₂ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (pp.toBlockShape.rulePrefixAt c)
      = some ([], Expr.sort .zero) := rfl
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts (envT := envC) hop hcr
    (fun a ha => nomatch ha) h₂ hTf hTb hTc rfl rfl (by simp)
  simp only [List.append_nil, Nat.add_zero] at hFr hlbF hcbF hher
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c).length
      = pp.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hdoms := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := envC) (ψ := ψ)
    (fdoms := []) (ihdoms := []) (fvsF := []) (fvsIh := []) hpl rfl rfl hlen rfl rfl
    (blockRulePdomsAV_reads hμ mpC h hr ψ hop) (fun l x hx => nomatch hx)
    (fun l x hx => nomatch hx)
  have hok := blockRulePdomsAV_graded hμ mpC h hr ψ
  have hokΔ := blockRuleHokΔ_of (V := V) (fdoms := []) (ihdoms := []) hpl rfl rfl
    (fun l hl σ' ys hys => by
      have := hok l (by simpa using hl) σ' ys (by simpa using hys)
      simpa using this)
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (pp.toBlockShape.rulePrefixAt c + 0)
      = some ([], Expr.sort .zero) := rfl
  have hW := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := [])
    (ihvals := []) (fdoms := []) (fs := []) hop h₂ h₃ hpl rfl rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher)
    (by simpa using hsp) (by simp [SpineFit])
  rw [hlen]
  exact ⟨hFr, by simpa using hW⟩

end Prefix

section Match

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}

set_option maxHeartbeats 4000000 in
/-- **A matched class reads its parameters as the matched
instantiation's** at every prefix spine it is guarded at. -/
theorem tgtMatch_frame (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas) (ψ : Name → Nat) (ρ : Nat → V)
    {c : Nat} (hc : c < (tgtRs out).length) {lvls : List Level} {eds : List Expr}
    (hCM : ClassMatches F envC pp.toBlockShape (cvTas.map (·.type)) (tgtMajor out c) lvls eds)
    {xs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs) :
    (tgtMajor out c).ds.map (fun x => interp V (consList xs ρ)
        ((denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) x).getD default))
      = eds.map (fun x => interp V (consList xs ρ)
        ((denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) x).getD default)) := by
  obtain rfl := CheckMode.eq_verified hμ
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨rc, uE, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hrP : pp.toBlockShape.rulePrefixAt c = rc.rP := by
    rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hRP : tgtRP pp.toBlockShape c = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨o, hop⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) _ 0
    (by have := E.hle; omega) E.hopen
  have hpf := tyEntry_pfvs E
  have hlp : (E.fvs.take rc.rP).length = rc.rP := by
    have := ConLeche.Verify.openPisAtFvars_length _ hop
    exact this
  obtain ⟨hL, hW⟩ := tgtPrefix_walk (mpC := mpC) rfl h ψ hr (by rw [hrP]; exact hop) hsp
  rw [hlp] at hL hW
  -- the holes at the members' own values
  let hv : List V := (List.range cvTas.length).map fun t =>
    interp V ρ (mpC.base2.acval (d.memberName t) ψ)
  have hvl : hv.length = (cvTas.map (·.type)).length := by simp [hv]
  have hvget : ∀ t, t < cvTas.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ) := by
    intro t ht; simp [hv, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  have hnames := memberHoles_names (pp := pp) hN hmr ψ ρ (hvC := fun t => hv.getD t pt) hvget
  have hformer := memberHoles_formers (mpC := mpC) hmr ψ ρ (memberHoles_ty hmr ψ ρ hvget)
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨-, hPD⟩ := ConLeche.targetClassMatch_true hCM
  rw [hpf, hlp] at hPD
  have hr' := params_read_eq (μ := .verified) rfl hacl (Rules.RulesInputs.ofSem mpC ψ)
    (pfvs := E.fvs.take rc.rP) hL hW hvl hformer hnames hPD
  rw [hRP]
  exact hr'

/-- **The frame half of the node tie** (`NodeFrameTie`) at any node
list: a class matching a node's key read back reads as it. -/
theorem nodeFrameTie_of (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas) (ctx : NestCtx) (ns : List PosTree)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    NodeFrameTie mpC.base2.acval ctx pp.toBlockShape out ns ψ ρ xs envC F (cvTas.map (·.type)) :=
  fun _ hc _ _ hNM hg => tgtMatch_frame hμ h R hN hmr ψ ρ hc hNM.2.2 hg

end Match

end ConLeche.Model
