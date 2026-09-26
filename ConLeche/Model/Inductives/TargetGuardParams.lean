module

public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.DeclNative

public section

/-!
# A class guard fits the block's PARAMETERS (lane NESTIND, session 23)

`tgtClsG` guards recursor class `c` by the prefix fit — and, at a MEMBER
major, by the parameters' fit too.  At an OUTSIDE major the parameters'
fit is not in the guard; it FOLLOWS from the prefix fit, by the kernel's
K6 check in `targetRecTy`: the recursor's first `nP` binder domains are
compared binder by binder with the MAJOR's former's parameter domains —
an outside major's former being the block's FIRST (`cvTas.head?`).  The
hop is `blockRecParams_run`'s forward direction, stated here at any
former `t` of the block (`recParams_fit_former`), and the members'
parameter agreement (`paramsIff`) at `t` closes it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars
  BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The recursor's parameter domains fit the block's, against ANY
former `t` of the block** its first `nP` binder domains were checked
defeq to — `blockRecParams_run`'s forward direction, with the former
(and the recursor type's opening) as data rather than a `RecTyEntry`. -/
theorem recParams_fit_former (hμ : μ.verifiedChecks = true) {envC : Env} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {d : BlockData V} (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {fvs : List Expr} {concl : Expr}
    (hop : openPisAtFvars (p.toBlockShape.majorIdxAt c + 1) r.1.type 0 = some (fvs, concl))
    (hnPle : p.nP ≤ p.toBlockShape.majorIdxAt c)
    {t : Nat} {cvTP : ConstantVal} (hcvT : cvTas[t]? = some cvTP)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTP.type 0 = some (tfvs, trest))
    (hdeq : ∀ l, l < p.nP →
      ConLeche.isDefEqCore μ envC F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
        (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hfit : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take d.nP) xs) :
    SpineFit ρ (d.params ψ) xs := by
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, hparIff⟩ := hmr
  have hmemk : t < d.k := by
    rw [← hlenCv]; exact (List.getElem?_eq_some_iff.mp hcvT).1
  obtain ⟨fvsL, conclL, hopL, hread, hmk, hlenRds, -, hbind, -, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = fvs := congrArg Prod.fst (Option.some.inj (hopL.symm.trans hop))
  rw [hfvE] at hbind
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvT
  have hppsLen : (d.ppsM t ψ).length = d.nP + d.nIdxAt t := hFD.len ψ
  -- the two openings, at the block's parameter count
  obtain ⟨hwA, hbA⟩ := recStage_tyClosed h hr
  obtain ⟨fvsA, fvs', oA, hopA, -, hfvsplit⟩ :=
    openPisAtFvars_split (e := r.1.type) (d := 0) p.nP
      (by rw [show p.nP + (p.toBlockShape.majorIdxAt c + 1 - p.nP)
            = p.toBlockShape.majorIdxAt c + 1 from by omega]
          exact hop)
  have hlenA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hfvsA : fvs.take p.nP = fvsA := by
    rw [hfvsplit, List.take_append_of_le_length (Nat.le_of_eq hlenA.symm),
      List.take_of_length_le (Nat.le_of_eq hlenA)]
  have hdA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
            (·.2.2)).getD i default) := by
    intro i x hx
    have hi : i < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenA] at this; exact this
    have hx' : fvs[i]? = some x := by
      rw [← hfvsA, List.getElem?_take, if_pos hi] at hx
      exact hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbind i x hx'
    rw [hreadD, List.map_take, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi, List.getElem?_map, hpd]
    rfl
  have hokA : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
        p.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ')
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
          (·.2.2)).getD i default) :=
    fun i hi ρ' ys hys => prefixDoms_graded_of_tower (V := V)
      (cc := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (by rw [hlenRds]; omega) (fun ρ'' => by rw [← hmk]; exact hwdTy ρ'') hi hys
  -- the former's side
  obtain ⟨ppsT, bT, hstT, -, -, hbindT⟩ :=
    denoteMeta_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) p.nP hopT (hFD.read ψ)
  have hppsT : ppsT = (d.ppsM t ψ).take p.nP := by
    have := stripPisAV_mkPisAV_take p.nP (d.ppsM t ψ)
      (.sort (d.resSort.eval ψ)) (by rw [hppsLen, hnPq]; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hdB : ∀ (i : Nat) (x : Expr), tfvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((d.ppsM t ψ).take d.nP).map (·.2.2)).getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbindT i x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, hnPq, ← hppsT, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hokB : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((d.ppsM t ψ).take d.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ') ((((d.ppsM t ψ).take d.nP).map (·.2.2)).getD i
        default) := by
    intro i hi ρ' ys hys
    rw [hnPq] at hys ⊢
    exact prefixDoms_graded_of_tower (V := V) (cc := .sort (d.resSort.eval ψ))
      (by rw [hppsLen, hnPq]; omega) (fun ρ'' => hFD.okTy ψ ρ'') hi hys
  have hlenPD : (d.params ψ).length = d.nP := by
    obtain ⟨cvT0, hcvT0⟩ : ∃ cvT0, cvTas[0]? = some cvT0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; omega)⟩
    obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
    rw [BlockData.params, List.length_map, List.length_take, hFD0.len ψ]; omega
  have hlenT : (((d.ppsM t ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, hppsLen]; omega
  -- the certified hop, then the members' parameter agreement at `t`
  have hfitA : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
      p.nP).map (·.2.2)) xs := by
    rw [hnPq] at hfit
    rw [List.map_take]
    exact hfit
  have hfitB := prefixDoms_spineFit (V := V) hμ mpC hopA hopT hwA
    (Expr.WScoped.of_not_hasFvar hfvT) hbA hbndT
    (by rw [List.length_map, List.length_take, hlenRds]; omega)
    (by rw [List.length_map, List.length_take, hppsLen, hnPq]; omega)
    hdA hdB hokA hokB
    (fun l hl => Or.inr (by
      rw [← hfvsA]
      exact hdeq l hl))
    hfitA
  have hsat : Sat V ((((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse) (consList xs ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfitB
  exact spineFit_of_sat_consList (by rw [hfitB.length_eq, hlenT, hlenPD])
    ((hparIff _ hmemk ψ _).mp hsat)

/-- **A class guard fits the block's parameters**: at a member class the
guard says so; at an OUTSIDE class it follows from the prefix fit, by the
kernel's K6 comparison of the recursor's parameter domains with the
block's first former's. -/
theorem tgtGuard_params (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : ConLeche.BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR)
    {c : Nat} (hc : c < (tgtRs out).length) {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    (hg : tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) :
    SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
  unfold tgtClsG at hg
  split at hg
  · exact hg.1
  next hMs =>
  obtain ⟨hRec, -, -, hnames, -, hN, hS, hcore, -, hdR, -⟩ := hctx
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hmr := blockMembersRun_seam hN hS hcore
  obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
  obtain ⟨rc, cvRi, M, u, rhssA, hrc, -, ho, rfl, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
  have hM : tgtMajor out c = M := by
    simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
  rw [hM] at hMs
  have hMn : M.member = none := by
    cases hm : M.member with
    | none => rfl
    | some _ => rw [hm] at hMs; exact absurd rfl hMs
  obtain ⟨-, hMI, hRP⟩ := ConLeche.recShape_at (q := pp.toBlockShape) hrc
  have hnPq : (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).nP = pp.nP := hmr.1
  have hroom := E.hroom
  have hle := E.hle
  -- the former K6 compared against: the block's first
  have hcvTP := E.hcvTP
  rw [hMn] at hcvTP
  have hlenT : E.tfvs.length = pp.nP := ConLeche.Verify.openPisAtFvars_length _ E.hopenT
  have hRdsLen := blockRulePdomsAV_length hμ mpC h hr ψ
  -- the prefix fit, cut to the parameters
  have ht := spineFit_take hg (i := pp.nP) (by rw [hRdsLen, hRP]; exact hroom)
  have hte : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).take pp.nP
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)).take (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).nP := by
    rw [blockRulePdomsAV, List.map_take, List.take_take, hnPq,
      Nat.min_eq_left (by rw [hRP]; exact hroom)]
  rw [hte] at ht
  rw [hnPq]
  refine recParams_fit_former hμ mpC h hmr hr (fvs := E.fvs) (concl := E.concl)
    (by rw [hMI]; exact E.hopen) (by rw [hMI]; omega) (t := 0) (cvTP := E.cvTP)
    (by rw [← List.head?_eq_getElem?]; exact hcvTP) E.hopenT
    (fun l hl => E.hparams l (by rw [List.length_map, hlenT]; exact hl)) ψ ρ _ ?_
  rw [← hnPq]; exact ht

end ConLeche.Model
