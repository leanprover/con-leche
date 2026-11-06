module

import ConLeche.Model.OpenedCtx
import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.GenRecStage
public import ConLeche.Model.Inductives.BlockRecData
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Verify.Inductives.GenRecScoped

public section

/-!
# The generated recursors' parameter domains fit the block's

`genParams_fit_run`: a spine fitting a generated recursor's rule prefix fits the block's parameters
on its first `nP` values. The generated type's first binders are the canonical parameters' own
(`ClassGen.prefixBinders`), and those open the first member's telescope (`genRun_ctx`): the
recursor's parameter domains read as that telescope's, with no comparison between them.
-/

namespace ConLeche
open ConLeche.Term (Term)


/-- An application spine erasure-equal to another: heads and arguments
pairwise. -/
theorem erasedEq_mkAppN_args :
    ∀ (as : List Expr) {as' : List Expr} {f f' : Expr}, as'.length = as.length →
      Expr.ErasedEq (Expr.mkAppN f' as') (Expr.mkAppN f as) →
      Expr.ErasedEq f' f ∧
        ∀ (j : Nat) (x x' : Expr), as[j]? = some x → as'[j]? = some x' → Expr.ErasedEq x' x
  | [], [], _, _, _, h => ⟨h, fun j x x' hx _ => nomatch hx⟩
  | a :: as, a' :: as', f, f', hl, h => by
    obtain ⟨hh, hargs⟩ := erasedEq_mkAppN_args as (as' := as') (f := .app f a) (f' := .app f' a')
      (by simpa using hl) h
    refine ⟨hh.1, fun j x x' hx hx' => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
      subst hx hx'
      exact hh.2
    | succ j => exact hargs j x x' (by simpa using hx) (by simpa using hx')

end ConLeche

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars closeTelescope
  ClassGen ClassGenScoped SameDoms classGenRecTy classBinder GenRecRun ClassRecTyRun
  FEnv mkFEnv NestState TargetMajor RecShape BlockShape BlockShape instPisWith)


section GenRun

variable {F : Nat} {env₁ envC : Env} {p : BlockShape} {nestedBit : Bool} {pos : NestState}
  {formers : List ConstantVal} {block : List ConstantInfo}
  {memberCtors : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **A member class, as the run checked it**: the member's own
inductive, at the block's levels, over the canonical parameters. -/
theorem genRec_memberClass
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos
      block out)
    {c t : Nat} (hm : (R.Ms.getD c default).member = some t) :
    p.memberNames.findIdx? (· == (R.Ms.getD c default).ind) = some t ∧
    (R.Ms.getD c default).lvls = p.lps.map .param ∧
    (R.Ms.getD c default).ds = R.ctx.params.take p.nP := by
  by_cases hc : c < R.Ms.length
  · obtain ⟨hlenN, hallN⟩ := ConLeche.classesNfs_run R.hMs
    obtain ⟨hlenK, hallK⟩ := R.majors
    have hc₀ : c < R.Ms₀.length := by omega
    obtain ⟨nfs, hMc, -⟩ := hallN c _ (List.getElem?_eq_getElem hc₀)
    have hck : c < R.keys.length := by
      omega
    obtain ⟨M, hM, ⟨CM⟩⟩ := hallK c _ (List.getElem?_eq_getElem hck)
    rw [List.getElem?_eq_getElem hc₀, Option.some.injEq] at hM
    have hget : R.Ms.getD c default = { M with nfs := nfs } := by
      rw [List.getD_eq_getElem?_getD, hMc, hM, Option.getD_some]
    rw [hget] at hm ⊢
    have hmaj := CM.major
    cases hmaj with
    | member I t' ms hfn ht hms hpar nfs' =>
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨ht, rfl, rfl⟩
    | outside => exact nomatch hm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at hm
    exact nomatch hm

end GenRun

/-! ## The parameters' fit -/

section Fit

universe w'

variable {V : Type w'} [SetTheory V]

/-- A generated type's first binders are the canonical parameters'. -/
theorem ClassGen_pre_param {g : ConLeche.ClassGen} (hg : ConLeche.ClassGenScoped g) {i : Nat}
    {x : Expr} (h : g.params[i]? = some x) : g.pre[i]? = some (g.binder x) := by
  have hp := hg.pre
  unfold ConLeche.ClassGen.prefixBinders at hp
  simp only [bind, Option.bind] at hp
  split at hp
  · simp at hp
  · have hpe := Option.some.inj hp
    rw [← hpe, List.getElem?_append_left (by
      simpa using (List.getElem?_eq_some_iff.mp h).1), List.getElem?_map, h]
    rfl

/-- **The generated recursors' parameter domains fit the block's**, at
the members' run facts (`BlockMembersRun`): a spine fitting any stored
recursor's rule prefix fits the block's parameters on its first `nP`
values. -/
theorem genParams_fit_run {F : Nat} {envI envC : Env}
    {pp : BlockShape} {nestedBit : Bool} {pos : NestState}
    {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} (mpC : EnvModelM V envC)
    (R : GenRecRun .verified F (mkFEnv envI) envI (mkFEnv envC) pp nestedBit pos
      block out)
    (hg : ClassGenScoped R.g)
    (h : RecStageG .verified F envC pp (ConLeche.tgtRs out))
    {dR : BlockData V}
    (hmr : BlockMembersRun mpC.base2 dR pp) :
    ∀ c, c < (ConLeche.tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (ConLeche.tgtRs out) ψ c)
        xs →
      SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
  intro c hc ψ ρ xs hfit
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, -⟩ := hmr
  have hnPq' : dR.nP = pp.nP := hnPq
  -- recursor `c`
  have hlenT : (ConLeche.tgtRs out).length = pp.recs.length := by
    obtain ⟨S⟩ := h; exact S.len
  obtain ⟨rc, hrc⟩ : ∃ rc, pp.recs[c]? = some rc := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cc, cvG, rhss, hcc, -, ⟨T⟩, ho, -, -⟩ := genRecRun_at R hrc
  have hr : (ConLeche.tgtRs out)[c]? = some (cvG, rhss, (R.Ms.getD cc default).nIdx,
      (R.Ms.getD cc default).ctors) := by
    simp [ConLeche.tgtRs, List.getElem?_map, ho]
  obtain ⟨fvsL, conclL, hopL, -, -, hlenRds, hbind, -, -⟩ := recStage_tyPis mpC h hr ψ
  have hle := blockRecHrPle (p := pp) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hrP, -⟩ := genRecTy_shape R hg T
  obtain ⟨-, -, hRc⟩ := ConLeche.recShape_at (q := pp) hrc
  have hpl : R.pre.length = pp.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hroom : pp.nP ≤ pp.rulePrefixAt c := by
    rw [hRc, hrP, hpl]; exact Nat.le_add_right _ _
  -- the generated type's binders: the canonical parameters first
  have htype : cvG.type = T.gty := T.type_eq
  obtain ⟨ifs, maj, -, -, hgty, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg T.hgty
  simp only [List.append_assoc] at hgty hcl
  generalize hB : Expr.mkAppN (R.g.motVar cc) _ = B at hgty hbb
  obtain ⟨xsG, restG, hopG, -, hxsG⟩ := open_of_erasedEq_closeTelescope _ 0 B cvG.type hcl hbb
    (by rw [htype, hgty]; exact Expr.ErasedEq.rfl _)
  have hlenPre : pp.nP ≤ (R.g.pre ++ (ifs.map R.g.binder ++ [maj])).length := by
    have : R.g.pre.length = R.pre.length := rfl
    simp only [List.length_append]; omega
  obtain ⟨oG, hopGP⟩ := ConLeche.openPisAtFvars_prefix pp.nP _ cvG.type 0 hlenPre hopG
  obtain ⟨oc, hopc⟩ := ConLeche.openPisAtFvars_prefix pp.nP _ cvG.type 0 (by omega) hopL
  have hsame : fvsL.take pp.nP = xsG.take pp.nP := by
    rw [hopc] at hopGP
    exact congrArg Prod.fst (Option.some.inj hopGP)
  -- the canonical parameters: the first member's telescope, opened
  obtain ⟨cvT0, rest0, h0, hop0, -, -⟩ := ConLeche.genRun_ctx R
  have hcvT0 : pp.formers[0]? = some cvT0 := by rwa [List.head?_eq_getElem?] at h0
  obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
  obtain ⟨ppsT, bT, hstT, -, hlenT0, hbindT⟩ :=
    denote_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) pp.nP hop0 (hFD0.read ψ)
  have hlenP0 : (dR.ppsM 0 ψ).length = dR.nP + dR.nIdxAt 0 := hFD0.len ψ
  have hppsT : ppsT = (dR.ppsM 0 ψ).take pp.nP := by
    have := stripPisAV_mkPisAV_take pp.nP (dR.ppsM 0 ψ)
      (.sort (dR.resSort.eval ψ)) (by rw [hlenP0, hnPq']; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hplenC : R.ctx.params.length = pp.nP := hg.params_len
  -- the recursor's parameter domains are the first member's
  have hlenPd := blockRulePdomsAV_length mpC h hr ψ
  generalize hPd : blockRulePdomsAV mpC.base2.acval envC pp (ConLeche.tgtRs out) ψ c
    = pdoms at hfit hlenPd
  have heq : pdoms.take pp.nP = dR.params ψ := by
    show _ = (dR.ppsM 0 ψ).take dR.nP
    rw [hnPq', ← hppsT]
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < pp.nP
    · obtain ⟨x, hx⟩ : ∃ x, fvsL[i]? = some x := ⟨_, List.getElem?_eq_getElem (by
        have := ConLeche.Verify.openPisAtFvars_length _ hopL; omega)⟩
      obtain ⟨pd, hpd, hreadD⟩ := hbind i x hx
      obtain ⟨xg, hxg⟩ : ∃ xg, xsG[i]? = some xg := by
        have h' : (xsG.take pp.nP)[i]? = some x := by
          rw [← hsame, List.getElem?_take, ite_eq_left hi]; exact hx
        rw [List.getElem?_take, ite_eq_left hi] at h'
        exact ⟨x, h'⟩
      have hxx : xg = x := by
        have h' : (xsG.take pp.nP)[i]? = some x := by
          rw [← hsame, List.getElem?_take, ite_eq_left hi]; exact hx
        rw [List.getElem?_take, ite_eq_left hi, hxg] at h'
        exact Option.some.inj h'
      subst hxx
      obtain ⟨pi, hpi⟩ : ∃ pi, R.ctx.params[i]? = some pi :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨p', hp', hreadT⟩ := hbindT i pi hpi
      rw [Nat.zero_add] at hreadT
      have hnd : (R.g.pre ++ (ifs.map R.g.binder ++ [maj]))[i]? = some (R.g.binder pi) := by
        rw [List.getElem?_append_left (by have : R.g.pre.length = R.pre.length := rfl; omega)]
        exact ClassGen_pre_param hg hpi
      have hE := hxsG i xg _ hxg hnd
      have hval : pd = p' := by
        have h1 : denote mpC.base2.acval envC ψ i xg.fvarTypeD
            = denote mpC.base2.acval envC ψ i pi.fvarTypeD := denote_erasedEq hE i
        rw [hreadD, hreadT] at h1
        exact Option.some.inj h1
      rw [List.getElem?_take, ite_eq_left hi, hp', ← hPd, blockRulePdomsAV, List.getElem?_take,
        ite_eq_left (by omega), hpd, hval]
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by omega)]
  rw [hnPq', ← heq]
  exact spineFit_take hfit (by rw [hlenPd]; omega)

end Fit

end ConLeche.Model
