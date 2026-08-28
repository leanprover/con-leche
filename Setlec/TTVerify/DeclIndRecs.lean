import Setlec.TTVerify.DeclIndMember
import Setlec.TTVerify.IndBottomNested
import Setlec.TTVerify.MajorStep
import Setlec.Verify.Extend.Recs

/-!
# The recursor-group install

Transpose of `Setlec/Model/Extend/Recs.lean`: the rule-less
provisioning phase (`provisionRecsTT`, each member an
`extendModeledOneTT`), the per-recursor fold obligations from the
checked rule kits (`recMemberTT_of_kit` — where the three landed
bottoms fire), and the group install by the rule-list swap
(`checkIndRecsTT`, through `EnvTT.swap`).
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-! ## Small computation facts

`recRulePlain_le`/`_le_mI` are ninth `V`-free duplicates
(`Setlec/Model/IotaWalk.lean`); the eight ahead of them in that class
were relocated to `Setlec/Verify/{EnvGuards,EnvPreds}.lean` by task
#148's T1, and these two are the residue it did not cover.  The `recFireComparands` computations are what turn
`RecMemberTT`'s level premise into the bottoms' spelling. -/

/-! ## The provisioning phase -/

set_option maxHeartbeats 3200000 in
/-- Phase 0: provisioning a block's recursors rule-less preserves
having a derivation model with the block invariant, and records the
per-item facts.  Transpose of `provisionRecs_sound`; every capability
and residual head obligation is refuted by kind and name shape. -/
theorem provisionRecsTT {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    (∀ ci ∈ recs, blockNames.contains ci.name = true) →
    ∀ (m : EnvTT envAcc), BlockInstalledTT blockNames envAcc m.cval →
    ∃ mS : EnvTT p.1,
      BlockInstalledTT blockNames p.1 mS.cval ∧
      (∀ (n : Name) (ψ : Name → Nat), (envAcc.find? n).isSome = true →
        mS.cval n ψ = m.cval n ψ) ∧
      ProvFacts F blockNames envAcc p.1 p.2
  | [], envAcc, p, h, _, m, hI => by
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m, hI, fun n ψ _ => rfl, ProvFacts.nil⟩
  | ci :: rest, envAcc, p, h, hbn, m, hI => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    obtain ⟨hccv, hms, cvm, mval, hmcvm, hfm, hlps, hrenf⟩ :=
      checkMemberVal_inv hcmv
    obtain ⟨hfind0raw, hnres0raw, hpshape0raw, hnd, hlb, hfv, tyA, stype,
      u, hann, hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
    have hnameA : cvA.name = cv.name := by rw [hcvA]; rfl
    have hfind0 : envAcc.find? cvA.name = none := by
      rw [hnameA]
      exact hfind0raw
    have hnres0 : reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]
      exact hnres0raw
    have hpshape0 : cvA.name.isProjFnShape = false := by
      rw [hnameA]
      exact hpshape0raw
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]
      exact hbn (ConstantInfo.recInfo cv mI rP rules)
        List.mem_cons_self
    have htyf : cvA.type.hasFvar = false := by
      rw [hcvA]
      exact Expr.not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F _ hann
          (Expr.WScoped.of_not_hasFvar hfv)).fvarsBelow)
    have htyb : cvA.type.looseBVarsBounded 0 = true := by
      rw [hcvA]
      exact annotateCore_looseBVars F _ hann hlb
    have htlp : cvA.type.allLevelParamsDefined cvA.levelParams = true := by
      rw [hcvA]
      exact hlp
    have htres : cvA.type.constsResolve envAcc = true := by
      rw [hcvA]
      exact hres
    -- the head is a rule-less recursor: everything refutes by kind
    have hwf₀ : ConstWF ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩
        (.recInfo cvA mI rP []) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq
        exact nomatch heq
      · intro cv2 mI' rP' rules'' heq r hr
        injection heq with e1 e2 e3 e4
        subst e4
        exact nomatch hr
      · intro cv2 v2 heq
        exact nomatch heq
    obtain ⟨m₁, hcval₁⟩ : ∃ m₁ : EnvTT
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩,
        m₁.cval = cvalAlias m.cval cvA.name (cvA.name.str "_model") :=
      ⟨extendModeledOneTT m (.recInfo cvA mI rP [])
      hfind0 hnres0 hwf₀ htres htyf htyb
      (Or.inr (Or.inr ⟨cvA, mI, rP, rfl⟩))
      hfm hlps hrenf hI
      (by
        -- eta head: kind and shape refute every participation
        intro T cvT capsT hfT hcape hresT hfam hpart
        exfalso
        rcases hpart with rfl | hC | ⟨j, hj, hP⟩
        · rw [Env.find?_cons, if_pos rfl] at hfT
          exact nomatch (Option.some.inj hfT)
        · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
          rw [hC, Env.find?_cons, if_pos rfl] at hfC
          exact nomatch (Option.some.inj hfC)
        · have hP' : projFnName T j = cvA.name := hP
          rw [← hP'] at hpshape0
          simp [projFnName, Name.isProjFnShape] at hpshape0)
      (by
        -- unit head: not an inductive former
        intro cv2 caps2 heq
        exact nomatch heq)
      (by
        -- residual head: kind refutes both participations
        intro T cvT capsT cvC hfT hcape hTres hCres hfC hor
        exfalso
        rcases hor with rfl | hC
        · rw [Env.find?_cons, if_pos rfl] at hfT
          exact nomatch (Option.some.inj hfT)
        · rw [hC, Env.find?_cons, if_pos rfl] at hfC
          exact nomatch (Option.some.inj hfC)), rfl⟩
    have hI₁ : BlockInstalledTT blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ m₁.cval := by
      rw [hcval₁]
      refine BlockInstalledTT.step (ci₁ := .recInfo cvA mI rP []) hI
        hms hfm hlps hrenf ?_ ?_
      · intro ψ
        rw [show (ConstantInfo.recInfo cvA mI rP []).name = cvA.name
          from rfl, cvalAlias_self]
      · intro n ψ hn
        rw [cvalAlias_ne (show n ≠ cvA.name from hn)]
    obtain ⟨mS, hIS, hpresS, hchain⟩ := provisionRecsTT rest _ p' hrec
      (fun cj hcj => hbn cj (List.mem_cons_of_mem _ hcj)) m₁ hI₁
    refine ⟨mS, hIS, ?_, ?_⟩
    · intro n ψ hn
      have hne : n ≠ cvA.name := by
        intro he
        rw [he, hfind0] at hn
        exact nomatch hn
      have hn₁ : ((⟨.recInfo cvA mI rP [] ::
          envAcc.consts⟩ : Env).find? n).isSome = true := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
            []).name = n from fun h => hne h.symm)]
        exact hn
      rw [hpresS n ψ hn₁, hcval₁, cvalAlias_ne hne]
    · exact ProvFacts.cons hfind0 hnres0 hpshape0 hms hbnA htyf htyb
        htlp htres ⟨cvm, mval, hmcvm, hfm, hlps, hrenf⟩ hchain

set_option maxHeartbeats 12800000 in
/-- One installed recursor's fold obligations at the final environment,
from its checked rule kits over the provisional one — where the plain
and nested bottoms fire.  Transpose of `recMemberOk_of_kit`. -/
theorem recMemberTT_of_kit {env₂ envS env₃ : Env} (mS : EnvTT envS)
    (F : Nat) {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hro : RenameOkT mS.cval envS f)
    (hIS : BlockInstalledTT blockNames envS mS.cval)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envS.find? n = some ci)
    (henvLev : ∀ n, (envS.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported envS = natLitSupported env₃)
    (hstr : strLitSupported envS = strLitSupported env₃)
    (hcorr : ∀ n : Name, env₃.find? n = envS.find? n ∨
      ∃ cv mI' rP' rules',
        envS.find? n = some (.recInfo cv mI' rP' []) ∧
        env₃.find? n = some (.recInfo cv mI' rP' rules') ∧
        cv.name = n)
    {cvA : ConstantVal} {mI rP : Nat} {rules' : List RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envS.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkits : ∀ r' ∈ rules', ∃ j,
      RuleChecked mode F env₂ envS f cvA mI rP j r') :
    RecMemberTT env₃ mS.cval (.recInfo cvA mI rP rules') := by
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote mS.cval envS φ d e = denote mS.cval env₃ φ d e :=
    fun φ => denote_env_ext henvLev hnat hstr
  have hfindDown : ∀ (n : Name) (ci : ConstantInfo),
      env₃.find? n = some ci →
      (∀ cv mI' rP' rules'', ci ≠ .recInfo cv mI' rP' rules'') →
      envS.find? n = some ci := by
    intro n ci hf' hnr
    rcases hcorr n with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
    · rw [← heq]; exact hf'
    · rw [h₃] at hf'
      obtain rfl := Option.some.inj hf'
      exact absurd rfl (hnr cv2 a b c2)
  intro cvR mI' rP' rules₀ hceq rl hrl hfire
  injection hceq with e1 e2 e3 e4
  subst e1; subst e2; subst e3; subst e4
  obtain ⟨jj, cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, hnf, hcp,
    hplIff, hnestK, hrawf, hrawb, hann, hrhsf, hrhsb, hrlp, hrres,
    hstripR, hity, hplainImp⟩ := hkits rl hrl
  -- the recursor's and constructor's stored facts
  obtain ⟨htyw, -, -, htyb, -, -, -⟩ := mS.wf _ (find?_mem hself)
  have hfcS : envS.find? (RecRule.ctor rl) =
      some (.ctorInfo cvj cnP cnF) := hup _ _ hfc
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ := mS.wf _ (find?_mem hfcS)
  -- the recursor's model constant
  obtain ⟨cvm, mval, hm, hfm, hlpsm, -, -⟩ := hIS cvA.name hbnA _ hself
  have hfRm : envS.find? (f cvA.name) = some (.defnInfo cvm mval hm) := by
    rw [hf]
    dsimp only
    rw [if_pos hbnA]
    exact hfm
  have hRmlps : (ConstantInfo.defnInfo cvm mval
      hm).toConstantVal.levelParams = cvA.levelParams := hlpsm
  -- the constructor's renamed head
  obtain ⟨cimC, hfCm, hCmlps⟩ : ∃ cimC,
      envS.find? (f (RecRule.ctor rl)) = some cimC ∧
      cimC.toConstantVal.levelParams = cvj.levelParams := by
    by_cases hbc : blockNames.contains (RecRule.ctor rl) = true
    · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -, -⟩ := hIS _ hbc _ hfcS
      refine ⟨.defnInfo cvmC mvalC hmC, ?_, hlpsC⟩
      rw [hf]
      dsimp only
      rw [if_pos hbc]
      exact hfmC
    · refine ⟨.ctorInfo cvj cnP cnF, ?_, rfl⟩
      rw [hf]
      dsimp only
      rw [if_neg hbc]
      exact hfcS
  have heqfS : envS.find? eqName = some eqA := hup _ _ heqfind
  -- the ctor identification at the law's own lookup
  have hctorId : ∀ {cvj' : ConstantVal} {cnP' cnF' : Nat},
      env₃.find? (RecRule.ctor rl) = some (.ctorInfo cvj' cnP' cnF') →
      cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
    intro cvj' cnP' cnF' hctor₃
    have hctorS := hfindDown _ _ hctor₃ (fun _ _ _ _ hh => nomatch hh)
    rw [hfcS] at hctorS
    have h0 := Option.some.inj hctorS
    injection h0 with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  cases hfr : RecRule.fire rl with
  | inert => exact absurd hfr hfire
  | plain =>
    have hplain : Expr.recRulePlain cvA.type mI rP cnP = true :=
      hplIff.mp hfr
    obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms,
      cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2,
      ldoms, lrest, hfthm, hcvt, -, hlpt, hopen, hheadEq, hargs3, hlhead,
      hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
      hrinst, hdePre, hopenP, hcinstP, hdePars, hopenX, hlinst, hdeLam,
      hdeRhs, hlhsTyC, hrhsTyC, hslot⟩ := hplainImp hplain
    -- the theorem's stored facts
    have hfthmS : envS.find? thmName = some ci := hup _ _ hfthm
    obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ := mS.wf _ (find?_mem hfthmS)
    rw [hcvt] at hSw0 hSb0
    have hthm : ∀ ψ' : Name → Nat, ∃ pv t,
        denoteClosed mS.cval envS ψ' cvt.type = some t ∧
        HasType [] pv t := by
      intro ψ'
      obtain ⟨t, ht, hd⟩ := mS.has_type _ (find?_mem hfthmS) ψ'
      rw [hcvt] at ht
      exact ⟨_, t, ht, hd⟩
    have hbot := IndBottomPlainTT (F := F) mS checkStepTT hro heqfS
      htyw htyb hfRm hRmlps hfcS hfCm hCmlps hCw hCb hClp
      (recRulePlain_le_mIT hplain) (recRulePlain_leT hplain)
      hrhsf hrhsb hity hSw0 hSb0 hthm hopen hheadEq hargs3 hlhead
      hlarity hlpre hmaj hcstrip hcinst hclen hdeIdx hrinst hdePre
      hdeFld hopenP hcinstP hdePars hdeRhs hlhsTyC hrhsTyC (hslot rfl)
    refine ⟨recRulePlain_le_mIT hplain, ?_⟩
    intro φ d us hlenU
    obtain ⟨RV, hRV, hlaw⟩ := hbot φ d us hlenU
    refine ⟨RV, by rw [← hde]; exact hRV, ?_⟩
    intro cvj' cnP' cnF' hctor₃
    obtain ⟨g1, g2, g3⟩ := hctorId hctor₃
    subst g1; subst g2; subst g3
    intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar
      hparN hidx hTV hTVj hfitR hfitC
    rw [recFireComparands_plain hfr] at hlev
    rw [hcp, hnf] at hlenY
    rw [hcp] at hidx
    have hpar' := hpar rfl
    rw [hcp] at hpar'
    have := hlaw Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev
      hpar' hidx (by rw [hde]; exact hTV) (by rw [hde]; exact hTVj)
      hfitR hfitC
    rw [hcp]
    exact this
  | nested lvls pins =>
    obtain ⟨hmIrP, hlvlsDef, hpinsFacts, hshapeM, hpinsLen, hnck⟩ :=
      hnestK lvls pins hfr
    obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms,
      cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2,
      ldoms, lrest, hfthm, hcvt, -, hlpt, hopen, hheadEq, hargs3, hlhead,
      hlarity, hlpre, hmaj, hCresHead, hcinst, hclen, hdeIdx, hdeFld,
      hrinst, hdePre, hopenP, hannP0, hcinstN0, htlP0, hopenX,
      hcrest2Len, hlinst, hdeLam, hdeRhs, hlhsTyC, hrhsTyC, hslot⟩ :=
      hnck
    -- the theorem's stored facts
    have hfthmS : envS.find? thmName = some ci := hup _ _ hfthm
    obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ := mS.wf _ (find?_mem hfthmS)
    rw [hcvt] at hSw0 hSb0
    have hthm : ∀ ψ' : Name → Nat, ∃ pv t,
        denoteClosed mS.cval envS ψ' cvt.type = some t ∧
        HasType [] pv t := by
      intro ψ'
      obtain ⟨t, ht, hd⟩ := mS.has_type _ (find?_mem hfthmS) ψ'
      rw [hcvt] at ht
      exact ⟨_, t, ht, hd⟩
    -- the stored levels have the constructor's arity (semantic; see
    -- `nestedLvlsLength`)
    have hlvlsLen : lvls.length = cvj.levelParams.length := by
      obtain ⟨pv0, T0, hT0, -⟩ := hthm (fun _ => 0)
      rw [← hCmlps]
      exact nestedLvlsLength (K := rP + cnF) hT0 hopen hheadEq hargs3
        hlhead hlarity hmaj hfCm
    have hCstrips : (cvj.type.stripPis (cnP + cnF)).isSome = true := by
      obtain ⟨bsC0, cbody0, Dc, usc, hCs, -⟩ := hCresHead
      rw [hCs]
      rfl
    have hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
        p.looseBVarsBounded rP = true := by
      intro p hp
      exact ⟨(hpinsFacts p hp).1, (hpinsFacts p hp).2.2.2⟩
    have hbot := IndBottomNestedTT (F := F) mS checkStepTT hro heqfS
      htyw htyb hfRm hRmlps hfcS hfCm hCmlps hCw hCb hClp hmIrP
      hlvlsLen hpinsLen hpinsWf
      hrhsf hrhsb hity hSw0 hSb0 hthm hopen hheadEq hargs3 hlhead
      hlarity hlpre hmaj hCstrips hCresHead hcinst hclen hdeIdx hrinst
      hdePre hdeFld hopenP hcinstN0 htlP0 hdeRhs hlhsTyC hrhsTyC (hslot rfl)
    refine ⟨hmIrP, ?_⟩
    intro φ d us hlenU
    obtain ⟨RV, hRV, hlaw⟩ := hbot φ d us hlenU
    refine ⟨RV, by rw [← hde]; exact hRV, ?_⟩
    intro cvj' cnP' cnF' hctor₃
    obtain ⟨g1, g2, g3⟩ := hctorId hctor₃
    subst g1; subst g2; subst g3
    intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar
      hparN hidx hTV hTVj hfitR hfitC
    rw [recFireComparands_nested hfr] at hlev
    rw [hcp, hnf] at hlenY
    rw [hcp] at hidx
    have hparN' : ∀ i, i < RecRule.ctorParams rl →
        ∀ vp : VExpr,
          denote mS.cval envS φ rP (openRev 0 rP
            ((pins.getD i default).instantiateLevelParams
              cvA.levelParams us)) = some vp →
          Deq Δ (ys.getD i default)
            (VExpr.instRevChain (xs.take rP) vp) := by
      intro i hi vp hvp
      refine hparN lvls pins rfl i hi vp ?_
      rw [← hde]
      exact hvp
    rw [hcp] at hparN'
    have := hlaw Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev
      hparN' hidx (by rw [hde]; exact hTV) (by rw [hde]; exact hTVj)
      hfitR hfitC
    rw [hcp]
    exact this

/-! ## The group swap, assembled -/

/-- A component check that ignores a recursor's rule list is congruent
across the shape-level swap correspondence. -/
private theorem corr_chk {env₀ env₃ : Env}
    (hcorr : ∀ n : Name, env₃.find? n = env₀.find? n ∨
      ∃ cv mI rP rules, env₀.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧ cv.name = n)
    (chk : Option ConstantInfo → Bool)
    (hins : ∀ cv mI rP rules rules',
      chk (some (.recInfo cv mI rP rules)) =
      chk (some (.recInfo cv mI rP rules'))) :
    ∀ n, chk (env₀.find? n) = chk (env₃.find? n) := by
  intro n
  rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq]
  · rw [h₀, h₃]
    exact hins cv mI rP [] rules

/-- The two chains' environments are swap-related, given each pair's
obligations.  Transpose of `chains_swap`. -/
private theorem chains_swapT {blockNames : List Name}
    {env' envS env₃ : Env} {f : Name → Name} {cval : TConstVal} :
    ∀ {zipped : List ((ConstantVal × Nat × Nat × List RecRule) ×
        List RecRule)}
      {accS acc₃ envSelf env₃' : Env},
      ProvFacts F blockNames accS envSelf (zipped.map Prod.fst) →
      RulesChain mode F env' envS f acc₃ env₃' zipped →
      (∀ z ∈ zipped, SwapPairT env₃ cval
        (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 [])
        (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 z.2)) →
      SwapListT env₃ cval accS.consts acc₃.consts →
      SwapListT env₃ cval envSelf.consts env₃'.consts := by
  intro zipped
  induction zipped with
  | nil =>
    intro accS acc₃ envSelf env₃' hp hr hob hacc
    cases hp
    cases hr
    exact hacc
  | cons z rest ih =>
    intro accS acc₃ envSelf env₃' hp hr hob hacc
    obtain ⟨⟨cvA, mI, rP, rules⟩, rules'⟩ := z
    cases hp with
    | cons hfresh hnres hshape hms hbn htyf htyb htlp htres hmodel hp' =>
      cases hr with
      | cons hcir hr' =>
        exact ih hp' hr'
          (fun z hz => hob z (List.mem_cons_of_mem _ hz))
          (SwapListT.cons (hob _ List.mem_cons_self) hacc)

set_option maxHeartbeats 6400000 in
/-- Checking and installing a block's recursor group preserves having
a derivation model with the block invariant.  Transpose of
`checkIndRecs_sound`, through `EnvTT.swap`. -/
theorem checkIndRecsTT {blockNames : List Name}
    {env₂ env₃ : Env} {recs : List ConstantInfo}
    (h : checkIndRecs mode (fueledOps mode F) blockNames env₂ recs = .ok env₃)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hnm : ∀ n, blockNames.contains n = true →
      n.isModelSuffix = false)
    (m : EnvTT env₂) (hI : BlockInstalledTT blockNames env₂ m.cval) :
    ∃ m₃ : EnvTT env₃, BlockInstalledTT blockNames env₃ m₃.cval := by
  rw [checkIndRecs] at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m, hI⟩
  rw [if_neg hemp] at h
  simp only [Bind.bind, Except.bind] at h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg => rw [if_neg heqf] at h; exact nomatch h
  rw [if_pos heqf] at h
  simp only [pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases hprov : provisionRecs (fueledOps mode F) blockNames env₂ recs with
  | error e => intro h; exact nomatch h
  | ok p => ?_
  intro h
  try dsimp only at h
  obtain ⟨envSelf, checked⟩ := p
  try dsimp only at h
  obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv checked env₂ env₃ h
  obtain ⟨mS, hIS, hpres, hProv⟩ := provisionRecsTT recs env₂
    (envSelf, checked) hprov hbn m hI
  rw [show checked = zipped.map Prod.fst from hmap.symm] at hProv
  -- shape-level correspondence and its congruences
  have hswSh := chains_swapSh hProv hchain (SwapShList.of_eq env₂.consts)
  have hcorr := swapSh_find?_corr hswSh
  have henvLev : ∀ n, (envSelf.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      rfl
  have hisoSome : ∀ n, (envSelf.find? n).isSome =
      (env₃.find? n).isSome := by
    intro n
    rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      rfl
  have hnat : natLitSupported envSelf = natLitSupported env₃ := by
    unfold natLitSupported
    rw [corr_chk hcorr natIndOk (fun _ _ _ _ _ => rfl) natName,
      corr_chk hcorr natZeroOk (fun _ _ _ _ _ => rfl) natZeroName,
      corr_chk hcorr natSuccOk (fun _ _ _ _ _ => rfl) natSuccName]
  have hstr : strLitSupported envSelf = strLitSupported env₃ := by
    unfold strLitSupported
    rw [hnat,
      corr_chk hcorr stringTyOk (fun _ _ _ _ _ => rfl) stringName,
      corr_chk hcorr stringOfListTyOk (fun _ _ _ _ _ => rfl)
        stringOfListName,
      corr_chk hcorr listTyOk (fun _ _ _ _ _ => rfl) listName,
      corr_chk hcorr listNilTyOk (fun _ _ _ _ _ => rfl) listNilName,
      corr_chk hcorr listConsTyOk (fun _ _ _ _ _ => rfl) listConsName,
      corr_chk hcorr charTyOk (fun _ _ _ _ _ => rfl) charName,
      corr_chk hcorr charOfNatTyOk (fun _ _ _ _ _ => rfl) charOfNatName]
  have hfindUp3 : ∀ (n : Name) (ci : ConstantInfo),
      envSelf.find? n = some ci →
      (∀ cv mI' rP' rules', ci ≠ .recInfo cv mI' rP' rules') →
      env₃.find? n = some ci := by
    intro n ci hfx hnr
    rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
    · rw [heq]
      exact hfx
    · rw [h₀] at hfx
      obtain rfl := Option.some.inj hfx
      exact absurd rfl (hnr cv a b [])
  -- all block members are stored in the provisional environment
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, hcn⟩
    · cases hf : env₂.find? n with
      | none => rw [hf] at hfound; exact nomatch hfound
      | some ci =>
        rw [ProvFacts.find?_preserved hProv n ci hf]
        rfl
    · obtain ⟨c, hc, hcn'⟩ := provisionRecs_names recs env₂
        (envSelf, checked) hprov ci hci
      have hc' : c ∈ zipped.map Prod.fst := by
        rw [hmap]
        exact hc
      obtain ⟨-, -, -, -, -, -, -, -, -, hself⟩ :=
        ProvFacts.mem_facts hProv c hc'
      rw [← hcn, ← hcn', hself]
      rfl
  -- the full block renaming is sound at the provisional environment
  have hro : RenameOkT mS.cval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -, -⟩ := hIS n hc ci₂ hf₂
        exact ⟨.defnInfo cvm₂ mval₂ hm₂, hfm₂, hlps₂⟩
      · rw [if_neg hc]
        exact ⟨ci₂, hf₂, rfl⟩
    · intro n hf₂
      dsimp only
      by_cases hc : blockNames.contains n = true
      · have := hnames n hc
        rw [hf₂] at this
        exact nomatch this
      · rw [if_neg hc]
        exact hf₂
    · intro n ψ
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        cases hf₂ : envSelf.find? n with
        | none =>
          have := hnames n hc
          rw [hf₂] at this
          exact nomatch this
        | some ci₂ =>
          obtain ⟨cvm₂, mval₂, -, -, -, -, hv₂⟩ := hIS n hc ci₂ hf₂
          exact (hv₂ ψ).symm
      · rw [if_neg hc]
  -- per-item swap obligations
  have hob : ∀ z ∈ zipped, SwapPairT env₃ mS.cval
      (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 [])
      (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 z.2) := by
    intro z hz
    have hz1 : z.1 ∈ zipped.map Prod.fst := List.mem_map_of_mem hz
    obtain ⟨hnres, hshape, hms, hbnc, htyf, htyb, htlp, htres, hmodel,
      hself⟩ := ProvFacts.mem_facts hProv z.1 hz1
    have hcir := RulesChain.mem_facts hchain z hz
    have hkits : ∀ r' ∈ z.2, ∃ j, RuleChecked mode F env₂ envSelf
        (fun n => if blockNames.contains n then n.str "_model" else n)
        z.1.1 z.1.2.1 z.1.2.2.1 j r' := fun r' hr' => by
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hr'
      exact ⟨_, checkIotaRules_inv 0 _ _ hcir k r' hk⟩
    refine Or.inr ⟨z.1.1, z.1.2.1, z.1.2.2.1,
      z.2, rfl, rfl, hnres, hshape, ?_, ?_, ?_⟩
    · -- ConstWF at the final environment
      refine ⟨htyf, htlp, ?_, htyb, ?_, ?_,
        fun cv2 v2 heq => nomatch heq⟩
      · rw [← Expr.constsResolve_congr hisoSome]
        exact htres
      · intro cv2 v2 h2 heq
        exact nomatch heq
      · intro cv2 mI2 rP2 rules2 heq r hr
        injection heq with e1 e2 e3 e4
        subst e1; subst e2; subst e3; subst e4
        obtain ⟨jj, cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -,
          hnestK, -, -, -, hrf, hrb, hrlp, hrres, -, -, -⟩ := hkits r hr
        refine ⟨hrf, hrlp, ?_, hrb, ?_⟩
        · rw [← Expr.constsResolve_congr hisoSome]
          exact hrres
        · intro lvls pins hfr
          obtain ⟨n1, n2, n3, n4, -⟩ := hnestK lvls pins hfr
          refine ⟨n1, n2, ?_, n4⟩
          · intro pin hpin
            obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
            refine ⟨p1, p2, ?_, p4⟩
            rw [← Expr.constsResolve_congr hisoSome]
            exact p3
    · -- the rules' constructors are stored
      intro r hr
      obtain ⟨jj, cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, -⟩ :=
        hkits r hr
      refine ⟨cvj, cnP, cnF, ?_⟩
      refine hfindUp3 _ _ (ProvFacts.find?_preserved hProv _ _ hfc)
        (fun _ _ _ _ hcon => nomatch hcon)
    · -- the fold obligations, from the bottoms
      exact recMemberTT_of_kit mS F rfl hro hIS
        (ProvFacts.find?_preserved hProv) henvLev hnat hstr hcorr
        hbnc hself heqf hkits
  -- the group swap
  have hswap : SwapListT env₃ mS.cval envSelf.consts env₃.consts :=
    chains_swapT hProv hchain hob (SwapListT.of_eq env₂.consts)
  refine ⟨mS.swap hswap, ?_⟩
  intro n hn ci₃ hf₃
  rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm₂, mval₂, hm₂,
      hfindUp3 _ _ hfm₂ (fun _ _ _ _ hcon => nomatch hcon),
      hlps₂, hren₂, hv₂⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hIS n hn _ h₀
    exact ⟨cvm₂, mval₂, hm₂,
      hfindUp3 _ _ hfm₂ (fun _ _ _ _ hcon => nomatch hcon),
      hlps₂, hren₂, hv₂⟩

end Setlec.TTVerify
