import Setlec.Verify.Extend.Recs
import Setlec.Model.Extend.Modeled
import Setlec.Model.Extend.GroupSwap
import Setlec.Model.IndInstall

/-!
# Recs — soundness of the recursor-group install

`checkIndRecs_sound`: a block's recursors are provisioned rule-less
together (phase 0, `provisionRecs` — each an `extend_modeled_one`),
their rules are checked against the provisional environment, and the
group installs by the rule-list swap (`extend_rules_eq`), with each
rule's fold obligation discharged from its checked `iota` theorem
(`modeled_rule_fold`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Phase 0: provisioning a block's recursors rule-less preserves
having a model with the block invariant, and records the per-item
facts. -/
theorem provisionRecs_sound {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps F) blockNames envAcc recs = .ok p →
    (∀ ci ∈ recs, blockNames.contains ci.name = true) →
    ∀ (m : EnvModel V envAcc), BlockInstalled blockNames envAcc m.val →
    ∃ mS : EnvModel V p.1,
      BlockInstalled blockNames p.1 mS.val ∧
      (∀ (n : Name) (ψ : Name → Nat), (envAcc.find? n).isSome = true →
        mS.val n ψ = m.val n ψ) ∧
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
      exact not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F _ hann
          (WScoped.of_not_hasFvar hfv)).fvarsBelow)
    have htyb : cvA.type.looseBVarsBounded 0 = true := by
      rw [hcvA]
      exact annotateCore_looseBVars F _ hann hlb
    have htlp : cvA.type.allLevelParamsDefined cvA.levelParams = true := by
      rw [hcvA]
      exact hlp
    have htres : cvA.type.constsResolve envAcc = true := by
      rw [hcvA]
      exact hres
    -- the pruned renaming for the one-member extension
    obtain ⟨fb, hfb⟩ : ∃ fb : Name → Name, fb = fun n =>
        if blockNames.contains n then n.str "_model" else n := ⟨_, rfl⟩
    have hrenfb := hrenf
    rw [← hfb] at hrenfb
    obtain ⟨fS, hfS⟩ : ∃ fS : Name → Name, fS = fun n =>
        if (envAcc.find? n).isSome then fb n else n := ⟨_, rfl⟩
    have hfSfound : ∀ n, (envAcc.find? n).isSome = true → fS n = fb n := by
      intro n hn
      rw [hfS]
      simp only [hn, if_true]
    have hfSnone : ∀ n, envAcc.find? n = none → fS n = n := by
      intro n hn
      rw [hfS]
      simp [hn]
    have hroS : RenameOk m.val envAcc fS := by
      refine ⟨?_, ?_, ?_⟩
      · intro n ci₂ hf₂
        have hsome : (envAcc.find? n).isSome = true := by rw [hf₂]; rfl
        rw [hfSfound n hsome, hfb]
        dsimp only
        by_cases hc : blockNames.contains n = true
        · rw [if_pos hc]
          obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -, -⟩ := hI n hc ci₂ hf₂
          exact ⟨.defnInfo cvm₂ mval₂ hm₂, hfm₂, hlps₂⟩
        · rw [if_neg hc]
          exact ⟨ci₂, hf₂, rfl⟩
      · intro n hf₂
        rw [hfSnone n hf₂]
        exact hf₂
      · intro n ψ
        cases hf₂ : envAcc.find? n with
        | none => rw [hfSnone n hf₂]
        | some ci₂ =>
          have hsome : (envAcc.find? n).isSome = true := by rw [hf₂]; rfl
          rw [hfSfound n hsome, hfb]
          dsimp only
          by_cases hc : blockNames.contains n = true
          · rw [if_pos hc]
            obtain ⟨cvm₂, mval₂, -, -, -, -, hv₂⟩ := hI n hc ci₂ hf₂
            exact (hv₂ ψ).symm
          · rw [if_neg hc]
    have hrenS : Expr.eqUpToNames (cvA.type.renameConsts fS) cvm.type =
        true := by
      rw [← Expr.renameConsts_congr_resolve
        (fun n hn => (hfSfound n hn).symm) cvA.type htres]
      exact hrenfb
    have hannT : ∀ ψ : Name → Nat,
        AnnotOk V m.val envAcc ψ 0 (rho0 V) cvA.type := by
      intro ψ
      rw [hcvA]
      have htyf' : tyA.hasFvar = false := by
        have := htyf; rw [hcvA] at this; exact this
      exact (inferTypeCore_sound m F hst (WScoped.of_not_hasFvar htyf')
        (annotateCore_looseBVars F _ hann hlb)
        (Expr.LeavesBounded.of_not_hasFvar htyf')
        (FvarsOk.of_not_hasFvar htyf')).1
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
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.recInfo cvA mI rP []) fS (cvA.name.str "_model")
      hfind0 hnres0 hwf₀ htres
      (Or.inr (Or.inr ⟨cvA, mI, rP, rfl⟩)) hfm hlps hrenS hannT hroS
      (fun val₁ _ _ =>
        ⟨capsEtaHead_of_rec_shape
          (fun cv2 caps2 hcon => nomatch hcon)
          (fun cv2 cnP2 cnF2 hcon => nomatch hcon)
          hpshape0,
        fun cv2 caps2 hcon => nomatch hcon⟩)
    have hI₁ : BlockInstalled blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ m₁.val :=
      BlockInstalled.step (ci₁ := .recInfo cvA mI rP []) hI hms hfm
        hlps hrenf hval₁ hpres₁
    obtain ⟨mS, hIS, hpresS, hchain⟩ := provisionRecs_sound rest _ p' hrec
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
      rw [hpresS n ψ hn₁, hpres₁ n ψ hne]
    · exact ProvFacts.cons hfind0 hnres0 hpshape0 hms hbnA htyf htyb
        htlp htres
        ⟨cvm, mval, hmcvm, hfm, hlps, hrenf⟩
        hchain

/-- A successful `Option`-`mapM` preserves length. -/
private theorem mapM_option_length {α : Type _} {β : Type _}
    {g : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM g = some ys →
      l.length = ys.length
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: l, ys, h => by
    cases hg : g x with
    | none => rw [List.mapM_cons, hg] at h; simp at h
    | some y =>
      cases hl : l.mapM g with
      | none => rw [List.mapM_cons, hg, hl] at h; simp at h
      | some ys' =>
        rw [List.mapM_cons, hg, hl] at h
        have h' : some (y :: ys') = some ys := h
        obtain rfl := Option.some.inj h'
        simpa using mapM_option_length hl

set_option maxHeartbeats 1600000 in
/-- One installed recursor's fold obligations at the final environment,
from its checked rule kits over the provisional one. -/
theorem recMemberOk_of_kit {env₂ envS env₃ : Env} (mS : EnvModel V envS)
    (F : Nat) {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hnm : ∀ n, blockNames.contains n = true →
      n.isModelSuffix = false)
    (hro : RenameOk mS.val envS f)
    (hIS : BlockInstalled blockNames envS mS.val)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envS.find? n = some ci)
    (henvLev : ∀ n, (envS.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported envS = natLitSupported env₃)
    (hcorr : ∀ n : Name, env₃.find? n = envS.find? n ∨
      ∃ cv mI' rP' rules',
        envS.find? n = some (.recInfo cv mI' rP' []) ∧
        env₃.find? n = some (.recInfo cv mI' rP' rules') ∧
        cv.name = n)
    {cvA : ConstantVal} {mI rP : Nat} {rules' : List RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envS.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkits : ∀ r' ∈ rules',
      RuleChecked F env₂ envS f cvA mI rP r') :
    RecMemberOk (V := V) env₃ mS.val
      (.recInfo cvA mI rP rules') := by
  intro cvR mI' rP' rules₀ hceq r hr
  injection hceq with e1 e2 e3 e4
  subst e1 e2 e3 e4
  obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, hnf, hcp,
    hplIff, hnestK, hrawf,
    hrawb, hann, hrhsf, hrhsb, hrlp, hrres, hstripR, hity, hplainImp⟩ :=
    hkits r hr
  have henvLev' : ∀ n, (env₃.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (envS.find? n).map (fun ci => ci.toConstantVal.levelParams) :=
    fun n => (henvLev n).symm
  have htoCV : ∀ n, (envS.find? n).map ConstantInfo.toConstantVal =
      (env₃.find? n).map ConstantInfo.toConstantVal := by
    intro n
    rcases hcorr n with heq | ⟨cv, a', b', c', hS0, h30, -⟩
    · rw [heq]
    · rw [hS0, h30]; rfl
  have hstr : strLitSupported envS = strLitSupported env₃ :=
    strLitSupported_env_ext htoCV hnat
  -- the rule right-hand side's truthfulness, transported up
  have hArhsS : ∀ ψ : Name → Nat,
      AnnotOk V mS.val envS ψ 0 (rho0 V) (RecRule.rhs r) := by
    intro ψ
    exact (inferTypeCore_sound (φ := ψ) mS F hity
      (WScoped.of_not_hasFvar hrhsf) hrhsb
      (Expr.LeavesBounded.of_not_hasFvar hrhsf)
      (FvarsOk.of_not_hasFvar hrhsf)).1
  refine ⟨fun ψ => AnnotOk.env_ext henvLev hnat hstr _ 0 (rho0 V)
    (hArhsS ψ), ?_, ?_, ?_, ?_⟩
  · intro hpt
    cases hfr : RecRule.fire r with
    | inert => exact absurd hfr hpt
    | plain =>
      exact recRulePlain_le_mI (recTy := cvA.type) (cnP := cnP)
        (hplIff.mp hfr)
    | nested lvls pins =>
      have h0 := (hnestK lvls pins hfr).1
      omega
  · intro hfr
    rw [hcp]
    exact recRulePlain_le (hplIff.mp hfr)
  · intro lvls pins hfr
    obtain ⟨-, -, -, -, hpinsLen, -⟩ := hnestK lvls pins hfr
    rw [hcp]
    exact hpinsLen
  intro cvj' cnP' cnF' hfj hne
  -- identify the constructor at the provisional environment
  have hfjS : envS.find? (RecRule.ctor r) =
      some (.ctorInfo cvj' cnP' cnF') := by
    rcases hcorr (RecRule.ctor r) with heq | ⟨cv2, a, b, e0, h₀,
      h₃, -⟩
    · rw [← heq]
      exact hfj
    · rw [h₃] at hfj
      exact nomatch (Option.some.inj hfj)
  have hfcS : envS.find? (RecRule.ctor r) =
      some (.ctorInfo cvj cnP cnF) := hup _ _ hfc
  obtain ⟨g1, g2, g3⟩ : cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
    rw [hfjS] at hfcS
    have h0 := Option.some.inj hfcS
    injection h0 with a1 a2 a3
    exact ⟨a1, a2, a3⟩
  subst cvj' cnP' cnF'
  -- environment agreement on stored names
  have hsome : ∀ n, (envS.find? n).isSome = (env₃.find? n).isSome := by
    intro n
    have h := henvLev n
    cases hS : envS.find? n with
    | none =>
      cases h3 : env₃.find? n with
      | none => rfl
      | some c => rw [hS, h3] at h; exact nomatch h
    | some c =>
      cases h3 : env₃.find? n with
      | none => rw [hS, h3] at h; exact nomatch h
      | some c' => rfl
  -- fire-mode case split
  cases hfr : RecRule.fire r with
  | inert => exact absurd hfr hne
  | nested lvls pins =>
    obtain ⟨hmIrP, hlvlsDef, hpinsFacts, hshapeM, hpinsLen0, hnck⟩ :=
      hnestK lvls pins hfr
    obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms,
      cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2,
      ldoms, lrest, hfthm, hcvt, hlpt, hopen, hheadEq, hargs3, hlhead,
      hlarity, hlpre, hmaj, hCresHead, hcinst, hclen, hdeIdx, hdeFld,
      hrinst, hdePre, hopenP, hannP0, hcinstN0, htlP0, hopenX,
      hcrest2Len, hlinst, hdeLam, hdeRhs, hlhsTyC, hrhsTyC, -⟩ := hnck
    -- the public prefix spine has exactly `rP` variables
    have hfvsPLen : fvsP.length = rP :=
      (openPisAtFvars_spec rP 0 hopenP).2.1
    have htake : fvsP.take rP = fvsP :=
      List.take_of_length_le (Nat.le_of_eq hfvsPLen)
    rw [htake] at hannP0 hcinstN0 htlP0
    -- the member-type shape
    obtain ⟨preM, nmM, domM, bodyM, bmM, Dn, hstripM0, -, -⟩ := hshapeM
    have htyStrip : (cvA.type.stripPis mI).isSome = true := by
      rw [hstripM0]
      rfl
    -- the pins' wf facts in the kit's terms
    have hpinsW : ∀ p ∈ pins, p.hasFvar = false ∧
        p.looseBVarsBounded rP = true := by
      intro p hp
      exact ⟨(hpinsFacts p hp).1, (hpinsFacts p hp).2.2.2⟩
    have hpinsRes : ∀ p ∈ pins, p.constsResolve envS = true :=
      fun p hp => (hpinsFacts p hp).2.2.1
    -- the block renaming is idempotent (model-shaped names are
    -- never members)
    have hffEq : ∀ n, f (f n) = f n := by
      intro n
      rw [hf]
      dsimp only
      by_cases hb : blockNames.contains n = true
      · rw [if_pos hb]
        rw [if_neg (fun hb2 => by
          have h0 := hnm _ hb2
          exact absurd h0 (by simp [Name.isModelSuffix]))]
      · rw [if_neg hb, if_neg hb]
    have hpinsRen2 : ∀ p ∈ pins, Expr.ErasedEq
        ((p.renameConsts f).renameConsts f) (p.renameConsts f) := by
      intro p _
      rw [Expr.renameConsts_idem_of hffEq]
      exact Expr.ErasedEq.rfl _
    -- the valuation reads only each constant's own parameters
    have hcvp : ConstValParams mS.val envS :=
      fun n ci' hfn => mS.val_params n ci' hfn
    -- the recursor's own stored facts
    have hselfMem := find?_mem hself
    obtain ⟨htyw, htyps, htyres, htyb, -, -⟩ := mS.wf _ hselfMem
    have hAty : ∀ ψ'' : Name → Nat,
        AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvA.type :=
      fun ψ'' => (mS.annot_ok _ hselfMem ψ'').1
    have hIty : ∀ ψ'' : Name → Nat, ∃ T,
        interpClosed V mS.val envS ψ'' cvA.type = some T := by
      intro ψ''
      obtain ⟨t, ht, -⟩ := mS.mem_type _ hselfMem ψ''
      exact ⟨t, ht⟩
    -- the constructor's stored facts
    have hfcMem := find?_mem hfcS
    obtain ⟨hCw, hCps, hCres, hCb, -, -⟩ := mS.wf _ hfcMem
    have hACty : ∀ ψ'' : Name → Nat,
        AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvj.type :=
      fun ψ'' => (mS.annot_ok _ hfcMem ψ'').1
    have hICty : ∀ ψ'' : Name → Nat, ∃ T,
        interpClosed V mS.val envS ψ'' cvj.type = some T := by
      intro ψ''
      obtain ⟨t, ht, -⟩ := mS.mem_type _ hfcMem ψ''
      exact ⟨t, ht⟩
    -- the recursor's model
    obtain ⟨cvm, mval, hm, hfm, hlpsm, -⟩ := hIS cvA.name hbnA _ hself
    have hfRm : envS.find? (f cvA.name) =
        some (.defnInfo cvm mval hm) := by
      rw [hf]
      dsimp only
      rw [if_pos hbnA]
      exact hfm
    -- the constructor's renamed head is stored with the right
    -- parameters
    obtain ⟨cimC, hfCm, hCmlps⟩ : ∃ cimC,
        envS.find? (f (RecRule.ctor r)) = some cimC ∧
        cimC.toConstantVal.levelParams = cvj.levelParams := by
      by_cases hbc : blockNames.contains (RecRule.ctor r) = true
      · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -⟩ := hIS _ hbc _ hfcS
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
    -- the pinned equality
    have heqfindS : envS.find? eqName = some eqA := hup _ _ heqfind
    have heqval : ∀ ψ'' : Name → Nat,
        mS.val eqName ψ'' = eqVal V ψ'' := by
      intro ψ''
      obtain ⟨-, hpv⟩ :=
        mS.ind_ok.2.2.2.1 eqName eqA heqfindS (by rfl) (by decide)
      rw [hpv ψ'']
      simp [pinnedVal]
    -- the theorem's facts
    have hfthmS : envS.find? thmName = some ci :=
      hup _ _ hfthm
    have hthmMem := find?_mem hfthmS
    obtain ⟨hSw, -, -, hSb, -, -⟩ := mS.wf _ hthmMem
    rw [hcvt] at hSw hSb
    have hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
        interpClosed V mS.val envS ψ'' cvt.type = some P ∧
        mS.val thmName ψ'' ∈ˢ P := by
      intro ψ''
      obtain ⟨P, hP, hm'⟩ := mS.mem_type _ hthmMem ψ''
      rw [hcvt] at hP
      have h3 : ci.name = thmName := by
        simpa using List.find?_some hfthmS
      exact ⟨P, hP, by rw [← h3]; exact hm'⟩
    have hthm_annot : ∀ ψ'' : Name → Nat,
        AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvt.type :=
      fun ψ'' => hcvt ▸ (mS.annot_ok _ hthmMem ψ'').1
    -- the rule's interpretation exists
    have hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
        interpClosed V mS.val envS ψ'' (RecRule.rhs r) = some L := by
      intro ψ''
      obtain ⟨-, ⟨v, tv', hiv, -, -⟩, -, -⟩ :=
        inferTypeCore_sound (φ := ψ'') mS F hity
          (WScoped.of_not_hasFvar hrhsf) hrhsb
          (Expr.LeavesBounded.of_not_hasFvar hrhsf)
          (FvarsOk.of_not_hasFvar hrhsf)
      exact ⟨v, hiv⟩
    -- the full clause at the provisional environment
    have hout := modeled_rule_eq_nested (R := cvA.name)
      (lps := cvA.levelParams) (ctor := RecRule.ctor r)
      (rhsA := RecRule.rhs r) (tyA := cvA.type) mS F hro hcvp
      hfr rfl hcp hnf rfl rfl rfl
      hself rfl hfRm hlpsm hfCm hCmlps hfcS rfl heqfindS heqval
      hthm_mem hthm_annot hSw hSb
      hmIrP htyStrip hpinsW hpinsLen0 hpinsRen2
      hpinsRes
      hopen hheadEq hargs3 hlhead hlarity hlpre hmaj hCresHead hCps
      hcinst hclen hdeIdx hrinst hdePre hdeFld
      hcrest2Len hopenP hcinstN0 htlP0 hopenX hlinst hdeLam
      hdeRhs hlhsTyC hrhsTyC
      hrhsf hrhsb hArhsS hIrhs htyw htyb hAty hIty hCw hCb hACty
      hICty htyres hCres
    obtain ⟨fvms, bL, hparts, hwf, hlen, hres, hsem⟩ := hout
    refine ⟨fvms, bL, hparts, hwf, hlen, ?_, ?_⟩
    · rw [← Expr.constsResolve_congr hsome]
      exact hres
    · intro ψ
      obtain ⟨hA, Rv, h1, h2⟩ := hsem ψ
      refine ⟨AnnotOk.env_ext henvLev hnat hstr _ 0 (rho0 V) hA,
        Rv, ?_, ?_⟩
      · show interpClosed V mS.val env₃ ψ (closeLamsAt fvms bL) =
          some Rv
        unfold interpClosed
        rw [← interp_env_ext henvLev hnat hstr _ 0 (rho0 V)]
        exact h1
      · show interpClosed V mS.val env₃ ψ (RecRule.rhs r) = some Rv
        unfold interpClosed
        rw [← interp_env_ext henvLev hnat hstr _ 0 (rho0 V)]
        exact h2
  | plain =>
  have hplain : Expr.recRulePlain cvA.type mI rP cnP = true :=
    hplIff.mp hfr
  -- the plain kit
  have hkit := hplainImp hplain
  obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms,
    cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2,
    ldoms, lrest, hfthm, hcvt, hlpt, hopen, hheadEq, hargs3, hlhead,
    hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
    hrinst, hdePre, hopenP, hcinstP, hdePars, hopenX, hlinst, hdeLam,
    hdeRhs, hlhsTyC, hrhsTyC, -⟩ := hkit
  -- the recursor's own stored facts
  have hselfMem := find?_mem hself
  obtain ⟨htyw, htyps, htyres, htyb, -, -⟩ := mS.wf _ hselfMem
  have hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvA.type :=
    fun ψ'' => (mS.annot_ok _ hselfMem ψ'').1
  have hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V mS.val envS ψ'' cvA.type = some T := by
    intro ψ''
    obtain ⟨t, ht, -⟩ := mS.mem_type _ hselfMem ψ''
    exact ⟨t, ht⟩
  -- the constructor's stored facts
  have hfcMem := find?_mem hfcS
  obtain ⟨hCw, hCps, hCres, hCb, -, -⟩ := mS.wf _ hfcMem
  have hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvj.type :=
    fun ψ'' => (mS.annot_ok _ hfcMem ψ'').1
  have hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V mS.val envS ψ'' cvj.type = some T := by
    intro ψ''
    obtain ⟨t, ht, -⟩ := mS.mem_type _ hfcMem ψ''
    exact ⟨t, ht⟩
  -- the recursor's model
  obtain ⟨cvm, mval, hm, hfm, hlpsm, -⟩ := hIS cvA.name hbnA _ hself
  have hfRm : envS.find? (f cvA.name) = some (.defnInfo cvm mval hm) := by
    rw [hf]
    dsimp only
    rw [if_pos hbnA]
    exact hfm
  -- the constructor's renamed head is stored with the right parameters
  obtain ⟨cimC, hfCm, hCmlps⟩ : ∃ cimC,
      envS.find? (f (RecRule.ctor r)) = some cimC ∧
      cimC.toConstantVal.levelParams = cvj.levelParams := by
    by_cases hbc : blockNames.contains (RecRule.ctor r) = true
    · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -⟩ := hIS _ hbc _ hfcS
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
  -- the pinned equality
  have heqfindS : envS.find? eqName = some eqA := hup _ _ heqfind
  have heqval : ∀ ψ'' : Name → Nat, mS.val eqName ψ'' = eqVal V ψ'' := by
    intro ψ''
    obtain ⟨-, hpv⟩ :=
      mS.ind_ok.2.2.2.1 eqName eqA heqfindS (by rfl) (by decide)
    rw [hpv ψ'']
    simp [pinnedVal]
  -- the theorem's facts (kind-agnostic: any stored constant
  -- witnesses its type's inhabitation, `mem_type`)
  have hfthmS : envS.find? thmName = some ci :=
    hup _ _ hfthm
  have hthmMem := find?_mem hfthmS
  obtain ⟨hSw, -, -, hSb, -, -⟩ := mS.wf _ hthmMem
  rw [hcvt] at hSw hSb
  have hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V mS.val envS ψ'' cvt.type = some P ∧
      mS.val thmName ψ'' ∈ˢ P := by
    intro ψ''
    obtain ⟨P, hP, hm⟩ := mS.mem_type _ hthmMem ψ''
    rw [hcvt] at hP
    have h3 : ci.name = thmName := by
      simpa using List.find?_some hfthmS
    exact ⟨P, hP, by rw [← h3]; exact hm⟩
  have hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V mS.val envS ψ'' 0 (rho0 V) cvt.type :=
    fun ψ'' => hcvt ▸ (mS.annot_ok _ hthmMem ψ'').1
  -- the rule's interpretation exists
  have hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V mS.val envS ψ'' (RecRule.rhs r) = some L := by
    intro ψ''
    obtain ⟨-, ⟨v, tv', hiv, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ'') mS F hity
        (WScoped.of_not_hasFvar hrhsf) hrhsb
        (Expr.LeavesBounded.of_not_hasFvar hrhsf)
        (FvarsOk.of_not_hasFvar hrhsf)
    exact ⟨v, hiv⟩
  -- the full clause at the provisional environment
  have hout := modeled_rule_eq_plain (R := cvA.name)
    (lps := cvA.levelParams) (ctor := RecRule.ctor r)
    (rhsA := RecRule.rhs r) (tyA := cvA.type) mS F hro
    hfr rfl hcp hnf rfl rfl rfl
    hself rfl hfRm hlpsm hfCm hCmlps hfcS rfl heqfindS heqval
    hthm_mem hthm_annot hSw hSb
    (recRulePlain_strip hplain) (recRulePlain_le_mI hplain)
    (recRulePlain_le hplain)
    hopen hheadEq hargs3 hlhead hlarity hlpre hmaj hcstrip hcinst
    hclen hdeIdx hrinst hdePre hdeFld
    hopenP hcinstP hdePars hopenX hlinst hdeLam hdeRhs hlhsTyC hrhsTyC
    hrhsf hrhsb hArhsS hIrhs htyw htyb hAty hIty hCw hCb hACty hICty
    htyres hCres
  obtain ⟨fvms, bL, hparts, hwf, hlen, hres, hsem⟩ := hout
  refine ⟨fvms, bL, hparts, hwf, hlen, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr hsome]
    exact hres
  · intro ψ
    obtain ⟨hA, Rv, h1, h2⟩ := hsem ψ
    refine ⟨AnnotOk.env_ext henvLev hnat hstr _ 0 (rho0 V) hA,
      Rv, ?_, ?_⟩
    · show interpClosed V mS.val env₃ ψ (closeLamsAt fvms bL) = some Rv
      unfold interpClosed
      rw [← interp_env_ext henvLev hnat hstr _ 0 (rho0 V)]
      exact h1
    · show interpClosed V mS.val env₃ ψ (RecRule.rhs r) = some Rv
      unfold interpClosed
      rw [← interp_env_ext henvLev hnat hstr _ 0 (rho0 V)]
      exact h2

theorem SwapList.of_eq {env₃ : Env} {val : ConstVal V} :
    ∀ (l : List ConstantInfo), SwapList env₃ val l l
  | [] => SwapList.nil
  | _c :: l => SwapList.cons (Or.inl rfl) (SwapList.of_eq l)

/-- The two chains' environments are swap-related, given each pair's
obligations. -/
theorem chains_swap {F : Nat} {blockNames : List Name}
    {env' envS env₃ : Env} {f : Name → Name} {val : ConstVal V} :
    ∀ {zipped : List ((ConstantVal × Nat × Nat × List RecRule) × List RecRule)}
      {accS acc₃ envSelf env₃' : Env},
      ProvFacts F blockNames accS envSelf (zipped.map Prod.fst) →
      RulesChain F env' envS f acc₃ env₃' zipped →
      (∀ z ∈ zipped, SwapPair env₃ val
        (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 [])
        (.recInfo z.1.1 z.1.2.1 z.1.2.2.1
          z.2)) →
      SwapList env₃ val accS.consts acc₃.consts →
      SwapList env₃ val envSelf.consts env₃'.consts := by
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
          (SwapList.cons (hob _ List.mem_cons_self) hacc)

set_option maxHeartbeats 3200000 in
/-- Checking and installing a block's recursor group preserves having
a model with the block invariant. -/
theorem checkIndRecs_sound {F : Nat} {blockNames : List Name}
    {env₂ env₃ : Env} {recs : List ConstantInfo}
    (h : checkIndRecs (fueledOps F) blockNames env₂ recs = .ok env₃)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hnm : ∀ n, blockNames.contains n = true →
      n.isModelSuffix = false)
    (m : EnvModel V env₂) (hI : BlockInstalled blockNames env₂ m.val) :
    ∃ m₃ : EnvModel V env₃, BlockInstalled blockNames env₃ m₃.val := by
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
  cases hprov : provisionRecs (fueledOps F) blockNames env₂ recs with
  | error e => intro h; exact nomatch h
  | ok p => ?_
  intro h
  try dsimp only at h
  obtain ⟨envSelf, checked⟩ := p
  try dsimp only at h
  obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv checked env₂ env₃ h
  obtain ⟨mS, hIS, hpres, hProv⟩ := provisionRecs_sound recs env₂
    (envSelf, checked) hprov hbn m hI
  rw [show checked = zipped.map Prod.fst from hmap.symm] at hProv
  -- shape-level correspondence and its congruences
  have hswSh := chains_swapSh hProv hchain (SwapShList.of_eq env₂.consts)
  have hcorr0 := swapSh_find?_corr hswSh
  have hcorr : ∀ n : Name, env₃.find? n = envSelf.find? n ∨
      ∃ cv mI' rP' rules',
        envSelf.find? n = some (.recInfo cv mI' rP' []) ∧
        env₃.find? n = some (.recInfo cv mI' rP' rules') ∧
        cv.name = n := hcorr0
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
    have hone : ∀ (chk : Option ConstantInfo → Bool) (n : Name),
        (∀ cv mI' rP' rules',
          chk (some (.recInfo cv mI' rP' rules')) = false) →
        chk (envSelf.find? n) = chk (env₃.find? n) := by
      intro chk n hrec
      rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃, hrec, hrec]
    rw [hone natIndOk natName (fun _ _ _ _ => rfl),
      hone natZeroOk natZeroName (fun _ _ _ _ => rfl),
      hone natSuccOk natSuccName (fun _ _ _ _ => rfl)]
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
  have hro : RenameOk mS.val envSelf (fun n =>
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
  have hob : ∀ z ∈ zipped, SwapPair env₃ mS.val
      (.recInfo z.1.1 z.1.2.1 z.1.2.2.1 [])
      (.recInfo z.1.1 z.1.2.1 z.1.2.2.1
        z.2) := by
    intro z hz
    have hz1 : z.1 ∈ zipped.map Prod.fst := List.mem_map_of_mem hz
    obtain ⟨hnres, hshape, hms, hbnc, htyf, htyb, htlp, htres, hmodel,
      hself⟩ := ProvFacts.mem_facts hProv z.1 hz1
    have hcir := RulesChain.mem_facts hchain z hz
    have hkits : ∀ r' ∈ z.2, RuleChecked F env₂ envSelf (fun n =>
        if blockNames.contains n then n.str "_model" else n)
        z.1.1 z.1.2.1 z.1.2.2.1 r' :=
      checkIotaRules_inv 0 _ _ hcir
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
        obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -,
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
      obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, -⟩ :=
        hkits r hr
      refine ⟨cvj, cnP, cnF, ?_⟩
      refine hfindUp3 _ _ (ProvFacts.find?_preserved hProv _ _ hfc)
        (fun _ _ _ _ hcon => nomatch hcon)
    · -- the fold obligations
      exact recMemberOk_of_kit mS F rfl hnm hro hIS
        (ProvFacts.find?_preserved hProv) henvLev hnat hcorr hbnc hself
        heqf hkits
  -- the group swap
  have hswap : SwapList env₃ mS.val envSelf.consts env₃.consts :=
    chains_swap hProv hchain hob (SwapList.of_eq env₂.consts)
  obtain ⟨m₃, hveq⟩ := extend_rules_eq mS hswap
  refine ⟨m₃, ?_⟩
  intro n hn ci₃ hf₃
  rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hIS n hn ci₃ hf₃
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · exact hfindUp3 _ _ hfm₂ (fun _ _ _ _ hcon => nomatch hcon)
    · intro ψ
      rw [hveq n ψ, hveq (n.str "_model") ψ]
      exact hv₂ ψ
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hIS n hn _ h₀
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · exact hfindUp3 _ _ hfm₂ (fun _ _ _ _ hcon => nomatch hcon)
    · intro ψ
      rw [hveq n ψ, hveq (n.str "_model") ψ]
      exact hv₂ ψ





end Setlec
