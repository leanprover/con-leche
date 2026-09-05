import Setlec.SetBase.IndBlockRun
import Setlec.SetP.ProjConsP

/-!
# The projection-function phase, P tier (task #161, IND TIER part 10)

`projFnS`/`projInstallS`/`templateConsS`/`templatesS` at the reading,
**unblocked by the fifth widening**: `ProjFnR` now records the sides
pack's two runs, which is exactly what `indBottomProjP` takes.

The shape is v1's, with one deliberate difference: `projFnP` and
`projInstallP` carry the v1 carrier *with* them (they call `projFnS`
and `projInstallS` internally) rather than taking it as a premise.  The
projection fold is the one phase where the two tiers' step data are
genuinely coupled — the P cons needs `EnvS V ⟨c₀ :: env'.consts⟩`
constructively, and the *next* step's v1 premises (`ProjPhaseInvS`,
`BlockInstalledTT`) are the previous step's v1 outputs — so running the
two folds separately would mean re-deriving the whole v1 chain at every
index.

**Where the bottom runs** is v1's own reading, unchanged: `checkProjFn`
performs its checks *before* the recursor is stored, so the whole kit
lives at the base environment, and instantiating `indBottomProjP` at
`Rn := projModelName T i` makes its conclusion a law about
`acval (T._model.proj_i)` — which at the cons *is* the installed
constant's leaf (`acvalWith_self`).  P1's "a helper premised on a
bundle cannot establish a field of that bundle" applies verbatim at the
P tier: `rec_rules` is an `EnvS2PM` field, so the bottom cannot fire at
the extension.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule RecRuleFire IndCaps ProjEntry BinderMeta projFnName
  projModelName projFwd ReducibilityHint inferTypeCore isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

set_option maxHeartbeats 6400000 in
/-- **One projection field installs, at both tiers** (`projFnS`'s
twin).  The bottom fires at the *base* environment under
`Rn := projModelName T i`; `projConsP` then stores the entry, and
`acvalWith_self` makes the base law's head the installed constant's
leaf. -/
theorem projFnP (hμ : μ.verified = true) {F : Nat} {env' env₁ : Env}
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {blockNames : List Name} (mp : EnvS2PM V μ env')
    (hR : ProjFnRunR μ F env' T ctorName lps nP nF i env₁)
    (hinv : ProjPhaseInvS T ctorName nF env' mp.base2.cvalE)
    (hinvA : ProjPhaseAcvalP T ctorName nF env' mp.base2.acval)
    (hIB : BlockInstalledTT blockNames env' mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env' mp.base2.acval)
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false)
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      Setlec.EtaPins μ env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) :
    ∃ mp₁ : EnvS2PM V μ env₁,
      mp₁.base2.cvalE = cvalWith mp.base2.cvalE (projFnName T i)
        (fun ψ => mp.base2.cvalE (projModelName T i) ψ) ∧
      ProjPhaseInvS T ctorName nF env₁ mp₁.base2.cvalE ∧
      ProjPhaseAcvalP T ctorName nF env₁ mp₁.base2.acval ∧
      BlockInstalledTT blockNames env₁ mp₁.base2.cvalE ∧
      BlockAcvalInstalled blockNames env₁ mp₁.base2.acval := by
  -- the kit, unpacked exactly as `projFnS` unpacks it (the two H1
  -- widenings' rows named rather than dropped)
  have hRid := hR
  obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps, hpnone,
    hTf, heqf, hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1,
    hilt, hstripP, hbig, henv⟩ := hR
  obtain ⟨cbinders, cbody, hCstrip, hcbodyArity, hcbodyHead, hrhsw,
    -- `-` at position 11: `ProjFnR`'s rule-rhs **derivation** row, no
    -- longer consumed (task #161 S10 — the reading comes from the run
    -- below).  The campaign's own diagnostic, applied to itself: a
    -- conjunct every proof projects away is a layering artifact.
    hrhsb, hrlp, hrres, hrstrip, hrhsRun, hthmpack⟩ := hbig
  obtain ⟨rbinders, hrhsAstrip, hrdomsEq⟩ := hrstrip
  obtain ⟨tcv, tval, hthmE, htlps, hsbodyPin, fvsI, sbodyO, hopen,
    hsty1, hsty2⟩ := hthmpack
  obtain ⟨sbinders, ℓA, tySlot, hSstrip, hdomsSC⟩ := hsbodyPin
  subst henv
  have hfresh : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hCf : (env'.find? ctorName).isSome = true := by rw [hctor]; rfl
  -- the model projection is not the constructor: the stored kinds clash
  have hPCne : projModelName T i ≠ ctorName := by
    intro hh
    rw [hh, hctor] at hfm
    exact nomatch (Option.some.inj hfm)
  -- the pruned projection renaming, at both tiers
  have hro := projFwd_renameOkT hinv
  have hroP := projFwd_renameOkP hinv hinvA
  have hfRn : (if (env'.find? (projModelName T i)).isSome = true then
      projFwd T ctorName nF (projModelName T i)
      else projModelName T i) = projModelName T i := by
    rw [if_pos (show (env'.find? (projModelName T i)).isSome = true
      from by rw [hfm]; rfl)]
    exact projFwd_model_self hPCne
  have hfCt : (if (env'.find? ctorName).isSome = true then
      projFwd T ctorName nF ctorName else ctorName)
      = ctorName.str "_model" := by
    rw [if_pos hCf]
    unfold projFwd
    by_cases hCT : ctorName = T
    · rw [if_pos hCT, hCT]
    · rw [if_neg hCT, if_pos rfl]
  -- the stored constants' syntactic facts
  obtain ⟨hCw, -, hCres, hCb, -, -, -⟩ :=
    mp.base2.wf _ (find?_mem hctor)
  obtain ⟨hSw, -, -, hSb, -, -, -⟩ :=
    mp.base2.wf _ (find?_mem hthmE)
  have hClp :
      cvj.type.allLevelParamsDefined cvj.levelParams = true := by
    obtain ⟨-, h2, -⟩ := mp.base2.wf _ (find?_mem hctor)
    exact h2
  -- the model constructor, from the phase invariant
  obtain ⟨cvmC, mvalC, hmC, hfCm, hlpsC, -⟩ := hinv.2.1 _ hctor
  -- the statement's opened parts (V-free, v1's own computation)
  obtain ⟨hfvsIlen, hheadEqO, αS, hargs3O⟩ :=
    projStmtParts hilt hSb hopen hSstrip
  obtain ⟨ctorSpine, hctorSpine⟩ : ∃ e, e = Expr.mkAppN
      (.const (ctorName.str "_model") (cvj.levelParams.map .param))
      (fvsI.take nP ++ fvsI.drop nP) := ⟨_, rfl⟩
  obtain ⟨lhsLit, hlhsLit⟩ : ∃ e, e = Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (fvsI.take nP ++ [ctorSpine]) := ⟨_, rfl⟩
  have hargs3 : sbodyO.getAppArgs
      = [αS, lhsLit, fvsI.getD (nP + i) default] := by
    rw [hlhsLit, hctorSpine]; exact hargs3O
  have hlargsE : lhsLit.getAppArgs = fvsI.take nP ++ [ctorSpine] := by
    rw [hlhsLit]; exact Expr.getAppArgs_mkAppN _ _
  have htakeLen : (fvsI.take nP).length = nP := by
    rw [List.length_take]; omega
  have hlhead : lhsLit.getAppFn
      = Expr.const (if (env'.find? (projModelName T i)).isSome = true
        then projFwd T ctorName nF (projModelName T i)
        else projModelName T i) (lps.map .param) := by
    rw [hlhsLit, Expr.getAppFn_mkAppN, hfRn]
    rfl
  have hlarity : lhsLit.getAppArgs.length = nP + 1 := by
    rw [hlargsE]
    simp [htakeLen]
  have hlpre : lhsLit.getAppArgs.take nP = fvsI.take nP := by
    rw [hlargsE]
    exact List.take_left' htakeLen
  have hmaj : lhsLit.getAppArgs.getLastD (.bvar 0) = ctorSpine := by
    rw [hlargsE]
    simp
  -- the domain pin, at the pruned renaming
  have hdomsSCp : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < nP + nF → sbinders[i0]? = some b → cbinders[i0]? = some b' →
      b.2.1 = b'.2.1.renameConsts (fun n =>
        if (env'.find? n).isSome = true then
          projFwd T ctorName nF n else n) := by
    intro i0 b b' hi0 hb hb'
    rw [Expr.renameConsts_congr_resolve
      (g := projFwd T ctorName nF)
      (fun n hn => by simp only [hn, if_true]) _
      ((Expr.constsResolve_stripPis (nP + nF) hCstrip hCres).1 b'
        (List.mem_of_getElem? hb'))]
    exact hdomsSC i0 b b' hi0 hb hb'
  -- the sides pack's two recorded runs, at the opened body's arguments
  have hsideL : ∃ tl, inferTypeCore μ env' F (nP + nF) lhsLit = .ok tl ∧
      isDefEqCore μ env' F (nP + nF) tl αS = .ok true := by
    have h := hsty1
    rw [hargs3] at h
    simpa using h
  have hsideR : ∃ tr, inferTypeCore μ env' F (nP + nF)
      (fvsI.getD (nP + i) default) = .ok tr ∧
      isDefEqCore μ env' F (nP + nF) tr αS = .ok true := by
    have h := hsty2
    rw [hargs3] at h
    simpa using h
  -- the four claims and the reads, at every assignment
  have hclaims := fun ψ =>
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hdeq : ∀ ψ : Name → Nat, DefEqClaims2P μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.1
  have hinf : ∀ ψ : Name → Nat, InferClaims2P μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.2
  have hreadsP : ∀ ψ : Name → Nat, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
  -- ===== the rule rhs's front door, at the reading (the H1 exposure,
  -- fourth widening — `iotaRulePlainP`'s three-part construction)
  have hrhsLeafNil : ∀ l ∈ rhsA.fvarLeaves, False := by
    intro l hl
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at hl
    exact nomatch hl
  have hrhsWs : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsw
  have hrhsLb : Expr.LeavesBounded rhsA :=
    fun l hl => absurd hl (fun h => hrhsLeafNil l h)
  obtain ⟨t', hrun⟩ := hrhsRun
  have hrhsKey : ∀ ψ : Name → Nat, ∃ Ra ta,
      denoteP mp.base2.acval env' ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, AnnotOkP V ρ Ra ∧
        interp2 V ρ Ra ∈ˢ interp2 V ρ ta := by
    intro ψ
    -- **the reading, from the RUN** (task #161 S10).  It used to come
    -- from `ProjFnR`'s derivation row (`hrhsKeyV`: `∀ φ, ∃ Rv t,
    -- denoteClosed … ∧ Infer …`) through `denotePClosed_isSome_of_
    -- denoteClosed`.  `acceptedReadsP_of` — "whatever `inferTypeCore`
    -- accepts, `denoteP` reads", ENDGAME A's own walk — produces it
    -- from `hrun`, the record's *recorded run*, with no derivation and
    -- no relation.  That leaves the derivation row unconsumed here,
    -- which is what makes the ind tier's record split a deletion.
    obtain ⟨Ra, hRa⟩ :=
      acceptedReadsP_of mp.base2 ψ hrun hrhsWs hrhsb hrhsLb
    have hctx : CtxOkP mp.base2 ψ 0 [] rhsA :=
      ⟨rfl, fun l hl => absurd hl (fun h => hrhsLeafNil l h)⟩
    obtain ⟨ta, hta⟩ := hreadsP ψ hrun hrhsWs hrhsb hrhsLb
      (LeafReadsP.of_ctxOkP hctx) hRa
    obtain ⟨hokRa, -, hmemRa⟩ :=
      hinf ψ hrun hrhsWs hrhsb hrhsLb hctx hRa hta
    exact ⟨Ra, ta, hRa, fun ρ =>
      ⟨hokRa ρ (Sat2_nil V ρ), hmemRa ρ (Sat2_nil V ρ)⟩⟩
  -- the statement's front doors
  have hthmP : ∀ ψ : Name → Nat, ∃ ta,
      denoteP mp.base2.acval env' ψ 0 tcv.type = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp2 V ρ ta) ∧
        AnnotOkP V ρ ta := by
    intro ψ
    obtain ⟨ta, hta, hok, hmem⟩ := mp.acval_memTypeP hthmE ψ
    exact ⟨ta, hta, fun ρ => ⟨⟨_, hmem ρ⟩, hok ρ⟩⟩
  -- **the bottom fires, at the base environment**
  have hbot := indBottomProjP (V := V) (Rn := projModelName T i)
    (lps := lps) (tyA := pty) (mI := nP) (rP := nP) (i := i)
    mp hdeq hinf hreadsP hroP heqf (by rw [hfRn]; exact hfm)
    (show ConstantVal.levelParams
      (ConstantInfo.defnInfo mcv mval mhint).toConstantVal = lps
      from hmlps) hctor
    (by rw [hfCt]; exact hfCm)
    (show ConstantVal.levelParams
      (ConstantInfo.defnInfo cvmC mvalC hmC).toConstantVal
      = cvj.levelParams from hlpsC)
    hCw hCb hClp rfl rfl hilt
    hCstrip hcbodyArity hrhsw hrhsb hrhsAstrip hrdomsEq
    hrhsKey hSw hSb hthmP hopen hheadEqO hargs3 hlhead hlarity hlpre
    (by rw [hmaj, hctorSpine, hfCt]) rfl hSstrip hdomsSCp
    hsideL hsideR
  -- **the install's model-free half** (task #161 S7, Wall C): the
  -- phase and block invariants at the installed environment are
  -- `projFnInv`'s and the store's `EnvWF` and the head rule's
  -- constructor are `projFnR_head`'s — both off `ProjFnR` alone.
  obtain ⟨hinv₁, hIB₁⟩ :=
    projFnInv (cval := mp.base2.cvalE) hRid hinv hIB hbshape
  obtain ⟨hwf₁, hctors₁⟩ := projFnR_head mp.base2.wf hRid
  have hnotb : blockNames.contains (projFnName T i) = false := by
    cases hc : blockNames.contains (projFnName T i) with
    | false => rfl
    | true =>
      exact absurd (hbshape _ hc)
        (by rw [show (projFnName T i).isProjFnShape = true from rfl]
            exact fun hh => nomatch hh)
  have hfreshC : env'.find? (ConstantInfo.name (projEntry T lps pty nP i
      [(⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ : RecRule)])) = none := hfresh
  have hCne : ctorName ≠ projFnName T i := by
    intro hh
    rw [hh, hfresh] at hctor
    exact nomatch hctor
  -- **the bridge**: the base law, read at the installed entry
  have hcbRhs : ∀ us : List Level,
      ConstsBound env' (rhsA.instantiateLevelParams lps us) := by
    intro us
    refine constsBound_of_constsResolve _ ?_
    rw [Expr.constsResolve_instantiateLevelParams]
    exact hrres
  have hcbPty : ∀ us : List Level,
      ConstsBound env' (pty.instantiateLevelParams lps us) := by
    intro us
    refine constsBound_of_constsResolve _ ?_
    rw [Expr.constsResolve_instantiateLevelParams]
    exact hptyres
  have hptyReadPre : ∀ (ψ : Name → Nat), ∃ ta : AVExpr,
      denoteP mp.base2.acval env' ψ 0 pty = some ta := by
    intro ψ
    obtain ⟨ta, hta, -, -⟩ := mp.acval_memTypeP hfm ψ
    refine ⟨ta, ?_⟩
    rw [← denoteP_renameConsts hroP pty 0,
      Expr.renameConsts_congr_resolve (g := projFwd T ctorName nF)
        (fun n hn => by simp only [hn, if_true]) _ hptyres,
      eq_of_beq hround]
    exact hta
  have hnew : ∀ m₂ : EnvS2Core V
      ⟨projEntry T lps pty nP i [⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩] :: env'.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (projFnName T i)
        (fun ψ => mp.base2.acval (projModelName T i) ψ) →
      ∀ (φ : Name → Nat), ∀ rl ∈ [(⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ : RecRule)],
        RecRule.fire rl ≠ .inert →
        RecRuleLawP m₂ φ (projFnName T i) ⟨projFnName T i, lps, pty⟩
          nP nP rl := by
    intro m₂ hac φ rl hrl hfire
    obtain rfl : rl = ⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ := by
      rcases List.mem_cons.mp hrl with h | h
      · exact h
      · exact nomatch h
    have hplainFire : (if Expr.recRulePlain pty nP nP nP then
        RecRuleFire.plain else .inert) = .plain := by
      by_cases hc : Expr.recRulePlain pty nP nP nP = true
      · simp [hc]
      · exact absurd (show RecRule.fire _ = RecRuleFire.inert from by
          simp only [eq_false_of_ne_true hc]; rfl) hfire
    refine ⟨Nat.le_refl _, ?_⟩
    intro us hus
    obtain ⟨Ra, hRaden, hokRa, hRalaw⟩ := hbot φ us hus
    refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
    · rw [hac]
      exact denoteP_cons_fresh_mono hfreshC
        (fun _ h => ConstantInfo.noConfusion h) φ 0 _ (hcbRhs us) hRaden
    · -- the `.nested` pin conjunct: the rule is `.plain`
      intro lvls pins hn
      rw [hplainFire] at hn
      exact nomatch hn
    intro cvj' cnP' cnF' hfc' usj ρ xs ys TVa TVja restR restC hlenX
      hlenY husjlen hlev hplain hnested hidx hTVa hTVja hfitR hfitC
    -- the stored constructor is the one the kit named
    have hfcjE : env'.find? ctorName = some (.ctorInfo cvj' cnP' cnF') := by
      rw [Env.find?_cons, if_neg (show ¬(projEntry T lps pty nP i
        [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
          .plain else .inert, rhsA⟩]).name = ctorName from
        fun hh => hCne hh.symm)] at hfc'
      exact hfc'
    obtain ⟨rfl, rfl, rfl⟩ : cvj' = cvj ∧ cnP' = nP ∧ cnF' = nF := by
      rw [hctor] at hfcjE
      obtain ⟨h1, h2, h3⟩ :=
        ConstantInfo.ctorInfo.inj (Option.some.inj hfcjE)
      exact ⟨h1.symm, h2.symm, h3.symm⟩
    -- the two type readings, produced at the prefix and identified
    -- with the given extension readings by determinism
    obtain ⟨TVa', hTVa'⟩ : ∃ ta,
        denoteP mp.base2.acval env' φ 0
          (pty.instantiateLevelParams lps us) = some ta := by
      obtain ⟨ta, hta⟩ := hptyReadPre (Level.substFn φ lps us)
      exact ⟨ta, by rw [denotePInstLevels]; exact hta⟩
    obtain rfl : TVa' = TVa := by
      refine Option.some.inj (Eq.trans ?_ hTVa)
      rw [hac]
      exact (denoteP_cons_fresh_mono hfreshC
        (fun _ h => ConstantInfo.noConfusion h) φ 0 _ (hcbPty us)
        hTVa').symm
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mp.constTypeP 0 ctorName _ usj hctor (by exact husjlen)
    obtain rfl : TVja' = TVja := by
      refine Option.some.inj (Eq.trans ?_ hTVja)
      rw [hac]
      exact (denoteP_cons_fresh_mono hfreshC
        (fun _ h => ConstantInfo.noConfusion h) φ 0 _
        (constsBound_instType mp.base2.wf
          (Env.find?_mem hctor) usj) hTVja').symm
    -- the two leaves the conclusion mentions
    dsimp only at hfitR ⊢
    rw [hac, acvalWith_ne hCne] at hfitR
    rw [hac, acvalWith_ne hCne, acvalWith_self]
    refine hRalaw usj ρ xs ys TVa' TVja' restR restC hlenX hlenY
      husjlen ?_ (fun i0 h1 h2 => hplain hplainFire i0 h1 h2) hidx
      hTVa' hTVja' hfitR hfitC
    rw [hlev, recFireComparands_plain hplainFire]
  -- the P cons
  obtain ⟨mp₁, hacc, hinvA₁, hIA₁⟩ :=
    projConsP mp rfl hfm hmlps hpnone hround hptyres hinv hinvA hilt
      hTf hCf hIB hIA hTblock hnotb hpinsT hCblock hFields hwf₁
      (fun cvR mI rP rules₀ heq => hctors₁ cvR mI rP rules₀ heq)
      hnew
  -- the v1 valuation at the extension, read off the leaf equation
  -- through `acval_erase` (`memberInstallPM`'s move)
  have hcval₁ : mp₁.base2.cvalE
      = cvalWith mp.base2.cvalE (projFnName T i)
        (fun ψ => mp.base2.cvalE (projModelName T i) ψ) := by
    funext n ψ
    rw [← mp₁.base2.acval_erase n ψ, hacc]
    by_cases hn : n = projFnName T i
    · subst hn
      rw [acvalWith_self]
      show (mp.base2.acval (projModelName T i) ψ).erase = _
      rw [mp.base2.acval_erase]
      exact (congrFun cvalWith_self ψ).symm
    · rw [acvalWith_ne hn, mp.base2.acval_erase]
      exact (congrFun (cvalWith_ne hn) ψ).symm
  exact ⟨mp₁, hcval₁, by rw [hcval₁]; exact hinv₁,
    hinvA₁, by rw [hcval₁]; exact hIB₁, hIA₁⟩

set_option maxHeartbeats 1600000 in
/-- **The projection-function fold, at both tiers** (`projInstallS`).
The skip branch is a no-op; the block-level premises are re-established
at each step exactly as in v1 (`EtaPins.step` plus "a projection name
is never a block name"). -/
theorem projInstallP (hμ : μ.verified = true) {F : Nat}
    {T ctorName : Name} {lps : List Name} {nP nF : Nat}
    {blockNames : List Name}
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ∀ (fields : List Nat) {env' : Env} (mp : EnvS2PM V μ env')
      {env₄ : Env},
      ProjInstallRunR μ F T ctorName lps nP nF env' fields env₄ →
      ProjPhaseInvS T ctorName nF env' mp.base2.cvalE →
      ProjPhaseAcvalP T ctorName nF env' mp.base2.acval →
      BlockInstalledTT blockNames env' mp.base2.cvalE →
      BlockAcvalInstalled blockNames env' mp.base2.acval →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        Setlec.EtaPins μ env' T cvT.levelParams capsT) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → blockNames.contains capsT.etaCtor = true) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → capsT.etaFields = nF) →
      ∃ mp₄ : EnvS2PM V μ env₄,
        ProjPhaseInvS T ctorName nF env₄ mp₄.base2.cvalE ∧
        ProjPhaseAcvalP T ctorName nF env₄ mp₄.base2.acval ∧
        BlockInstalledTT blockNames env₄ mp₄.base2.cvalE ∧
        BlockAcvalInstalled blockNames env₄ mp₄.base2.acval := by
  intro fields
  induction fields with
  | nil =>
    intro env' mp env₄ h hinv hinvA hIB hIA hpinsT hCblock hFields
    subst h
    exact ⟨mp, hinv, hinvA, hIB, hIA⟩
  | cons i rest ih =>
    intro env' mp env₄ h hinv hinvA hIB hIA hpinsT hCblock hFields
    obtain ⟨env'', hstep, hrec⟩ := h
    rcases hstep with hR | ⟨hskip, rfl⟩
    case inr =>
      exact ih mp hrec hinv hinvA hIB hIA hpinsT hCblock hFields
    -- the install branch
    obtain ⟨mp₁, -, hinv₁, hinvA₁, hIB₁, hIA₁⟩ :=
      projFnP hμ mp hR hinv hinvA hIB hIA hTblock hbshape hpinsT
        hCblock hFields
    -- the block-level premises, re-established (v1's argument)
    obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps,
      hpnone, hTf, -, -, -, -, -, -, -, -, hilt, -, -, henv⟩ := hR
    have hfresh : env'.find? (projFnName T i) = none :=
      Option.isNone_iff_eq_none.mp hpnone
    have hTne : T ≠ projFnName T i := by
      intro hh
      rw [hh, hfresh] at hTf
      exact nomatch hTf
    have hdown : ∀ (cvT : ConstantVal) (capsT : IndCaps),
        env''.find? T = some (.indInfo cvT capsT) →
        env'.find? T = some (.indInfo cvT capsT) := by
      intro cvT capsT hf
      rw [henv, Env.find?_cons,
        if_neg (fun hh => hTne hh.symm)] at hf
      exact hf
    refine ih mp₁ hrec hinv₁ hinvA₁ hIB₁ hIA₁
      (fun cvT capsT hf => by
        rw [henv]
        exact Setlec.EtaPins.step (hpinsT cvT capsT (hdown cvT capsT hf))
          hfresh)
      (fun cvT capsT hf => hCblock cvT capsT (hdown cvT capsT hf))
      (fun cvT capsT hf => hFields cvT capsT (hdown cvT capsT hf))

/-! ## The elimination templates

The entry carries no model artifact, so the install *chooses* a leaf.
v1 chooses `VExpr.eqE (.sort 0) .prf .prf`; the reading tier's leaf must
erase to it, so the only choice is `AVExpr.eqE (.sort 0) .prf .prf` —
and, unlike the *spine padding* of part 4 (where `.prf` fails
`pt_not_mem_univZero`), that is fine here: the `.prf`s sit inside
`eqv`'s arguments, which no membership obligation reads, and the whole
entry's obligation is `eqv pt pt ∈ˢ univ 0` — `eqv_mem_univ`, which is
blind to its arguments. -/

/-- The reading tier's elimination-template leaf. -/
def templateValP : (Name → Nat) → AVExpr :=
  fun _ => .eqE (.sort 0) .prf .prf

set_option maxHeartbeats 1600000 in
/-- **One elimination-template entry installs, at both tiers**
(`templateConsS`). -/
theorem templateConsP {env' : Env} (mp : EnvS2PM V μ env')
    {T : Name} {lps : List Name} {i : Nat} {entry : ProjEntry}
    (hstruct : entry.structName = T) (hidx : entry.idx = i)
    (hnat : entry.native = false)
    (htower : entry.tower = false)
    (hlps : entry.levelParams = lps)
    (hty : entry.ty = .sort .zero)
    (hpnone : (env'.find? (projFnName T i)).isNone = true)
    (hTnres : Setlec.reservedBasisNames.contains T = false) :
    ∃ mp' : EnvS2PM V μ ⟨.projInfo entry :: env'.consts⟩,
      mp'.base2.cvalE
        = cvalWith mp.base2.cvalE (projFnName T i) templateVal := by
  have hname : (ConstantInfo.projInfo entry).name = projFnName T i := by
    show projFnName entry.structName entry.idx = projFnName T i
    rw [hstruct, hidx]
  have hfresh : env'.find? (ConstantInfo.projInfo entry).name = none := by
    rw [hname]; exact Option.isNone_iff_eq_none.mp hpnone
  have hnres : Setlec.reservedBasisNames.contains
      (ConstantInfo.projInfo entry).name = false := by
    rw [hname]; exact Setlec.reservedBasisNames_not_num _ _
  have htyE : (ConstantInfo.projInfo entry).toConstantVal.type
      = Expr.sort .zero := hty
  -- the stored type reads to `univ 0`, at every assignment
  have htyRead : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval
          (ConstantInfo.projInfo entry).name templateValP)
        ⟨.projInfo entry :: env'.consts⟩ ψ 0
        (ConstantInfo.projInfo entry).toConstantVal.type
        = some (.sort 0) := by
    intro ψ
    rw [htyE, denoteP]
    rfl
  have hcvA : (ConstantInfo.projInfo entry).toConstantVal
      = ⟨projFnName T i, lps, .sort .zero⟩ := by
    show (⟨projFnName entry.structName entry.idx, entry.levelParams,
      entry.ty⟩ : ConstantVal) = _
    rw [hstruct, hidx, hlps, hty]
  have hheadP : ConsHeadP env' (.projInfo entry) templateValP := by
    refine ⟨?_, (fun _ => ⟨trivial, trivial, trivial⟩),
      (fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h)),
      (fun e2 heq hnat2 => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        rw [hnat] at hnat2
        exact nomatch hnat2),
      (fun i2 e2 heq hpair => by
        exfalso
        obtain rfl := ConstantInfo.projInfo.inj heq
        rw [hname] at hpair
        have hTps : T = Setlec.psigmaName := by
          have hh : Name.num (T.str "proj") i
            = Name.num (Setlec.psigmaName.str "proj") i2 := hpair
          exact (Name.str.inj (Name.num.inj hh).1).1
        rw [hTps] at hTnres
        exact absurd hTnres (by decide)),
      (ConsCrossEnv.ofNtc fun e2 heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact htower),
      (fun e2 heq htw => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact absurd (htower.symm.trans htw) (by decide)),
      (fun _ _ _ _ heq => nomatch heq)⟩
    refine Setlec.EnvWF.cons mp.base2.wf ⟨?_, ?_, ?_, ?_,
      (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq),
      (fun cv2 mI2 rP2 rules2 heq => ConstantInfo.noConfusion heq),
      (fun cv2 v2 heq => ConstantInfo.noConfusion heq)⟩ <;>
      rw [hcvA] <;> rfl
  have htyOkH : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval
          (ConstantInfo.projInfo entry).name templateValP)
        ⟨.projInfo entry :: env'.consts⟩ ψ 0
        (ConstantInfo.projInfo entry).toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta := by
    intro ψ ta hta ρ
    obtain rfl : (AVExpr.sort 0) = ta :=
      Option.some.inj ((htyRead ψ).symm.trans hta)
    exact ⟨trivial, trivial⟩
  have hmemH : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval
          (ConstantInfo.projInfo entry).name templateValP)
        ⟨.projInfo entry :: env'.consts⟩ ψ 0
        (ConstantInfo.projInfo entry).toConstantVal.type = some ta →
      ∀ ρ : Nat → V,
        interp2 V ρ (templateValP ψ) ∈ˢ interp2 V ρ ta := by
    intro ψ ta hta ρ
    obtain rfl : (AVExpr.sort 0) = ta :=
      Option.some.inj ((htyRead ψ).symm.trans hta)
    show interp2 V ρ (AVExpr.eqE (.sort 0) .prf .prf) ∈ˢ
      interp2 V ρ (AVExpr.sort 0)
    rw [interp2_eqE, interp2_sort]
    exact eqv_mem_univ _ _
  obtain ⟨mp', hmp'⟩ :=
    declStepPM_of_projTemplate_cons mp (A := templateValP) hfresh hnres
      hheadP (fun ψ k => rfl) (fun ψ₁ ψ₂ _ => rfl)
      (fun ψ ρ => by
        show AnnotOk2 V ρ (AVExpr.eqE (.sort 0) .prf .prf)
        rw [AnnotOk2_eqE]
        exact ⟨trivial, trivial⟩)
      (fun ψ ρ => by
        show AnnotValidV V ρ (AVExpr.eqE (.sort 0) .prf .prf)
        rw [AnnotValidV_eqE]
        exact ⟨trivial, trivial⟩)
      (fun ψ => ⟨_, htyRead ψ⟩) htyOkH hmemH htower
  refine ⟨mp', ?_⟩
  funext n ψ
  rw [← mp'.base2.acval_erase n ψ, hmp']
  by_cases hn : n = (ConstantInfo.projInfo entry).name
  · subst hn
    rw [acvalWith_self, hname, cvalWith_self]
    rfl
  · rw [acvalWith_ne hn, mp.base2.acval_erase,
      cvalWith_ne (show n ≠ projFnName T i by
        rw [← hname]; exact hn)]

set_option maxHeartbeats 1600000 in
/-- **The elimination-template fold, at both tiers** (`templatesS`).
Nothing but the model survives it, so nothing is carried out. -/
theorem templatesP {T ctorName : Name} {lps : List Name} {nP nF : Nat}
    (hTnres : Setlec.reservedBasisNames.contains T = false) :
    ∀ (fields : List Nat) {env' : Env} (_mp : EnvS2PM V μ env')
      {env₂ : Env},
      DeclIndR.TemplatesR T ctorName lps nP nF env' fields env₂ →
      Nonempty (EnvS2PM V μ env₂) := by
  intro fields
  induction fields with
  | nil =>
    intro env' mp env₂ h
    obtain rfl := h
    exact ⟨mp⟩
  | cons i rest ih =>
    intro env' mp env₂ h
    obtain ⟨env'', hstep, hrec⟩ := h
    rcases hstep with rfl | ⟨entry, hstruct, hidx, hnat, htower, hlps,
      hty, hpnone, rfl⟩
    · exact ih mp hrec
    · obtain ⟨mp', hcval'⟩ :=
        templateConsP mp hstruct hidx hnat htower hlps hty hpnone hTnres
      exact ih mp' hrec

end Setlec.SetR.Interp2
