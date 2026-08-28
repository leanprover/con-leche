import Setlec.Verify.Denote
import Setlec.TTVerify.EnvTT
import Setlec.Verify.Extend.Sibs
import Setlec.Verify.EnvWF
import Setlec.Verify.InferLemmas
import Setlec.Verify.InstLevels
import Setlec.Verify.Denote.Levels
import Setlec.Verify.Denote.Install

/-!
# Denotations survive environment extension

The transpose of the environment-transport machinery of
`Setlec/Model/Extend/*`, at the one lemma the bridge actually needs:
**a term that denotes in `env` denotes to the same `VExpr` in any
extension of `env`.**

Every install step needs it in the same place the set model does.  The
invariant `EnvTT.has_type` quantifies over the constants stored *so
far* and mentions `denote … env …`; installing one more constant
replaces `env` by `⟨c₀ :: env.consts⟩`, so the already-established
derivations have to be re-read against the larger environment.  Since
`denote` reads the environment only in the `.const` clause (for the
arity check and the stored level parameters) and in the two literal
guards, extension can only *add* denotations, never change one.

Note what does **not** appear: nothing about `AnnotOk`, and nothing
about interpretations agreeing pointwise on a set-theoretic universe.
The set-model side needs a family of transport lemmas because
`AnnotOk` and the `IndOk`/`RecRulesOk`/`CapsOk` clauses all mention
`interpExpr` and each has to be moved separately
(`Setlec/Model/Extend/Transport.lean` and its siblings); here the
single fact below is what the corresponding clauses will consume.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode; the seven gated checks
reduce definitionally at `.ttModel`. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT


/-- Old constants keep their derivations across a fresh install.

The seven literal-support agreements are separate hypotheses rather
than consequences of `hag`, and the reason is a real case rather than
caution: during a **basis install** the new constant *is* one of those
names, so `n ≠ c₀.name` does not hold for them.  An ordinary install
discharges all seven from `hag` immediately; the basis install owes
them, which is correct — it is the one changing those valuations. -/
theorem has_type_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hlit : LitAgree env m.cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
        = levelParamsAt env listNilName)
    (hlpCons : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
        = levelParamsAt env listConsName) :
    ∀ c ∈ env.consts, ∀ φ : Name → Nat,
      ∃ t, denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c.toConstantVal.type
          = some t ∧ HasType [] (cval' c.name φ) t := by
  -- freshness gives name-distinctness for every stored constant, with
  -- no appeal to well-formedness
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  have hagE : ∀ n ci, env.find? n = some ci → m.cval n = cval' n := by
    intro n ci hfind
    refine hag n ?_
    intro h
    rw [h, hfresh] at hfind
    exact nomatch hfind
  intro c hc φ
  obtain ⟨t, ht, hd⟩ := m.has_type c hc φ
  refine ⟨t, ?_, ?_⟩
  · rw [denoteClosed] at ht ⊢
    rw [denote_cval_congr hagE hlit.nat hlit.succ hlit.sol hlit.nil
      hlit.cons hlit.char hlit.ofn 0 _] at ht
    exact denote_mono (EnvExtends.cons hfresh) hguardN hguardS hlpNil
      hlpCons 0 _ ht
  · rw [← hag c.name (hne c hc)]
    exact hd


theorem defn_eq_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hlit : LitAgree env m.cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
        = levelParamsAt env listNilName)
    (hlpCons : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
        = levelParamsAt env listConsName) :
    ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hint hmem φ
  have := denote_install hfresh hag hlit hguardN hguardS hlpNil hlpCons
    (m.defn_eq cv value hint hmem φ)
  rwa [hag cv.name (hne _ hmem)] at this

/-- Theorems likewise. -/
theorem thm_ok_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hlit : LitAgree env m.cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
        = levelParamsAt env listNilName)
    (hlpCons : strLitSupported env = true →
      levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
        = levelParamsAt env listConsName) :
    ∀ cv value, ConstantInfo.thmInfo cv value ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hmem φ
  have := denote_install hfresh hag hlit hguardN hguardS hlpNil hlpCons
    (m.thm_ok cv value hmem φ)
  rwa [hag cv.name (hne _ hmem)] at this

/-! ## The capability laws across an install

The transport that the §8.1 correction exists for, and the direct test
that it worked: `CapsOkTT` is the field whose laws quantify over
spines, so if the restatement had not fixed the shape, this is where it
would fail.  It is the transpose of `CapsOk.cons`
(`Setlec/Model/Extend/Sibs.lean`) step for step — the head cases are
handed over, and the non-head case runs the stored type's denotation
*down* to the smaller environment before applying the old law.

The two `denote` moves compose in one order only: `denote_env_shrink`
first (the expression resolves in the small environment, so it may
descend), then `denote_cval_congr` (the valuations agree on everything
stored *there*, but not on the new constant).  Doing it the other way
would need agreement at `c₀.name`, which is exactly what an install
does not have. -/

/-- The residual pin clause survives a fresh install: it is purely
syntactic, so only the two `find?`s can change, and a head obligation
covers the disjunction.  (Task #119 §16.3.) -/
theorem CtorResidualOkT.cons {env : Env} {c₀ : ConstantInfo}
    (h : CtorResidualOkT env)
    (hhead : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps)
      (cvC : ConstantVal),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains caps.etaCtor = false →
      (⟨c₀ :: env.consts⟩ : Env).find? caps.etaCtor =
        some (.ctorInfo cvC caps.etaParams caps.etaFields) →
      (T = c₀.name ∨ caps.etaCtor = c₀.name) →
      CtorResidualPin T cvT.levelParams cvC caps.etaParams
        caps.etaFields) :
    CtorResidualOkT ⟨c₀ :: env.consts⟩ := by
  intro T cvT caps cvC hf heta hrT hrC hfc
  by_cases hd : T = c₀.name ∨ caps.etaCtor = c₀.name
  · exact hhead T cvT caps cvC hf heta hrT hrC hfc hd
  · have hnT : T ≠ c₀.name := fun hh => hd (Or.inl hh)
    have hnC : caps.etaCtor ≠ c₀.name := fun hh => hd (Or.inr hh)
    rw [Env.find?_cons, if_neg (fun hh => hnT hh.symm)] at hf
    rw [Env.find?_cons, if_neg (fun hh => hnC hh.symm)] at hfc
    exact h T cvT caps cvC hf heta hrT hrC hfc

/-- The capability laws survive a fresh install, given the head
obligations.  Transpose of `CapsOk.cons`. -/
theorem CapsOkTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo}
    (h : CapsOkTT env cval) (hwfe : EnvWF env)
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hlit : LitAgree env cval cval')
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawTT ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawTT ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps) :
    CapsOkTT ⟨c₀ :: env.consts⟩ cval' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hf
    refine hag n ?_
    intro hh
    rw [hh, hfresh] at hf
    exact nomatch hf
  -- the stored type descends, then the valuation changes
  have hdown : ∀ (φ : Name → Nat) (d : Nat) (e : Expr) (v : VExpr),
      e.constsResolve env = true →
      denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v →
      denote cval env φ d e = some v := by
    intro φ d e v hres hv
    rw [denote_env_shrink hfresh d e hres] at hv
    rwa [denote_cval_congr hagE hlit.nat hlit.succ hlit.sol hlit.nil
      hlit.cons hlit.char hlit.ofn d e]
  refine ⟨?_, ?_⟩
  · intro T cvT caps hf hcape hres hfam
    by_cases hpart : T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name
    · exact hheadEta T cvT caps hf hcape hres hfam hpart
    · have hnT : T ≠ c₀.name := fun hh => hpart (Or.inl hh)
      have hnC : caps.etaCtor ≠ c₀.name := fun hh => hpart (Or.inr (Or.inl hh))
      have hnP : ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name :=
        fun j hj hh => hpart (Or.inr (Or.inr ⟨j, hj, hh⟩))
      rw [hfind _ hnT] at hf
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      rw [hfind _ hnC] at hfC
      have hfam₀ : EtaFamilyStored env T caps := by
        refine ⟨hCres, ⟨cvC, hfC⟩, ?_⟩
        intro j hj
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
        rw [hfind _ (hnP j hj)] at hf2
        exact ⟨cv2, mI2, rP2, rules2, hf2⟩
      have hlaw := h.1 T cvT caps hf hcape hres hfam₀
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        simpa [ConstantInfo.toConstantVal] using h3
      intro φ d Δ us xs TV rest B hlen hTV hfit hBt hfabT
      have hTV' := hdown φ d _ TV
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hag T hnT] at hBt hfabT
      have hproj : ∀ j ∈ List.range caps.etaFields,
          VExpr.mkAppN (cval' (projFnName T j)
            (Level.substFn φ
              (levelParamsAt ⟨c₀ :: env.consts⟩ (projFnName T j)) us))
            (xs ++ [B])
          = VExpr.mkAppN (cval (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
            (xs ++ [B]) := by
        intro j hj
        rw [← hag _ (hnP j (List.mem_range.mp hj)),
          levelParamsAt_cons_of_ne
            (fun hh => (hnP j (List.mem_range.mp hj)) hh.symm)]
      rw [List.map_congr_left hproj, ← hag _ hnC,
        levelParamsAt_cons_of_ne (fun hh => hnC hh.symm)] at hfabT ⊢
      exact hlaw φ d Δ us xs TV rest B hlen hTV' hfit hBt hfabT
  · intro T cvT caps hf hcapu hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadUnit cvT caps (Option.some.inj hf) hcapu hres
    · rw [hfind _ hn] at hf
      have hlaw := h.2 T cvT caps hf hcapu hres
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        simpa [ConstantInfo.toConstantVal] using h3
      intro φ d Δ us xs TV rest B B' hlen hTV hfit hBt hBt'
      have hTV' := hdown φ d _ TV
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hag T hn] at hBt hBt'
      exact hlaw φ d Δ us xs TV rest B B' hlen hTV' hfit hBt hBt'


/-! ## The remaining field transports (TT forms)

One `.cons` per remaining `EnvTT` field, same shape as the relocated
`BasisPinnedTT.cons`/`ProjOkT.cons` (`Setlec/Verify/Denote/Install.lean`):
the head case is a hypothesis, everything else transports through the
`Installs` context. -/


/-- The compiler-trust identities survive an install. -/
theorem ReduceOpsTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : ReduceOpsTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
          HasType Δ X (cval' (reduceElemName c₀.name) φ) →
          Deq Δ (.app (cval' c₀.name φ) X) X) :
    ReduceOpsTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv hf hpin
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv (Option.some.inj hf) hc hpin
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hs, hlaw⟩ := h c hc cv hf hpin
    refine ⟨by rw [hi.find hs]; exact hs, ?_⟩
    intro φ Δ X hX
    rw [← hi.agree hs] at hX
    rw [← hi.ag c (fun hh => hn hh.symm)]
    exact hlaw φ Δ X hX

/-- The structural `Nat` recurrences survive an install. -/
theorem NatOpsTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : NatOpsTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint → c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ φ : Name → Nat, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        Deq [cval' natName φ, cval' natName φ] L R) :
    NatOpsTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv v hint hf
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv v hint (Option.some.inj hf) hc
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hg, hlaw⟩ := h c hc cv v hint hf
    -- the guard pins `Nat`, so the valuation there is unchanged
    have hnat : cval natName = cval' natName := by
      refine hi.agree ?_
      have h0 : natLitSupported env = true := by
        simp only [natOpGuard, Bool.and_eq_true] at hg
        exact hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      revert h0
      cases env.find? natName <;> simp [natIndOk]
    refine ⟨natOpGuard_cons hi.fresh hg, ?_⟩
    intro eq heq φ
    obtain ⟨L, R, hL, hR, hD⟩ := hlaw eq heq φ
    exact ⟨L, R, hi.denoteUp hL, hi.denoteUp hR, by rw [← hnat]; exact hD⟩

/-- The recursor rules survive an install.  The "the rule's own
constructor is the constant being installed" case is *refuted*, not
handled: a stored recursor's rules name constructors that are already
stored, which is `hctors` — the same discharge the set model's
`RecRulesOk.cons` makes from `ind_ok`. -/
theorem RecRulesTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : RecRulesTT env cval) (hwfe : EnvWF env)
    (hi : Installs env cval cval' c₀)
    (hctors : ∀ n cv mI rP rules,
      env.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hhead : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ (φ : Name → Nat) (d : Nat) (us : List Level),
        us.length = cv.levelParams.length →
        ∃ R, denote cval' ⟨c₀ :: env.consts⟩ φ d
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R ∧
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
              = some (.ctorInfo cvj cnP cnF) →
          ∀ (Δ : List VExpr) (usj : List Level) (xs ys : List VExpr)
            (TV TVj restR restC : VExpr),
            xs.length = mI →
            ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
            usj.length = cvj.levelParams.length →
            Level.substFn φ cvj.levelParams usj
              = Level.substFn φ cvj.levelParams
                  (recFireComparands rl cv.levelParams us cvj.levelParams
                    [] rP).1 →
            (RecRule.fire rl = .plain →
              ∀ i, i < RecRule.ctorParams rl → i < mI →
                Deq Δ (ys.getD i default) (xs.getD i default)) →
            (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
              ∀ i, i < RecRule.ctorParams rl →
              ∀ vp : VExpr,
                denote cval' ⟨c₀ :: env.consts⟩ φ rP
                  (openRev 0 rP ((pins.getD i
                    default).instantiateLevelParams cv.levelParams us))
                  = some vp →
                Deq Δ (ys.getD i default)
                  (VExpr.instRevChain (xs.take rP) vp)) →
            IotaIndexPin Δ restC (RecRule.ctorParams rl) mI rP xs →
            denote cval' ⟨c₀ :: env.consts⟩ φ d
              (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
            denote cval' ⟨c₀ :: env.consts⟩ φ d
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              = some TVj →
            VTeleTyped Δ TV
              (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            VTeleTyped Δ TVj ys restC →
            Deq Δ
              (VExpr.mkAppN
                (cval' c₀.name (Level.substFn φ cv.levelParams us))
                (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
              (VExpr.mkAppN R
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))) :
    RecRulesTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n cv mI rP rules hf rl hrl hfire
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv mI rP rules (Option.some.inj hf) rl hrl hfire
  · rw [Env.find?_cons, if_neg hn] at hf
    -- the rule's constructor is stored already, so it is not `c₀`
    obtain ⟨cvj2, cnP2, cnF2, hfc2⟩ := hctors n cv mI rP rules hf rl hrl
    have hnc : c₀.name ≠ RecRule.ctor rl :=
      ne_of_isSome_fresh hi.fresh (by rw [hfc2]; rfl)
    obtain ⟨hple, hbody⟩ := h n cv mI rP rules hf rl hrl hfire
    refine ⟨hple, ?_⟩
    intro φ d us hlenU
    obtain ⟨R, hR, hlaw⟩ := hbody φ d us hlenU
    -- the right-hand side's denotation moves **forward**, which is what
    -- makes the produced form the easier one (§12.9)
    refine ⟨R, hi.denoteUp hR, ?_⟩
    intro cvj cnP cnF hctor
    rw [Env.find?_cons, if_neg hnc] at hctor
    obtain ⟨-, -, hres1, -, -, -, -⟩ := hwfe _ (find?_mem hf)
    obtain ⟨-, -, hres2, -⟩ := hwfe _ (find?_mem hctor)
    intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar hparN
      hidx hTV hTVj hfitR hfitC
    have hTV' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cv.levelParams us]
          simpa [ConstantInfo.toConstantVal] using hres1) hTV
    have hTVj' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cvj.levelParams usj]
          simpa [ConstantInfo.toConstantVal] using hres2) hTVj
    rw [← hi.ag _ (Ne.symm hnc)] at hfitR
    rw [← hi.ag n (fun hh => hn hh.symm), ← hi.ag _ (Ne.symm hnc)]
    exact hlaw cvj cnP cnF hctor Δ usj xs ys TV TVj restR restC hlenX hlenY
      hlenJ hlev hpar
      (fun lvls pins hn i hi' vp hvp =>
        hparN lvls pins hn i hi' vp (hi.denoteUp hvp))
      hidx hTV' hTVj' hfitR hfitC

/-! ### The WF-recursive clauses

`DivModClausesTT` reads the valuation at a dozen names, and every one
of them is pinned by `natOpGuard` — that is what the dependency list is
*for*.  So the transport needs no new hypothesis, only the observation
that a pinned name is stored and therefore not the one being
installed. -/

/-- Every name a clause set reads is valued the same after an install
at a different name. -/
theorem divModNames_agree {env : Env} {cval cval' : TConstVal} {c : Name}
    (hag : ∀ n, (env.find? n).isSome = true → cval n = cval' n)
    (hg : natOpGuard env c = true) :
    (∀ n ∈ natOpDeps c, cval n = cval' n) ∧
      cval natZeroName = cval' natZeroName ∧
      cval natSuccName = cval' natSuccName ∧
      (natDivModNames.contains c = true →
        cval boolTrueName = cval' boolTrueName ∧
        cval boolFalseName = cval' boolFalseName) := by
  simp only [natOpGuard, Bool.and_eq_true] at hg
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := hg
  simp only [natLitSupported, Bool.and_eq_true] at h0
  obtain ⟨⟨-, h2⟩, h3⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [List.all_eq_true] at hdeps
    have hn' := hdeps n (by simpa using hn)
    exact hag n (by revert hn'; cases env.find? n <;> simp)
  · exact hag _ (by revert h2; cases env.find? natZeroName <;> simp [natZeroOk])
  · exact hag _ (by revert h3; cases env.find? natSuccName <;> simp [natSuccOk])
  · intro hc
    rw [show (decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true from by
          simp only [hc, Bool.or_true]] at hbool
    simp only [if_true] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    exact ⟨hag _ (by revert hT; cases env.find? boolTrueName <;> simp),
      hag _ (by revert hF; cases env.find? boolFalseName <;> simp)⟩

/-- The guarded recurrences survive an install. -/
theorem DivModTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : DivModTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
        HasType Δ x (cval' natName φ) → HasType Δ y (cval' natName φ) →
        DivModClausesTT cval' c₀.name φ Δ x y) :
    DivModTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv v hint hf
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv v hint (Option.some.inj hf) hc
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hg, hlaw⟩ := h c hc cv v hint hf
    have hagS : ∀ n, (env.find? n).isSome = true → cval n = cval' n :=
      fun n hn' => hi.agree hn'
    obtain ⟨hdep, hz, hs, hbool⟩ := divModNames_agree hagS hg
    obtain ⟨hT, hF⟩ := hbool (by simpa using hc)
    have hnat : cval natName = cval' natName := by
      simp only [natOpGuard, Bool.and_eq_true] at hg
      have h0 := hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      exact hagS _ (by revert h0; cases env.find? natName <;> simp [natIndOk])
    refine ⟨natOpGuard_cons hi.fresh hg, ?_⟩
    intro φ Δ x y hx hy
    rw [← hnat] at hx hy
    have := hlaw φ Δ x y hx hy
    have hc' : cval c = cval' c := hi.ag c (fun hh => hn hh.symm)
    clear hc'
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natModName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natBleName (by decide),
        hdep natModName (by decide), hdep natGcdName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide),
        hdep natLandName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natSubName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide), hdep natLorName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide),
        hdep natXorName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natShiftLeftName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natShiftRightName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natLog2Name (by decide)] at this ⊢
      exact this

/-! ## Assembling an install

`EnvTT.cons` is the one theorem the six `checkDecl` cases share: it
takes the head obligations for the constant being installed and returns
the invariant for the extended environment.  Everything else is the
transports above.

The shape mirrors `Setlec/Model/Extend/Transport.lean`'s: obligations
are stated *only* for the new constant, and every clause about an
already-stored constant is discharged here once rather than nine times
in the case analysis. -/

/-- The environment invariant survives an ordinary install, given the
new constant's own obligations. -/
def EnvTT.cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hclosed : ∀ ψ : Name → Nat, VExpr.Closed (cval' c₀.name ψ))
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval' c₀.name φ₁ = cval' c₀.name φ₂)
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c₀.toConstantVal.type = some t ∧
        HasType [] (cval' c₀.name φ) t)
    (hdefn : ∀ cv value hint, c₀ = .defnInfo cv value hint →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value = some (cval' cv.name φ))
    (hthm : ∀ cv value, c₀ = .thmInfo cv value → ∀ φ : Name → Nat,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value = some (cval' cv.name φ))
    (hempty : c₀.name = emptyName →
      ∀ ψ : Name → Nat, ∃ u, cval' emptyName ψ = emptyT u)
    (hheadCtors : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ (φ : Name → Nat) (d : Nat) (us : List Level),
        us.length = cv.levelParams.length →
        ∃ R, denote cval' ⟨c₀ :: env.consts⟩ φ d
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R ∧
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
              = some (.ctorInfo cvj cnP cnF) →
          ∀ (Δ : List VExpr) (usj : List Level) (xs ys : List VExpr)
            (TV TVj restR restC : VExpr),
            xs.length = mI →
            ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
            usj.length = cvj.levelParams.length →
            Level.substFn φ cvj.levelParams usj
              = Level.substFn φ cvj.levelParams
                  (recFireComparands rl cv.levelParams us cvj.levelParams
                    [] rP).1 →
            (RecRule.fire rl = .plain →
              ∀ i, i < RecRule.ctorParams rl → i < mI →
                Deq Δ (ys.getD i default) (xs.getD i default)) →
            (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
              ∀ i, i < RecRule.ctorParams rl →
              ∀ vp : VExpr,
                denote cval' ⟨c₀ :: env.consts⟩ φ rP
                  (openRev 0 rP ((pins.getD i
                    default).instantiateLevelParams cv.levelParams us))
                  = some vp →
                Deq Δ (ys.getD i default)
                  (VExpr.instRevChain (xs.take rP) vp)) →
            IotaIndexPin Δ restC (RecRule.ctorParams rl) mI rP xs →
            denote cval' ⟨c₀ :: env.consts⟩ φ d
              (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
            denote cval' ⟨c₀ :: env.consts⟩ φ d
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              = some TVj →
            VTeleTyped Δ TV
              (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            VTeleTyped Δ TVj ys restC →
            Deq Δ
              (VExpr.mkAppN
                (cval' c₀.name (Level.substFn φ cv.levelParams us))
                (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
              (VExpr.mkAppN R
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawTT ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawTT ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps)
    (hheadResid : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps)
      (cvC : ConstantVal),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains caps.etaCtor = false →
      (⟨c₀ :: env.consts⟩ : Env).find? caps.etaCtor =
        some (.ctorInfo cvC caps.etaParams caps.etaFields) →
      (T = c₀.name ∨ caps.etaCtor = c₀.name) →
      CtorResidualPin T cvT.levelParams cvC caps.etaParams
        caps.etaFields)
    (hheadProj : ∀ entry, c₀ = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hheadProjPair : ∀ i entry, c₀ = .projInfo entry →
      c₀.name = projFnName psigmaName i → entry.native = true)
    (hheadEq : c₀.name = eqName → EqLawTT ⟨c₀ :: env.consts⟩ cval')
    (hheadBasis : reservedBasisNames.contains c₀.name = true →
      (ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name) ∧
      ∀ (ψ : Name → Nat) (t : VExpr),
        pinnedDirectT c₀.name ψ = some t → cval' c₀.name ψ = t)
    (hheadNat : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ φ : Name → Nat, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        Deq [cval' natName φ, cval' natName φ] L R)
    (hheadDivMod : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
        HasType Δ x (cval' natName φ) → HasType Δ y (cval' natName φ) →
        DivModClausesTT cval' c₀.name φ Δ x y)
    (hheadReduce : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
          HasType Δ X (cval' (reduceElemName c₀.name) φ) →
          Deq Δ (.app (cval' c₀.name φ) X) X) :
    EnvTT ⟨c₀ :: env.consts⟩ := by
  refine
    { cval := cval'
      cval_closed := ?_
      wf := hwf
      val_params := ?_
      has_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := ?_
      rec_rules := RecRulesTT.cons m.rec_rules m.wf hi m.rec_ctors hheadRec
      caps_ok := CapsOkTT.cons m.caps_ok m.wf hi.fresh hi.ag hi.lit
        hheadEta hheadUnit
      ctor_residual := CtorResidualOkT.cons m.ctor_residual hheadResid
      proj_ok := ProjOkT.cons m.proj_ok hi.fresh hheadProj hheadProjPair
      rec_ctors := RecCtorsStored.cons m.rec_ctors hi.fresh hheadCtors
      eq_law := EqLawTT.cons m.eq_law hi.ag hheadEq
      basis_pinned := BasisPinnedTT.cons m.basis_pinned hi hheadBasis
      nat_ops := NatOpsTT.cons m.nat_ops hi hheadNat
      div_mod := DivModTT.cons m.div_mod hi hheadDivMod
      reduce_ops := ReduceOpsTT.cons m.reduce_ops hi hheadReduce }
  · intro n ψ
    by_cases hn : n = c₀.name
    · subst hn; exact hclosed ψ
    · rw [← hi.ag n hn]; exact m.cval_closed n ψ
  · intro n ci hf φ₁ φ₂ hp
    by_cases hn : c₀.name = n
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      rw [← Option.some.inj hf] at hp
      exact hparams φ₁ φ₂ hp
    · rw [Env.find?_cons, if_neg hn] at hf
      rw [← hi.ag n (fun hh => hn hh.symm)]
      exact m.val_params n ci hf φ₁ φ₂ hp
  · intro c hc φ
    rcases hc with _ | ⟨_, hc⟩
    · exact htype φ
    · exact has_type_cons m hi.fresh hi.ag hi.lit
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons c hc φ
  · intro cv value hint hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hdefn cv value hint rfl φ
    · exact defn_eq_cons m hi.fresh hi.ag hi.lit
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons cv value hint hmem φ
  · intro cv value hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hthm cv value rfl φ
    · exact thm_ok_cons m hi.fresh hi.ag hi.lit
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons cv value hmem φ
  · intro ψ
    by_cases hn : c₀.name = emptyName
    · exact hempty hn ψ
    · rw [← hi.ag emptyName (fun hh => hn hh.symm)]
      exact m.empty_pinned ψ

end Setlec.TTVerify
