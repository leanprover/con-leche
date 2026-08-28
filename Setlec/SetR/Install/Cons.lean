import Setlec.SetR.EnvS
import Setlec.Verify.Extend.Sibs
import Setlec.Verify.InstLevels
import Setlec.Verify.InferLemmas

/-!
# `EnvS` survives an ordinary install (task #148, T5)

One `.cons` per `EnvS` field, transposing `Setlec/TTVerify/Extend.lean`'s
TT-form transports (whose skeletons these mirror step for step), and
the assembler `EnvS.cons` transposing `EnvTT.cons`: head obligations
are stated *only* for the constant being installed; everything about
an already-stored constant transports through the `Installs` context
(`Setlec/Verify/Denote/Install.lean`).

The [set] transports are *lighter* than their TT twins in exactly the
way the campaign design predicts: every `interp`/`AnnotOkV`/`TeleFitV`
component is env-free, so only the `denote` facts and the `cval`
occurrences move — hypothesis-side denotations run **down** to the
smaller environment (`Installs.denoteDown`, fed by `EnvWF`'s resolve
facts), conclusion-side ones run **up** (`Installs.denoteUp`), and the
valuation occurrences rewrite by agreement at stored names.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The V-free-shaped laws -/

/-- The pinned-`Eq` law survives an install: `Eq` is reserved, so an
ordinary install neither stores it nor changes its valuation.
Transpose of `EqLawTT.cons`. -/
theorem EqLawV.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : EqLawV V env cval)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hhead : c₀.name = eqName → EqLawV V ⟨c₀ :: env.consts⟩ cval') :
    EqLawV V ⟨c₀ :: env.consts⟩ cval' := by
  intro hf
  by_cases hn : c₀.name = eqName
  · exact hhead hn hf
  · rw [Env.find?_cons, if_neg hn] at hf
    rw [show cval' eqName = cval eqName from
      (hag eqName (fun hh => hn hh.symm)).symm]
    exact h hf

/-- The compiler-trust identities survive an install.  Transpose of
`ReduceOpsTT.cons`. -/
theorem ReduceOpsV.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : ReduceOpsV V env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
          x ∈ˢ interp V ρ (cval' (reduceElemName c₀.name) ψ) →
          SetTheory.app (interp V ρ (cval' c₀.name ψ)) x = x) :
    ReduceOpsV V ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv hf hpin
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv (Option.some.inj hf) hc hpin
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hs, hlaw⟩ := h c hc cv hf hpin
    refine ⟨by rw [hi.find hs]; exact hs, ?_⟩
    intro ψ ρ x hx
    rw [← hi.agree hs] at hx
    rw [← hi.ag c (fun hh => hn hh.symm)]
    exact hlaw ψ ρ x hx

/-- The structural-`Nat` recurrences survive an install.  Transpose of
`NatOpsTT.cons`. -/
theorem NatOpsV.cons {env : Env} {cval cval' : TConstVal} {φ : Name → Nat}
    {c₀ : ConstantInfo} (h : NatOpsV V env cval φ)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint → c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        ∀ (ρ : Nat → V) (x y : V),
          x ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
          y ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
          interp V (cons V y (cons V x ρ)) L
            = interp V (cons V y (cons V x ρ)) R) :
    NatOpsV V ⟨c₀ :: env.consts⟩ cval' φ := by
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
    intro eq heq
    obtain ⟨L, R, hL, hR, hE⟩ := hlaw eq heq
    refine ⟨L, R, hi.denoteUp hL, hi.denoteUp hR, ?_⟩
    intro ρ x y hx hy
    rw [← hnat] at hx hy
    exact hE ρ x y hx hy

/-- The guarded WF-recursive recurrences survive an install.
Transpose of `DivModTT.cons`; the clause set reads the valuation only
at names `natOpGuard` pins, so the transport needs no new
hypothesis. -/
theorem DivModV.cons {env : Env} {cval cval' : TConstVal} {φ : Name → Nat}
    {c₀ : ConstantInfo} (h : DivModV V env cval φ)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
        y ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
        DivModClausesV V
          (fun n => interp V ρ (cval' n (Level.substFn φ [] [])))
          c₀.name x y) :
    DivModV V ⟨c₀ :: env.consts⟩ cval' φ := by
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
    have hcc : cval c = cval' c := hi.ag c (fun hh => hn hh.symm)
    refine ⟨natOpGuard_cons hi.fresh hg, ?_⟩
    intro ρ x y hx hy
    rw [← hnat] at hx hy
    have this := hlaw ρ x y hx hy
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false]
      at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natSubName (by decide), hdep natBleName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natSubName (by decide), hdep natBleName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natBleName (by decide), hdep natModName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natAddName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide)]
        at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natAddName (by decide), hdep natSubName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natAddName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide)]
        at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natSubName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide)]
        at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natSubName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide)]
        at this ⊢
      exact this
    · simp only [DivModClausesV, hz, hs, hT, hF, hcc,
        hdep natBleName (by decide), hdep natDivName (by decide)] at this ⊢
      exact this

/-! ## The capability laws across an install

Transpose of `CapsOkTT.cons`: the head cases are handed over; the
non-head case runs the stored former type's denotation *down* to the
smaller environment and rewrites the valuation occurrences (all at
stored names — `EtaFamilyStored` is what stores them). -/

theorem CapsOkV.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo}
    (h : CapsOkV V env cval) (hwfe : EnvWF env)
    (hi : Installs env cval cval' c₀)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawV V ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawV V ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps) :
    CapsOkV V ⟨c₀ :: env.consts⟩ cval' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  refine ⟨?_, ?_⟩
  · intro T cvT caps hf hcape hres hfam
    by_cases hpart : T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name
    · exact hheadEta T cvT caps hf hcape hres hfam hpart
    · have hnT : T ≠ c₀.name := fun hh => hpart (Or.inl hh)
      have hnC : caps.etaCtor ≠ c₀.name :=
        fun hh => hpart (Or.inr (Or.inl hh))
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
      intro φ' us ρ xs TV rest B hlen hTV hfit hBt
      have hTV' := hi.denoteDown
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hi.ag T hnT] at hBt
      have hproj : ∀ j ∈ List.range caps.etaFields,
          VExpr.mkAppN (cval' (projFnName T j)
            (Level.substFn φ' cvT.levelParams us)) (xs ++ [B])
          = VExpr.mkAppN (cval (projFnName T j)
            (Level.substFn φ' cvT.levelParams us)) (xs ++ [B]) := by
        intro j hj
        rw [← hi.ag _ (hnP j (List.mem_range.mp hj))]
      have hfab : etaFabArgsV cval' T (Level.substFn φ' cvT.levelParams us)
            xs B caps.etaFields
          = etaFabArgsV cval T (Level.substFn φ' cvT.levelParams us)
            xs B caps.etaFields := by
        unfold etaFabArgsV projSpinesV
        congr 1
        refine List.map_congr_left fun j hj => ?_
        rw [← hi.ag _ (hnP j (List.mem_range.mp hj))]
      rw [hfab, ← hi.ag _ hnC]
      exact hlaw φ' us ρ xs TV rest B hlen hTV' hfit hBt
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
      intro φ' us ρ xs TV rest x y hlen hTV hfit hx hy
      have hTV' := hi.denoteDown
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hi.ag T hn] at hx hy
      exact hlaw φ' us ρ xs TV rest x y hlen hTV' hfit hx hy

/-! ## The fired iota contract across an install

Transpose of `RecRulesTT.cons`: hypothesis-side denote facts run down,
the rhs denotation runs up, and every `interp`/`TeleFitV`/`AnnotOkV`
component passes through untouched (env-free). -/

theorem RecRulesV.cons {env : Env} {cval cval' : TConstVal}
    {φ : Name → Nat} {c₀ : ConstantInfo}
    (h : RecRulesV V env cval φ) (hwfe : EnvWF env)
    (hi : Installs env cval cval' c₀)
    (hctors : RecCtorsStored env)
    (hhead : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ us : List Level, us.length = cv.levelParams.length →
        ∃ R, denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R ∧
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
              = some (.ctorInfo cvj cnP cnF) →
          ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List VExpr)
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
                interp V ρ (ys.getD i default)
                  = interp V ρ (xs.getD i default)) →
            (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
              ∀ i, i < RecRule.ctorParams rl →
              ∀ vp : VExpr,
                denote cval' ⟨c₀ :: env.consts⟩ φ rP
                  (openRev 0 rP
                    ((pins.getD i default).instantiateLevelParams
                      cv.levelParams us)) = some vp →
                VExpr.bvarsBelow rP vp →
                interp V ρ (ys.getD i default)
                  = interp V ρ (VExpr.instRevChain (xs.take rP) vp)) →
            IotaIndexPinV V ρ restC (RecRule.ctorParams rl) mI rP xs →
            denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TV →
            denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              = some TVj →
            TeleFitV V ρ TV
              (xs ++ [VExpr.mkAppN
                (cval' (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            TeleFitV V ρ TVj ys restC →
            interp V ρ
                (VExpr.mkAppN
                  (cval' c₀.name (Level.substFn φ cv.levelParams us))
                  (xs ++ [VExpr.mkAppN
                    (cval' (RecRule.ctor rl)
                      (Level.substFn φ cvj.levelParams usj)) ys]))
              = interp V ρ
                  (VExpr.mkAppN R
                    (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
            ((∀ a ∈ xs, AnnotOkV V ρ a) →
              (∀ b ∈ ys, AnnotOkV V ρ b) →
              AnnotOkV V ρ
                (VExpr.mkAppN R
                  (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))) :
    RecRulesV V ⟨c₀ :: env.consts⟩ cval' φ := by
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
    intro us hlenU
    obtain ⟨R, hR, hlaw⟩ := hbody us hlenU
    refine ⟨R, hi.denoteUp hR, ?_⟩
    intro cvj cnP cnF hctor
    rw [Env.find?_cons, if_neg hnc] at hctor
    obtain ⟨-, -, hres1, -, -, -, -⟩ := hwfe _ (find?_mem hf)
    obtain ⟨-, -, hres2, -⟩ := hwfe _ (find?_mem hctor)
    intro usj ρ xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar hparN
      hidx hTV hTVj hfitR hfitC
    have hTV' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cv.levelParams us]
          simpa [ConstantInfo.toConstantVal] using hres1) hTV
    have hTVj' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cvj.levelParams usj]
          simpa [ConstantInfo.toConstantVal] using hres2) hTVj
    rw [← hi.ag _ (Ne.symm hnc)] at hfitR
    rw [← hi.ag n (fun hh => hn hh.symm), ← hi.ag _ (Ne.symm hnc)]
    exact hlaw cvj cnP cnF hctor usj ρ xs ys TV TVj restR restC hlenX
      hlenY hlenJ hlev hpar
      (fun lvls pins hnst i hi' vp hvp =>
        hparN lvls pins hnst i hi' vp (hi.denoteUp hvp))
      hidx hTV' hTVj' hfitR hfitC

/-! ## Old constants keep their facts

Transposes of `has_type_cons`/`defn_eq_cons`/`thm_ok_cons`, at the
[set] fields.  The membership and truthfulness components are
statements about the *same* `VExpr`s (env-free), so only the
`denoteClosed` fact and the valuation occurrence move. -/

theorem mem_type_consS {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀) :
    ∀ c ∈ env.consts, ∀ φ : Name → Nat,
      ∃ t, denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c.toConstantVal.type
          = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (cval' c.name φ) ∈ˢ interp V ρ t ∧
          AnnotOkV V ρ t := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hi.fresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro c hc φ
  obtain ⟨t, ht, hd⟩ := m.mem_type c hc φ
  refine ⟨t, hi.denoteUp ht, ?_⟩
  rw [← hi.ag c.name (hne c hc)]
  exact hd

theorem defn_eq_consS {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀) :
    ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hi.fresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hint hmem φ
  have := hi.denoteUp (m.defn_eq cv value hint hmem φ)
  rwa [hi.ag cv.name (hne _ hmem)] at this

theorem thm_ok_consS {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀) :
    ∀ cv value, ConstantInfo.thmInfo cv value ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hi.fresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hmem φ
  have := hi.denoteUp (m.thm_ok cv value hmem φ)
  rwa [hi.ag cv.name (hne _ hmem)] at this

/-! ## Assembling an install -/

/-- The [set] environment invariant survives an ordinary install, given
the new constant's own obligations.  Transpose of `EnvTT.cons` (minus
its `ctor_residual` slot — the field is absent by design). -/
def EnvS.cons {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hclosed : ∀ ψ : Name → Nat, VExpr.Closed (cval' c₀.name ψ))
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval' c₀.name φ₁ = cval' c₀.name φ₂)
    (hannot : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkV V ρ (cval' c₀.name ψ))
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c₀.toConstantVal.type
        = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (cval' c₀.name φ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t)
    (hdefn : ∀ cv value hint, c₀ = .defnInfo cv value hint →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ))
    (hthm : ∀ cv value, c₀ = .thmInfo cv value → ∀ φ : Name → Nat,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
        = some (cval' cv.name φ))
    (hempty : c₀.name = emptyName →
      ∀ ψ : Name → Nat, ∃ u, cval' emptyName ψ = emptyT u)
    (hheadCtors : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ (φ : Name → Nat) (us : List Level),
        us.length = cv.levelParams.length →
        ∃ R, denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R ∧
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
              = some (.ctorInfo cvj cnP cnF) →
          ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List VExpr)
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
                interp V ρ (ys.getD i default)
                  = interp V ρ (xs.getD i default)) →
            (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
              ∀ i, i < RecRule.ctorParams rl →
              ∀ vp : VExpr,
                denote cval' ⟨c₀ :: env.consts⟩ φ rP
                  (openRev 0 rP
                    ((pins.getD i default).instantiateLevelParams
                      cv.levelParams us)) = some vp →
                VExpr.bvarsBelow rP vp →
                interp V ρ (ys.getD i default)
                  = interp V ρ (VExpr.instRevChain (xs.take rP) vp)) →
            IotaIndexPinV V ρ restC (RecRule.ctorParams rl) mI rP xs →
            denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TV →
            denoteClosed cval' ⟨c₀ :: env.consts⟩ φ
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              = some TVj →
            TeleFitV V ρ TV
              (xs ++ [VExpr.mkAppN
                (cval' (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            TeleFitV V ρ TVj ys restC →
            interp V ρ
                (VExpr.mkAppN
                  (cval' c₀.name (Level.substFn φ cv.levelParams us))
                  (xs ++ [VExpr.mkAppN
                    (cval' (RecRule.ctor rl)
                      (Level.substFn φ cvj.levelParams usj)) ys]))
              = interp V ρ
                  (VExpr.mkAppN R
                    (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
            ((∀ a ∈ xs, AnnotOkV V ρ a) →
              (∀ b ∈ ys, AnnotOkV V ρ b) →
              AnnotOkV V ρ
                (VExpr.mkAppN R
                  (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))))
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawV V ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawV V ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps)
    (hheadProj : ∀ entry, c₀ = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hheadProjPair : ∀ i entry, c₀ = .projInfo entry →
      c₀.name = projFnName psigmaName i → entry.native = true)
    (hheadEq : c₀.name = eqName → EqLawV V ⟨c₀ :: env.consts⟩ cval')
    (hheadBasis : reservedBasisNames.contains c₀.name = true →
      (ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name) ∧
      ∀ (ψ : Name → Nat) (t : VExpr),
        pinnedDirectT c₀.name ψ = some t → cval' c₀.name ψ = t)
    (hheadNat : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ φ : Name → Nat, ∀ eq ∈ natOpEquations 0 c₀.name, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        ∀ (ρ : Nat → V) (x y : V),
          x ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
          y ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
          interp V (cons V y (cons V x ρ)) L
            = interp V (cons V y (cons V x ρ)) R)
    (hheadDivMod : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
        y ∈ˢ interp V ρ (cval' natName (Level.substFn φ [] [])) →
        DivModClausesV V
          (fun n => interp V ρ (cval' n (Level.substFn φ [] [])))
          c₀.name x y)
    (hheadReduce : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
          x ∈ˢ interp V ρ (cval' (reduceElemName c₀.name) ψ) →
          SetTheory.app (interp V ρ (cval' c₀.name ψ)) x = x) :
    EnvS V ⟨c₀ :: env.consts⟩ := by
  refine
    { cval := cval'
      cval_closed := ?_
      wf := hwf
      val_params := ?_
      annot_okV := ?_
      mem_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := ?_
      basis_pinned := BasisPinnedTT.cons m.basis_pinned hi hheadBasis
      proj_ok := ProjOkT.cons m.proj_ok hi.fresh hheadProj hheadProjPair
      rec_ctors := RecCtorsStored.cons m.rec_ctors hi.fresh hheadCtors
      eq_lawV := EqLawV.cons m.eq_lawV hi.ag hheadEq
      rec_rules := fun φ => RecRulesV.cons (m.rec_rules φ) m.wf hi
        m.rec_ctors (fun cv mI rP rules hc rl hrl hfire =>
          ⟨(hheadRec cv mI rP rules hc rl hrl hfire).1,
            (hheadRec cv mI rP rules hc rl hrl hfire).2 φ⟩)
      caps_ok := CapsOkV.cons m.caps_ok m.wf hi hheadEta hheadUnit
      nat_ops := fun φ => NatOpsV.cons (m.nat_ops φ) hi
        (fun cv v hint hc hmem =>
          ⟨(hheadNat cv v hint hc hmem).1,
            (hheadNat cv v hint hc hmem).2 φ⟩)
      div_mod := fun φ => DivModV.cons (m.div_mod φ) hi
        (fun cv v hint hc hmem =>
          ⟨(hheadDivMod cv v hint hc hmem).1,
            (hheadDivMod cv v hint hc hmem).2 φ⟩)
      reduce_ops := ReduceOpsV.cons m.reduce_ops hi hheadReduce }
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
  · intro n ψ ρ
    by_cases hn : n = c₀.name
    · subst hn; exact hannot ψ ρ
    · rw [← hi.ag n hn]; exact m.annot_okV n ψ ρ
  · intro c hc φ
    rcases hc with _ | ⟨_, hc⟩
    · exact htype φ
    · exact mem_type_consS m hi c hc φ
  · intro cv value hint hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hdefn cv value hint rfl φ
    · exact defn_eq_consS m hi cv value hint hmem φ
  · intro cv value hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hthm cv value rfl φ
    · exact thm_ok_consS m hi cv value hmem φ
  · intro ψ
    by_cases hn : c₀.name = emptyName
    · exact hempty hn ψ
    · rw [← hi.ag emptyName (fun hh => hn hh.symm)]
      exact m.empty_pinned ψ

end Setlec.SetR
