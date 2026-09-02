import Setlec.SetR.Install.SwapS
import Setlec.SetR.Install.IndBottomPlainS
import Setlec.SetR.Install.IndBottomNestedS

/-!
# The per-rule bridge (task #148, T5, stage 3b)

`iotaRuleS` turns one checked rule kit (`IotaRuleR`) into the
`RecRulesV` clause the recursor group's install owes, firing
`indBottomPlainS` on the `.plain` branch and `indBottomNestedS` on the
`.nested` one (`.inert` is excluded by the clause's own premise).

Everything the bottoms need beyond the kit is glue the environment
already carries: `BlockInstalledTT` gives the block renaming's
`RenameOkT` and the model counterparts of the recursor and the
constructor, `EnvWF` gives the stored types' syntactic guards,
`EnvS.mem_type` gives the `iota_j` theorem's front doors, `Infer.sound`
turns the kit's rhs inference into the rule's key, and
`recRulePlain_leT`/`_le_mIT` give the two arity bounds.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 12800000 in
/-- **One checked rule's fired law**, at the self environment. -/
theorem iotaRuleS {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mS : EnvS V envSelf) {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hro : RenameOkT mS.cval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mS.cval)
    -- the rule kits are checked against the *running accumulator*,
    -- which is `envSelf` with some of the group's recursors already
    -- carrying their rules — so this is a correspondence, not an
    -- inclusion (the inclusion is false exactly at those recursors)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal} {mI rP j : Nat} {r r' : RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleR μ F env₂ envSelf mS.cval f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    (hfire : RecRule.fire r' ≠ .inert) (φ : Name → Nat) :
    RecRuleLawV V envSelf mS.cval φ cvA.name cvA mI rP r' := by
  unfold RecRuleLawV
  obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
    hrres, hstripRhs, hkey, fire, hr'eq, hbranch⟩ := hkit
  -- the rule's stored shape
  have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]
  have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]
  have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]
  have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq, hnfK]
  have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]
  -- the recursor's and the constructor's stored guards
  obtain ⟨htyw, -, -, htyb, -, -, -⟩ := mS.wf _ (Env.find?_mem hself)
  have hfcS : envSelf.find? (RecRule.ctor r)
      = some (.ctorInfo cvjK cnPK cnFK) := by
    rcases hup _ _ hfcK with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ := mS.wf _ (Env.find?_mem hfcS)
  -- the recursor's model counterpart
  obtain ⟨cvm, mval, hm, hfm, hlpsm, -, -⟩ :=
    hIS cvA.name hbnA _ hself
  have hfRnE : envSelf.find? (f cvA.name)
      = some (.defnInfo cvm mval hm) := by
    rw [hf]
    dsimp only
    rw [if_pos hbnA]
    exact hfm
  -- the constructor's renamed head
  obtain ⟨ciCm, hfCmE, hCmlps⟩ : ∃ ciCm,
      envSelf.find? (f (RecRule.ctor r)) = some ciCm ∧
      ciCm.toConstantVal.levelParams = cvjK.levelParams := by
    by_cases hbc : blockNames.contains (RecRule.ctor r) = true
    · obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC, -, -⟩ := hIS _ hbc _ hfcS
      refine ⟨.defnInfo cvmC mvalC hmC, ?_, hlpsC⟩
      rw [hf]
      dsimp only
      rw [if_pos hbc]
      exact hfmC
    · refine ⟨.ctorInfo cvjK cnPK cnFK, ?_, rfl⟩
      rw [hf]
      dsimp only
      rw [if_neg hbc]
      exact hfcS
  have heqfS : envSelf.find? eqName = some eqA := by
    rcases hup _ _ heqfind with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hrhsAw, hrhsAb⟩ := annotate_syntax hann hrf hrb
  have hRmlps : (ConstantInfo.defnInfo cvm mval
      hm).toConstantVal.levelParams = cvA.levelParams := hlpsm
  -- the rule's right-hand side key
  have hrhsKey : ∀ ψ' : Name → Nat, ∃ Rv t,
      denoteClosed mS.cval envSelf ψ' rhsA = some Rv ∧
      ∀ ρ : Nat → V,
        AnnotOkV V ρ Rv ∧ interp V ρ Rv ∈ˢ interp V ρ t := by
    intro ψ'
    obtain ⟨Rv, t, hRv, hInf⟩ := hkey ψ'
    exact ⟨Rv, t, hRv, fun ρ =>
      Infer.sound (mS.toHyp ψ') hInf ρ (Sat_nil V ρ)⟩
  -- the constructor's identification at the law's own lookup
  have hctorId : ∀ {cvj' : ConstantVal} {cnP' cnF' : Nat},
      envSelf.find? (RecRule.ctor r')
        = some (.ctorInfo cvj' cnP' cnF') →
      cvj' = cvjK ∧ cnP' = cnPK ∧ cnF' = cnFK := by
    intro cvj' cnP' cnF' hf'
    rw [hr'ctor, hfcS] at hf'
    injection hf' with h1
    injection h1 with e1 e2 e3
    exact ⟨e1.symm, e2.symm, e3.symm⟩
  rcases hbranch with ⟨hpl, hfireP, hthmR⟩ | ⟨hnpl, hrest⟩
  · -- ===== the canonical branch =====
    refine ⟨recRulePlain_le_mIT hpl, ?_⟩
    intro us huslen
    -- unpack the canonical `iota_j` kit
    obtain ⟨cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH, hlen3,
      hlhead0, hlarity0, hlpre0, hmaj0, hCstrips,
      cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms,
      lrest, hcinst, hclen, hrinst, hopenP, hcinstP, hopenXP,
      ldomsL, lrest2, hinstLam, hdePars, -, hwalks, -⟩ := hthmR
    -- the statement's stored entry and front doors
    -- only the stored `ConstantVal` matters, so a swapped entry
    -- (were the statement's name a recursor's) serves just as well
    obtain ⟨ciT, hciTS, hciTcv⟩ : ∃ ciT, envSelf.find?
        ((cvA.name.str "_model").str s!"iota_{j}") = some ciT ∧
        ciT.toConstantVal = cvt := by
      unfold Env.findCV? at hcvtE
      rcases h : env₂.find? ((cvA.name.str "_model").str s!"iota_{j}")
        with _ | ci₂
      · rw [h] at hcvtE; exact nomatch hcvtE
      · rw [h] at hcvtE
        have hcv₂ : ci₂.toConstantVal = cvt := Option.some.inj hcvtE
        rcases hup _ _ h with h' |
          ⟨cv, mI', rP', rules, rules', heq, h'⟩
        · exact ⟨ci₂, h', hcv₂⟩
        · exact ⟨.recInfo cv mI' rP' rules', h',
          by rw [← hcv₂, heq]; rfl⟩
    obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ :=
      mS.wf _ (Env.find?_mem hciTS)
    rw [hciTcv] at hSw0 hSb0
    have hSw : cvt.type.hasFvar = false := hSw0
    have hSb : cvt.type.looseBVarsBounded 0 = true := hSb0
    have hthm : ∀ ψ' : Name → Nat, ∃ t,
        denoteClosed mS.cval envSelf ψ' cvt.type = some t ∧
        ∀ ρ : Nat → V,
          (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t := by
      intro ψ'
      obtain ⟨t, ht, hd⟩ := mS.mem_type ciT (Env.find?_mem hciTS) ψ'
      rw [hciTcv] at ht
      exact ⟨t, ht, fun ρ => ⟨⟨_, (hd ρ).1⟩, (hd ρ).2⟩⟩
    -- the equation head and its three arguments
    obtain ⟨ℓA, hheadEq⟩ : ∃ ℓA,
        tbody.getAppFn = .const eqName [ℓA] := by
      unfold isEqHead at hEqH
      split at hEqH
      · next c ℓ heq =>
        exact ⟨ℓ, by rw [heq, eq_of_beq hEqH]⟩
      · exact nomatch hEqH
    obtain ⟨αS, lhsS, rhsS, hargs3⟩ : ∃ αS lhsS rhsS,
        tbody.getAppArgs = [αS, lhsS, rhsS] := by
      rcases h : tbody.getAppArgs with _ | ⟨a, l1⟩
      · rw [h] at hlen3; exact nomatch hlen3
      rcases l1 with _ | ⟨b, l2⟩
      · rw [h] at hlen3; exact nomatch hlen3
      rcases l2 with _ | ⟨c, l3⟩
      · rw [h] at hlen3; exact nomatch hlen3
      rcases l3 with _ | ⟨d, l4⟩
      · exact ⟨a, b, c, rfl⟩
      · rw [h] at hlen3; exact nomatch hlen3
    have hα : tbody.getAppArgs.getD 0 (.bvar 0) = αS := by
      rw [hargs3]; rfl
    have hL : tbody.getAppArgs.getD 1 (.bvar 0) = lhsS := by
      rw [hargs3]; rfl
    have hR : tbody.getAppArgs.getD 2 (.bvar 0) = rhsS := by
      rw [hargs3]; rfl
    simp only [hL] at hlhead0 hlarity0 hlpre0 hmaj0
    simp only [hα, hL, hR] at hwalks
    -- fire the plain bottom
    obtain ⟨Rv, hRvden, hRvlaw⟩ := indBottomPlainS (V := V) mS hro heqfS
      htyw htyb hfRnE hRmlps hfcS hfCmE hCmlps hCw hCb hClp
      (recRulePlain_le_mIT hpl) (recRulePlain_leT hpl) hrhsAw hrhsAb
      hrhsKey
      hSw hSb hthm hopen hheadEq hargs3
      (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0) (eq_of_beq hmaj0)
      hCstrips hcinst hclen hrinst hopenP hcinstP hopenXP hstripRhs
      hinstLam
      (fun ψ' => (hwalks ψ').1) (fun ψ' => (hwalks ψ').2.2.1)
      (fun ψ' => (hwalks ψ').2.1) hdePars
      (fun ψ' => (hwalks ψ').2.2.2.1) (fun ψ' => (hwalks ψ').2.2.2.2.1)
      (fun ψ' => (hwalks ψ').2.2.2.2.2) φ us huslen
    refine ⟨Rv, by rw [hr'rhs]; exact hRvden, ?_⟩
    intro cvj cnP cnF hfcv usj ρ xs ys TV TVj restR restC hlenX hlenY
      husjlen hlev hparP hparN hidx hTV hTVj hfitR hfitC
    obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
    rw [hr'cp, hr'nf] at hlenY
    rw [hr'cp] at hparP hidx ⊢
    rw [hr'ctor] at hfitR ⊢
    refine hRvlaw usj ρ xs ys TV TVj restR restC hlenX hlenY husjlen
      ?_ ?_ hidx hTV hTVj hfitR hfitC
    · rw [hlev, recFireComparands_plain (hr'fire.trans hfireP)]
    · intro i hi him
      exact hparP (hr'fire.trans hfireP) i hi him
  · -- ===== the nested branch =====
    rcases hrest with ⟨hfireI, -⟩ | ⟨lvls, pins, hfireN, hthmN⟩
    · exact absurd (hr'fire.trans hfireI) hfire
    · obtain ⟨hshape, cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH,
        hlen3, hlhead0, hlarity0, hlpre0, hmaj0, hCstripsHead,
        cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP,
        ldoms, hcinst, hclen, hrinst, hopenP,
        ⟨hpinAnn, hcinstP, hopenXP, hldomsAr⟩,
        ldomsL, lrest2, hinstLam, hTypedP, -, hwalks, -⟩ := hthmN
      obtain ⟨hrPmI, -, hpinsWf0, -⟩ := nestedRuleShape_inv hshape
      obtain ⟨-, -, -, pre, nmD, domD, bodyD, bmD, D,
        -, -, -, hpinsLen⟩ := nestedRuleShape_inv hshape
      refine ⟨hrPmI, ?_⟩
      intro us huslen
      -- the statement's stored entry and front doors
      -- only the stored `ConstantVal` matters, so a swapped entry
      -- (were the statement's name a recursor's) serves just as well
      obtain ⟨ciT, hciTS, hciTcv⟩ : ∃ ciT, envSelf.find?
          ((cvA.name.str "_model").str s!"iota_{j}") = some ciT ∧
          ciT.toConstantVal = cvt := by
        unfold Env.findCV? at hcvtE
        rcases h : env₂.find? ((cvA.name.str "_model").str s!"iota_{j}")
          with _ | ci₂
        · rw [h] at hcvtE; exact nomatch hcvtE
        · rw [h] at hcvtE
          have hcv₂ : ci₂.toConstantVal = cvt := Option.some.inj hcvtE
          rcases hup _ _ h with h' |
            ⟨cv, mI', rP', rules, rules', heq, h'⟩
          · exact ⟨ci₂, h', hcv₂⟩
          · exact ⟨.recInfo cv mI' rP' rules', h',
          by rw [← hcv₂, heq]; rfl⟩
      obtain ⟨hSw0, -, -, hSb0, -, -, -⟩ :=
      mS.wf _ (Env.find?_mem hciTS)
      rw [hciTcv] at hSw0 hSb0
      have hSw : cvt.type.hasFvar = false := hSw0
      have hSb : cvt.type.looseBVarsBounded 0 = true := hSb0
      have hthm : ∀ ψ' : Name → Nat, ∃ t,
          denoteClosed mS.cval envSelf ψ' cvt.type = some t ∧
          ∀ ρ : Nat → V,
            (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t := by
        intro ψ'
        obtain ⟨t, ht, hd⟩ := mS.mem_type ciT (Env.find?_mem hciTS) ψ'
        rw [hciTcv] at ht
        exact ⟨t, ht, fun ρ => ⟨⟨_, (hd ρ).1⟩, (hd ρ).2⟩⟩
      -- the equation head and its three arguments
      obtain ⟨ℓA, hheadEq⟩ : ∃ ℓA,
          tbody.getAppFn = .const eqName [ℓA] := by
        unfold isEqHead at hEqH
        split at hEqH
        · next c ℓ heq =>
          exact ⟨ℓ, by rw [heq, eq_of_beq hEqH]⟩
        · exact nomatch hEqH
      obtain ⟨αS, lhsS, rhsS, hargs3⟩ : ∃ αS lhsS rhsS,
          tbody.getAppArgs = [αS, lhsS, rhsS] := by
        rcases h : tbody.getAppArgs with _ | ⟨a, l1⟩
        · rw [h] at hlen3; exact nomatch hlen3
        rcases l1 with _ | ⟨b, l2⟩
        · rw [h] at hlen3; exact nomatch hlen3
        rcases l2 with _ | ⟨c, l3⟩
        · rw [h] at hlen3; exact nomatch hlen3
        rcases l3 with _ | ⟨d, l4⟩
        · exact ⟨a, b, c, rfl⟩
        · rw [h] at hlen3; exact nomatch hlen3
      have hα : tbody.getAppArgs.getD 0 (.bvar 0) = αS := by
        rw [hargs3]; rfl
      have hL : tbody.getAppArgs.getD 1 (.bvar 0) = lhsS := by
        rw [hargs3]; rfl
      have hR : tbody.getAppArgs.getD 2 (.bvar 0) = rhsS := by
        rw [hargs3]; rfl
      simp only [hL] at hlhead0 hlarity0 hlpre0 hmaj0
      simp only [hα, hL, hR] at hwalks
      have hCstrips' : ∃ bsC0 cbody0 Dc usc,
          cvjK.type.stripPis (cnPK + cnFK) = some (bsC0, cbody0) ∧
          cbody0.getAppFn = Expr.const Dc usc := by
        obtain ⟨bsC0, cbody0, hstripC0, hheadB⟩ := hCstripsHead
        split at hheadB
        · next n us heq =>
          exact ⟨bsC0, cbody0, n, us, hstripC0, heq⟩
        · exact nomatch hheadB
      -- the stored levels' arity, forced semantically
      obtain ⟨Tst0, hTst0, -⟩ := hthm φ
      have hlvlsLen : lvls.length = cvjK.levelParams.length := by
        rw [← hCmlps]
        exact nestedLvlsLength hTst0 hopen hheadEq hargs3
          (eq_of_beq hlhead0) hlarity0
          hmaj0 hfCmE
      -- fire the nested bottom
      obtain ⟨Rv, hRvden, hRvlaw⟩ := indBottomNestedS (V := V) mS hro
        heqfS htyw htyb hfRnE hRmlps hfcS hfCmE hCmlps hCw hCb hClp
        hrPmI hlvlsLen hpinsLen
        (fun p hp => ⟨(hpinsWf0 p hp).1, (hpinsWf0 p hp).2.2.2⟩)
        hrhsAw hrhsAb hrhsKey hSw hSb hthm hopen hheadEq hargs3
        (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0)
        hmaj0 hCstrips'
        hcinst hclen hrinst hopenP hcinstP hopenXP hstripRhs hinstLam
        hTypedP
        (fun ψ' => (hwalks ψ').1) (fun ψ' => (hwalks ψ').2.2.1)
        (fun ψ' => (hwalks ψ').2.1) (fun ψ' => (hwalks ψ').2.2.2.1)
        (fun ψ' => (hwalks ψ').2.2.2.2.1)
        (fun ψ' => (hwalks ψ').2.2.2.2.2) φ us huslen
      refine ⟨Rv, by rw [hr'rhs]; exact hRvden, ?_⟩
      intro cvj cnP cnF hfcv usj ρ xs ys TV TVj restR restC hlenX hlenY
        husjlen hlev hparP hparN hidx hTV hTVj hfitR hfitC
      obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
      rw [hr'cp, hr'nf] at hlenY
      rw [hr'cp] at hparN hidx ⊢
      rw [hr'ctor] at hfitR ⊢
      refine hRvlaw usj ρ xs ys TV TVj restR restC hlenX hlenY husjlen
        ?_ ?_ hidx hTV hTVj hfitR hfitC
      · rw [hlev,
          recFireComparands_nested (hr'fire.trans hfireN)]
      · exact hparN lvls pins (hr'fire.trans hfireN)

end Setlec.SetR
