import Setlec.SetP.IndBottomProjP
import Setlec.SetP.Annot.BitReads

/-!
# The per-rule bridge, canonical branch (task #161, IND TIER part 9)

`iotaRuleS`'s transpose on the `.plain` branch: one checked rule kit
(`IotaRuleR`, `SetR/Decl.lean`) whose fire mode is `.plain` yields the
`RecRuleLawP` row the recursor group's install owes, by firing
`indBottomPlainP`.

**Everything the bottom needs beyond the kit comes from the P
environment invariant**, and this file is where that is shown:

* the statement's front doors (`hthm`) are `EnvS2PM`'s `type_reads`
  (the reading exists), `mem_typeP` (the stored theorem's leaf
  inhabits it — the "there is a proof" conjunct) and `type_okP` (it is
  graded).  v1 reads all three off `EnvS.mem_type`;
* the recursor type's grading (`htyOk`) is `type_okP` at the
  *provisioned* entry — the recursor is stored rule-less in the self
  environment (`hself`), so unlike the plain bottom's own docstring
  warns for a general caller, `mp.type_okP` does apply here;
* **the rule right-hand side's front door (`hrhsKey`) is the H1
  exposure, cashed.**  Its three parts come from three different
  places: the *reading exists* by `denoteP_isSome_of_denote`
  (`Annot/BitReads.lean`) applied to the kit's own v1 derivation row;
  the *inferred type reads* by `InferReadsP` on the kit's recorded run
  (`∃ t', inferTypeCore μ envSelf F 0 rhsA = .ok t'`, the fourth
  widening); and the *grading and membership* by `InferClaims2P` on the
  same run at the empty context (`Sat2_nil`).  No row is owed and
  nothing is routed.

The `.nested` branch is not here: `RecRuleLawP`'s repaired pin
conjunct owes the pins' `openRev` readings, whose supply is the
successor's first item (see the seal).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta RecRule isDefEqCore inferTypeCore DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 12800000 in
/-- **One checked `.plain` rule's fired law, at the reading**
(`iotaRuleS`'s canonical branch). -/
theorem iotaRulePlainP {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mp : EnvS2PM V μ envSelf)
    (hdeq : ∀ ψ : Name → Nat, DefEqClaims2P μ mp.base2 ψ F)
    (hinf : ∀ ψ : Name → Nat, InferClaims2P μ mp.base2 ψ F)
    (hreadsP : ∀ ψ : Name → Nat, InferReadsP mp.base2 μ ψ F)
    {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hroT : RenameOkP mp.base2.acval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    -- the rule kits are checked against the running accumulator (see
    -- `iotaRuleS`: a correspondence, not an inclusion)
    (hup : ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
      envSelf.find? n = some ci ∨
      ∃ cv mI' rP' rules rules',
        ci = .recInfo cv mI' rP' rules ∧
        envSelf.find? n = some (.recInfo cv mI' rP' rules'))
    {cvA : ConstantVal} {mI rP j : Nat} {r r' : RecRule}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA)
    (hkit : IotaRuleR μ F env₂ envSelf mp.base2.cvalE f cvA.name
      cvA.levelParams cvA.type mI rP j r r')
    (hfireP : RecRule.fire r' = .plain) (φ : Name → Nat) :
    RecRuleLawP mp.base2 φ cvA.name cvA mI rP r' := by
  obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
    hrres, hstripRhs, hkey, hrun0, fire, hr'eq, hbranch⟩ := hkit
  -- the rule's stored shape
  have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]
  have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]
  have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]
  have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq, hnfK]
  have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]
  -- the recursor's and the constructor's stored guards
  obtain ⟨htyw, -, -, htyb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hself)
  have hfcS : envSelf.find? (RecRule.ctor r)
      = some (.ctorInfo cvjK cnPK cnFK) := by
    rcases hup _ _ hfcK with h |
      ⟨cv, mI', rP', rules, rules', heq, -⟩
    · exact h
    · exact nomatch heq
  obtain ⟨hCw, hClp, -, hCb, -, -, -⟩ :=
    mp.base2.wf _ (Env.find?_mem hfcS)
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
  -- the recursor type's grading, at the provisioned entry
  have htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP mp.base2.acval envSelf ψ 0 cvA.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta :=
    mp.type_okP _ (Env.find?_mem hself)
  -- ===== the rule rhs's front door, at the reading (the H1 exposure)
  have hrhsLeafNil : ∀ l ∈ rhsA.fvarLeaves, False := by
    intro l hl
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsAw] at hl
    exact nomatch hl
  have hrhsWs : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsAw
  have hrhsLb : Expr.LeavesBounded rhsA :=
    fun l hl => absurd hl (fun h => hrhsLeafNil l h)
  obtain ⟨t', hrun⟩ := hrun0
  have hrhsKey : ∀ ψ : Name → Nat, ∃ Ra ta,
      denoteP mp.base2.acval envSelf ψ 0 rhsA = some Ra ∧
      ∀ ρ : Nat → V, AnnotOkP V ρ Ra ∧
        interp2 V ρ Ra ∈ˢ interp2 V ρ ta := by
    intro ψ
    obtain ⟨Rv, -, hRv, -⟩ := hkey ψ
    obtain ⟨Ra, hRa⟩ := denotePClosed_isSome_of_denoteClosed
      (acval := mp.base2.acval) hRv
    have hctx : CtxOkP mp.base2 ψ 0 [] rhsA :=
      ⟨rfl, fun l hl => absurd hl (fun h => hrhsLeafNil l h)⟩
    obtain ⟨ta, hta⟩ := hreadsP ψ hrun hrhsWs hrhsAb hrhsLb
      (LeafReadsP.of_ctxOkP hctx) hRa
    obtain ⟨hokRa, -, hmemRa⟩ :=
      hinf ψ hrun hrhsWs hrhsAb hrhsLb hctx hRa hta
    exact ⟨Ra, ta, hRa, fun ρ =>
      ⟨hokRa ρ (Sat2_nil V ρ), hmemRa ρ (Sat2_nil V ρ)⟩⟩
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
  -- ===== the canonical branch =====
  obtain ⟨hpl, hfireP0, hthmR⟩ :
      Expr.recRulePlain cvA.type mI rP cnPK = true ∧ fire = .plain ∧
        IotaThmR μ F env₂ envSelf mp.base2.cvalE f cvA.name
          cvA.levelParams cvA.type mI rP j r cvjK cnPK cnFK rhsA := by
    rcases hbranch with h | ⟨hnpl, hrest⟩
    · exact h
    · exfalso
      rcases hrest with ⟨hfireI, -⟩ | ⟨lvls, pins, hfireN, -⟩
      · rw [hr'fire, hfireI] at hfireP; exact nomatch hfireP
      · rw [hr'fire, hfireN] at hfireP; exact nomatch hfireP
  refine ⟨recRulePlain_le_mIT hpl, ?_⟩
  intro us huslen
  -- unpack the canonical `iota_j` kit
  obtain ⟨cvt, fvs, tbody, hcvtE, hcvtlps, hopen, hEqH, hlen3,
    hlhead0, hlarity0, hlpre0, hmaj0, hCstrips,
    cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hcinst, hclen, hrinst, hopenP, hcinstP, hopenXP,
    ldomsL, lrest2, hinstLam, -, hdeParsRun, -, hruns⟩ := hthmR
  -- the statement's stored entry and front doors
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
    mp.base2.wf _ (Env.find?_mem hciTS)
  rw [hciTcv] at hSw0 hSb0
  have hSw : cvt.type.hasFvar = false := hSw0
  have hSb : cvt.type.looseBVarsBounded 0 = true := hSb0
  have hthm : ∀ ψ : Name → Nat, ∃ ta,
      denoteP mp.base2.acval envSelf ψ 0 cvt.type = some ta ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp2 V ρ ta) ∧
        AnnotOkP V ρ ta := by
    intro ψ
    obtain ⟨ta, hta0⟩ := mp.type_reads ciT (Env.find?_mem hciTS) ψ
    have hta : denoteP mp.base2.acval envSelf ψ 0 cvt.type = some ta := by
      rwa [hciTcv] at hta0
    exact ⟨ta, hta, fun ρ =>
      ⟨⟨_, mp.mem_typeP ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩,
        mp.type_okP ciT (Env.find?_mem hciTS) ψ ta hta0 ρ⟩⟩
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
  simp only [hα, hL, hR] at hruns
  obtain ⟨hdeIdx, hdeFld, hdePre, hdeLam, hdeRhs, hsideL, hsideR⟩ :=
    hruns
  -- fire the plain bottom
  obtain ⟨Ra, hRaden, hokRa, hRalaw⟩ := indBottomPlainP (V := V) mp
    hdeq hinf hreadsP hroT heqfS htyw htyb htyOk hfRnE hRmlps hfcS
    hfCmE hCmlps hCw hCb hClp
    (recRulePlain_le_mIT hpl) (recRulePlain_leT hpl) hrhsAw hrhsAb
    hrhsKey hSw hSb hthm hopen hheadEq hargs3
    (eq_of_beq hlhead0) hlarity0 (eq_of_beq hlpre0) (eq_of_beq hmaj0)
    hCstrips hcinst hclen hrinst hopenP hcinstP hopenXP hinstLam
    hdeIdx hdePre hdeFld hdeParsRun hdeLam hdeRhs hsideL hsideR
    φ us huslen
  refine ⟨Ra, by rw [hr'rhs]; exact hRaden, hokRa, ?_, ?_⟩
  · -- the `.nested` pin conjunct: the rule is `.plain`
    intro lvls pins hn
    rw [hfireP] at hn
    exact nomatch hn
  intro cvj cnP cnF hfcv usj ρ xs ys TVa TVja restR restC hlenX hlenY
    husjlen hlev hplain hnested hidx hTVa hTVja hfitR hfitC
  obtain ⟨rfl, rfl, rfl⟩ := hctorId hfcv
  rw [hr'cp, hr'nf] at hlenY
  rw [hr'cp] at hidx ⊢
  rw [hr'ctor] at hfitR ⊢
  refine hRalaw usj ρ xs ys TVa TVja restR restC hlenX hlenY husjlen
    ?_ ?_ hidx hTVa hTVja hfitR hfitC
  · rw [hlev, recFireComparands_plain hfireP]
  · intro i hi him
    exact hplain hfireP i (by rw [hr'cp]; exact hi) him

end Setlec.SetR.Interp2
