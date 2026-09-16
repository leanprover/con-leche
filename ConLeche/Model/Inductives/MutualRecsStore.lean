module

public import ConLeche.Model.Inductives.MutualRecsLaw
public import ConLeche.Model.Inductives.MutualRecsSwap
public import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Swap
import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualWF
import ConLeche.Model.Inductives.MutualFormersKit
public section

/-!
# The recursors' store (task #315 U-9, M4 s4b)

`MutualRecsStored`, discharged: at the provisioned model
(`ProvisionedRecs`, M4 s4a) the group store — the same `k` recursors
with their rules, a swap of the rule-less provision
(`MutualRecsSwap.lean`) — cons a model of the recursors' environment
at which the datum still holds, every other leaf the constructors'
model's.

The store's rule law (`mutualRecsStore`'s `hlaws`) is the datum's
(`blockRecRuleLaw`, `MutualRecsLaw.lean`) at every stored rule: a rule
of member `t` is its `i`-th own constructor's (`memberRule_of`,
through `checkMutualMemberRules_inv` and the block's grouping), its
right-hand side reads at the provisioned model to the λ-tower over the
rule's binder data with the provisioned leaves as the recursors
(`ruleRhs_read_of`: `denoteMeta_mutualRecRhs` at the datum's readings,
the recursor table total below `k` through `mutualRecRhs_congr_recOf`),
and the reading crosses the swap unchanged (`denoteMeta_swap`).

The datum is transported twice (`BlockRepCross.lean`): from the
constructors' model to the provisioned one along the fresh recursor
conses (the leaves of every stored name untouched, `ProvisionedRecs.agree`),
and across the swap (the same leaves, `EnvModelM.swapP`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  BinderMeta MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

omit [SetTheory V] in
/-- The generated inductive hypothesis reads the recursor table at the
field's target only. -/
theorem mutualIhApp_congr_recOf {recOf recOf' : Nat → Name} {rlvls : List Level}
    {pw : ConLeche.PropWhen} {nP k n nF i m' : Nat} {tele : List (Expr × BinderMeta)}
    {idx : List Expr} (h : recOf m' = recOf' m') :
    ConLeche.mutualIhApp recOf rlvls pw nP k n nF i m' tele idx
      = ConLeche.mutualIhApp recOf' rlvls pw nP k n nF i m' tele idx := by
  unfold ConLeche.mutualIhApp
  rw [h]

omit [SetTheory V] in
theorem mutualRuleBody_congr_recOf {recOf recOf' : Nat → Name} {rlvls : List Level}
    {pw : ConLeche.PropWhen} {nP k n nF J : Nat} {recFields : List (Nat × Nat)}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (h : ∀ im ∈ recFields, recOf im.2 = recOf' im.2) :
    ConLeche.mutualRuleBody recOf rlvls pw nP k n nF J recFields teleOf idxOf
      = ConLeche.mutualRuleBody recOf' rlvls pw nP k n nF J recFields teleOf idxOf := by
  unfold ConLeche.mutualRuleBody
  congr 2
  exact List.map_congr_left fun im him => mutualIhApp_congr_recOf (h im him)

omit [SetTheory V] in
/-- **The generated rule reads the recursor table at the block's
members only** (`denoteMeta_mutualRecRhs` asks for a table stored at
EVERY index; the caller passes one agreeing with `recName` below `k`). -/
theorem mutualRecRhs_congr_recOf {lps : List Name} {elim : Name} {large : Bool} {nP : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4}
    {recOf recOf' : Nat → Name} {rlvls : List Level} {J : Nat}
    (h : ∀ c ∈ ctors, ∀ im ∈ c.recFields, recOf im.2 = recOf' im.2) :
    ConLeche.mutualRecRhs lps elim large nP formers ctors recOf rlvls J
      = ConLeche.mutualRecRhs lps elim large nP formers ctors recOf' rlvls J := by
  unfold ConLeche.mutualRecRhs
  cases hc : ctors[J]? with
  | none => rfl
  | some c =>
    cases hf : formers[0]? with
    | none => rfl
    | some f₀ =>
      simp only []
      rw [mutualRuleBody_congr_recOf (h c (List.mem_of_getElem? hc))]

omit [SetTheory V] in
/-- The rule core reads the recursors at the fields' targets only. -/
theorem mutualRuleCoreAV_congr_Rof {b k nP n nF J : Nat} {Rof Rof' : Nat → AnnotTerm}
    {tgtsJ : Nat → Nat} {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eiss : List (List AnnotTerm)} (h : ∀ i ∈ recIdx, Rof (tgtsJ i) = Rof' (tgtsJ i)) :
    mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss
      = mutualRuleCoreAV b Rof' tgtsJ nP k n nF J recIdx tls Eiss := by
  unfold mutualRuleCoreAV
  congr 2
  exact List.map_congr_left fun i hi => by rw [h i hi]

omit [SetTheory V] in
/-- **A stored rule's shape**: the generated right-hand side of one of
the member's constructors, `paramsBlind`, firing plainly or inert. -/
theorem mutualRules_mem_shape {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ ConLeche.mutualRules find? recName nP mI rP recTy l →
      ∃ cr ∈ l, ∃ kb eb : Bool,
        r = ⟨cr.1.cv.name, cr.1.nF, nP,
          (if Expr.recRulePlain recTy mI rP nP then .plain else .inert), cr.2, kb, eb, true⟩
  | [], r, h => by simp [ConLeche.mutualRules] at h
  | cr :: cs, r, h => by
    simp only [ConLeche.mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨cr, List.mem_cons_self, _, _, rfl⟩
    · obtain ⟨cr', hm, kb, eb, he⟩ := mutualRules_mem_shape h
      exact ⟨cr', List.mem_cons_of_mem _ hm, kb, eb, he⟩

omit [SetTheory V] in
/-- The provision stores every entry rule-less under its own name. -/
theorem provisionMutualRecs_find?_mem {b : MutualBlock} {fms : List MutualFormerA} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {x : ConstantVal × Nat},
      (l.map (·.1.name)).Nodup → x ∈ l →
      (ConLeche.provisionMutualRecs b fms l env).find? x.1.name
        = some (.recInfo x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix [])
  | [], _, _, _, hx => absurd hx (by simp)
  | (cvRa, mIdx) :: rest, env, x, hnd, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [ConLeche.provisionMutualRecs]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [provisionMutualRecs_find?_of_ne (fun y hy heq => hnd.1 (by
        rw [heq]; exact List.mem_map_of_mem hy))]
      exact ConLeche.Env.find?_cons_self _ _
    · exact provisionMutualRecs_find?_mem hnd.2 hx'

omit [SetTheory V] in
/-- The recursors' level parameters extend the block's. -/
theorem MutualBlock.mem_rlps_of_mem_lps (b : MutualBlock) {q : Name} (hq : q ∈ b.lps) :
    q ∈ b.rlps := by
  unfold MutualBlock.rlps
  split
  · exact List.mem_cons_of_mem _ hq
  · exact hq

omit [SetTheory V] in
/-- Every constructor datum of the block is a constructor's. -/
theorem BlockRepData.mem_recCds (d : BlockRepData V) {ψ : Name → Nat} {cd : CtorDatumR}
    (h : cd ∈ d.recCds ψ) :
    ∃ (c j : Nat) (cA : ConstantVal × Nat), c < d.k ∧ (d.ctorsM c)[j]? = some cA ∧
      cd.1 = cA.1.name := by
  unfold BlockRepData.recCds at h
  obtain ⟨c, hc, hcd⟩ := List.mem_flatMap.mp h
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcd
  have hjl : j < (d.cds c ψ).length := (List.getElem?_eq_some_iff.mp hj).1
  rw [d.cds_length] at hjl
  obtain ⟨cA, hcA⟩ : ∃ cA, (d.ctorsM c)[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjl⟩
  rw [d.cds_getElem? ψ hcA] at hj
  refine ⟨c, j, cA, List.mem_range.mp hc, hcA, ?_⟩
  rw [← Option.some.inj hj]

/-! ## A member's rules -/

section Rules

variable {b : MutualBlock} {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {d : BlockRepData V} {env₀ : Env}

omit [SetTheory V] in
/-- **A stored rule of member `t` is its `i`-th constructor's**: the
generated right-hand side at the block position `minorIdx t i`, the
constructor the datum's, with the block's level parameters. -/
theorem memberRule_of (hd : MutualDatumOf env₀ b fms ctorsA d)
    (hg : ConLeche.mutualCtorsGrouped b.ctors = true) (hlenA : ctorsA.length = b.ctors.length)
    (hnames : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    {t : Nat} (ht : t < b.k) {envR : Env} {formers4 : List MutualFormer}
    {ctors4 : List MutualCtor4} {streamRec : Option (ConstantVal × List RecRule)}
    {rules : List (MutualCtor × Expr)}
    (hrun : ConLeche.checkMutualMemberRules (m := ConLeche.CheckM) envR b formers4 ctors4 t
      streamRec = .ok rules)
    {cr : MutualCtor × Expr} (hcr : cr ∈ rules) :
    ∃ (i : Nat) (cA : ConstantVal × Nat), (d.ctorsM t)[i]? = some cA ∧
      cA.1.name = cr.1.cv.name ∧ cA.2 = cr.1.nF ∧ cA.1.levelParams = b.lps ∧
      ConLeche.mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4 b.recName
        (b.rlps.map Level.param) (d.minorIdx t i) = some cr.2 ∧
      cr.2.allLevelParamsDefined b.rlps = true ∧ cr.2.constsResolve envR = true ∧
      cr.2.looseBVarsBounded 0 = true ∧ cr.2.hasFvar = false := by
  obtain ⟨-, hlen, hall⟩ := ConLeche.checkMutualMemberRules_inv hrun
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcr
  have hi' : i < (b.ownCtors t).length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨J, c, rhs, hown, hget, hgen, hlp, hres, hbv, hfv⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  have hJ := ConLeche.ownCtors_getElem?_idx hg hown
  obtain ⟨hct, -⟩ := ConLeche.ownCtors_getElem?_ctors hown
  have hctorsM : (d.ctorsM t)[i]? = some (ctorsA.getD J default) := by
    rw [hd.ctors t ht, List.getElem?_map, hown]; rfl
  obtain ⟨-, hJA, -⟩ := hd.ctorsM_get hg hlenA ht hctorsM
  rw [← hJ] at hJA
  obtain ⟨hnm, hnF, hlps⟩ := hnames J _ c hJA hct
  refine ⟨i, ctorsA.getD J default, hctorsM, hnm, hnF, hlps, ?_, hlp, hres, hbv, hfv⟩
  rw [hd.minorIdx_eq ht i, ← hJ]
  exact hgen

end Rules

/-! ## The rule's reading at the provisioned model -/

section Reading

variable {F : Nat} {b : MutualBlock} {fms : List MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
  {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {d : BlockRepData V}
  {env₀ envP : Env}

/-- **A rule's right-hand side reads at the provisioned model** to the
λ-tower over the rule's binder data (the datum's readings) with the
model's recursor leaves as the recursors (`denoteMeta_mutualRecRhs`
at the datum, the recursor table total below `k`). -/
theorem ruleRhs_read_of (hd : MutualDatumOf env₀ b fms ctorsA d)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hlenF : fms.length = b.k) (h0k : 0 < b.k)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (hg : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (hlenK : kinds.length = ctorsA.length)
    (hnames : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    (hkinds : ∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
      d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
      ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    {mP : EnvModel V envP} (hrepsP : BlockReps mP d)
    (hstoredP : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mP b.lps b.nP f d.resSort (d.ppsM t))
    (hfR : ∀ t, t < d.k → ∃ ci : ConstantInfo,
      envP.find? (b.recName t) = some ci ∧ ci.toConstantVal.levelParams = b.rlps)
    {t i : Nat} (ht : t < d.k) {cA : ConstantVal × Nat} (hi : (d.ctorsM t)[i]? = some cA)
    {rhs : Expr}
    (hgen : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4 b.recName
      (b.rlps.map Level.param) (d.minorIdx t i) = some rhs)
    (ψ : Name → Nat) :
    denoteMeta mP.acval envP ψ 0 rhs
      = some (mkLamsAV
          (mutualRuleDataAV mP ψ (d.recLs mP ψ) d.nP d.recNIdxs b.elimLevel (d.recPps ψ)
            (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts (d.dsF t i ψ))
          (mutualRuleCoreAV (pwBit ψ (Level.zeronessOf b.elimLevel))
            (fun t' => mP.acval (b.recName t') ψ) (d.tgts t i) d.nP d.k d.nCtors cA.2
            (d.minorIdx t i) (ConLeche.recIdxOf (d.ksF t i)) (d.tssF t i ψ) (d.eissF t i ψ))) := by
  have hk4 : formers4.length = d.k := by rw [formers4_length hgd, hlenF, hd.k]
  have hn4 : ctors4.length = d.nCtors := by
    rw [ctors4_length hgd hlenK hlenA, hd.nCtors_eq h2 hlenA]
  have h0k' : 0 < d.k := by rw [hd.k]; exact h0k
  have hi' : i < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hi).1
  have hFReads := blockFormerReadsM_of hd hgd hstoredP
  have hCReads := blockCtorReadsM_of hd hrepsP h2 hg hlenA hlenK hnames hgd hkinds
  have hmots : ∀ J, J < ctors4.length → d.recMots J < formers4.length := by
    intro J hJ
    rw [hn4] at hJ
    obtain ⟨c, j, cA', hc, hj, rfl⟩ := d.minor_index hJ
    rw [d.recMots_at hc (List.getElem?_eq_some_iff.mp hj).1, hk4]
    exact hc
  have hmemF : ∀ t', t' < d.k → ∃ f, fms[t']? = some f ∧ d.memberName t' = f.cvTa.name := by
    intro t' ht'
    have ht'' : t' < fms.length := by rw [hlenF, ← hd.k]; exact ht'
    refine ⟨fms.getD t' default,
      by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht'']; rfl, ?_⟩
    show d.memberNames.getD t' .anonymous = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht'', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht'']
    rfl
  have hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      envP.find? (d.recTname q) = some ci ∧ ci.toConstantVal.levelParams = b.lps := by
    intro q
    have hq : (if q < d.k then q else 0) < d.k := by
      split
      · assumption
      · exact h0k'
    obtain ⟨f, hf, hname⟩ := hmemF _ hq
    obtain ⟨caps, hfind⟩ := (hstoredP _ f hf).find
    refine ⟨.indInfo f.cvTa caps, ?_, (hstoredP _ f hf).lps⟩
    show envP.find? (d.memberName (if q < d.k then q else 0)) = _
    rw [hname]
    exact hfind
  -- the recursor table, total below `k`
  have hfR' : ∀ q : Nat, ∃ ci : ConstantInfo,
      envP.find? (b.recName (if q < d.k then q else 0)) = some ci ∧
      ci.toConstantVal.levelParams = b.rlps := by
    intro q
    refine hfR _ ?_
    split
    · assumption
    · exact h0k'
  -- every generated constructor's recursive fields target members
  have htgts : ∀ c4 ∈ ctors4, ∀ im ∈ c4.recFields, im.2 < d.k := by
    intro c4 hc4 im him
    obtain ⟨J, hJ⟩ := List.getElem?_of_mem hc4
    have hJn : J < d.nCtors := by rw [← hn4]; exact (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨c, j, cA', hc, hj, rfl⟩ := d.minor_index hJn
    have hck : c < b.k := by rw [← hd.k]; exact hc
    have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨hlt, hJA, ct, hct, -⟩ := hd.ctorsM_get hg hlenA hck hj
    have hoff := hd.minorIdx_eq hck j
    have hks : kinds[b.ownOffset c + j]? = some (mutKsOf kinds (b.ownOffset c + j)) := by
      unfold mutKsOf
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenK]; exact hlt)]
      rfl
    have h4 := ctors4_getElem? hgd hJA hct hks
    rw [hoff] at hJ
    obtain rfl := Option.some.inj (hJ.symm.trans h4)
    obtain ⟨hksF, htgtsE⟩ := hkinds c j hck hj'
    have hfields : ConLeche.mutualRecFieldsOf (mutKsOf kinds (b.ownOffset c + j))
        = (ConLeche.recIdxOf (d.ksF c j)).map fun i => (i, d.tgts c j i) := by
      rw [mutualRecFieldsOf_eq, hksF]
      exact List.map_congr_left fun i _ => by rw [htgtsE i]
    simp only [hfields, List.mem_map] at him
    obtain ⟨i', hi'', rfl⟩ := him
    obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hrepsP c hc
    exact hrep.tgtsLt c j i' hc hj' (mem_recIdxOf.mp hi'').1
  have hgen' : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4
      (fun q => b.recName (if q < d.k then q else 0)) (b.rlps.map Level.param) (d.minorIdx t i)
      = some rhs := by
    rw [← hgen]
    exact mutualRecRhs_congr_recOf fun c4 hc4 im him => by rw [if_pos (htgts c4 hc4 im him)]
  have hJd : (d.recCds ψ)[d.minorIdx t i]?
      = some (cA.1.name, cA.2, d.dsF t i ψ, d.esF t i ψ, ConLeche.recIdxOf (d.ksF t i),
          d.eissF t i ψ, d.tssF t i ψ) := by
    rw [d.recCds_getElem? ψ ht hi', d.cds_getElem? ψ hi]
  have h := denoteMeta_mutualRecRhs (hFReads ψ) (hCReads ψ) hmots hfT hfR' hgen' hJd
  rw [hk4, hn4, ← hd.nP, d.recTgts_at ht hi'] at h
  rw [h]
  congr 2
  refine mutualRuleCoreAV_congr_Rof fun i' hi'' => ?_
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hrepsP t ht
  rw [if_pos (hrep.tgtsLt t i i' ht hi' (mem_recIdxOf.mp hi'').1)]

end Reading

/-! ## The store -/

section Store

variable {F : Nat} {b : MutualBlock} {fms : List MutualFormerA} {f₀ : MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
  {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {d : BlockRepData V}
  {env₀ env₂ : Env}

/-- **The store at the datum**: from the provisioned model, the group
store cons a model of the recursors' environment at which the datum
holds, every other leaf the constructors' model's. -/
theorem mutualRecsStore_of (mp₂ : EnvModelM V μ env₂)
    (h0 : b.blockNames.Nodup)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hf₀ : fms[0]? = some f₀) (hlenF : fms.length = b.k) (hL : b.large = f₀.s.isNeverZero)
    (hlenA : ctorsA.length = b.ctors.length) (hlenK : kinds.length = ctorsA.length)
    (hnames : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂ b
      formers4 ctors4 streamRecs b.k = .ok cvRas)
    {rulesOf : List (List (MutualCtor × Expr))}
    (hrules : ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf)
    (hd : MutualDatumOf env₀ b fms ctorsA d) (hreps : BlockReps mp₂.base2 d)
    (htyped : ∀ ψ : Name → Nat, FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ)
    (hrecNames : ∀ t, t < b.k → env₂.find? (b.recName t) = none ∧
      ConLeche.reservedBasisNames.contains (b.recName t) = false ∧
      (b.recName t).isProjFnShape = false)
    (hstored : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mp₂.base2 b.lps b.nP f d.resSort (d.ppsM t))
    (hkinds : ∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
      d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
      ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    {s : (Name → Nat) → Nat}
    {mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)}
    (hP : ProvisionedRecs mp₂ b fms cvRas d s mpP) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₃.base2.acval n ψ = mp₂.base2.acval n ψ) ∧
      BlockReps mp₃.base2 d ∧
      ∀ ψ : Name → Nat, FormersTyped mp₃.base2 d ψ ∧ CtorsTyped mp₃.base2 d ψ := by
  have hkd : d.k = b.k := hd.k
  have h0k : 0 < b.k := by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hf₀).1
  have hnC : d.nCtors = b.ctors.length := by rw [hd.nCtors_eq h2 hlenA, hlenA]
  -- **the recursors' names**
  have hfresh : ∀ t, t < d.k → env₂.find? (cvRas.getD t default).name = none := by
    intro t ht
    rw [(hP.names t ht).1]
    exact (hrecNames t (by rw [← hkd]; exact ht)).1
  have hnres : ∀ t, t < d.k →
      ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false := by
    intro t ht
    rw [(hP.names t ht).1]
    exact (hrecNames t (by rw [← hkd]; exact ht)).2.1
  have hzip : ∀ x ∈ cvRas.zipIdx, x.2 < d.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← hP.lenR]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hfreshZ : ∀ x ∈ cvRas.zipIdx, env₂.find? x.1.name = none := by
    intro x hx
    rw [(hzip x hx).2]
    exact hfresh _ (hzip x hx).1
  have hnd : (cvRas.map (·.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun t => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases ht : t < b.k
      · have htl : t < cvRas.length := by rw [hP.lenR, hkd]; exact ht
        rw [List.getElem?_range ht, List.getElem?_eq_getElem htl]
        have := (hP.names t (by rw [hkd]; exact ht)).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl] at this
        simp only [Option.map_some, Option.some.injEq]
        exact this
      · rw [List.getElem?_eq_none (by rw [hP.lenR, hkd]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [hmapEq]
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  have hndZ : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst]]
    exact hnd
  -- **the datum at the provisioned model**
  obtain ⟨hFP, -, -⟩ := provisionMutualRecs_extend (b := b) (fms := fms) hfreshZ hndZ
  have hF₁ : ∀ (n : Name) (ci : ConstantInfo), (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₂.find? n = some ci →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some ci :=
    fun _ _ _ h => hFP h
  have hres₁ := constsResolve_of_findPreserved hFP
  have hag₁ : ∀ n : Name, (env₂.find? n).isSome = true →
      mpP.base2.acval n = mp₂.base2.acval n := by
    intro n hn
    refine hP.agree n fun t ht heq => ?_
    rw [heq, hfresh t ht] at hn
    exact nomatch hn
  have hde₁ := provision_hde (m := mp₂.base2) (mP := mpP.base2) hfreshZ hndZ hag₁
  have hrepsP : BlockReps mpP.base2 d := hreps.crossEnv hF₁ hres₁ hag₁ hde₁
  have htypedP : ∀ ψ : Name → Nat, FormersTyped mpP.base2 d ψ ∧ CtorsTyped mpP.base2 d ψ :=
    fun ψ => ⟨(htyped ψ).1.crossEnv hag₁ hreps, (htyped ψ).2.crossEnv hag₁ hreps⟩
  have hstoredP : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mpP.base2 b.lps b.nP f d.resSort (d.ppsM t) :=
    fun t f hf => (hstored t f hf).crossEnv hF₁ hde₁
  -- **the swap**
  have hcg := swapCongr_provision_store (b := b) (fms := fms) (rulesOf := rulesOf) (env₂ := env₂)
    (cvRas := cvRas)
  have hF₂ : ∀ (n : Name) (ci : ConstantInfo), (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some ci →
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).find? n = some ci :=
    fun n ci hnr h => hcg.findUp n ci h hnr
  have hres₂ := constsResolve_of_swapCongr hcg
  -- **the run facts** about the rules
  obtain ⟨hlenU, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
  have hrulesAt : ∀ t, t < d.k → ∃ rules, rulesOf.getD t [] = rules ∧
      ConLeche.checkMutualMemberRules (m := ConLeche.CheckM)
        (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 t
        (streamRecs.bind (·[t]?)) = .ok rules := by
    intro t ht
    obtain ⟨rules, hget, hrun⟩ := hallU t (by rw [← hkd]; exact ht)
    exact ⟨rules, by rw [List.getD_eq_getElem?_getD, hget]; rfl, hrun⟩
  -- the constructors' leaves are untouched by the provision
  have hagC : ∀ (c j : Nat) (cA : ConstantVal × Nat), c < d.k → (d.ctorsM c)[j]? = some cA →
      mpP.base2.acval cA.1.name = mp₂.base2.acval cA.1.name := by
    intro c j cA hc hj
    obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hreps c hc
    exact hag₁ _ (by rw [(hrep.ctors c j cA hc hj).1]; rfl)
  -- the recursor table at the provision
  have hfR : ∀ t, t < d.k → ∃ ci : ConstantInfo,
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? (b.recName t) = some ci ∧
      ci.toConstantVal.levelParams = b.rlps := by
    intro t ht
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hP.lenR]; exact ht)]
      rfl
    refine ⟨.recInfo (cvRas.getD t default) (b.rulePrefix + (fms.getD t default).nIdx)
      b.rulePrefix [], ?_, (hP.names t ht).2⟩
    rw [← (hP.names t ht).1]
    exact provisionMutualRecs_find?_mem hndZ hmem
  -- **the regime fact**
  have hwℓ : ∀ ψ : Name → Nat, d.w ψ = 0 → b.elimLevel.eval ψ = 0 := by
    intro ψ hw
    have hw' : f₀.s.eval ψ = 0 := by
      have : d.w ψ = (fms.getD 0 default).s.eval ψ := by
        show d.resSort.eval ψ = _
        rw [hd.resSort]
      rw [this, List.getD_eq_getElem?_getD, hf₀] at hw
      exact hw
    exact elimLevel_zero_of_w_zero hL ψ hw'
  -- **the readings**
  have hR : ∀ ψ : Name → Nat, BlockReadings mp₂.base2 d ψ b.elimLevel (d.recLs mp₂.base2 ψ)
      d.recNIdxs (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts :=
    fun ψ => d.blockReadings_of mp₂.base2 ψ b.elimLevel (fun mm hmm => (hP.recData mm hmm).below ψ)
  -- the leaves are closed
  have hleafCl : ∀ t, t < d.k → ∀ ψ : Name → Nat,
      Term.bvarsBelow 0 (d.recLeaf mp₂.base2 b.elimLevel s b.rlps t ψ).erase := by
    intro t ht ψ
    rw [← hP.leaves t ht ψ]
    exact mpP.base2.cval_closedL _ ψ
  -- the readings at the restricted assignment
  have hrdsR : ∀ t, t < d.k → ∀ ψ : Name → Nat,
      d.blockRds mp₂.base2 b.elimLevel t (restrictΨ b.rlps ψ) = d.blockRds mp₂.base2 b.elimLevel t ψ :=
    fun t ht ψ => (hP.recData t ht).params _ ψ fun q hq =>
      restrictΨ_agree b.rlps ψ q (by rw [← (hP.names t ht).2]; exact hq)
  -- **every stored rule's constructor is stored at the constructors' environment**
  have hctorStored : ∀ t, t < d.k → ∀ r ∈ ConLeche.mutualRules env₂.find?
      (cvRas.getD t default).name b.nP (b.rulePrefix + (fms.getD t default).nIdx)
      b.rulePrefix (cvRas.getD t default).type (rulesOf.getD t []),
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) := by
    intro t ht r hr
    obtain ⟨cr, hcr, kb, eb, rfl⟩ := mutualRules_mem_shape hr
    obtain ⟨rules, hrulesD, hrun⟩ := hrulesAt t ht
    rw [hrulesD] at hcr
    obtain ⟨i, cA, hi, hnm, -, -, -, -, -, -, -⟩ :=
      memberRule_of hd h3 hlenA hnames (by rw [← hkd]; exact ht) hrun hcr
    obtain ⟨cvT, cvR, mI, rP, rules', hrep⟩ := hreps t ht
    refine ⟨cA.1, d.nP, cA.2, ?_⟩
    show env₂.find? cr.1.cv.name = _
    rw [← hnm]
    exact (hrep.ctors t i cA ht hi).1
  -- **the block's rule law at the store**
  have hlaws : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → ∀ (φ : Name → Nat) (t : Nat), t < d.k →
      ∀ rl ∈ ConLeche.mutualRules env₂.find? (cvRas.getD t default).name b.nP
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix
          (cvRas.getD t default).type (rulesOf.getD t []),
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ (cvRas.getD t default).name (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix rl := by
    intro m₃ hac φ t ht rl hrl hfire
    obtain ⟨cr, hcr, kb, eb, rfl⟩ := mutualRules_mem_shape hrl
    obtain ⟨rules, hrulesD, hrun⟩ := hrulesAt t ht
    rw [hrulesD] at hcr
    obtain ⟨i, cA, hi, hnm, hnF, hlps, hgen, hlpsRhs, -, -, -⟩ :=
      memberRule_of hd h3 hlenA hnames (by rw [← hkd]; exact ht) hrun hcr
    have hi' : i < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hi).1
    -- the rule fires plainly
    by_cases hplain : Expr.recRulePlain (cvRas.getD t default).type
        (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix b.nP = true
    case neg =>
      exfalso
      apply hfire
      show (if Expr.recRulePlain _ _ _ _ then ConLeche.RecRuleFire.plain else ConLeche.RecRuleFire.inert) = _
      rw [if_neg hplain]
    rw [if_pos hplain]
    -- the datum at the store's model
    have hrepsS : BlockReps m₃ d :=
      hrepsP.crossEnv hF₂ hres₂ (fun n _ => congrFun hac n) (swap_hde hcg hac)
    obtain ⟨cvT₃, cvR₃, mI₃, rP₃, rules₃, hrep₃⟩ := hrepsS t ht
    obtain ⟨hfC₃, -, hcd₃⟩ := hrep₃.ctors t i cA ht hi
    -- the arities
    have hmI : b.rulePrefix + (fms.getD t default).nIdx = d.nP + d.k + d.nCtors + d.nIdxAt t := by
      unfold ConLeche.MutualBlock.rulePrefix ConLeche.MutualBlock.n
      rw [hd.nP, hkd, hnC]
      congr 1
      have htf : t < fms.length := by rw [hlenF, ← hkd]; exact ht
      show _ = d.nIdxs.getD t 0
      rw [hd.nIdxs, List.getD_eq_getElem?_getD (l := fms.map (·.nIdx)), List.getElem?_map,
        List.getElem?_eq_getElem htf, List.getD_eq_getElem?_getD (l := fms),
        List.getElem?_eq_getElem htf]
      rfl
    have hrP : b.rulePrefix = d.nP + d.k + d.nCtors := by
      unfold ConLeche.MutualBlock.rulePrefix ConLeche.MutualBlock.n
      rw [hd.nP, hkd, hnC]
    -- the rule's reading at the store
    have hread : ∀ ψ : Name → Nat,
        denoteMeta m₃.acval (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) ψ 0 cr.2
          = some (d.ruleRhsAV mp₂.base2 b.elimLevel
              (fun t' => d.recLeaf mp₂.base2 b.elimLevel s b.rlps t' ψ) t i cA.2 ψ) := by
      intro ψ
      rw [hac, ← denoteMeta_swap hcg,
        ruleRhs_read_of hd hgd hlenF h0k h2 h3 hlenA hlenK hnames hkinds hrepsP hstoredP hfR ht hi
          hgen ψ]
      unfold BlockRepData.ruleRhsAV BlockRepData.ruleData
      congr 2
      · -- the binder data: the members' leaves and the constructors' are the constructors' model's
        rw [mutualRuleDataAV_congr (m₂ := mp₂.base2) fun cd hcd => by
          obtain ⟨c, j, cA', hc, hj, hname⟩ := d.mem_recCds hcd
          rw [hname]
          exact congrFun (hagC c j cA' hc hj) ψ]
        congr 1
        unfold BlockRepData.recLs
        refine List.map_congr_left fun t' ht' => ?_
        have ht'' : t' < d.k := List.mem_range.mp ht'
        have ht''' : t' < fms.length := by rw [hlenF, ← hkd]; exact ht''
        obtain ⟨caps, hfind⟩ := (hstored t' (fms.getD t' default)
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht''']; rfl)).find
        have hname : d.memberName t' = (fms.getD t' default).cvTa.name := by
          show d.memberNames.getD t' .anonymous = _
          rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem ht''', List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem ht''']
          rfl
        exact congrFun (hag₁ _ (by rw [hname, hfind]; rfl)) ψ
      · -- the core: the recursors are the provisioned leaves
        refine mutualRuleCoreAV_congr_Rof fun i' hi'' => ?_
        obtain ⟨cvT, cvR, mI, rP, rules', hrep⟩ := hreps t ht
        have htgt := hrep.tgtsLt t i i' ht hi' (mem_recIdxOf.mp hi'').1
        rw [← (hP.names _ htgt).1]
        exact hP.leaves _ htgt ψ
    have hrule : (⟨cr.1.cv.name, cr.1.nF, b.nP, ConLeche.RecRuleFire.plain, cr.2, kb, eb, true⟩ : RecRule)
        = ⟨cA.1.name, cA.2, d.nP, .plain, cr.2, kb, eb, true⟩ := by
      rw [hnm, hnF, hd.nP]
    refine blockRecRuleLaw m₃ hreps (fun ψ => (htyped ψ).1) (fun ψ => (htyped ψ).2)
      (fun n ψ ρ => mp₂.acval_validV n ψ ρ) hwℓ hR (fun ψ mm hmm ρ => (hP.recData mm hmm).okTy ψ ρ)
      hrdsR hleafCl (fun t' ht' ψ ρ => hP.leafTyped ψ ρ t' ht') hP.iota
      (fun c j cA' hc hj ψ => by rw [hac]; exact congrFun (hagC c j cA' hc hj) ψ) ht hi
      (fun q hq => MutualBlock.mem_rlps_of_mem_lps b (by rw [← hlps]; exact hq))
      ((hP.recData t ht).crossEnv (swap_hde hcg hac))
      (fun ψ => by rw [hac]; exact hP.leaves t ht ψ) hfC₃ (fun ψ => hcd₃.read ψ) hlpsRhs hread
      hmI hrP hrule φ
  -- **the store**
  obtain ⟨mp₃, hac, -⟩ := mutualRecsStore (k := d.k) mp₂.base2.wf hrectys hrules mpP hP.lenR hfresh
    hnres hctorStored hlaws
  refine ⟨mp₃, fun n hn ψ => ?_, ?_, fun ψ => ?_⟩
  · rw [hac]
    refine congrFun (hP.agree n fun t ht heq => hn ?_) ψ
    rw [heq, (hP.names t ht).1]
    unfold ConLeche.MutualBlock.blockNames
    exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr (by rw [← hkd]; exact ht)))
  · exact hrepsP.crossEnv hF₂ hres₂ (fun n _ => congrFun hac n) (swap_hde hcg hac)
  · exact ⟨(htypedP ψ).1.crossEnv (fun n _ => congrFun hac n) hrepsP,
      (htypedP ψ).2.crossEnv (fun n _ => congrFun hac n) hrepsP⟩

end Store

/-! ## `MutualRecsStored`, discharged -/

/-- **The store's stage, proved**: `mutualRecsStore_of` at the run
facts of `MutualRecsStored`. -/
theorem mutualRecsStored {F : Nat} : MutualRecsStored V μ F := by
  intro hμ env mp hE b streamRecs fms f₀ tq₀ ctorsA sortss kinds formers4 ctors4 cvRas rulesOf
    h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkindsC hfo hgd hrectys hrules mp₂ hE₂ hagree
    d hd hreps htyped hrecNames hstored hkinds s mpP hP
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv hformers
  have hlenF : fms.length = b.k := (mutualFormerChecks_pos hchecks).1
  obtain ⟨-, -, -, hlenK⟩ := ConLeche.classifyMutualKinds_inv hkindsC
  obtain ⟨hlenA, hnames⟩ := ctorsA_names_of hctors h1
  exact mutualRecsStore_of mp₂ h0 h2 h3 hf₀ hlenF hL hlenA hlenK hnames hgd hrectys hrules hd hreps
    htyped hrecNames hstored hkinds hP

/-- **The recursors' stage, proved.** -/
theorem mutualRecsModeled {F : Nat} : MutualRecsModeled V μ F :=
  mutualRecsModeled_of mutualRecsStored

/-- **Stages 0–4 keep the model and leave the datum** — `MutualCoreModeled`,
proved. -/
theorem mutualCoreModeled {F : Nat} : MutualCoreModeled V μ F :=
  mutualCoreModeled_of mutualRecsModeled

/-- **`declBlock` at the core, proved**: the model survives a mutual
block given the tables' stage (`MutualTablesModeled`). -/
theorem declBlock_of_tables (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : ConLeche.MutualParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpinOk : ConLeche.mutualRecPinOk p = true) (htables : MutualTablesModeled V μ)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) :=
  declBlock hμ mp hE hpinOk mutualCoreModeled htables h

end ConLeche.Model
