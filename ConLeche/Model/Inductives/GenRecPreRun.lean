module

public import ConLeche.Model.Inductives.GenRecPre
public import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.ClassGenRead

public section

/-!
# `GenPreHyps` from the generated stage's run: the run-level fields

The fields of `GenPreHyps` (`GenRecPre.lean`) that are facts of the
generated stage's RUN alone — the family's lengths, the shared prefix's
length, the prefix positions of the motives and minor premises, the
callees of the generated `ih`s.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Run

variable {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The pre-pass reads one class per recursor. -/
theorem genRun_recCls_length
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) :
    R.rd.recCls.length = p.recs.length := by
  have hrd := R.hrd
  obtain ⟨hlc, -⟩ := ConLeche.classStreamRecs_run R.hcvRis
  unfold ConLeche.classRead at hrd
  obtain ⟨rc0, -, hrd⟩ := Option.bind_eq_some_iff.mp hrd
  obtain ⟨⟨_, body⟩, -, hrd⟩ := Option.bind_eq_some_iff.mp hrd
  obtain ⟨slots, -, hrd⟩ := Option.bind_eq_some_iff.mp hrd
  obtain ⟨recCls, hrc, hrd⟩ := Option.bind_eq_some_iff.mp hrd
  simp only [Option.pure_def, Option.some.injEq] at hrd
  rw [← hrd]
  show recCls.length = _
  rw [ConLeche.option_mapM_length hrc]
  simp [List.length_zip, hlc]

/-- The stored family has one entry per recursor, as do the generated
constants. -/
theorem genRun_lengths
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) :
    out.length = p.recs.length ∧ R.cvGs.length = p.recs.length := by
  obtain ⟨hlenG, -⟩ := ConLeche.classRecTysOk_run R.hcvGs
  obtain ⟨hlenO, -⟩ := ConLeche.classRecsRulesOk_run R.hrules
  have hlc := genRun_recCls_length R
  refine ⟨?_, hlenG⟩
  rw [hlenO, hlenG]
  have : R.rd.recCls.length = p.recs.length := hlc
  simp [this]

/-- **The run at a stored recursor**, by its position in the stored
family. -/
theorem genRun_at
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ rc cls cvG rhss, p.recs[c]? = some rc ∧ R.rd.recCls[c]? = some cls ∧
      R.cvGs[c]? = some cvG ∧ Nonempty (ConLeche.ClassRecTyRun μ F (mkFEnv envC) R.g p.k rc cls cvG) ∧
      out[c]? = some (cvG, R.Ms.getD cls default, rhss) ∧
      tgtMajor out c = R.Ms.getD cls default ∧ genClsOf R.rd c = cls := by
  have hco : c < p.recs.length := by
    rw [← (genRun_lengths R).1]; simpa [tgtRs] using hc
  obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[c]? = some rc := ⟨_, List.getElem?_eq_getElem hco⟩
  obtain ⟨cls, cvG, rhss, hcls, hG, T, ho, -, -⟩ := genRecRun_at R hrc
  refine ⟨rc, cls, cvG, rhss, hrc, hcls, hG, T, ho, ?_, ?_⟩
  · simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
  · simp [genClsOf, List.getD_eq_getElem?_getD, hcls]

/-- The generator of a run: its fields are the run's. -/
theorem genRun_g_pre
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) :
    R.g.pre = R.pre ∧ R.g.slots = R.rd.slots ∧ R.g.nP = p.nP ∧ R.g.ctors = R.ctors ∧
      R.g.cls = R.Ms := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`GenPreHyps.gpre`**: the shared prefix is every recursor's rule
prefix. -/
theorem genRun_gpre (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → R.g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).length := by
  intro c hc
  obtain ⟨rc, cls, cvG, rhss, hrc, hcls, -, ⟨T⟩, -, -, -⟩ := genRun_at R hc
  rw [blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ]
  obtain ⟨hrP, -, -⟩ := genRecTy_run hμ R hg hrc hcls T
  show R.pre.length = (p.recs.getD c default).rP
  rw [List.getD_eq_getElem?_getD, hrc, Option.getD_some, hrP]

/-- The prefix is the parameters and the slots. -/
theorem genRun_pre_length
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) :
    R.pre.length = p.nP + R.rd.slots.length :=
  (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1

/-- A recursor's class has a motive slot. -/
theorem genRun_motive
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ s, ConLeche.ClassRead.motiveSlot ⟨R.rd.slots, []⟩ (genClsOf R.rd c) = some s ∧
      s < R.rd.slots.length := by
  obtain ⟨-, cls, -, -, -, hcls, -, -, -, -, hgc⟩ := genRun_at R hc
  obtain ⟨s, hs⟩ := ConLeche.classRead_recCls_motive R.hrd cls (List.mem_of_getElem? hcls)
  rw [hgc]
  exact ⟨s, hs, ConLeche.ClassRead.motiveSlot_lt hs⟩

/-- **`GenPreHyps.mot`**: a recursor's motive sits in its rule prefix. -/
theorem genRun_mot (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC) :
    ∀ c, c < (tgtRs out).length →
      classMotPos R.g (genClsOf R.rd c) < p.toBlockShape.rulePrefixAt c := by
  intro c hc
  obtain ⟨s, hs, hsl⟩ := genRun_motive R hc
  have hg' := genRun_gpre hμ R hg h mpC (fun _ => 0) c hc
  rw [blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc)] at hg'
  rw [← hg']
  show R.g.nP + (ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ (genClsOf R.rd c)).getD 0 < _
  have hpl := genRun_pre_length R hg
  show p.nP + (ConLeche.ClassRead.motiveSlot ⟨R.rd.slots, []⟩ (genClsOf R.rd c)).getD 0
    < R.pre.length
  rw [hs, hpl]
  simp only [Option.getD_some]
  omega

/-- **`GenPreHyps.min`**: a minor premise's slot sits in the rule prefix. -/
theorem genRun_min (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      R.g.nP + genMinorSlot R.g R.rd c j < p.toBlockShape.rulePrefixAt c := by
  intro c hc j _
  obtain ⟨s, -, hsl⟩ := genRun_motive R hc
  have hg' := genRun_gpre hμ R hg h mpC (fun _ => 0) c hc
  rw [blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc)] at hg'
  rw [← hg']
  have hpl := genRun_pre_length R hg
  have hlt : genMinorSlot R.g R.rd c j < R.rd.slots.length := by
    unfold genMinorSlot
    cases hf : (List.range R.g.slots.length).find? _ with
    | none => simp only [Option.getD_none]; omega
    | some s' =>
      simp only [Option.getD_some]
      have := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      exact this
  show p.nP + genMinorSlot R.g R.rd c j < R.pre.length
  omega

/-- **`GenPreHyps.cal`**: every generated `ih` calls a recursor of the
family (the first recursor at its class, `genRecIdx`). -/
theorem genRun_cal
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (bit : Nat)
    (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV acval env R.g R.rd bit ψ c j, q.1 < (tgtRs out).length := by
  intro c hc j _ q hq
  have hK : (tgtRs out).length = R.rd.recCls.length := by
    rw [genRun_recCls_length R]; simpa [tgtRs] using (genRun_lengths R).1
  simp only [genIhdAV, List.mem_map] at hq
  obtain ⟨r, -, rfl⟩ := hq
  show genRecIdx R.rd r.2.1 < _
  unfold genRecIdx
  cases hf : (List.range R.rd.recCls.length).find? _ with
  | none => simp only [Option.getD_none]; omega
  | some s' =>
    simp only [Option.getD_some]
    rw [hK]
    exact List.mem_range.mp (List.mem_of_find?_eq_some hf)

/-- **A class of the run**, checked as a major (`ClassMajorRun`), with its
table entries. -/
theorem genRun_class
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {i : Nat} (hi : i < R.Ms.length) :
    ∃ key M₀ nfs, R.Ms[i]? = some { M₀ with nfs := nfs } ∧
      Nonempty (ConLeche.ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params key M₀) := by
  obtain ⟨hlN, hallN⟩ := ConLeche.classesNfs_run R.hMs
  obtain ⟨hlM, hallM⟩ := ConLeche.classMajors_run R.hMs₀
  have hi0 : i < R.Ms₀.length := by omega
  have hik : i < (R.rd.classes.map (ConLeche.classKeyCanon R.ctx.params)).length := by omega
  obtain ⟨M, hM, hrun⟩ := hallM i _ (List.getElem?_eq_getElem hik)
  obtain ⟨nfs, hMs, -⟩ := hallN i M hM
  exact ⟨_, M, nfs, hMs, hrun⟩

/-- **A member class**: the block's member `t`, its index count the
member's. -/
theorem genRun_member
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {cls t : Nat} (hm : (R.Ms.getD cls default).member = some t) :
    ∃ ms, p.members[t]? = some ms ∧ (R.Ms.getD cls default).nIdx = ms.nIdx ∧
      t < p.toBlockShape.k := by
  have hi : cls < R.Ms.length := by
    rcases Nat.lt_or_ge cls R.Ms.length with hl | hl
    · exact hl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hm
      exact nomatch hm
  obtain ⟨key, M₀, nfs, hMs, ⟨CR⟩⟩ := genRun_class R hi
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  rw [hget] at hm ⊢
  have hmaj := CR.major
  cases hmaj with
  | member I t' ms ctorsA hfn ht hms hctors hpar nfs' =>
    obtain rfl : t' = t := by simpa using hm
    refine ⟨ms, hms, rfl, ?_⟩
    have := (List.getElem?_eq_some_iff.mp hms).1
    exact this
  | outside => exact nomatch hm

variable {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- The member recursor's record names its class's member. -/
theorem genRun_recTgt
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c t : Nat} (hc : c < (tgtRs out).length) (hm : (tgtMajor out c).member = some t) :
    p.toBlockShape.recTgtAt c = t := by
  obtain ⟨rc, cls, cvG, rhss, hrc, hcls, -, ⟨T⟩, -, hM, -⟩ := genRun_at R hc
  rw [hM] at hm
  show (p.recs.getD c default).tgt = t
  rw [List.getD_eq_getElem?_getD, hrc, Option.getD_some, T.htgt]
  show ((R.Ms.getD cls default).member.getD p.k) = t
  rw [hm]; rfl

/-- **`GenPreHyps.nIdx`**: a class's index count is the stored one. -/
theorem genRun_nIdx
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hd : d = blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) :
    ∀ c, c < (tgtRs out).length →
      tgtClsNIdx d p.toBlockShape out c = (tgtMajor out c).nIdx := by
  intro c hc
  cases hmb : (tgtMajor out c).member with
  | none => exact tgtClsNIdx_out hmb
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    rw [tgtClsNIdx_mem hm, genRun_recTgt R hc hmb]
    obtain ⟨-, cls, -, -, -, -, -, -, -, hM, -⟩ := genRun_at R hc
    rw [hM] at hmb ⊢
    obtain ⟨ms, hms, hn, -⟩ := genRun_member R hmb
    rw [hn, hd]
    show (p.toBlockShape.nIdxs).getD t 0 = ms.nIdx
    simp [ConLeche.BlockShape.nIdxs, List.getD_eq_getElem?_getD, hms]

/-- **`GenPreHyps.mN`**: a class's component is below its clause's width. -/
theorem genRun_mN (mpC : EnvModelM V μ envC)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hd : d = blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) :
    ∀ c, c < (tgtRs out).length → tgtClsM mc p.toBlockShape out c < (tgtClsD d Dc out c).N := by
  intro c hc
  cases hmb : (tgtMajor out c).member with
  | none =>
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    simp only [tgtClsM, tgtClsD, hm, Bool.false_eq_true, if_false]
    have hcl := hcls c hc hmb
    obtain ⟨hC, -⟩ := mpC.lfp_ok _ hcl.hD
    exact Nat.lt_of_lt_of_le hcl.hmm hC.kN
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    simp only [tgtClsM, tgtClsD, hm, if_true]
    rw [genRun_recTgt R hc hmb]
    obtain ⟨-, cls, -, -, -, -, -, -, -, hM, -⟩ := genRun_at R hc
    rw [hM] at hmb
    obtain ⟨-, -, -, htk⟩ := genRun_member R hmb
    rw [hd]
    show t < p.toBlockShape.k + 0
    omega

/-- **`GenPreHyps.din`**: every class's clause is recorded. -/
theorem genRun_din (mpC : EnvModelM V μ envC) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) :
    ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks := by
  intro c hc
  unfold tgtClsD
  cases hmb : (tgtMajor out c).member with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, if_false]; exact (hcls c hc hmb).hD
  | some t => simp only [Option.isSome_some, if_true]; exact hlfp

/-- The rule count is the class's constructor count. -/
theorem genRun_nCt {c : Nat} (hc : c < (tgtRs out).length) :
    blockRecNCt (tgtRs out) c = (tgtMajor out c).ctors.length := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
    tgtRs_ctors (List.getElem?_eq_getElem hc)]

set_option maxHeartbeats 800000 in
/-- **The rule frame of a generated rule**: at recursor `c` (class `cls`)
and constructor `j`, the class's constructor `cA`, the generator's
constructor `x` (`genCtorAt`), its run (`ClassCtorRun`), the declared
type at the class (`tgtCrest`) is `x.tyD`, and it opens at the rule
prefix to the rule's field openers (the rule was generated). -/
theorem genRun_frame (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g)
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c) :
    ∃ (cls : Nat) (cA : ConstantVal × Nat) (fvs : List Expr) (cb : Expr),
      genClsOf R.rd c = cls ∧ tgtMajor out c = R.Ms.getD cls default ∧
      (tgtMajor out c).ctors[j]? = some cA ∧ tgtCtorOf out c j = cA ∧
      Nonempty (ConLeche.ClassCtorRun μ F envC p.toBlockShape (cvTas.map (·.type)) R.rd R.Ms cls cA
        (genCtorAt R.g R.rd c j)) ∧
      (genCtorAt R.g R.rd c j).nF = cA.2 ∧
      tgtCrest out c j = (genCtorAt R.g R.rd c j).tyD ∧
      tgtRP p.toBlockShape c = R.pre.length ∧
      ConLeche.openPisAtFvars cA.2 (genCtorAt R.g R.rd c j).tyD R.pre.length = some (fvs, cb) ∧
      tgtFieldFvs p.toBlockShape out c j = fvs ∧ tgtCbody p.toBlockShape out c j = cb ∧
      (∃ ws, ConLeche.targetPiDomsWith fvs (genCtorAt R.g R.rd c j).tyN = some ws) ∧
      genCtorAt R.g R.rd c j ∈ R.g.ctors.getD cls [] := by
  obtain ⟨rc, cls, cvG, rhss, hrc, hcls, hG, ⟨T⟩, ho, hM, hgc⟩ := genRun_at R hc
  rw [genRun_nCt hc] at hj
  obtain ⟨cA, hcA⟩ : ∃ cA, (tgtMajor out c).ctors[j]? = some cA :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  have hclsL : cls < R.Ms.length := by
    rcases Nat.lt_or_ge cls R.Ms.length with hl | hl
    · exact hl
    · rw [hM, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hj
      exact absurd hj (Nat.not_lt_zero _)
  -- the class's constructors, as the generator read them
  obtain ⟨hlC, hallC⟩ := ConLeche.classesCtors_run R.hctors
  obtain ⟨xs, hxs, hxsR⟩ := hallC cls (R.Ms.getD cls default)
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hclsL]; rfl)
  rw [Nat.zero_add] at hxsR
  obtain ⟨-, hallX⟩ := ConLeche.classCtorsOf_run hxsR
  obtain ⟨x, hx, ⟨CR⟩⟩ := hallX j cA (by rw [← hM]; exact hcA)
  have hctorsCls : R.ctors.getD cls [] = xs := by
    rw [List.getD_eq_getElem?_getD, hxs, Option.getD_some]
  have hgx : genCtorAt R.g R.rd c j = x := by
    show ((R.ctors.getD (genClsOf R.rd c) []).getD j default) = x
    rw [hgc, hctorsCls, List.getD_eq_getElem?_getD, hx, Option.getD_some]
  have hnF : x.nF = cA.2 := by rw [CR.hx]
  -- the rules' run at the recursor: the rule of `x` was generated
  obtain ⟨-, hallO⟩ := ConLeche.classRecsRulesOk_run R.hrules
  obtain ⟨rhss', ho', hrules⟩ := hallO c cvG cls hG hcls
  obtain ⟨-, hallR⟩ := ConLeche.classRulesOk_run hrules
  obtain ⟨gen, -, -, hgen, -⟩ := hallR j x (by
    show (R.ctors.getD cls [])[j]? = some x
    rw [hctorsCls]; exact hx)
  unfold ConLeche.classGenRule at hgen
  obtain ⟨⟨s, sl⟩, -, hgen⟩ := Option.bind_eq_some_iff.mp hgen
  obtain ⟨⟨fvs, cb⟩, hop, hgen⟩ := Option.bind_eq_some_iff.mp hgen
  obtain ⟨ws, hws, -⟩ := Option.bind_eq_some_iff.mp hgen
  have hrP : rc.rP = R.pre.length := (genRecTy_run hμ R hg hrc hcls T).1
  have htRP : tgtRP p.toBlockShape c = R.pre.length := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some, hrP]
  have hctor : tgtCtorOf out c j = cA := by
    rw [tgtCtorOf, List.getD_eq_getElem?_getD, hcA, Option.getD_some]
  have hcrest : tgtCrest out c j = x.tyD := by
    rw [tgtCrest, hctor, hM, CR.hD, Option.getD_some]
  have hop' : ConLeche.openPisAtFvars cA.2 x.tyD R.pre.length = some (fvs, cb) := by
    rw [← hnF]; exact hop
  refine ⟨cls, cA, fvs, cb, hgc, hM, hcA, hctor, by rw [hgx]; exact ⟨CR⟩, by rw [hgx, hnF],
    by rw [hgx, hcrest], htRP, by rw [hgx]; exact hop', ?_, ?_, ⟨ws, by rw [hgx]; exact hws⟩, ?_⟩
  · rw [tgtFieldFvs, hctor, hcrest, htRP, hop']; rfl
  · rw [tgtCbody, hctor, hcrest, htRP, hop']; rfl
  · rw [hgx]
    show x ∈ R.ctors.getD cls []
    rw [hctorsCls]; exact List.mem_of_getElem? hx

/-- **`GenPreHyps.nF`**: the generator's constructor has the declared
field count. -/
theorem genRun_nF (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (acval : Name → (Name → Nat) → AnnotTerm)
    (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      (genCtorAt R.g R.rd c j).nF = (tgtFdomsAV p.toBlockShape out acval envC ψ c j).length := by
  intro c hc j hj
  obtain ⟨cls, cA, fvs, cb, -, -, -, -, -, hnF, -, -, hop, hfv, -, -, -⟩ := genRun_frame hμ R hg hc hj
  rw [hnF, tgtFdomsAV, readOpenedDoms_length_eq, hfv, ConLeche.Verify.openPisAtFvars_length _ hop]

/-- A reading of a scoped term (or the default reading, where the
reading fails) names no variable at or above its depth. -/
theorem readD_below {env : Env} (m : EnvModel V env) {φ : Name → Nat} {d : Nat} {e : Expr}
    (hd : 0 < d) (he : ConLeche.ScB d e) :
    Term.bvarsBelow d ((denoteMeta m.acval env φ d e).getD default).erase := by
  cases h : denoteMeta m.acval env φ d e with
  | some a => exact IsReadingAt.below ⟨e, he, h⟩
  | none =>
    show Term.bvarsBelow d (AnnotTerm.bvar 0).erase
    simp only [AnnotTerm.erase, Term.bvarsBelow]
    exact hd

/-- The readings of an opened telescope's domains are bounded at their
depths. -/
theorem readOpenedDoms_below {env : Env} (m : EnvModel V env) {φ : Name → Nat} :
    ∀ {d : Nat} {xs : List Expr}, 0 < d →
      (∀ (k : Nat) (x : Expr), xs[k]? = some x → ConLeche.ScB (d + k) x.fvarTypeD) →
      FieldsBelow d (readOpenedDoms m.acval env φ d xs)
  | _, [], _, _ => trivial
  | d, x :: xs, hd, h => by
    refine ⟨readD_below m hd (by simpa using h 0 x rfl), ?_⟩
    exact readOpenedDoms_below m (by omega) fun k y hy => by
      have := h (k + 1) y (by simpa using hy)
      rwa [show d + (k + 1) = d + 1 + k by omega] at this

set_option maxHeartbeats 800000 in
/-- **`GenPreHyps.below`**: the generated `ih` data (read raw) are bounded
at the rule frame's depth. -/
theorem genRun_below (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (bit : Nat) (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC R.g R.rd bit ψ c j,
        IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsAV p.toBlockShape out mpC.base2.acval envC ψ c j).length) q := by
  intro c hc j hj q hq
  obtain ⟨cls, cA, fvs, cb, -, -, -, -, -, hnF, -, -, hop, -, -, ⟨ws, hws⟩, hxmem⟩ :=
    genRun_frame hμ R hg hc hj
  rw [genRun_gpre hμ R hg h mpC ψ c hc |>.symm, ← genRun_nF hμ R hg mpC.base2.acval ψ c hc j hj]
  generalize hx : genCtorAt R.g R.rd c j = x at hnF hop hws hxmem
  have hpl := genRun_pre_length R hg
  obtain ⟨s, -, hsl⟩ := genRun_motive R hc
  have hD0 : 0 < R.g.pre.length + x.nF := by
    show 0 < R.pre.length + x.nF
    omega
  have hopx : ConLeche.openPisAtFvars x.nF x.tyD R.g.pre.length = some (fvs, cb) := by
    rw [hnF]; exact hop
  unfold genIhdAV at hq
  rw [hx] at hq
  simp only [hopx, Option.map_some, Option.getD_some, hws] at hq
  obtain ⟨⟨i, t, tele⟩, hr, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hi, -⟩ := ConLeche.ClassGen.recs_mem hr
  -- the opened fields, scoped
  have htyD : ConLeche.ScB R.g.pre.length x.tyD :=
    (hg.tyD cls x hxmem).mono (by show p.nP ≤ R.pre.length; omega)
  obtain ⟨hfl, hfvs, -⟩ := ConLeche.ScB.openPis hopx htyD
  have hfvsD : ∀ a ∈ fvs, ConLeche.ScB (R.g.pre.length + x.nF) a := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
    rw [hxe]
    exact ConLeche.ScB.fvar (by omega) hty
  have htyN : ConLeche.ScB (R.g.pre.length + x.nF) x.tyN :=
    (hg.tyN cls x hxmem).mono (by show p.nP ≤ R.pre.length + x.nF; omega)
  have hw : ConLeche.ScB (R.g.pre.length + x.nF) (ws.getD i default) :=
    ConLeche.ScB.targetPiDomsWith_getD hws htyN hfvsD (by omega)
  have hfi : ConLeche.ScB (R.g.pre.length + x.nF) (fvs.getD i default) := by
    apply hfvsD
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  cases hip : R.g.ihParts t tele (ws.getD i default) (R.g.pre.length + x.nF) with
  | none =>
    simp only [Option.getD_none]
    refine ⟨trivial, fun e he => ?_⟩
    simp only [List.nil_append, List.map_nil, List.mem_singleton, readOpenedDoms,
      List.length_nil, Nat.add_zero, Expr.mkAppN] at he ⊢
    subst he
    exact readD_below mpC.base2 hD0 hfi
  | some xi =>
    obtain ⟨xs, idx⟩ := xi
    simp only [Option.getD_some]
    obtain ⟨hxl, hxs, hidx⟩ := ConLeche.ClassGen.ihParts_scoped hw (Nat.le_refl _) hip
    refine ⟨?_, fun e he => ?_⟩
    · simp only [List.map_map, Function.comp_def, List.map_id']
      exact readOpenedDoms_below mpC.base2 hD0 fun k y hy => by
        obtain ⟨ty, rfl, hty⟩ := hxs k y hy
        simpa [Expr.fvarTypeD] using hty
    · simp only [List.length_map, readOpenedDoms_length_eq, hxl] at he ⊢
      rcases List.mem_append.mp he with he | he
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
        exact readD_below mpC.base2 (by omega) (hidx a ha)
      · rw [List.mem_singleton] at he
        subst he
        refine readD_below mpC.base2 (by omega) (ConLeche.ScB.mkAppN (hfi.mono (by omega)) ?_)
        intro y hy
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        obtain ⟨ty, hxe, hty⟩ := hxs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]
        exact ConLeche.ScB.fvar (by omega) hty

end Run

end ConLeche.Model
