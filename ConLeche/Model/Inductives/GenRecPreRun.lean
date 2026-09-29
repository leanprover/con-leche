module

public import ConLeche.Model.Inductives.GenRecPre
public import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.TargetGraph
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions

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
  have hrP := (genRecTy_shape R hg T).1
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
    ∃ key M₀ nfs, R.Ms[i]? = some { M₀ with nfs := nfs } ∧ R.Ms₀[i]? = some M₀ ∧
      Nonempty (ConLeche.ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params key M₀) := by
  obtain ⟨hlN, hallN⟩ := ConLeche.classesNfs_run R.hMs
  obtain ⟨hlM, hallM⟩ := ConLeche.classMajors_run R.hMs₀
  have hi0 : i < R.Ms₀.length := by omega
  have hik : i < (R.rd.classes.map (ConLeche.classKeyCanon R.ctx.params)).length := by omega
  obtain ⟨M, hM, hrun⟩ := hallM i _ (List.getElem?_eq_getElem hik)
  obtain ⟨nfs, hMs, -⟩ := hallN i M hM
  exact ⟨_, M, nfs, hMs, hM, hrun⟩

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
  obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi
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
theorem genRun_frame (_hμ : μ.verifiedChecks = true)
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
  have hrP : rc.rP = R.pre.length := (genRecTy_shape R hg T).1
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

/-- **The declared field domains are bounded** at the rule frame (read
off the scoped declared type). -/
theorem genRun_fdomsBelow (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      FieldsBelow (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).length
        (tgtFdomsAV p.toBlockShape out mpC.base2.acval envC ψ c j) := by
  intro c hc j hj
  obtain ⟨cls, cA, fvs, cb, -, -, -, -, -, -, -, hRP, hop, hfv, -, -, hxmem⟩ :=
    genRun_frame hμ R hg hc hj
  rw [← genRun_gpre hμ R hg h mpC ψ c hc, tgtFdomsAV, hRP, hfv]
  obtain ⟨s, -, hsl⟩ := genRun_motive R hc
  have hpl := genRun_pre_length R hg
  have htyD : ConLeche.ScB R.pre.length (genCtorAt R.g R.rd c j).tyD :=
    (hg.tyD cls _ hxmem).mono (by show p.nP ≤ R.pre.length; omega)
  obtain ⟨-, hfvs, -⟩ := ConLeche.ScB.openPis hop htyD
  exact readOpenedDoms_below mpC.base2 (by show 0 < R.pre.length; omega) fun k y hy => by
    obtain ⟨ty, rfl, hty⟩ := hfvs k y hy
    show ConLeche.ScB (R.pre.length + k) ty
    exact hty

/-! ## The stored conclusion is the motive applied -/

/-- **The stored type of recursor `c`**: the generated type of its class,
stored as generated (`classConstOk`); its reading and its peel at the
major index. -/
theorem genRun_storedTy (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ (cls : Nat) (gty : Expr) (S : Expr),
      genClsOf R.rd c = cls ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      ConLeche.classGenRecTy R.g cls = some gty ∧
      ConLeche.inferTypeCore μ envC F 0 gty = .ok S ∧
      denoteMeta mpC.base2.acval envC ψ 0 gty
        = some (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) ∧
      p.toBlockShape.majorIdxAt c + 1 = R.g.pre.length + (R.g.cls.getD cls default).nIdx + 1 ∧
      p.toBlockShape.rulePrefixAt c = R.g.pre.length ∧
      stripPisAV (R.g.pre.length + (R.g.cls.getD cls default).nIdx + 1)
          (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)
        = some (blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c,
            blockRecConclAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c) := by
  obtain ⟨rc, cls, cvG, rhss, hrc, hcls, -, ⟨T⟩, ho, hM, hgc⟩ := genRun_at R hc
  have hr : (tgtRs out)[c]? = some (cvG, rhss, (R.Ms.getD cls default).nIdx,
      (R.Ms.getD cls default).ctors) := by
    simp [tgtRs, List.getElem?_map, ho]
  obtain ⟨-, -, -, -, -, -, -, -, S, -, hinf, -, hcvEq⟩ := ConLeche.classConstOk_inv T.hcv
  have htype : cvG.type = T.gty := by
    have := congrArg ConstantVal.type hcvEq
    simpa using this
  dsimp only at hinf
  obtain ⟨-, -, -, hta, hTyE, hlenRds, -, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  replace hta : denoteMeta mpC.base2.acval envC ψ 0 T.gty
      = some (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) := by rw [← htype]; exact hta
  have hrP := (genRecTy_shape R hg T).1
  have hRP : p.toBlockShape.rulePrefixAt c = R.g.pre.length := by
    show (p.recs.getD c default).rP = _
    rw [List.getD_eq_getElem?_getD, hrc, Option.getD_some, hrP]; rfl
  have hmI : p.toBlockShape.majorIdxAt c + 1
      = R.g.pre.length + (R.g.cls.getD cls default).nIdx + 1 := by
    rw [genRec_mI h hr, hRP]; rfl
  refine ⟨cls, T.gty, S, hgc, hM, T.hgty, hinf, hta, hmI, hRP, ?_⟩
  rw [← hmI, hTyE, ← hlenRds]
  exact stripPisAV_mkPisAV _ _

/-- **`GenPreHyps.conclMot`**: the stored conclusion of recursor `c`, at a
spine of the prefix, an index spine and a major, is the class's motive
variable applied to the index spine and the major (`classGenRecTy_concl`
at the stored type). -/
theorem genRun_conclMot (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ (xs zs : List V) (x : V),
      xs.length = p.toBlockShape.rulePrefixAt c → zs.length = (tgtMajor out c).nIdx →
      interp V (consList (xs ++ (zs ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (classMotPos R.g (genClsOf R.rd c)) pt) := by
  intro c hc xs zs x hxl hzl
  obtain ⟨cls, gty, S, hgc, hM, hgty, -, hread, -, hRP, hst⟩ :=
    genRun_storedTy hμ R hg h mpC ψ hc
  obtain ⟨-, cls', -, -, -, hcls, -, -, -, -, hgc'⟩ := genRun_at R hc
  have hcc : cls' = cls := hgc'.symm.trans hgc
  rw [hcc] at hcls
  obtain ⟨s, hm0⟩ := ConLeche.classRead_recCls_motive R.hrd cls (List.mem_of_getElem? hcls)
  have hm : ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ cls = some s := hm0
  have := classGenRecTy_concl (V := V) (acval := mpC.base2.acval) (env := envC)
    (φ := ψ) hg hm hgty hread hst ρ xs zs x (by rw [hxl, hRP]) (by rw [hzl, hM])
  rw [this, classMotPos, hgc, hm]
  rfl

/-- The motive slots are as many as the classes. -/
theorem motiveSlot_lt_classes : ∀ (slots : List ConLeche.ClassSlot) (rc : List Nat) (c s : Nat),
    ConLeche.ClassRead.motiveSlot ⟨slots, rc⟩ c = some s →
      c < (ConLeche.ClassRead.classes ⟨slots, rc⟩).length
  | [], _, c, s, h => by
    simp [ConLeche.ClassRead.motiveSlot] at h
  | a :: l, rc, c, s, h => by
    unfold ConLeche.ClassRead.motiveSlot at h
    unfold ConLeche.ClassRead.classes
    simp only [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.getElem?_cons_zero] at h
    cases a with
    | motive k =>
      simp only [List.filterMap_cons, List.length_cons, if_true] at h ⊢
      cases c with
      | zero => omega
      | succ c =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at h
        obtain ⟨s', hs', -⟩ := h
        have := motiveSlot_lt_classes l rc c s' (by
          unfold ConLeche.ClassRead.motiveSlot
          simpa [Function.comp_def] using hs')
        unfold ConLeche.ClassRead.classes at this
        simpa using this
    | minor c' C ihs =>
      simp only [List.filterMap_cons] at h ⊢
      simp only [Bool.false_eq_true, if_false, List.getElem?_map, Option.map_eq_some_iff] at h
      obtain ⟨s', hs', -⟩ := h
      have := motiveSlot_lt_classes l rc c s' (by
        unfold ConLeche.ClassRead.motiveSlot
        simpa [Function.comp_def] using hs')
      unfold ConLeche.ClassRead.classes at this
      simpa using this

/-- A recursor's class is one of the run's classes. -/
theorem genRun_cls_lt
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) : genClsOf R.rd c < R.Ms.length := by
  obtain ⟨-, cls, -, -, -, hcls, -, -, -, -, hgc⟩ := genRun_at R hc
  obtain ⟨s, hs⟩ := ConLeche.classRead_recCls_motive R.hrd cls (List.mem_of_getElem? hcls)
  obtain ⟨hlN, -⟩ := ConLeche.classesNfs_run R.hMs
  obtain ⟨hlM, -⟩ := ConLeche.classMajors_run R.hMs₀
  rw [hgc, hlN, hlM, List.length_map]
  exact motiveSlot_lt_classes R.rd.slots [] cls s hs

/-- **An outside class's sort is the block's** at every level assignment
(`TargetMajorRun.outside`'s `isEquiv sI resSort`, read through the
recorded former). -/
theorem genRun_outW (mpC : EnvModelM V μ envC)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) (hMo : (tgtMajor out c).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out c) D mm cvI) (ψ : Name → Nat) :
    D.w (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
      = Level.eval ψ p.toBlockShape.resSort ∧
    R.Ms₀.any (·.member.isNone) = true := by
  obtain ⟨-, cls, -, -, -, -, -, -, -, hM, hgc⟩ := genRun_at R hc
  rw [hM] at hMo hcl ⊢
  have hi : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hc
  obtain ⟨key, M₀, nfs, hMs, hMs₀, ⟨CR⟩⟩ := genRun_class R hi
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  rw [hget] at hMo hcl ⊢
  have hmaj := CR.major
  cases hmaj with
  | member => exact nomatch hMo
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hdsLen hdsSc hment hinst hsort nfs' =>
    refine ⟨?_, List.any_eq_true.mpr ⟨_, List.mem_of_getElem? hMs₀, rfl⟩⟩
    obtain ⟨cvI', caps', ty, s, hf', hty, hs, hr'⟩ := targetOutsideInst_inv hinst
    obtain ⟨caps, hfI⟩ := hcl.hfind
    rw [mkFEnv_find?] at hf'
    change envC.find? I = _ at hfI
    rw [hfI] at hf'
    obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
    obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
    obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
    rw [hcl.hmem] at hf₂
    change envC.find? I = _ at hf₂
    rw [hfI] at hf₂
    obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
    obtain ⟨ab, hta, -, -⟩ := hab (Level.substFn ψ cvI.levelParams us)
    have hsI : s = sI := (congrArg Prod.snd hr').symm
    subst hsI
    show D.w (Level.substFn ψ cvI.levelParams us) = _
    rw [instPis_sort_of_read (φ := ψ) cvI.levelParams us hta hty hs]
    exact ConLeche.Level.isEquiv_sound hsort ψ

set_option maxHeartbeats 2000000 in
/-- **`GenPreSem.lic`, from the run**: under a nonzero elimination level a
class of sort zero is the block's one member (the elimination guard,
`blockLargeElim_counting`: an outside class would force a never-zero sort,
`genRun_outW`), with at most one constructor of the declared large shape,
whose fields are a function of the index (`blockStoredFit_srcVals_zero`). -/
theorem genRun_lic (mpC : EnvModelM V μ envC)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hN : BlockNamesOk (V := V) (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf)
      p.lps cvTas p.toBlockShape isRec A envI p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf)
      p.lps cvTas p.toBlockShape isRec A (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).toLfp ∈ mpC.lfpBlocks)
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))))
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (ψ : Name → Nat) (ρ : Nat → V) :
    Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
    ∀ xs, ∀ c, c < (tgtRs out).length →
    (tgtClsD (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) Dc out c).w
      (tgtClsψ cvc out ψ c) = 0 →
    ∀ t, t ∈ˢ tgtClsIs (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) Dc mc cvc
      mpC.base2.acval envC p.toBlockShape out ψ ρ xs c →
    ∀ j fs j' fs',
    tgtClsFit (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) Dc mc cvc mpC.base2.acval envC
      p.toBlockShape out ψ ρ xs c t j fs →
    tgtClsFit (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) Dc mc cvc mpC.base2.acval envC
      p.toBlockShape out ψ ρ xs c t j' fs' →
    j = j' ∧ fs = fs' := by
  intro hℓ xs c hc hw t ht j fs j' fs' hf hf'
  have hL : p.toBlockShape.large = true := by
    cases hl : p.toBlockShape.large with
    | true => rfl
    | false =>
      exfalso; apply hℓ
      simp [ConLeche.structElimLevel, hl, Level.eval]
  have hallow : ConLeche.blockLargeElimAllowed p.toBlockShape
      (nestedBit || R.Ms₀.any (·.member.isNone)) = true := by
    have he := R.helim
    rw [hL] at he
    simpa using he
  cases hmb : (tgtMajor out c).member with
  | none =>
    exfalso
    have hcl := hcls c hc hmb
    obtain ⟨hwE, hany⟩ := genRun_outW mpC R hc hmb hcl ψ
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    simp only [tgtClsD, tgtClsψ, hm, Bool.false_eq_true, if_false] at hw
    rw [hwE] at hw
    obtain ⟨-, -, hnest, -⟩ := blockLargeElim_counting hallow hw
    rw [hany] at hnest
    simp at hnest
  | some tm =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    simp only [tgtClsD, tgtClsψ, hm, if_true] at hw
    have hw' : Level.eval ψ p.toBlockShape.resSort = 0 := hw
    obtain ⟨hlarge, hk1, -, hnc⟩ := blockLargeElim_counting hallow hw'
    have htm : p.toBlockShape.recTgtAt c = tm := genRun_recTgt R hc hmb
    obtain ⟨-, cls, -, -, -, -, -, -, -, hM, -⟩ := genRun_at R hc
    rw [hM] at hmb
    obtain ⟨-, -, -, htk⟩ := genRun_member R hmb
    have htm0 : tm = 0 := by
      have : p.toBlockShape.k = 1 := hk1
      omega
    rw [tgtClsIs_mem hm] at ht
    rw [tgtClsFit_mem hm] at hf hf'
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits ht
    have htD := ht
    rw [blockRecIs_pos hpar hpref] at htD
    have hModel := blockModelAt_seam h hN hS hcore hlfp
    have hmr := blockMembersRun_seam hN hS hcore
    have hk0 : 0 < (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).k := by
      show 0 < p.toBlockShape.k; omega
    have hmN : p.toBlockShape.recTgtAt c
        < (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).N := by
      rw [htm, htm0]; show 0 < p.toBlockShape.k + 0; omega
    have hsf := (blockHoleFitRel_iff hModel hpar hmN htD).mp hf
    have hsf' := (blockHoleFitRel_iff hModel hpar hmN htD).mp hf'
    unfold blockStoredFitRel at hsf hsf'
    rw [htm, htm0] at hsf hsf' htD
    -- one constructor at most
    have hlen0 : ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM 0).length ≤ 1 := by
      have hm0 : ∃ ms, p.members[0]? = some ms := ⟨_, List.getElem?_eq_getElem (by
        show 0 < p.members.length; exact hk0)⟩
      obtain ⟨ms, hms⟩ := hm0
      have hc0 := congrArg (fun L => (L[0]?).map List.length) hnames
      simp only [List.getElem?_map, hms, Option.map_some, List.length_map] at hc0
      have hnc' : ms.ctors.length ≤ p.toBlockShape.numCtors := by
        show ms.ctors.length ≤ ConLeche.numCtorsOf p.members
        cases hmem : p.members with
        | nil => rw [hmem] at hms; exact nomatch hms
        | cons m0 rest =>
          rw [hmem] at hms
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hms
          subst hms
          simp only [ConLeche.numCtorsOf]; omega
      show (ctorsAs.getD 0 []).length ≤ 1
      cases hca : ctorsAs[0]? with
      | none => rw [List.getD_eq_getElem?_getD, hca]; simp
      | some L =>
        rw [hca] at hc0
        simp only [Option.map_some, Option.some.injEq, List.length_map] at hc0
        rw [List.getD_eq_getElem?_getD, hca, Option.getD_some, hc0]
        omega
    have hj0 : j = 0 := by have := hsf.1; omega
    have hj'0 : j' = 0 := by have := hsf'.1; omega
    subst hj0 hj'0
    refine ⟨rfl, ?_⟩
    obtain ⟨cA, hcj⟩ : ∃ cA,
        ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM 0)[0]? = some cA :=
      ⟨_, List.getElem?_eq_getElem hsf.1⟩
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 0 hk0 0 cA hcj
    obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 0 0 cA hcj
    have hsrc : ∀ gs : List V,
        (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).StoredFit ψ
          (consList (xs.take (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).nP) ρ)
          t 0 0 gs →
        gs = srcVals (isOfW ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).uM
            0 ψ) ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).nIdxAt 0) t)
          (srcList (((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).Ess
            0 ψ).getD 0 [])
            (((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).Fss
              0 ψ).getD 0 []).length) := fun gs hgs =>
      blockStoredFit_srcVals_zero hModel hcj ⟨hfindC, hlpsC, hcd⟩ hlarge hw
        (fun σ => ⟨fun hσ => ((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mp
            (hS.paramsOf 0 hk0 ψ σ hσ 0 hk0),
          fun hσ => hS.paramsOf 0 hk0 ψ σ (((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
        (blockMembers_IdsM_length hmr hk0 ψ) hpar
        (Nat.lt_of_lt_of_le hk0 (Nat.le_add_right _ _)) htD hgs
    rw [hsrc fs hsf, hsrc fs' hsf']

end Run

/-! ## `GenPreHyps` from the run and the class-side facts -/

section Hyps

variable {F : Nat} {envI envC : Env} {pp : BlockParts} {nestedBit : Bool} {posR : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

variable (pp out mpC d Dc mc cvc) in
/-- **The class-side facts `GenPreHyps` still asks** once the run's fields
are discharged: the class split both ways, the decoding both ways, the
elimination licence, the generated `ih` calls' typing, the minor
premise's typing at the rule frame, and the class induction. -/
structure GenPreSem (g : ClassGen) (rd : ClassRead) (ψ : Name → Nat) (ρ : Nat → V) : Prop where
  split : GenClsSplit pp out mpC d Dc mc cvc ψ ρ
  back : GenClsBack pp out mpC d Dc mc cvc ψ ρ
  dec : GenClsDec pp out mpC d Dc mc cvc ψ ρ
  decInv : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ
  callTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
    ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
      q.1 < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt q.1 ∧
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1).map
          (·.2.2))
        (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]))
  minor : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
    ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs →
    ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j).length →
    (∀ (l : Nat) (q : IhDatum) (hv : V),
      (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)[l]? = some q → hs[l]? = some hv →
      hv ∈ˢ interp V (consList (xs ++ fs) ρ)
        (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (classMotPos g (genClsOf rd q.1)) q)) →
    (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + genMinorSlot g rd c j) pt)
      ∈ˢ ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ))
          ++ [interp V (consList (xs ++ fs) ρ)
            (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
          (xs.getD (classMotPos g (genClsOf rd c)) pt)
  ind : GenClassInd mpC.base2.acval envC pp.toBlockShape out d Dc mc cvc
    (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j) ψ ρ

/-- **`GenPreHyps` from the generated stage's run** and the class-side facts
(`GenPreSem`): the run discharges the prefix, the positions, the callees,
the `ih` data's bounds, the field counts, the index counts, the classes'
clauses and components, the stored conclusion, and the elimination
licence (`genRun_lic`). -/
theorem genPreHyps_of_run (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nestedBit posR cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hd : d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI' : Env}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI' pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))))
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (ψ : Name → Nat) (ρ : Nat → V) (S : GenPreSem pp out mpC d Dc mc cvc R.g R.rd ψ ρ) :
    GenPreHyps pp out mpC d Dc mc cvc R.g R.rd ψ ρ where
  split := S.split
  back := S.back
  dec := S.dec
  decInv := S.decInv
  nIdx := genRun_nIdx R hd
  din := genRun_din mpC hlfp hcls
  mN := genRun_mN mpC R hd hcls
  lic := by
    subst hd
    exact genRun_lic mpC R h hN hS hcore hlfp hnames hcls ψ ρ
  gpre := genRun_gpre hμ R hg h mpC ψ
  nF := genRun_nF hμ R hg mpC.base2.acval ψ
  mot := genRun_mot hμ R hg h mpC
  min := genRun_min hμ R hg h mpC
  cal := genRun_cal R mpC.base2.acval envC (genBit pp ψ) ψ
  below := genRun_below hμ R hg h mpC (genBit pp ψ) ψ
  callTy := S.callTy
  conclMot := genRun_conclMot hμ R hg h mpC ψ ρ
  minor := S.minor
  ind := S.ind

set_option maxHeartbeats 4000000 in
/-- **THE SKELETON'S `hpre`, FROM THE GENERATED RUN** — the family
premise at every level assignment and base frame, from the run, the
stage record, the family's level (`hTy`, `blockRecLevel_run`), the block
context, and the class-side facts still open: `GenPreSem` (the class
split and decoding both ways, the generated calls' typing, the minor
premise's typing at the rule frame, the class induction), the rule
frame's grading (`hframe`), the declared index expressions' and
constructor application's grading (`hargs`), and the generated `ih`
terms' and residue's grading at typed tuples (`hrhs`). -/
theorem genRecPre_run (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nestedBit posR cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {s : (Name → Nat) → Nat}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (tgtRs out).length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) ∈ˢ univ (s ψ) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c))
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hd : d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI' : Env}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI' pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))))
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsem : ∀ (ψ : Name → Nat) (ρ : Nat → V), GenPreSem pp out mpC d Dc mc cvc R.g R.rd ψ ρ)
    (hframe : ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenoted V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default))
    (hargs : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
        WellDenotedV V (consList ys ρ) e) ∧
      WellDenotedV V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (hrhs : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ c j,
        WellDenotedV V (consList ys (consList rs ρ)) v) ∧
      WellDenotedV V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd
          (genBit pp ψ) ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV R.g R.rd c j)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V (s ψ) (tgtRs out).length (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd) ψ)
        ρ :=
  genRecPre hμ h hTy
    (fun ψ ρ rs hl ht => genRecEqs_wd hμ h ψ ρ (hsem ψ ρ).back (hsem ψ ρ).dec
      (genRun_fdomsBelow hμ R hg h mpC ψ) (hframe ψ) (hargs ψ ρ) (hrhs ψ ρ) rs hl ht)
    (fun ψ ρ => genPreHyps_of_run hμ R hg h hd hlfp hN hS hcore hnames hcls ψ ρ (hsem ψ ρ))

end Hyps

end ConLeche.Model
