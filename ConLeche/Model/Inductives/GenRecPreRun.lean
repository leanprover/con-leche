module

public import ConLeche.Model.Inductives.GenRecPre
public import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecData

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

end Run

end ConLeche.Model
