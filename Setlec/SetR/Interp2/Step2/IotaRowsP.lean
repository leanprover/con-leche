import Setlec.SetR.Interp2.Step2.MajorP
import Setlec.SetR.Interp2.Step2.ReadsP

/-!
# The two ι rows, discharged (task #161, iota tier)

`IotaReadsP` (`Step2/ReadsP.lean`) and `IotaStepP`
(`Step2/WhnfP.lean`), the last two semantic-tier entries of the P
census.

## FINDING — `IotaReadsP`'s supplier is `accepted_reads`, not the walk

The routed leaf says "a recursor's fired right-hand side reads", and
the freeze's recipe was: the law's carried `Ra` (depth-shifted by
closedness) plus `denoteP_mkAppN` over the argument spine's readings.
The recipe is right about the right-hand side and about
`e.getAppArgs.take rP`.  It is **not** right about the other half of
the reduct's spine, `major.getAppArgs.drop cnP`, and the reason is the
batch-8 defect one level out:

`major` is not a subterm of the subject.  In the rescued branches it
is a spine fabricated out of `whnf (infer major₁)`, and reading *that*
needs `InferReadsP`, whose own premise `LeafReadsP` (the batch-8
repair: `inferBody`'s `.fvar` clause returns the leaf's **stored
annotation**, which `denoteP` never looks at) is exactly what
`IotaReadsP` does not carry — it has no `CtxOkP` and no leaf package,
by design, because its consumer `whnfCoreReads_app` has neither.

The row is nevertheless **provable without touching its statement**,
and the supplier is already in the census: the fired reduct's
major-side arguments are each certified by the clause's own
`iotaCerts` run, so each of them was *inferred* — and
`SemTierInputsP.accepted_reads` says exactly that whatever inference
accepts, reads.  `iotaCertsP_infers` extracts the runs;
`accepted_reads` turns them into readings.  So `iota_reads` leaves the
census as the freeze intended, with `accepted_reads` (which stays
regardless) as its supplier rather than the reads walk.

Recorded as a finding because it is the second time a P row's routing
was decided by the leaf-annotation gap, and because it fixes which
census entry the row is charged to.

## `IotaStepP`

`iota_stepR` (`Bridge/Iota.lean`) segment by segment, with two
structural simplifications the P currency buys:

* the law's first conjunct `rP ≤ mI` and its carried `Ra` replace
  v1's `EnvR.rec_params_le` and `EnvR.rec_rhs_denotes`, so **no new
  environment field appears for the row**;
* the law's `xs` is already the recursor's *index* prefix and its last
  argument is already the constructor spine, so v1's
  `take mI ++ [major]` re-splitting of the subject
  (`take_getD_split`, `hsubj`) is done once, syntactically, instead of
  twice at two currencies.

Everything else is v1's walk: `iotaRec_inv`, the subject's spine
decomposition, the major through `whnf`/`litMajorToCtor`/`majorToCtor`
(`Step2/MajorP.lean`), the constructor spine, the level congruence
(`recFireComparands_fst_nil`, currency-free), the `.plain` comparands
(`map_interp2_of_defEqListP`), the `.nested` pins (`defEqListP_get`
plus the `denoteP_openRev` bridge), the index pin
(`teleFitPA_residual`), the two fits (`certs_telePA`), and then the
law.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule inferTypeCore whnf iotaRecP)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## Two extraction lemmas -/

/-- **A certified spine was inferred**, argument by argument — the
form `accepted_reads` consumes. -/
theorem iotaCertsP_infers {d : Nat} :
    ∀ (ty : Expr) (args : List Expr),
      Setlec.iotaCertsP μ env fuel d ty args = .ok true →
      ∀ a ∈ args, ∃ ta, inferTypeCore μ env fuel d a = .ok ta := by
  intro ty args
  induction args generalizing ty with
  | nil => intro _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro hc a ha
    match ty, hc with
    | .bvar _, hc => exact nomatch hc
    | .fvar _ _ _, hc => exact nomatch hc
    | .sort _, hc => exact nomatch hc
    | .const _ _, hc => exact nomatch hc
    | .app _ _, hc => exact nomatch hc
    | .lam _ _ _ _, hc => exact nomatch hc
    | .letE _ _ _ _, hc => exact nomatch hc
    | .lit _, hc => exact nomatch hc
    | .proj _ _ _, hc => exact nomatch hc
    | .forallE n dom body mb, hc =>
      obtain ⟨ta, hta, -, hrest⟩ := Setlec.iotaCerts_step_inv hc
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨ta, hta⟩
      · exact ih _ hrest a ha'

/-- The frame conditions of the whole major chain — `whnf`, then the
literal conversion, then the rescue.  Readings play no part: every
step either preserves the leaf set or produces a closed term. -/
theorem frame_majorChainP {d : Nat} {recName : Name}
    {rules : List RecRule} {a m₀ m₁ mj : Expr}
    (hw : whnf μ env fuel d a = .ok m₀)
    (hlit : Setlec.litMajorToCtorP μ env fuel d m₀ = .ok m₁)
    (hmaj : Setlec.majorToCtorP μ env fuel d recName rules m₁ = .ok mj)
    (hwf : Setlec.EnvWF env)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) :
    Expr.WScoped d mj ∧ mj.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded mj := by
  have hw₀ : Expr.WScoped d m₀ := Setlec.whnf_WScoped hwf fuel hw hwa
  have hb₀ : m₀.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars hwf fuel hw hba
  have hL₀ : Expr.LeavesBounded m₀ := fun l hl =>
    hLa l (Setlec.whnf_fvarLeaves hwf fuel hw l hl)
  obtain ⟨hw₁, hb₁, hL₁⟩ :
      Expr.WScoped d m₁ ∧ m₁.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded m₁ := by
    rcases Setlec.litMajorToCtorP_inv hlit with rfl | ⟨s, rfl, hg, hred⟩
    · match m₀ with
      | .lit (.natVal n) =>
        rw [Setlec.litToCtorIfNat]
        by_cases hg : Setlec.natLitSupported env = true
        · rw [if_pos hg]
          refine ⟨Setlec.natLitToConstructor_WScoped n,
            Setlec.natLitToConstructor_looseBVars n, fun l hl => ?_⟩
          rw [Setlec.natLitToConstructor_fvarLeaves] at hl
          exact nomatch hl
        · rw [if_neg hg]; exact ⟨hw₀, hb₀, hL₀⟩
      | .lit (.strVal _) | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _
      | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
      | .proj _ _ _ => exact ⟨hw₀, hb₀, hL₀⟩
    · have hwc : Expr.WScoped d (Setlec.strLitToConstructor s) :=
        Setlec.strLitToConstructor_WScoped s d
      have hbc : (Setlec.strLitToConstructor s).looseBVarsBounded 0 = true :=
        Setlec.strLitToConstructor_looseBVars s 0
      have hLc : Expr.LeavesBounded (Setlec.strLitToConstructor s) :=
        fun l hl => by
          rw [Setlec.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
      exact ⟨Setlec.whnf_WScoped hwf fuel hred hwc,
        Setlec.whnf_looseBVars hwf fuel hred hbc,
        fun l hl => hLc l (Setlec.whnf_fvarLeaves hwf fuel hred l hl)⟩
  rcases Setlec.majorToCtor_inv hmaj with rfl | ⟨hwsB, hbB, hleafB, -⟩
  · exact ⟨hw₁, hb₁, hL₁⟩
  · exact ⟨Expr.WScoped.of_wscopedB hwsB, hbB, fun l hl =>
      hL₁ l (by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)⟩

/-! ## The recursor's right-hand side, read at the ambient depth -/

/-- The fired rule's right-hand side reads at every depth, from the
law's carried reading at depth `0` and the rule's own closedness
(`EnvWF`'s recursor clause). -/
theorem recRhsP_depth {m : EnvS2Core V env}
    (hrec : RecRulesP m φ) {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) (hfire : RecRule.fire rl ≠ .inert)
    {us : List Level} (hlen : us.length = cv.levelParams.length) :
    ∃ Ra : AVExpr,
      (∀ d : Nat, denoteP m.acval env φ d
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra) ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ Ra) ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).hasFvar = false ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).looseBVarsBounded 0 = true := by
  obtain ⟨-, hlaw⟩ := hrec n cv mI rP rules hf rl hmem hfire
  obtain ⟨Ra, hRa, hokRa, -⟩ := hlaw us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    m.base.wf _ (Setlec.SetR.Env.find?_mem hf)
  obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP rules rfl rl hmem
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hRnf
  have hbd : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
  exact ⟨Ra, denoteP_depth_of_closed m.acval_closed hnf
      (fun k => denoteP_closed m.acval_erase m.base.cval_closed hnf hbd hRa 1 k)
      hRa,
    hokRa, hnf, hbd⟩

/-! ## `IotaReadsP` -/

/-- **`IotaReadsP`, discharged** (see the module docstring's finding
for why `accepted_reads` is the supplier).  The reduct is the fired
right-hand side applied to a prefix of the subject's own arguments and
a suffix of the rescued major's; the first spine reads because the
subject does, the second because the clause's `iotaCerts` run inferred
every one of its members. -/
theorem iotaReadsP_of {m : EnvS2Core V env} (hrec : RecRulesP m φ)
    (hacc : ∀ {F d' : Nat} {x t : Expr},
      inferTypeCore μ env F d' x = .ok t →
      Expr.WScoped d' x → x.looseBVarsBounded 0 = true →
      Expr.LeavesBounded x →
      ∃ xa, denoteP m.acval env φ d' x = some xa) :
    IotaReadsP μ m φ fuel := by
  intro d e e'' ea h hws hb hLb hea
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj, cnP,
    cnF, r, cbinders, cbody, residual, cr, usr, hfn, hfrec, hlenA, hlenU,
    hwmaj, hlitmaj, hmajc, hfnmaj, hfcj, hrfind, hlenM, hstripR, hstripC,
    hfire, hlev, hdefP, hcertR, hcertC, hstripEq, hpres, hcbody, hdefI,
    rfl⟩ := Setlec.iotaRec_inv h
  -- the subject's own spine
  have hfrE : ∀ x ∈ e.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := fun x hx =>
    ⟨hws.getAppArgs x hx, Setlec.looseBVarsBounded_getAppArgs hb x hx,
      fun l hl => hLb l (Setlec.fvarLeaves_getAppArgs hx l hl)⟩
  have heaSave := hea
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (Setlec.Expr.mkAppN_getApp e).symm, hfn] at hea
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denoteP_mkAppN_inv hea
  -- the major's frames, through the whole chain
  have hmIlt : mI < e.getAppArgs.length := by rw [hlenA]; omega
  obtain ⟨hwMa, hbMa, hLMa⟩ := hfrE _ (Setlec.getD_mem hmIlt)
  obtain ⟨hwm, hbm, hLm⟩ :=
    frame_majorChainP hwmaj hlitmaj hmajc m.base.wf hwMa hbMa hLMa
  have hfrM : ∀ x ∈ major.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := fun x hx =>
    ⟨hwm.getAppArgs x hx, Setlec.looseBVarsBounded_getAppArgs hbm x hx,
      fun l hl => hLm l (Setlec.fvarLeaves_getAppArgs hx l hl)⟩
  -- the major's arguments read, because the certificate inferred them
  have hspy : ∃ ys, DenoteSpineP m.acval env φ d major.getAppArgs ys := by
    have hall : ∀ x ∈ major.getAppArgs,
        ∃ xa, denoteP m.acval env φ d x = some xa := by
      intro x hx
      obtain ⟨tx, htx⟩ := iotaCertsP_infers _ _ hcertC x hx
      obtain ⟨hwx, hbx, hLx⟩ := hfrM x hx
      exact hacc htx hwx hbx hLx
    clear hcertC
    revert hall
    generalize major.getAppArgs = args
    intro hall
    induction args with
    | nil => exact ⟨[], .nil⟩
    | cons x xs ih =>
      obtain ⟨xa, hxa⟩ := hall x List.mem_cons_self
      obtain ⟨ys, hys⟩ := ih (fun y hy => hall y (List.mem_cons_of_mem x hy))
      exact ⟨xa :: ys, .cons hxa hys⟩
  obtain ⟨ys, hspy⟩ := hspy
  -- the right-hand side reads at the ambient depth
  obtain ⟨Ra, hRa, -, hRnf, hRbd⟩ :=
    recRhsP_depth hrec hfrec (List.mem_of_find?_eq_some hrfind) hfire hlenU
  -- the reduct
  have hspOut : DenoteSpineP m.acval env φ d
      (e.getAppArgs.take rP ++ major.getAppArgs.drop (RecRule.ctorParams r))
      (xs.take rP ++ ys.drop (RecRule.ctorParams r)) :=
    (hspx.take rP).append (hspy.drop (RecRule.ctorParams r))
  refine ⟨_, denoteP_mkAppN hspOut (hRa d), ?_, ?_, ?_⟩
  · exact Expr.WScoped.mkAppN (Expr.WScoped.of_not_hasFvar hRnf)
      (fun y hy => by
        rcases List.mem_append.mp hy with hy' | hy'
        · exact (hfrE y (List.mem_of_mem_take hy')).1
        · exact (hfrM y (List.mem_of_mem_drop hy')).1)
  · exact Setlec.looseBVarsBounded_mkAppN hRbd (fun y hy => by
      rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.1
      · exact (hfrM y (List.mem_of_mem_drop hy')).2.1)
  · intro l hl
    rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
    · exact absurd hl' (by
        rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf]; simp)
    · rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.2 l hly
      · exact (hfrM y (List.mem_of_mem_drop hy')).2.2 l hly

end Setlec.SetR.Interp2
