import ConLeche.Model.Steps.Major
import ConLeche.Model.Steps.IotaGate
import ConLeche.Model.Steps.Reads
import ConLeche.Semantics.DefEqList

/-!
# The two ι rows, discharged (task #161, iota tier)

`IotaReads` (`Steps/Reads.lean`) and `IotaStep`
(`Steps/Whnf.lean`), the last two semantic-tier entries of the P
census.

## FINDING — `IotaReads`'s supplier is `accepted_reads`, not the walk

The routed leaf says "a recursor's fired right-hand side reads", and
the freeze's recipe was: the law's carried `Ra` (depth-shifted by
closedness) plus `denoteMeta_mkAppN` over the argument spine's readings.
The recipe is right about the right-hand side and about
`e.getAppArgs.take rP`.  It is **not** right about the other half of
the reduct's spine, `major.getAppArgs.drop cnP`, and the reason is the
batch-8 defect one level out:

`major` is not a subterm of the subject.  In the rescued branches it
is a spine fabricated out of `whnf (infer major₁)`, and reading *that*
needs `InferReads`, whose own premise `LeafReads` (the batch-8
repair: `inferBody`'s `.fvar` clause returns the leaf's **stored
annotation**, which `denoteMeta` never looks at) is exactly what
`IotaReads` does not carry — it has no `CtxOk` and no leaf package,
by design, because its consumer `whnfCoreReads_app` has neither.

The row is nevertheless **provable without touching its statement**,
and the supplier is already in the census: the fired reduct's
major-side arguments are each certified by the clause's own
`iotaCerts` run, so each of them was *inferred* — and
`SemTierInputsP.accepted_reads` says exactly that whatever inference
accepts, reads.  (`iotaCertsP_infers` extracted the runs until the ι
batch, 2026-09-05, licensed the fire-time walks: a licensed slot runs
no inference, so the extraction is gone; B4 had already made the reads
row independent of the certificate.)  `accepted_reads` turns runs into
readings.  So `iota_reads` leaves the
census as the freeze intended, with `accepted_reads` (which stays
regardless) as its supplier rather than the reads walk.

Recorded as a finding because it is the second time a P row's routing
was decided by the leaf-annotation gap, and because it fixes which
census entry the row is charged to.

## `IotaStep`

`iota_stepR` (`Bridge/Iota.lean`) segment by segment, with two
structural simplifications the P currency buys:

* the law's first conjunct `rP ≤ mI` and its carried `Ra` replace
  v1's `EnvFacts.rec_params_le` and `EnvFacts.rec_rhs_denotes`, so **no new
  environment field appears for the row**;
* the law's `xs` is already the recursor's *index* prefix and its last
  argument is already the constructor spine, so v1's
  `take mI ++ [major]` re-splitting of the subject
  (`take_getD_split`, `hsubj`) is done once, syntactically, instead of
  twice at two currencies.

Everything else is v1's walk: `iotaRec_inv`, the subject's spine
decomposition, the major through `whnf`/`litMajorToCtor`/`majorToCtor`
(`Steps/Major.lean`), the constructor spine, the level congruence
(`recFireComparands_fst_nil`, currency-free), the `.plain` comparands
(`map_interp_of_defEqListFueled`), the `.nested` pins (`defEqListFueled_get`
plus the `denoteMeta_openRev` bridge), the index pin
(`teleFitPA_residual`), the two fits (`certs_telePA`), and then the
law.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule inferTypeCore whnf iotaRecFueled)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## List helpers at the annotated reading -/

/-- A read spine reads at every slot. -/
theorem DenoteMetaSpine.getD {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ (dflt : Expr) (i : Nat), i < as.length →
      denoteMeta acval env φ d (as.getD i dflt) = some (vs.getD i default) := by
  induction h with
  | nil => intro dflt i hi; exact absurd hi (by simp)
  | @cons a v as vs ha _ ih =>
    intro dflt i hi
    match i with
    | 0 => exact ha
    | j + 1 => exact ih dflt j (by simpa using hi)

/-- Pointwise reading of a map equality at `getD` slots
(`map_interp_getD_eq`'s mirror). -/
theorem map_interp_getD_eq {ρ : Nat → V} {as bs : List AnnotTerm}
    (h : as.map (interp V ρ) = bs.map (interp V ρ))
    {i : Nat} (hi : i < as.length) :
    interp V ρ (as.getD i default) = interp V ρ (bs.getD i default) := by
  have hlen : as.length = bs.length := by
    have := congrArg List.length h
    simpa using this
  have h1 : (as.map (interp V ρ))[i]? = (bs.map (interp V ρ))[i]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)] at h1
  simpa using h1

/-- `getD` through `take`, below the cut. -/
theorem getD_takeA {as : List AnnotTerm} {k i : Nat} (hi : i < k) :
    (as.take k).getD i default = as.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi]

/-- `getD` through `drop`. -/
theorem getD_dropA (as : List AnnotTerm) (k i : Nat) :
    (as.drop k).getD i default = as.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A list of length `k + 1` splits as its prefix plus its last
element. -/
theorem take_getD_splitA {as : List AnnotTerm} {k : Nat}
    (h : as.length = k + 1) :
    as = as.take k ++ [as.getD k default] := by
  have hlen : (as.drop k).length = 1 := by
    rw [List.length_drop, h]; omega
  obtain ⟨a, ha⟩ : ∃ a, as.drop k = [a] := by
    match hd : as.drop k with
    | [a] => exact ⟨a, rfl⟩
    | [] => rw [hd] at hlen; simp at hlen
    | a :: b :: t => rw [hd] at hlen; simp at hlen
  have hget : a = as.getD k default := by
    have h0 : (as.drop k).getD 0 default = a := by rw [ha]; rfl
    rw [getD_dropA, Nat.add_zero] at h0
    exact h0.symm
  calc as = as.take k ++ as.drop k := (List.take_append_drop k as).symm
    _ = as.take k ++ [as.getD k default] := by rw [ha, hget]

/-- The frame conditions of a `∀`-telescope's residual, P currency
(`piResidual_frameR`'s mirror): it is built by instantiating a scoped
type with scoped arguments. -/
theorem piResidual_frame {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      ConLeche.piResidual T args = some rest →
      Expr.WScoped d T → T.looseBVarsBounded 0 = true →
      Expr.LeavesBounded T → CtxOk m φ d Δa T →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
      Expr.WScoped d rest ∧ rest.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded rest ∧ CtxOk m φ d Δa rest := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hw hb hL hCt _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact ⟨hw, hb, hL, hCt⟩
  | cons a as ih =>
    intro rest h hw hb hL hCt hfr
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _ _, h => exact nomatch h
    | .letE _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE ty body mb, h =>
    obtain ⟨hwa, hba, hLa, hCa⟩ := hfr a (by simp)
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ih h (Expr.WScoped.instantiate1_gen hwa 0 hw.2)
      (Expr.looseBVarsBounded_instantiate1_gen hba hb.2) (fun l hl => ?_)
      ⟨hCt.1, fun l hl => ?_⟩ (fun x hx => hfr x (by simp [hx])) <;>
    · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · first
        | exact hL l (by simp [Expr.fvarLeaves, h2])
        | exact hCt.2 l (by simp [Expr.fvarLeaves, h2])
      · first
        | exact hLa l h2
        | exact hCa.2 l h2

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and framed (closed, so the frames are free). -/
theorem constType_pkg {m : EnvModel V env} (hct : ConstType m φ)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hnt : ci.isTowerEntry = false) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : AnnotTerm,
      (∀ d : Nat, denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hnt hlen
  have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hta 1 k)
      hta,
    hok, hmem, hnf, hbd⟩

/-- A `.const` that reads was applied at the stored arity, and its
reading is the leaf.  (The inversion `split at` cannot do in place
without closing the surrounding block.) -/
theorem denoteMeta_const_arity {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {n : Name} {us : List Level} {ci : ConstantInfo}
    {ea : AnnotTerm} (hf : env.find? n = some ci)
    (h : denoteMeta acval env φ d (.const n us) = some ea) :
    us.length = ci.toConstantVal.levelParams.length ∧
      ea = acval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [denoteMeta, hf] at h
  dsimp only at h
  split at h
  · next hlen => exact ⟨hlen, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The major chain's frames -/

/-- The frame conditions of the whole major chain (`prepareMajor`:
`whnf`, the literal conversion and the rescue, in either order — an
instance of `prepareMajorFueled_ind`).  Readings play no part: every step
either preserves the leaf set or produces a closed term. -/
theorem frame_prepareMajorFueled {d : Nat} {recName : Name}
    {rules : List RecRule} {a mj : Expr}
    (h : ConLeche.prepareMajorFueled μ env fuel d recName rules a = .ok mj)
    (hwf : ConLeche.EnvWF env)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) :
    Expr.WScoped d mj ∧ mj.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded mj :=
  ConLeche.prepareMajorFueled_ind h
    (fun x => Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x)
    (fun hw hP => ⟨ConLeche.whnf_WScoped hwf fuel hw hP.1,
      ConLeche.whnf_looseBVars hwf fuel hw hP.2.1,
      fun l hl => hP.2.2 l (ConLeche.whnf_fvarLeaves hwf fuel hw l hl)⟩)
    (fun hlit hP => by
      obtain ⟨hw₀, hb₀, hL₀⟩ := hP
      rcases ConLeche.litMajorToCtorFueled_inv hlit with rfl | ⟨s, rfl, hg, hred⟩
      · exact ⟨ConLeche.litToCtorIfNat_WScoped hw₀,
          ConLeche.litToCtorIfNat_looseBVars hb₀,
          fun l hl => hL₀ l (ConLeche.litToCtorIfNat_fvarLeaves l hl)⟩
      · have hwc : Expr.WScoped d (ConLeche.strLitToConstructor s) :=
          ConLeche.strLitToConstructor_WScoped s d
        have hbc : (ConLeche.strLitToConstructor s).looseBVarsBounded 0 = true :=
          ConLeche.strLitToConstructor_looseBVars s 0
        have hLc : Expr.LeavesBounded (ConLeche.strLitToConstructor s) :=
          fun l hl => by
            rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
        exact ⟨ConLeche.whnf_WScoped hwf fuel hred hwc,
          ConLeche.whnf_looseBVars hwf fuel hred hbc,
          fun l hl => hLc l (ConLeche.whnf_fvarLeaves hwf fuel hred l hl)⟩)
    (fun hmaj hP => by
      obtain ⟨hw₁, hb₁, hL₁⟩ := hP
      rcases ConLeche.majorToCtor_inv hmaj with rfl | ⟨hwsB, hbB, hleafB, -⟩
      · exact ⟨hw₁, hb₁, hL₁⟩
      · exact ⟨Expr.WScoped.of_wscopedB hwsB, hbB, fun l hl =>
          hL₁ l (by
            have := List.all_eq_true.mp hleafB l hl
            simpa using this)⟩)
    ⟨hwa, hba, hLa⟩

/-! ## The recursor's right-hand side, read at the ambient depth -/

/-- The fired rule's right-hand side reads at every depth, from the
law's carried reading at depth `0` and the rule's own closedness
(`EnvWF`'s recursor clause). -/
theorem recRhs_depth {m : EnvModel V env}
    {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) {us : List Level} {Ra : AnnotTerm}
    (hRa0 : denoteMeta m.acval env φ 0
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
      = some Ra) :
    (∀ d : Nat, denoteMeta m.acval env φ d
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra) ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).hasFvar = false ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP rules rfl rl hmem
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hRnf
  have hbd : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hRa0 1 k)
      hRa0,
    hnf, hbd⟩

/-! ## `IotaReads` -/

/-- **`IotaReads`, discharged** (see the module docstring's finding
for why `accepted_reads` is the supplier).  The reduct is the fired
right-hand side applied to a prefix of the subject's own arguments and
a suffix of the rescued major's; the first spine reads because the
subject does, the second because the clause's `iotaCerts` run inferred
every one of its members. -/
theorem iotaReads_of {m : EnvModel V env} (hrec : RecRules m φ)
    (ihw : WhnfReads m μ φ fuel) (ihio : InferReadsIO m μ φ fuel) :
    IotaReads μ m φ fuel := by
  intro d e e'' ea h hws hb hLb hlr hea
  obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj, cvj, cnP,
    cnF, r, hfn, hfrec, hlenA, hlenU,
    hprep, hfnmaj, hfcj, hrfind, hlenM,
    hfire, hlev, hdefP, hcertR, hcertC, hidx,
    rfl⟩ := ConLeche.iotaRec_inv h
  -- the subject's own spine
  have hfrE : ∀ x ∈ e.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := fun x hx =>
    ⟨hws.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hb x hx,
      fun l hl => hLb l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩
  have heaSave := hea
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp e).symm, hfn] at hea
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denoteMeta_mkAppN_inv hea
  -- the major's frames and reading, through the whole chain (either
  -- order: an instance of `prepareMajorFueled_ind`).  Task #172 B4: the
  -- io-graded certificate no longer traverses every argument, so
  -- per-argument readability comes from the subject's own reading,
  -- transported by the reads walk and the fabrication lemma.
  have hmIlt : mI < e.getAppArgs.length := by rw [hlenA]; omega
  obtain ⟨hwMa, hbMa, hLMa⟩ := hfrE _ (ConLeche.getD_mem hmIlt)
  have hlrM0 : LeafReads m φ d (e.getAppArgs.getD mI (.bvar 0)) :=
    hlr.of_subset
      (fun l hl => ConLeche.fvarLeaves_getAppArgs (ConLeche.getD_mem hmIlt) l hl)
  have hdM : denoteMeta m.acval env φ d (e.getAppArgs.getD mI (.bvar 0))
      = some (xs.getD mI default) := hspx.getD _ mI hmIlt
  obtain ⟨⟨ma, hma⟩, hlrMj, hwm, hbm, hLm⟩ :
      (∃ w, denoteMeta m.acval env φ d major = some w) ∧
        LeafReads m φ d major ∧ Expr.WScoped d major ∧
        major.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded major :=
    ConLeche.prepareMajorFueled_ind hprep
      (fun x => (∃ w, denoteMeta m.acval env φ d x = some w) ∧
        LeafReads m φ d x ∧ Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x)
      (fun hw hP => by
        obtain ⟨⟨xa, hxa⟩, hlrx, hwx, hbx, hLx⟩ := hP
        obtain ⟨ya, hya⟩ := ihw hw hwx hbx hLx hlrx hxa
        exact ⟨⟨ya, hya⟩, hlrx.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hw),
          ConLeche.whnf_WScoped m.wf fuel hw hwx,
          ConLeche.whnf_looseBVars m.wf fuel hw hbx,
          fun l hl => hLx l (ConLeche.whnf_fvarLeaves m.wf fuel hw l hl)⟩)
      (fun hlit hP => by
        obtain ⟨⟨xa, hxa⟩, hlrx, hwx, hbx, hLx⟩ := hP
        rcases ConLeche.litMajorToCtorFueled_inv hlit with rfl | ⟨st, rfl, hg, hred⟩
        · refine ⟨⟨xa, ?_⟩, hlrx.of_subset ConLeche.litToCtorIfNat_fvarLeaves,
            ConLeche.litToCtorIfNat_WScoped hwx,
            ConLeche.litToCtorIfNat_looseBVars hbx,
            fun l hl => hLx l (ConLeche.litToCtorIfNat_fvarLeaves l hl)⟩
          rw [denoteMeta_litToCtorIfNat]
          exact hxa
        · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ :=
            denotePStrLit_of_guard (m := m) d st hg hxa
          have hlrc : LeafReads m φ d (ConLeche.strLitToConstructor st) := by
            intro l hl; rw [hfv] at hl; exact nomatch hl
          obtain ⟨ya, hya⟩ := ihw hred hwc hbc hLc hlrc hSC
          exact ⟨⟨ya, hya⟩,
            hlrc.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hred),
            ConLeche.whnf_WScoped m.wf fuel hred hwc,
            ConLeche.whnf_looseBVars m.wf fuel hred hbc,
            fun l hl => hLc l (ConLeche.whnf_fvarLeaves m.wf fuel hred l hl)⟩)
      (fun hmaj hP => by
        obtain ⟨⟨xa, hxa⟩, hlrx, hwx, hbx, hLx⟩ := hP
        obtain ⟨hrd, hlry⟩ := majorToCtorFueled_reads ihw ihio hmaj hwx hbx hLx hlrx hxa
        refine ⟨hrd, hlry, ?_⟩
        rcases ConLeche.majorToCtor_inv hmaj with rfl | ⟨hwsB, hbB, hleafB, -⟩
        · exact ⟨hwx, hbx, hLx⟩
        · exact ⟨Expr.WScoped.of_wscopedB hwsB, hbB, fun l hl =>
            hLx l (by
              have := List.all_eq_true.mp hleafB l hl
              simpa using this)⟩)
      ⟨⟨_, hdM⟩, hlrM0, hwMa, hbMa, hLMa⟩
  have hfrM : ∀ x ∈ major.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := fun x hx =>
    ⟨hwm.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hbm x hx,
      fun l hl => hLm l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩
  -- its spine decomposes into per-argument readings
  have hspy : ∃ ys, DenoteMetaSpine m.acval env φ d major.getAppArgs ys := by
    have hma' := hma
    rw [show major = Expr.mkAppN major.getAppFn major.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp major).symm] at hma'
    obtain ⟨-, ys, -, hspy, -⟩ := denoteMeta_mkAppN_inv hma'
    exact ⟨ys, hspy⟩
  obtain ⟨ys, hspy⟩ := hspy
  -- the right-hand side reads at the ambient depth
  obtain ⟨-, hlaw0⟩ := hrec c cv mI rP rules hfrec r
    (List.mem_of_find?_eq_some hrfind) hfire
  obtain ⟨Ra, hRa0, -, -, -⟩ := hlaw0 us hlenU
  obtain ⟨hRa, hRnf, hRbd⟩ :=
    recRhs_depth hfrec (List.mem_of_find?_eq_some hrfind) hRa0
  -- the reduct
  have hspOut : DenoteMetaSpine m.acval env φ d
      (e.getAppArgs.take rP ++ major.getAppArgs.drop (RecRule.ctorParams r))
      (xs.take rP ++ ys.drop (RecRule.ctorParams r)) :=
    (hspx.take rP).append (hspy.drop (RecRule.ctorParams r))
  refine ⟨_, denoteMeta_mkAppN hspOut (hRa d), ?_, ?_, ?_, ?_⟩
  · exact Expr.WScoped.mkAppN (Expr.WScoped.of_not_hasFvar hRnf)
      (fun y hy => by
        rcases List.mem_append.mp hy with hy' | hy'
        · exact (hfrE y (List.mem_of_mem_take hy')).1
        · exact (hfrM y (List.mem_of_mem_drop hy')).1)
  · exact ConLeche.looseBVarsBounded_mkAppN hRbd (fun y hy => by
      rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.1
      · exact (hfrM y (List.mem_of_mem_drop hy')).2.1)
  · intro l hl
    rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
    · exact absurd hl' (by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf]; simp)
    · rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.2 l hly
      · exact (hfrM y (List.mem_of_mem_drop hy')).2.2 l hly
  · intro l hl
    rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
    · exact absurd hl' (by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf]; simp)
    · rcases List.mem_append.mp hy with hy' | hy'
      · exact hlr l (ConLeche.fvarLeaves_getAppArgs
          (List.mem_of_mem_take hy') l hly)
      · exact hlrMj l (ConLeche.fvarLeaves_getAppArgs
          (List.mem_of_mem_drop hy') l hly)

/-! ## THE NAMED WALL — the `.nested` pin comparand has no grading source

`DefEqClaim` demands `WellDenotedV` of **both** comparands where
`DefEqClaimsR` demands nothing, and in the P lane a term's grading
always comes from one place: `InferClaim` produces it from a
successful `inferTypeCore` run.  Every other comparand the ι clause
compares is inferred — the constructor's arguments by `hcertC`, the
subject's by the recursor telescope — but the `.nested` fire branch's
right-hand comparands are `pins.map (instSpine (args.take rP) (rP-1) ·)`,
stored rule data that the clause only ever *defeq*s.  Nothing infers
them, so nothing grades them.

The gap is an **asymmetry inside the frozen law itself**: `RecRuleLaw`
carries `∀ ρ, WellDenotedV V ρ Ra` for the rule's right-hand side — the
same species of fact, for the same reason — and carries nothing for
the pins, although its own `.nested` premise is what forces the
consumer to grade them.  It is true (the recursor install validates
the pins through the front door, `checkAnnotList`); it is simply not
carried.

RESOLVED (the lane lead's ratified one-conjunct repair, 2026-09-02):
`RecRuleLaw` now carries the open pins' readings graded at every
environment, parallel to `Ra`'s conjunct, and the row grades the
instantiated comparand through the `instRevChain` closure
(`wellDenotedV_instRevChain`, `Steps/IotaKit.lean` — proved as an iff at
a generalized body because the grading flows outside-in; the
arguments' gradings are needed at the ambient environment only, each
`liftN` popping the chain back down).  `IotaNestedPinP` is deleted;
the wall stood for one worker-session. -/

/-! ## `IotaStep` -/

/-- **`IotaStep`, discharged** (`iota_stepR`'s mirror; the wall above
is its one flagged premise). -/
theorem iotaStep_of {m : EnvModel V env}
    (hrec : RecRules m φ) (hcaps : CapsOk m) (htower : TowerOk m φ) (hct : ConstType m φ)
    (hav : AcvalValid m)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hexi : InferExistsIOS μ m φ fuel)
    (hreads_ios : InferReadsIOS m μ φ fuel)
    (hwreads : WhnfReads m μ φ fuel) :
    IotaStep μ m φ fuel := by
  intro d e e'' Δa h hws hb hLb ea hC hea hok
  obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj, cvj, cnP,
    cnF, r, hfn, hfrec, hlenA, hlenU,
    hprep, hfnmaj, hfcj, hrfind, hlenM,
    hfire, hlev, hdefP, hcertR, hcertC, hidx,
    rfl⟩ := ConLeche.iotaRec_inv h
  have hrmem : r ∈ rules := List.mem_of_find?_eq_some hrfind
  -- the law, and the right-hand side's reading at the ambient depth
  obtain ⟨hrPle, hlaw0⟩ := hrec c cv mI rP rules hfrec r hrmem hfire
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlenU
  obtain ⟨hRaD, hRnf, hRbd⟩ := recRhs_depth hfrec hrmem hRa0
  -- the recursor spine, read
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp e).symm, hfn] at hea
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denoteMeta_mkAppN_inv hea
  rw [denoteMeta_const hfrec (show us.length = _ from hlenU)] at hvc
  obtain rfl : vc = m.acval c (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hvc).symm
  have hfrE := frame_spine hws hb hLb hC
  obtain ⟨-, hoX⟩ := hoist_spine xs hok
  have hxsLen : xs.length = mI + 1 := by rw [← hspx.length]; exact hlenA
  -- the major, through the whole chain (either order: an instance of
  -- `prepareMajorFueled_ind`): read, graded, and equal to the argument's
  -- reading
  have hmIlt : mI < e.getAppArgs.length := by rw [hlenA]; omega
  obtain ⟨hwM, hbM, hLM, hCM⟩ := hfrE _ (ConLeche.getD_mem hmIlt)
  have hdMaj : denoteMeta m.acval env φ d (e.getAppArgs.getD mI (.bvar 0))
      = some (xs.getD mI default) := hspx.getD _ mI hmIlt
  have hokMajArg : ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ (xs.getD mI default) :=
    hoX _ (ConLeche.getD_mem (by rw [← hspx.length]; exact hmIlt))
  obtain ⟨vmaj, hvmajSave, hokMj, heqAll, hwmj, hbmj, hLmj, hCmj⟩ :
      ∃ v, denoteMeta m.acval env φ d major = some v ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ v) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ (xs.getD mI default) = interp V ρ v) ∧
        Expr.WScoped d major ∧ major.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded major ∧ CtxOk m φ d Δa major :=
    ConLeche.prepareMajorFueled_ind hprep
      (fun x => ∃ v, denoteMeta m.acval env φ d x = some v ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ v) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ (xs.getD mI default) = interp V ρ v) ∧
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x)
      (fun hw hP => by
        obtain ⟨v, hv, hok, heq, hwx, hbx, hLx, hCx⟩ := hP
        obtain ⟨v', hv'⟩ :=
          hwreads hw hwx hbx hLx (LeafReads.of_ctxOk hCx) hv
        obtain ⟨hok', heq'⟩ := ihw hw hwx hbx hLx hCx hv hv' hok
        exact ⟨v', hv', hok', fun ρ hρ => (heq ρ hρ).trans (heq' ρ hρ),
          ConLeche.whnf_WScoped m.wf fuel hw hwx,
          ConLeche.whnf_looseBVars m.wf fuel hw hbx,
          fun l hl => hLx l (ConLeche.whnf_fvarLeaves m.wf fuel hw l hl),
          hCx.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hw)⟩)
      (fun hlit hP => by
        obtain ⟨v, hv, hok, heq, hwx, hbx, hLx, hCx⟩ := hP
        obtain ⟨v', hv', hok', heq', hw', hb', hL', hC'⟩ :=
          litMajorToCtorFueled_step ihw hwreads hlit hwx hbx hLx hCx hv hok
        exact ⟨v', hv', hok', fun ρ hρ => (heq ρ hρ).trans (heq' ρ hρ),
          hw', hb', hL', hC'⟩)
      (fun hmaj hP => by
        obtain ⟨v, hv, hok, heq, hwx, hbx, hLx, hCx⟩ := hP
        obtain ⟨v', hv', hok', heq', hw', hb', hL', hC'⟩ :=
          majorToCtorFueled_step hcaps htower hct hav ihw ihd ihis hsss hexi
            hreads_ios hwreads hmaj hwx hbx hLx hCx hv hok
        exact ⟨v', hv', hok', fun ρ hρ => (heq ρ hρ).trans (heq' ρ hρ),
          hw', hb', hL', hC'⟩)
      ⟨_, hdMaj, hokMajArg, fun _ _ => rfl, hwM, hbM, hLM, hCM⟩
  -- the constructor spine
  have hrctor : r.ctor = cj := by
    have := List.find?_some hrfind
    simpa using this
  rw [← hrctor] at hfnmaj hfcj hrfind
  have hvmaj := hvmajSave
  rw [show major = Expr.mkAppN major.getAppFn major.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp major).symm, hfnmaj] at hvmaj
  obtain ⟨vj, ys, hvj, hspy, rfl⟩ := denoteMeta_mkAppN_inv hvmaj
  obtain ⟨hlenUj, rfl⟩ := denoteMeta_const_arity hfcj hvj
  have hfrC := frame_spine hwmj hbmj hLmj hCmj
  obtain ⟨-, hoY⟩ := hoist_spine ys hokMj
  -- the two stored types
  obtain ⟨TVa, hTVaD, hokTVa, hmemR, hnfR, hbdR⟩ :=
    constType_pkg hct hfrec rfl (show us.length = _ from hlenU)
  obtain ⟨TVja, hTVjaD, hokTVja, hmemJ, hnfJ, hbdJ⟩ :=
    constType_pkg hct hfcj rfl hlenUj
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVaD hnfR hbdR hmemR
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hnfJ hbdJ hmemJ
  have hCR : CtxOk m φ d Δa (cv.type.instantiateLevelParams cv.levelParams us) :=
    ⟨hC.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR] at hl
      exact nomatch hl⟩
  have hCJ : CtxOk m φ d Δa
      (cvj.type.instantiateLevelParams cvj.levelParams usj) :=
    ⟨hC.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ] at hl
      exact nomatch hl⟩
  -- the two telescope fits
  have hspR : DenoteMetaSpine m.acval env φ d (e.getAppArgs.take mI ++ [major])
      (xs.take mI ++ [AnnotTerm.mkAppN
        (m.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys]) :=
    (hspx.take mI).append (DenoteMetaSpine.cons hvmajSave DenoteMetaSpine.nil)
  have hframesR : ∀ x ∈ e.getAppArgs.take mI ++ [major],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hfrE x (List.mem_of_mem_take hx')
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hwmj, hbmj, hLmj, hCmj⟩
  have hoksR : ∀ x ∈ (xs.take mI ++ [AnnotTerm.mkAppN
      (m.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys]),
      ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoX x (List.mem_of_mem_take hx')
    · rcases List.mem_singleton.mp hx' with rfl; exact hokMj
  -- **the redex's own slots** (the ι-slot licence, `IotaGateP`): the
  -- subject's grading at the recursor spine with the rescued major in
  -- the major slot (`heqAll` exchanges the argument), and the rescued
  -- major's grading as the constructor spine's
  have hokSR : ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ (AnnotTerm.mkAppN (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [AnnotTerm.mkAppN
          (m.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
    intro ρ hρ
    have h := hok ρ hρ
    rw [take_getD_splitA hxsLen] at h
    exact wellDenotedV_mkAppN_snoc_congr h (hokMj ρ hρ) (heqAll ρ hρ)
  obtain ⟨restR, hfitR, -, -⟩ :=
    certs_teleLic ihd ihis hexi _ (e.getAppArgs.take mI ++ [major]) _ TVa _
      hcertR (ConLeche.Expr.WScoped.of_not_hasFvar hnfR) hbdR
      (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfR) hCR (hTVaD d)
      (fun σ _ => hokTVa σ) hframesR hspR hoksR hokSR (fun σ _ => hmemR σ)
  obtain ⟨restC, hfitC, hokRestC, -⟩ :=
    certs_teleLic ihd ihis hexi _ major.getAppArgs ys TVja _ hcertC
      (ConLeche.Expr.WScoped.of_not_hasFvar hnfJ) hbdJ
      (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfJ) hCJ (hTVjaD d)
      (fun σ _ => hokTVja σ) hfrC hspy hoY hokMj (fun σ _ => hmemJ σ)
  -- the level congruence (currency-free: the comparand reads no arguments)
  have hψ : Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (ConLeche.recFireComparands r cv.levelParams us cvj.levelParams
            [] rP).1 := by
    rw [recFireComparands_fst_nil] at hlev
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlev φ)
  -- the fired equation and the transported grading, at each valuation
  have hmain : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ (AnnotTerm.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us)) xs)
          = interp V ρ (AnnotTerm.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams r))) ∧
        WellDenotedV V ρ (AnnotTerm.mkAppN Ra
          (xs.take rP ++ ys.drop (RecRule.ctorParams r))) := by
    intro ρ hρ
    -- **the index pin**: trivial where the recursor has no indices
    -- (the ι batch: the checker compares nothing at `mI = rP`), else
    -- the constructor telescope's residual, decomposed, and the
    -- index comparands
    have hpinI : IotaIndexPin (V := V) ρ restC (RecRule.ctorParams r) mI rP
        (xs.take mI) := by
      by_cases hmr : mI = rP
      · exact ⟨restC, [], rfl, Or.inl hmr, fun i hi => absurd hi (by omega)⟩
      obtain ⟨residual, hpres, hdefI⟩ := ConLeche.iotaIndexOk_inv hidx hmr
      -- the residual's frames
      obtain ⟨hwRes, hbRes, hLRes, hCRes⟩ :=
        piResidual_frame hpres (ConLeche.Expr.WScoped.of_not_hasFvar hnfJ) hbdJ
          (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfJ) hCJ hfrC
      have hfrRes := frame_spine hwRes hbRes hLRes hCRes
      have hresC : denoteMeta m.acval env φ d residual = some restC :=
        teleFitPA_residual m.acval_closed (acval_inst_self m) major.getAppArgs
          hpres (ConLeche.Expr.WScoped.of_not_hasFvar hnfJ)
          (fun x hx => ⟨(hfrC x hx).1, (hfrC x hx).2.1⟩) (hTVjaD d) hspy
          (hfitC ρ hρ)
      rw [show residual = Expr.mkAppN residual.getAppFn residual.getAppArgs from
        (ConLeche.Expr.mkAppN_getApp residual).symm] at hresC
      obtain ⟨Ha, cargsa, -, hspRes, hCeq⟩ := denoteMeta_mkAppN_inv hresC
      obtain ⟨-, hoCargs⟩ :=
        hoist_spine cargsa (fun σ hσ => hCeq ▸ hokRestC σ hσ)
      have hspIdx : DenoteMetaSpine m.acval env φ d
          ((e.getAppArgs.take mI).drop rP) ((xs.take mI).drop rP) :=
        (hspx.take mI).drop rP
      have hmapI : (cargsa.drop (RecRule.ctorParams r)).map (interp V ρ)
          = ((xs.take mI).drop rP).map (interp V ρ) :=
        map_interp_of_defEqListFueled ihd hdefI
          (fun x hx => hfrRes x (List.mem_of_mem_drop hx))
          (fun x hx => hfrE x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
          (hspRes.drop _) hspIdx
          (fun x hx => hoCargs x (List.mem_of_mem_drop hx))
          (fun x hx => hoX x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
          ρ hρ
      have hlenDisj : mI = rP ∨
          cargsa.length = RecRule.ctorParams r + (mI - rP) := by
        have hlen := congrArg List.length hmapI
        simp only [List.length_map, List.length_drop, List.length_take] at hlen
        rw [hxsLen] at hlen
        omega
      refine ⟨Ha, cargsa, hCeq, hlenDisj, fun i hi => ?_⟩
      have hlt : i < (cargsa.drop (RecRule.ctorParams r)).length := by
        rw [List.length_drop]
        rcases hlenDisj with hh | hh <;> omega
      have hgi := map_interp_getD_eq hmapI hlt
      rw [getD_dropA, getD_dropA] at hgi
      exact hgi
    -- the `.plain` comparands
    have hplain : RecRule.fire r = .plain →
        ∀ i, i < RecRule.ctorParams r → i < mI →
          interp V ρ (ys.getD i default)
            = interp V ρ ((xs.take mI).getD i default) := by
      intro hp i hi him
      rw [show (ConLeche.recFireComparands r cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2 = e.getAppArgs.take (RecRule.ctorParams r) from by
        unfold ConLeche.recFireComparands; rw [hp]] at hdefP
      have hmapP := map_interp_of_defEqListFueled ihd hdefP
        (fun x hx => hfrC x (List.mem_of_mem_take hx))
        (fun x hx => hfrE x (List.mem_of_mem_take hx))
        (hspy.take _) (hspx.take _)
        (fun x hx => hoY x (List.mem_of_mem_take hx))
        (fun x hx => hoX x (List.mem_of_mem_take hx)) ρ hρ
      have hlt : i < (ys.take (RecRule.ctorParams r)).length := by
        rw [List.length_take, ← hspy.length, hlenM]
        omega
      have hgi := map_interp_getD_eq hmapP hlt
      rw [getD_takeA hi, getD_takeA hi] at hgi
      rw [getD_takeA him]
      exact hgi
    -- the `.nested` pins
    have hnested : ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams r →
        ∀ vpa : AnnotTerm,
          denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
            ((pins.getD i default).instantiateLevelParams cv.levelParams us))
            = some vpa →
          interp V ρ (ys.getD i default)
            = interp V ρ (AnnotTerm.instRevChain ((xs.take mI).take rP) vpa) := by
      intro lvls pins hn i hi vpa hvpa
      obtain ⟨-, -, -, -, -, hrec', -⟩ :=
        m.wf _ (ConLeche.Semantics.Env.find?_mem hfrec)
      obtain ⟨-, -, -, -, hnest⟩ := hrec' cv mI rP rules rfl r hrmem
      obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
      have hcmp : (ConLeche.recFireComparands r cv.levelParams us
          cvj.levelParams e.getAppArgs rP).2
          = pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us)) := by
        unfold ConLeche.recFireComparands; rw [hn]
      have hlenPins : pins.length = RecRule.ctorParams r := by
        have hl := defEqListFueled_length hdefP
        rw [hcmp, List.length_take, List.length_map, hlenM] at hl
        omega
      have hprelen : (e.getAppArgs.take rP).length = rP := by
        rw [List.length_take, hlenA]; omega
      have hargsPre : ∀ x ∈ e.getAppArgs.take rP, Expr.WScoped d x ∧
          x.looseBVarsBounded 0 = true := by
        intro x hx
        obtain ⟨hw2, hb2, -, -⟩ := hfrE x (List.mem_of_mem_take hx)
        exact ⟨hw2, hb2⟩
      have hilt : i < pins.length := by rw [hlenPins]; exact hi
      obtain ⟨hpinF, -, -, hpinB⟩ :=
        hpinsWf (pins.getD i default) (ConLeche.getD_mem hilt)
      have hpinF' : ((pins.getD i default).instantiateLevelParams
          cv.levelParams us).hasFvar = false := by
        rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hpinF
      have hpinB' : ((pins.getD i default).instantiateLevelParams
          cv.levelParams us).looseBVarsBounded
          (e.getAppArgs.take rP).length = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
        exact hpinB
      have hcden := denoteMeta_openRev m.acval_closed (acval_inst_self m)
        (e.getAppArgs.take rP) hargsPre
        ((ConLeche.Expr.WScoped.of_not_hasFvar (d := d) hpinF').fvarsBelow)
        hpinB' (hspx.take rP)
      rw [hprelen] at hcden
      have hbase := denoteMeta_openRev_base (env := env) (φ := φ)
        m.acval_closed m.acval_erase m.cval_closed hpinF'
        (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hpinB) d
      rw [hbase, hvpa] at hcden
      -- only the `i`-th comparand is known to read, so it is pulled out
      -- of `defEqList` syntactically
      have hiy : i < major.getAppArgs.length := by rw [hlenM]; omega
      have hgetL : (major.getAppArgs.take (RecRule.ctorParams r)).getD i
          (default : Expr) = major.getAppArgs.getD i default := by
        simp [List.getD, List.getElem?_eq_getElem hiy,
          show i < RecRule.ctorParams r from hi]
      have hgetR : ((pins.map (fun p =>
          Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us))).getD i default)
          = Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD i default).instantiateLevelParams
              cv.levelParams us) := by
        simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem hilt]
      rw [hcmp] at hdefP
      have hcert := defEqListFueled_get hdefP i (by
        rw [List.length_take, hlenM]; omega)
      rw [hgetL, hgetR] at hcert
      obtain ⟨hwA, hbA, hLA, hCA⟩ := hfrC _ (ConLeche.getD_mem hiy)
      have hgy : denoteMeta m.acval env φ d (major.getAppArgs.getD i default)
          = some (ys.getD i default) := hspy.getD _ i hiy
      have hcden' : denoteMeta m.acval env φ d
          (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD i default).instantiateLevelParams cv.levelParams us))
          = some (AnnotTerm.instRevChain (xs.take rP) vpa) := by
        rw [Expr.instSpine_eq_instSeq]
        simpa using hcden
      have hfrPinX : Expr.WScoped d (Expr.instSpine (e.getAppArgs.take rP)
            (rP - 1) ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) ∧
          (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD i default).instantiateLevelParams cv.levelParams
              us)).looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) ∧
          CtxOk m φ d Δa (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) := by
        refine ⟨ConLeche.instSpine_WScoped _
            (ConLeche.Expr.WScoped.of_not_hasFvar hpinF')
            (fun y hy => (hargsPre y hy).1), ?_, fun l hl => ?_,
          ⟨hC.1, fun l hl => ?_⟩⟩
        · rw [show rP - 1 = (e.getAppArgs.take rP).length - 1 from by
            rw [hprelen]]
          exact ConLeche.instSpine_closed (fun y hy => (hargsPre y hy).2) hpinB'
        · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
          · exact absurd hl' (by
              rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF']; simp)
          · exact (hfrE y (List.mem_of_mem_take hy)).2.2.1 l hly
        · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
          · exact absurd hl' (by
              rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF']; simp)
          · exact ((hfrE y (List.mem_of_mem_take hy)).2.2.2).2 l hly
      have hokCmp : ∀ σ : Nat → V, Sat V Δa σ →
          WellDenotedV V σ (AnnotTerm.instRevChain (xs.take rP) vpa) := by
        obtain ⟨vpa', hvpa', hok'⟩ := hpinsOk lvls pins hn i hi
        obtain rfl : vpa' = vpa :=
          Option.some.inj (hvpa'.symm.trans hvpa)
        intro σ hσ
        -- the fit in hand is at `xs.take mI ++ [ctor-app]`; the
        -- repaired conjunct wants its `rP`-prefix (part-6 probe
        -- repair: the grading is context-guarded through the fit)
        obtain ⟨mid, hmid⟩ := (hfitR σ hσ).take rP
        rw [List.take_append_of_le_length (by
              rw [List.length_take, hxsLen]; omega),
            List.take_take, Nat.min_eq_left hrPle] at hmid
        exact hok' σ (xs.take rP) TVa mid
          (by rw [List.length_take, hxsLen]; omega)
          (fun v hv => hoX v (List.mem_of_mem_take hv) σ hσ)
          (hTVaD 0) hmid
      have hstep := ihd hcert hwA hbA hLA hfrPinX.1 hfrPinX.2.1 hfrPinX.2.2.1
        hCA hfrPinX.2.2.2 hgy hcden'
        (hoY _ (ConLeche.getD_mem (by rw [← hspy.length]; exact hiy)))
        hokCmp ρ hρ
      rw [List.take_take, Nat.min_eq_left hrPle]
      exact hstep
    -- fire the law
    obtain ⟨heqLaw, htrans⟩ := hlaw cvj cnP cnF hfcj usj ρ (xs.take mI) ys
      TVa TVja restR restC
      (by rw [List.length_take, hxsLen]; omega)
      (by rw [← hspy.length, hlenM])
      hlenUj hψ hplain hnested hpinI (hTVaD 0) (hTVjaD 0)
      (hfitR ρ hρ) (hfitC ρ hρ)
    rw [List.take_take, Nat.min_eq_left hrPle] at heqLaw htrans
    have hsubj : interp V ρ (AnnotTerm.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us)) xs)
        = interp V ρ (AnnotTerm.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us))
          (xs.take mI ++ [AnnotTerm.mkAppN
            (m.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
      refine interp_mkAppN_congr xs _ rfl ?_
      have hsplit : xs.map (interp V ρ)
          = (xs.take mI ++ [xs.getD mI default]).map (interp V ρ) := by
        rw [← take_getD_splitA hxsLen]
      rw [hsplit, List.map_append, List.map_append]
      simp only [List.map_cons, List.map_nil, heqAll ρ hρ]
      rfl
    exact ⟨hsubj.trans heqLaw,
      htrans (fun a ha => hoX a (List.mem_of_mem_take ha) ρ hρ)
        (fun b hb2 => hoY b hb2 ρ hρ)⟩
  -- the reduct
  have hspOut : DenoteMetaSpine m.acval env φ d
      (e.getAppArgs.take rP ++ major.getAppArgs.drop (RecRule.ctorParams r))
      (xs.take rP ++ ys.drop (RecRule.ctorParams r)) :=
    (hspx.take rP).append (hspy.drop _)
  refine ⟨_, denoteMeta_mkAppN hspOut (hRaD d), fun ρ hρ => (hmain ρ hρ).2,
    fun ρ hρ => (hmain ρ hρ).1, ?_, ?_, ?_, ?_⟩
  · exact Expr.WScoped.mkAppN (ConLeche.Expr.WScoped.of_not_hasFvar hRnf)
      (fun y hy => by
        rcases List.mem_append.mp hy with hy' | hy'
        · exact (hfrE y (List.mem_of_mem_take hy')).1
        · exact (hfrC y (List.mem_of_mem_drop hy')).1)
  · exact ConLeche.looseBVarsBounded_mkAppN hRbd (fun y hy => by
      rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.1
      · exact (hfrC y (List.mem_of_mem_drop hy')).2.1)
  · intro l hl
    rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
    · exact absurd hl' (by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf]; simp)
    · rcases List.mem_append.mp hy with hy' | hy'
      · exact (hfrE y (List.mem_of_mem_take hy')).2.2.1 l hly
      · exact (hfrC y (List.mem_of_mem_drop hy')).2.2.1 l hly
  · refine ⟨hC.1, fun l hl => ?_⟩
    rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
    · exact absurd hl' (by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf]; simp)
    · rcases List.mem_append.mp hy with hy' | hy'
      · exact ((hfrE y (List.mem_of_mem_take hy')).2.2.2).2 l hly
      · exact ((hfrC y (List.mem_of_mem_drop hy')).2.2.2).2 l hly

end ConLeche.Model
