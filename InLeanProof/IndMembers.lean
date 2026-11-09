module

public import InLeanProof.IndBlockKS
public import InLeanProof.WalksIota
public import InLeanProof.CRuns
import ConLeche.Verify.Inductives.BlockInv

/-!
# O7: one member's reduction against master's (task #451, lane O7)

`reduceMemberSimI_of`: `ReduceMemberSimI` (`reduceMemberS_spec`'s twin) from the
specs of its two callees, named: the former's constant check
(`CheckConstantValFSimI`, `checkConstantValS_spec`'s twin; its guards are
`checkConstantValC`'s, O6's) and the whnf telescope's reduct
(`ReducedFormerSimI`, `reducedFormerWS_spec`'s twin), with the job's `defeq`
operation (`OpsSimI`).  `blockKSSimI_of_stages`: the recognised block's job from
those and `PassTailSimI`.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## Closed terms at a state -/

theorem okE_of_okC (fv : FVarId → Option ConLeche.Expr) :
    ∀ {e : Lean.Expr}, okC e = true → okE fv e = true := by
  intro e
  induction e <;> simp_all [okC, okE]

theorem OkS_of_okC (s : InLean.CState) {e : Lean.Expr} (h : okC e = true) : OkS s e = true :=
  okE_of_okC _ h

theorem trC_hasFvar (e : Lean.Expr) : (trC e).hasFvar = false := by
  induction e <;> simp_all [trC, trE, ConLeche.Expr.hasFvar]

theorem trC_wscoped (d : Nat) (e : Lean.Expr) : ConLeche.Expr.WScoped d (trC e) :=
  ConLeche.Expr.WScoped.of_not_hasFvar (trC_hasFvar e)

/-! ## The member's pure guards -/

theorem piResult_trC : ∀ e : Lean.Expr, trC (InLean.piResult e) = (trC e).piResult
  | .mdata _ e => by rw [InLean.piResult]; exact piResult_trC e
  | .forallE _ t b _ => by
    rw [InLean.piResult]
    simp only [trC, trE, ConLeche.Expr.piResult]
    exact piResult_trC b
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

theorem formerResSort_trC (t : Lean.Expr) :
    ConLeche.formerResSort (trC t) = (InLean.formerResSort t).map trL := by
  unfold ConLeche.formerResSort InLean.formerResSort
  rw [← piResult_trC, ← trC_stripTop (InLean.piResult t)]
  generalize hx : EO.stripTop (InLean.piResult t) = x
  cases x with
  | sort u => rfl
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rfl

theorem formerDefHeaded_tr (cv : Lean.ConstantVal) :
    ConLeche.formerDefHeaded (trCV cv) = InLean.formerDefHeaded cv := by
  unfold ConLeche.formerDefHeaded InLean.formerDefHeaded
  rw [trCV_type, formerResSort_trC]
  cases InLean.formerResSort cv.type <;> rfl

theorem declinedAtDefinition_tr :
    ConLeche.declinedAtDefinition = InLean.declinedAtDefinition.map toName := rfl

/-! ## The callees, named -/

/-- **A former's constant check** (`checkConstantValS_spec`'s twin): its
guards are `checkConstantValC`'s (O6), its operations the job's. -/
@[expose] def CheckConstantValFSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (cv : Lean.ConstantVal) (s₀ s' : InLean.CState),
    JobEnvI fe L → CSOKI .verified false L s₀ → okC cv.type = true →
    InLean.checkConstantValF (sharedOpsC .verified fe) fe cv false s₀ = .ok ((), s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (trC cv.type).looseBVarsBounded 0 = true ∧
      CRuns .verified (ConLeche.Cached.checkConstantValC .verified (ConLeche.mkFEnv L) (trCV cv))
        (ConLeche.checkConstantVal (ConLeche.fueledOpsM .verified) L (trCV cv)) () ()

/-- **A former's reduct** (`reducedFormerWS_spec`'s twin): the whnf telescope
walk (`whnfTelescope`, interned variables) and its closing. -/
@[expose] def ReducedFormerSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (cv cvR : Lean.ConstantVal) (n : Nat)
    (s₀ s' : InLean.CState),
    JobEnvI fe L → CSOKI .verified false L s₀ → okC cv.type = true →
    (trC cv.type).looseBVarsBounded 0 = true →
    InLean.reducedFormer (sharedOpsC .verified fe) fe cv n s₀ = .ok (cvR, s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC cvR.type = true ∧
      (trC cvR.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.reducedFormer (ConLeche.fueledOpsM .verified) L (trCV cv) n) (trCV cvR)

/-! ## One member -/

/-- **One member's reduction** from its callees' specs (`reduceMemberS_spec`'s
twin). -/
theorem reduceMemberSimI_of (hC : CheckConstantValFSimI) (hRF : ReducedFormerSimI) :
    ReduceMemberSimI := by
  intro fe L nP ms ms' s₀ s' hJ hs hok h
  unfold InLean.reduceMemberS at h
  by_cases hd : InLean.formerDefHeaded ms.cvT = true
  case neg =>
    rw [ite_eq_right hd] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    refine ⟨hs, hok, rfl, ?_⟩
    unfold ConLeche.reduceMember
    rw [show (trMember ms).cvT = trCV ms.cvT from rfl, formerDefHeaded_tr, ite_eq_right hd]
    exact Runs.pure _
  rw [ite_eq_left hd] at h
  have hdec : InLean.declinedAtDefinition.contains ms.cvT.name = false := by
    cases hc : InLean.declinedAtDefinition.contains ms.cvT.name
    · rfl
    · rw [ite_eq_left hc] at h; exact (throwI_ok h).elim
  rw [ite_eq_right (by rw [hdec]; exact Bool.false_ne_true)] at h
  obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hcl, hR1⟩ := hC fe L ms.cvT s₀ s₁ hJ hs hok.1 h1
  replace hR1 := hR1.runs
  obtain ⟨cvR, s₂, h2, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hokR, hclR, hR2⟩ := hRF fe L ms.cvT cvR (nP + ms.nIdx) s₁ s₂ hJ hs₁ hok.1 hcl h2
  obtain ⟨b, s₃, h3, h⟩ := bindI_ok h
  have hD := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₂) (d := 0) (i := ms.cvT.type) (j := cvR.type)
    hs₂ (OkS_of_okC _ hok.1) (OkS_of_okC _ hokR)
    (by rw [TrS_of_okC _ hok.1]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokR]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hok.1]; exact hcl) (by rw [TrS_of_okC _ hokR]; exact hclR)) b s₃ h3
  obtain ⟨hs₃, _, hR3⟩ := hD
  rw [TrS_of_okC _ hok.1, TrS_of_okC _ hokR] at hR3
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, h4, _⟩ := bindI_ok h
    exact (throwI_ok h4).elim
  simp only [↓reduceIte] at h
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  refine ⟨hs₃, ⟨hokR, hok.2.1, hok.2.2⟩, rfl, ?_⟩
  unfold ConLeche.reduceMember
  have hdec' : ConLeche.declinedAtDefinition.contains (toName ms.cvT.name) = false := by
    rw [declinedAtDefinition_tr, contains_map_toName, hdec]
  rw [show (trMember ms).cvT = trCV ms.cvT from rfl, formerDefHeaded_tr, ite_eq_left hd, trCV_name,
    ite_eq_right (by rw [hdec']; exact Bool.false_ne_true)]
  refine Runs.bind hR1 (Runs.bind hR2 (Runs.bind hR3 ?_))
  simp only [↓reduceIte]
  exact Runs.pure _

/-- **The recognised block's job** from the member callees and the pass with its
tail. -/
theorem blockKSSimI_of_stages (hC : CheckConstantValFSimI) (hRF : ReducedFormerSimI)
    (hPT : PassTailSimI) : BlockKSSimI :=
  blockKSSimI_of (reduceMemberSimI_of hC hRF) hPT fun _ _ _ hk h => readBlock_memberOk hk h

/-! ## The pass and the tail, split at a relation

Master's `checkBlockKS_run` splits at `BlockPass Env`.  For InLean the split
needs a relation between InLean's `BlockPass` (at the state the pass ends in:
its parameters are interned variables) and master's; `passTailSimI_of` splits
`PassTailSimI` at *any* such relation.  `PassRelI` is the relation the stages
are to be proved at: the formers' environment related by `JobEnvI` under the
block's mark (`PassEnvRelI`), the shape by `trShape`, the parameters by `TrS`,
and the positivity and class data by their translations (`D`, left to the
lane that proves the stages).  The job's freshness tests read Lean's
environment itself, so the pushes are read by `EnvLaws` from the run alone. -/

/-- **The pass** (`checkBlockPassS_run`'s twin), into a relation `R`; it starts from the
invariant at `L` (after the job's flush) and ends in it at the formers' environment. -/
@[expose] def PassSimI (R : InLean.CState → InLean.BlockPass → ConLeche.BlockPass ConLeche.Env → Prop) :
    Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (p₀ : InLean.BlockShape) (isRec : Bool)
    (q : InLean.BlockPass) (s₀ s' : InLean.CState),
    JobEnvI fe L → CSOKI .verified false L s₀ → (∀ ms ∈ p₀.members, MemberOk ms) →
    (∀ rc ∈ p₀.recs, okC rc.cvR.type = true ∧ (trC rc.cvR.type).looseBVarsBounded 0 = true) →
    PassPremI fe L p₀ →
    InLean.checkBlockPassS .verified fe p₀ isRec s₀ = .ok (q, s') →
    ∃ F cq, ConLeche.checkBlockPass (ConLeche.fueledOps .verified F) L (trShape p₀) isRec
      = .ok cq ∧ CSOKI .verified false cq.env₁ s' ∧ R s' q cq ∧
      q.p.members = p₀.members ∧ q.p.nP = p₀.nP

/-- **The stages after the pass** (`checkBlockTailS_run`'s twin), from `R`, at the
projection tables built from the pass's members (`blockTables`). -/
@[expose] def TailSimI (R : InLean.CState → InLean.BlockPass → ConLeche.BlockPass ConLeche.Env → Prop) :
    Prop :=
  ∀ (block : List Lean.ConstantInfo) (q : InLean.BlockPass) (cq : ConLeche.BlockPass ConLeche.Env)
    (Q : List InLean.ProjTable) (s₀ s' : InLean.CState),
    R s₀ q cq → CSOKI .verified false cq.env₁ s₀ → (∀ ci ∈ block, CIRange ci) →
    (∀ ci ∈ block, CIClosed ci) →
    (∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true) →
    InLean.blockTables q.p q.p.members = some Q →
    InLean.checkBlockTailS .verified block q Q s₀ = .ok ((), s') →
    CSOKIF s' ∧ ∃ F cQ, ConLeche.blockTables cq.p cq.p.members = some cQ ∧
      ConLeche.checkBlockTail (ConLeche.fueledOps .verified F) (block.map trCI) cq cQ = .ok ()

/-- **The formers' environment after the pass**, the relation's environment
part (rulings of 2026-11-08).  InLean's `env₁` is `fe` with the block's
members marked (`blockMarks`, read by `capsOf` and the table readers) and the
formers pushed; master's is `L` with the formers pushed at `blockCapsAt` and
no table.  Under the mark InLean reads a member as master's staged
environments hold it (its capabilities at the shape's field count, no
projection table), so the job's premises can hold between the two: a former's
`EntryRelI` clause is `toCaps_capsOf` at the marked field count, its table
clause `none` on both sides.  The same reading carries through the tail's
pushes (the constructors, the generated recursors), which keep the mark. -/
@[expose] def PassEnvRelI (q : InLean.BlockPass) (cq : ConLeche.BlockPass ConLeche.Env) : Prop :=
  (∃ rest, q.env₁.pending = InLean.blockMarks q.p ++ rest) ∧ cq.p = trShape q.p ∧
    JobEnvI q.env₁ cq.env₁

/-- **The pass's relation**, concrete but for the positivity and class data
(`D`: the field kinds, the class reading, the classes, the table, each to be
related by its translation at the state `s` by the lane that proves the
stages): the environment and shape by `PassEnvRelI`, the parameters by `TrS`. -/
@[expose] def PassRelI (D : InLean.CState → InLean.BlockPass → ConLeche.BlockPass ConLeche.Env → Prop)
    (s : InLean.CState) (q : InLean.BlockPass) (cq : ConLeche.BlockPass ConLeche.Env) : Prop :=
  PassEnvRelI q cq ∧ cq.params = q.params.map (TrS s) ∧ D s q cq

/-- Master's `blockTables` reads of the shape only its parameter count and level parameters. -/
theorem cblockTables_shape {p p' : ConLeche.BlockShape} (hn : p.nP = p'.nP) (hl : p.lps = p'.lps) :
    ∀ l, ConLeche.blockTables p l = ConLeche.blockTables p' l
  | [] => rfl
  | ms :: rest => by simp only [ConLeche.blockTables, hn, hl, cblockTables_shape hn hl rest]

/-- **The pass and the tail together** from the two, at any relation. -/
theorem passTailSimI_of {R : InLean.CState → InLean.BlockPass → ConLeche.BlockPass ConLeche.Env → Prop}
    (hP : PassSimI R) (hT : TailSimI R) : PassTailSimI := by
  intro fe L block p₀ isRec s₀ s' hJ hs hr hcl hk hms hrecs hpre Q hQ h
  obtain ⟨q, s₁, h1, h2⟩ := bindI_ok h
  obtain ⟨F₁, cq, hF₁, hs₁, hR, hqm, hqn⟩ := hP fe L p₀ isRec q s₀ s₁ hJ hs hms hrecs hpre h1
  have hQq : InLean.blockTables q.p q.p.members = some Q := by
    rw [← hQ]
    exact blockTables_congr hqn (lps_congr (by rw [hqm])) (by rw [hqm])
  obtain ⟨hs', F₂, cQ, hcQ, hF₂⟩ := hT block q cq Q s₁ s' hR hs₁ hr hcl hk hQq h2
  -- master's pass keeps the members and the parameter count
  obtain ⟨-, -, -, -, -, -, hInd, -⟩ := ConLeche.checkBlockPass_inv hF₁
  have hcm := ConLeche.checkBlockInds_members hInd
  obtain ⟨-, -, -, s0, -, -, hp1, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hcn : cq.p.nP = (trShape p₀).nP := by rw [hp1]; rfl
  have hcl' : cq.p.lps = (trShape p₀).lps := by
    unfold ConLeche.BlockShape.lps; rw [hcm]
  have hcQ' : ConLeche.blockTables (trShape p₀) (trShape p₀).members = some cQ := by
    rw [← hcQ, ← hcm, cblockTables_shape hcn hcl']
  refine ⟨hs', max F₁ F₂, cq, cQ, ?_, hcQ', ?_⟩
  · rw [← ConLeche.checkBlockPass_datF]
    exact FueledM.up (Nat.le_max_left _ _) (by rw [ConLeche.checkBlockPass_datF]; exact hF₁)
  · rw [← ConLeche.checkBlockTail_datF]
    exact FueledM.up (Nat.le_max_right _ _) (by rw [ConLeche.checkBlockTail_datF]; exact hF₂)

/-! ## O7's top, from the named stages -/

variable {pins : List ConLeche.NatOpPinSet}

/-- **InLean's inductive declaration simulates master's pure declaration kind
check** on the translated block, from the remaining named stages: the
former's constant check (`CheckConstantValFSimI`), its reduct
(`ReducedFormerSimI`), the pass and the tail at a relation of the prover's
choice (`PassSimI R`, `TailSimI R`). -/
theorem checkIndDeclC_sim_stages (hC : CheckConstantValFSimI)
    (hRF : ReducedFormerSimI)
    {R : InLean.CState → InLean.BlockPass → ConLeche.BlockPass ConLeche.Env → Prop}
    (hP : PassSimI R) (hT : TailSimI R)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo} {nP : Nat}
    (hso : ∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true)
    {s₀ s' : InLean.CState} (hs : CSOKIF s₀) (hr : ∀ ci ∈ block, CIRange ci)
    (hcl : ∀ ci ∈ block, CIClosed ci) (hb : toBlock block = some cb)
    (hTS : ∀ p s, InLean.readBlock nP block = .ok p →
      InLean.genEntriesAgree p block s = .ok ((), s) → TailShapeOkI p)
    (h : InLean.checkIndDeclC .verified fe block nP s₀ = .ok ((), s')) :
    CSOKIF s' ∧ ∃ F L', ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pins L
      (.indDecl cb nP) = .ok L' :=
  checkIndDeclC_sim_of (blockKSSimI_of_stages hC hRF (passTailSimI_of hP hT)) hJ hso hs hr hcl hb
    hTS h

end InLeanProof
