module

public import InLeanProof.IndBlockKS
public import InLeanProof.WalksIota

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
      Runs (ConLeche.checkConstantVal (ConLeche.fueledOpsM .verified) L (trCV cv)) ()

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
    refine ⟨hs, hok, ?_⟩
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
  refine ⟨hs₃, ⟨hokR, hok.2.1, hok.2.2⟩, ?_⟩
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
  blockKSSimI_of (reduceMemberSimI_of hC hRF) hPT fun _ _ _ hk h => blockShape?_memberOk hk h

end InLeanProof
