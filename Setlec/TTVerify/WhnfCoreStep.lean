import Setlec.TTVerify.Iota
import Setlec.TTVerify.WhnfCore
import Setlec.TTVerify.Extend
import Setlec.TT.Nat

/-!
# The `whnfCore` step of `CheckStepTT`

The first quarter of `CheckStepTT` (`Setlec/TTVerify/Claims.lean`):
`WhnfCoreClaimsTT` at `fuel + 1` from the four claims at `fuel`.
Transpose of `whnfCore_claims` (`Setlec/Model/Core/Whnf.lean`), and it
follows the same case split, driven by the same inversion lemma
(`whnf_app_inv`, `whnf_proj_inv`, `Setlec/Verify/InferLemmas.lean`) —
which is one more piece of shared checker-side infrastructure the
bridge did not have to build.

**Two clauses are named obligations rather than proofs.**  The iota
clause and the projection clause each need their reduct's *frame
conditions* as well as its denotation, and the checker-side scope
lemma for `iotaRec` is `private` in `Setlec/Verify/Deep.lean`.  Rather
than widen that file from here, the two clauses are stated as
`IotaStepTT` and `ProjStepTT` and consumed — the same discipline as
`CheckStepTT` and `CheckDeclTT`: an unproved step is a named `Prop`, so
every consumer of one is visible in the source.  Their content is
already built (`rec_rules_fire`, `proj_reduction_step`); what is
missing is the scope bookkeeping around it.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The two named clause obligations -/

/-- **The iota clause.**  A fired recursor application denotes to a
`Deq`-equal term, and the reduct carries the frame conditions the
recursive `whnfCore` call needs.  The equation half is
`rec_rules_fire`; the frame half is checker-side bookkeeping. -/
def IotaStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e'' : Expr} {v : VExpr},
    iotaRecP env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v →
    ∃ w, denote m.cval env φ d e'' = some w ∧ Deq Δ v w ∧
      Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e'' ∧ CtxOk m.cval env φ d Δ e''

/-- **The projection clause**, whole.  Stated at *clause* granularity
where `IotaStepTT` is stated at *reduct* granularity, and the asymmetry
is deliberate rather than untidy: `whnf_app_inv` hands the ι case its
reduct directly, so the obligation can be isolated to the reduct and
the rest of the application clause proved around it.  The projection
clause reduces its scrutinee with `whnf` *and* expands string literals
with `projLitToCtor` before the table is consulted, so isolating the
reduct would leave two more unproved steps outside the obligation
rather than one inside it.

Its content is `proj_reduction_step` and `proj_tele_typed`, both
already built, plus the scrutinee reduction and the literal
expansion. -/
def ProjStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {sn : Name} {i : Nat} {pe e' : Expr}
    {v : VExpr},
    whnfCore env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOk m.cval env φ d Δ (.proj sn i pe) →
    denote m.cval env φ d (.proj sn i pe) = some v →
    ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v'

/-! ## The beta clause

The only clause that consumes a certificate directly.  `whnf_app_inv`
hands back `inferTypeCore … a = .ok ta` and `isDefEqCore … ta ty =
.ok true`; the inference claim turns the first into `⊢ ⟦a⟧ : ⟦ta⟧`, the
equality claim turns the second into `⟦ta⟧ ≡ ⟦ty⟧`, and `Deq.conv`
combines them into the argument typed **at the domain the redex names**
— which is exactly `HasType.beta`'s premise.

This is §6's headline fact at its most visible: the premise is supplied
where the rule fires, and nothing carried from above would do. -/

/-- The beta step: a certified redex and its contractum denote to
`Deq`-equal terms. -/
theorem denote_beta_step_certified {env : Env} (m : EnvTT env)
    (φ : Name → Nat) {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body a ta : Expr}
    {A B x : VExpr}
    (hta : inferTypeCore env fuel d a = .ok ta)
    (hde : isDefEqCore env fuel d ta ty = .ok true)
    (hty : denote m.cval env φ d ty = some A)
    (hbody : denote m.cval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some B)
    (hax : denote m.cval env φ d a = some x)
    (hfb : Expr.fvarsBelow d body)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOk m.cval env φ d Δ a)
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hLty : Expr.LeavesBounded ty) (hCty : CtxOk m.cval env φ d Δ ty) :
    denote m.cval env φ d (body.instantiate1 a) = some (VExpr.inst B x) ∧
      Deq Δ (.app (.lam A B) x) (VExpr.inst B x) := by
  -- the certificate: the argument is derivably of the redex's domain
  obtain ⟨x', tv, hix, hita, hxt⟩ := ihi hta hwa hba hLa hCa
  obtain rfl : x' = x := by rw [hix] at hax; exact Option.some.inj hax
  have hCta : CtxOk m.cval env φ d Δ ta :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hwa) hCa
  have hwta : Expr.WScoped d ta := inferTypeCore_WScoped m.wf fuel hta hwa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (inferTypeCore_fvarLeaves m.wf fuel hta hwa l hl)
  have hbta : ta.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hta hwa hba hLa
  have hDeq : Deq Δ tv A :=
    ihd hde hwta hbta hLta hwty hbty hLty hCta hCty hita hty
  refine ⟨?_, ⟨.sort 0, HasType.beta (Deq.conv hxt hDeq)⟩⟩
  rw [denote_beta (n := n) (ty := ty) hcl hfb hwa hba hax 0, hbody]
  rfl

/-! ## The application clause

Three sub-cases, from `whnf_app_inv`: the head whnfs to a λ and the
redex is certified (β), the head whnfs to something a recursor rule
fires on (ι), or nothing fires and the reduct is the head-reduced
application.  All three end in the same place — a `Deq` chain from the
subject through `Deq.appFun` and then the clause's own equation — and
all three recurse. -/

/-- The `.app` clause of `whnfCore_claimsTT`. -/
theorem whnfCore_app_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hiota : IotaStepTT m φ fuel)
    (ihwc : WhnfCoreClaimsTT m φ fuel)
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {f a e' : Expr} {v : VExpr}
    (h : whnfCore env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk m.cval env φ d Δ (.app f a))
    (hv : denote m.cval env φ d (.app f a) = some v) :
    ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOk m.cval env φ d Δ f :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOk m.cval env φ d Δ a :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the subject's denotation splits
  rw [denote_app] at hv
  split at hv
  · next vf va hif hia =>
    obtain rfl : v = .app vf va := (Option.some.inj hv).symm
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨vf', hif', hDf⟩ := ihwc hwf hws.1 hb.1 hLf hCf hif
    -- the head-reduced application, and its frame conditions
    have hwf' : Expr.WScoped d f' := whnfCore_WScoped m.wf fuel hwf hws.1
    have hbf' : f'.looseBVarsBounded 0 = true :=
      whnfCore_looseBVars m.wf fuel hwf hb.1
    have hLf' : Expr.LeavesBounded f' := fun l hl =>
      hLf l (whnfCore_fvarLeaves m.wf fuel hwf l hl)
    have hCf' : CtxOk m.cval env φ d Δ f' :=
      CtxOk.of_subset (whnfCore_fvarLeaves m.wf fuel hwf) hCf
    have hiapp : denote m.cval env φ d (.app f' a)
        = some (VExpr.app vf' va) := by
      rw [denote_app, hif', hia]
    have hDapp : Deq Δ (VExpr.app vf va) (VExpr.app vf' va) :=
      Deq.appFun hDf
    have hwapp : Expr.WScoped d (.app f' a) := by
      simp only [Expr.WScoped]
      exact ⟨hwf', hws.2⟩
    have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf', hb.2⟩
    have hLapp : Expr.LeavesBounded (.app f' a) := fun l hl => by
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hLf' l hl
      · exact hLa l hl
    have hCapp : CtxOk m.cval env φ d Δ (.app f' a) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hCf'.2 l hl
      · exact hCa.2 l hl
    rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, ta, hta, hde⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- β
      rw [denote_lam] at hif'
      split at hif'
      · exact nomatch hif'
      · next A hty =>
        split at hif'
        · exact nomatch hif'
        · next B hbody =>
          obtain rfl : vf' = .lam A B := (Option.some.inj hif').symm
          simp only [Expr.WScoped] at hwf'
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
          have hLty : Expr.LeavesBounded ty := fun l hl =>
            hLf' l (by simp [Expr.fvarLeaves, hl])
          have hCty : CtxOk m.cval env φ d Δ ty :=
            CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCf'
          obtain ⟨hred, hDbeta⟩ :=
            denote_beta_step_certified (Δ := Δ) m φ hcl ihd ihi hta hde hty
              hbody hia hwf'.2.fvarsBelow hws.2 hb.2 hLa hCa
              hwf'.1 hbf'.1 hLty hCty
          -- the contractum's frame conditions
          have hwred : Expr.WScoped d (body.instantiate1 a) :=
            Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2
          have hbred : (body.instantiate1 a).looseBVarsBounded 0 = true :=
            Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2
          have hLred : Expr.LeavesBounded (body.instantiate1 a) :=
            fun l hl => by
              rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
              · exact hLf' l (by simp [Expr.fvarLeaves, h2])
              · exact hLa l h2
          have hCred : CtxOk m.cval env φ d Δ (body.instantiate1 a) := by
            refine ⟨hC.1, fun l hl => ?_⟩
            rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
            · exact hCf'.2 l (by simp [Expr.fvarLeaves, h2])
            · exact hCa.2 l h2
          obtain ⟨w, hw, hDw⟩ := ihwc hbeta hwred hbred hLred hCred hred
          exact ⟨w, hw, (hDapp.trans hDbeta).trans hDw⟩
    · -- ι
      obtain ⟨w, hw, hDio, hwe, hbe, hLe, hCe⟩ :=
        hiota hio hwapp hbapp hLapp hCapp hiapp
      obtain ⟨w', hw', hDw'⟩ := ihwc hwe'' hwe hbe hLe hCe hw
      exact ⟨w', hw', (hDapp.trans hDio).trans hDw'⟩
    · -- stuck
      exact ⟨_, hiapp, hDapp⟩
  · exact nomatch hv

/-! ## The step

The case split is `whnfCoreBody`'s, and every clause is one of: the
subject is its own reduct (the six leaves), the subject is outside the
fragment (`bvar`), or the subject reduces and the claim recurses.  The
three reducing clauses differ only in where their equation comes from —
`zeta` (premise-free), `beta` (one certificate), and the two named
obligations. -/

/-- **`WhnfCoreClaimsTT` at `fuel + 1`.**  Transpose of
`whnfCore_claims`.

`_ihw` is deliberately unconsumed: the reduction-loop claim is needed
by exactly one clause — the projection clause reduces its scrutinee
with `whnf` — and that clause is currently `hproj`.  The binder stays
so that discharging `ProjStepTT` does not change this signature, and
because its absence would misreport which claims this step depends
on. -/
theorem whnfCore_claimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hiota : IotaStepTT m φ fuel) (hproj : ProjStepTT m φ fuel)
    (ihwc : WhnfCoreClaimsTT m φ fuel) (_ihw : WhnfClaimsTT m φ fuel)
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel) :
    WhnfCoreClaimsTT m φ (fuel + 1) := by
  intro d e e' Δ h hws hb hLb hC v hv
  match e with
  | .sort u => exact whnfCore_leaf_claim (Or.inl ⟨u, rfl⟩) h hv
  | .fvar idx n ty =>
    exact whnfCore_leaf_claim (Or.inr (Or.inl ⟨idx, n, ty, rfl⟩)) h hv
  | .forallE n ty body bi =>
    exact whnfCore_leaf_claim
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hv
  | .lam n ty body mb =>
    exact whnfCore_leaf_claim
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩)))) h hv
  | .const n us =>
    exact whnfCore_leaf_claim
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩))))) h hv
  | .lit l =>
    exact whnfCore_leaf_claim
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))))  h hv
  | .bvar i =>
    rw [denote_bvar] at hv
    exact nomatch hv
  | .letE nn tt vv bb =>
    -- ζ: the equation is premise-free, so this clause needs no
    -- certificate and no typing at all
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, whnfCore_def] at h
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hfb : Expr.fvarsBelow d bb := hws.2.2.fvarsBelow
    obtain ⟨W, hW, hDeq⟩ :=
      denote_zeta_step (Δ := Δ) hcl hfb hws.2.1 hb.1.2 hv
    have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
      Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
    have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
    have hLred : Expr.LeavesBounded (bb.instantiate1 vv) := fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
    have hCred : CtxOk m.cval env φ d Δ (bb.instantiate1 vv) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
      · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    obtain ⟨v', hv', hDeq'⟩ := ihwc h hwred hbred hLred hCred hW
    exact ⟨v', hv', hDeq.trans hDeq'⟩
  | .app f a =>
    exact whnfCore_app_claim m φ hcl hiota ihwc ihd ihi h hws hb hLb hC hv
  | .proj sn i pe => exact hproj h hws hb hLb hC hv

/-! ## The delta step

`whnfStep`'s third move: unfold one stored definition.  It is the
cheapest clause in the whole bridge, and the reason is worth a line —
**the reduct denotes to the *same* term, not merely to a `Deq`-equal
one.**  `EnvTT.defn_eq` says a definition's valuation *is* its value's
denotation, so unfolding is invisible to the denotation and the
equation is `rfl`.

Where the model's delta case needs its `val` to agree with the value's
interpretation and then rewrites, the bridge's says the same thing;
what makes it short here is that the two pieces the rewrite needs —
level instantiation composing the assignment (`denote_instLevels`) and
a closed value being depth-independent (`denote_lift` at a closed
valuation) — are both already available. -/

/-- The shared core of the two unfolding branches (`defnInfo` and
`thmInfo`): they differ only in which `EnvTT` field supplies the
value's equation. -/
private theorem delta_core {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {e : Expr} {n : Name} {us : List Level} {cv : ConstantVal}
    {value : Expr} {v : VExpr} {ci : ConstantInfo}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : ∀ ψ : Name → Nat,
      denoteClosed m.cval env ψ value = some (m.cval ci.name ψ))
    (hv : denote m.cval env φ d e = some v) :
    denote m.cval env φ d
      (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
        e.getAppArgs) = some v := by
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e := Expr.mkAppN_getApp e
  rw [← he] at hv
  obtain ⟨vf, vs, hf, hsp, rfl⟩ := denote_mkAppN_inv hv
  rw [hfn, denote_const, hfind] at hf
  simp only [hcvt] at hf
  rw [if_pos hlen] at hf
  obtain rfl : vf = m.cval n (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hf).symm
  -- `find?` matches on the name, so the stored constant is this one
  obtain rfl : ci.name = n := by
    rw [Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  refine denote_mkAppN hsp ?_
  rw [denote_instLevels m.val_params]
  have hfb : Expr.fvarsBelow 0 value :=
    (Expr.WScoped.of_not_hasFvar hnofv).fvarsBelow
  rw [denote_lift hcl hfb d (Nat.zero_le d)]
  have hv0 := hval (Level.substFn φ cv.levelParams us)
  rw [denoteClosed] at hv0
  rw [hv0]
  simp only [Option.map_some, Nat.sub_zero]
  rw [VExpr.liftN_eq_self_of_closed (hcl _ _)]

/-- **The delta step.**  A definition's unfolding denotes identically. -/
theorem denote_delta_step {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {e e' : Expr} {v : VExpr}
    (h : unfoldDefinition env e = some e')
    (hv : denote m.cval env φ d e = some v) :
    denote m.cval env φ d e' = some v := by
  -- read the unfolding apart
  rw [unfoldDefinition] at h
  split at h
  · next n us hfn =>
    split at h
    · next cv value hint hfind =>
      split at h
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj h).symm
        exact delta_core m φ hcl hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ := m.wf _ (find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (fun ψ => m.defn_eq cv value hint (find?_mem hfind) ψ) hv
      · exact nomatch h
    · next cv value hfind =>
      split at h
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj h).symm
        exact delta_core m φ hcl hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, -, -, ht⟩ := m.wf _ (find?_mem hfind)
              exact (ht cv value rfl).1)
          (fun ψ => m.thm_ok cv value (find?_mem hfind) ψ) hv
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-! ## Literals are numerals

The entry point for everything `reduceNat` needs, and the place where
the bridge's `natLitT` and the layer's `numeral` are shown to be the
same term.

They are *defined* the same way — `Nat.succ` applied `n` times to
`Nat.zero` — but over different constants: `natLitT` is built from the
valuation (`cval natZeroName ψ`, `cval natSuccName ψ`) because the
denotation cannot know which term a stored constant means, while
`numeral` is built from the basis constants (`natZeroT`, `natSuccT`)
because the layer has no environment.  `EnvTT.basis_pinned` closes the
gap: `Nat`, `Nat.zero` and `Nat.succ` are reserved basis names, so a
stored declaration under one of them is valued by its pin and by
nothing else.

This is the recipe of `Setlec/TTVerify/DESIGN.md` §5 in one lemma: a
literal denotes to a numeral, and from there the meta-induction
lemmas of `Setlec/TT/Nat/*` apply without any 12345-step derivation. -/

/-- A pinned basis constant is valued by its pin. -/
theorem cval_pinned {env : Env} (m : EnvTT env) {n : Name}
    (hres : reservedBasisNames.contains n = true)
    (hst : (env.find? n).isSome = true) (ψ : Name → Nat) {t : VExpr}
    (hpin : pinnedDirectT n ψ = some t) : m.cval n ψ = t := by
  cases hf : env.find? n with
  | none => rw [hf] at hst; exact nomatch hst
  | some ci => exact m.basis_pinned n ci t hf hres ψ hpin

/-- **A `Nat` literal's term is the layer's numeral.** -/
theorem natLitT_eq_numeral {env : Env} (m : EnvTT env)
    (hg : natLitSupported env = true) (ψ : Name → Nat) :
    ∀ n : Nat,
      natLitT (m.cval natZeroName ψ) (m.cval natSuccName ψ) n
        = numeral n := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, h3⟩ := hg
  have hz : m.cval natZeroName ψ = natZeroT :=
    cval_pinned m (by decide)
      (by revert h2; cases env.find? natZeroName <;> simp [natZeroOk])
      ψ (by
        simp only [pinnedDirectT]
        rw [if_neg (by decide : ¬ (natZeroName = natName))]
        simp [natZeroT])
  have hs : m.cval natSuccName ψ = .const .natSucc [] :=
    cval_pinned m (by decide)
      (by revert h3; cases env.find? natSuccName <;> simp [natSuccOk])
      ψ (by
        simp only [pinnedDirectT]
        rw [if_neg (by decide : ¬ (natSuccName = natName)),
          if_neg (by decide : ¬ (natSuccName = natZeroName))]
        simp)
  intro n
  induction n with
  | zero => rw [natLitT, hz, numeral_zero]
  | succ n ih =>
    rw [natLitT, ih, hs, numeral_succ, natSuccT]

/-- **A `Nat` literal denotes to its numeral.**  The form every
`reduceNat` clause consumes. -/
theorem denote_natLit_numeral {env : Env} (m : EnvTT env)
    (φ : Name → Nat) (hg : natLitSupported env = true) (d n : Nat) :
    denote m.cval env φ d (.lit (.natVal n)) = some (numeral n) := by
  rw [denote_natLit, if_pos hg, natLitT_eq_numeral m hg]

/-! ## The reduction loop

`whnfStep` is three moves — head-normalize, accelerate a literal,
unfold one definition — and `whnfLoop` iterates it on its own budget.
The budget induction is therefore structural and needs nothing from the
`Nat` machinery: it consumes the `whnfCore` claim at the same knot
level, the literal-acceleration obligation, and `denote_delta_step`.

Note which of the three contributes a `Deq` and which does not.  The
`whnfCore` move does (β, ζ, ι, projection all have layer rules); the
literal move does (the recurrences are `Deq`s); the delta move does
not, because it is an identity (§2).  So the loop's accumulated
equation is exactly as long as the number of *non-delta* steps taken,
however many constants were unfolded along the way — which is the
unfolding-strategy independence of §2, visible in the proof term. -/

/-- **The literal-acceleration obligation.**  `reduceNat` replaces an
operation applied to literals by the literal of its value; the
recurrences that justify that live in `EnvTT.nat_ops` and
`EnvTT.div_mod`, and are closed at numerals by meta-induction
(`Setlec/TT/Nat/*`).  Named rather than proved here for the same reason
as the other two: an unproved step is a `Prop` its consumers name. -/
def ReduceNatStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e₂ : Expr} {v : VExpr},
    reduceNatP env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v →
    ∃ w, denote m.cval env φ d e₂ = some w ∧ Deq Δ v w ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOk m.cval env φ d Δ e₂

/-- The budget induction: every iteration of the reduction loop
preserves the denotation up to a derivable equation. -/
theorem whnfLoop_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT m φ fuel) (hnat : ReduceNatStepTT m φ fuel) :
    ∀ (budget : Nat) {d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr},
      whnfLoop (pureFns env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
      denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δ e e' v h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δ e e' v h hws hb hLb hC hv
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, whnfCore_def] at h
    -- move one: head normalization
    cases hwc : whnfCore env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨v₁, hv₁, hD₁⟩ := ihwc hwc hws hb hLb hC hv
    have hws₁ : Expr.WScoped d e₁ := whnfCore_WScoped m.wf fuel hwc hws
    have hb₁ : e₁.looseBVarsBounded 0 = true :=
      whnfCore_looseBVars m.wf fuel hwc hb
    have hLb₁ : Expr.LeavesBounded e₁ := fun l hl =>
      hLb l (whnfCore_fvarLeaves m.wf fuel hwc l hl)
    have hC₁ : CtxOk m.cval env φ d Δ e₁ :=
      CtxOk.of_subset (whnfCore_fvarLeaves m.wf fuel hwc) hC
    -- move two: literal acceleration
    cases hrn : reduceNatP env fuel d e₁ with
    | error err => rw [reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨w, hw, hD₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hv₁
      obtain ⟨v', hv', hD₃⟩ := ih h hws₂ hb₂ hLb₂ hC₂ hw
      exact ⟨v', hv', (hD₁.trans hD₂).trans hD₃⟩
    | none, h =>
      dsimp only at h
      -- move three: delta, which changes no denotation at all
      cases hud : unfoldDefinition env e₁ with
      | none => rw [hud] at h; exact ⟨v₁, (Except.ok.inj h) ▸ hv₁, hD₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        have hw₂ : denote m.cval env φ d e₂ = some v₁ :=
          denote_delta_step m φ hcl hud hv₁
        obtain ⟨v', hv', hD₃⟩ :=
          ih h (unfoldDefinition_WScoped m.wf hud hws₁)
            (unfoldDefinition_looseBVars m.wf hud hb₁)
            (fun l hl => hLb₁ l (unfoldDefinition_fvarLeaves m.wf hud l hl))
            (CtxOk.of_subset (unfoldDefinition_fvarLeaves m.wf hud) hC₁) hw₂
        exact ⟨v', hv', hD₁.trans hD₃⟩

/-- **`WhnfClaimsTT` at `fuel + 1`.**  The reduction loop run at its own
budget; the second quarter of `CheckStepTT`, and the shortest of the
four because `whnfBody` *is* the loop. -/
theorem whnf_claimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT m φ fuel) (hnat : ReduceNatStepTT m φ fuel) :
    WhnfClaimsTT m φ (fuel + 1) := by
  intro d e e' Δ h hws hb hLb hC v hv
  rw [whnf_succ, whnfBody] at h
  exact whnfLoop_claim m φ hcl ihwc hnat whnfLoopFuel h hws hb hLb hC hv

end Setlec.TTVerify
