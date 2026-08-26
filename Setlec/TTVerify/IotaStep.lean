import Setlec.TTVerify.DefEqStep

/-!
# The iota clause

`IotaStepTT` (`Setlec/TTVerify/WhnfCoreStep.lean`): a fired recursor
application denotes to a `Deq`-equal term, with the frame conditions
the recursive `whnfCore` call needs.

**The revised decomposition** (§12.7, after the size estimate was
corrected).  `iotaRec_inv` hands back a *chain*, not a redex:

```
e's major  --whnf-->  major₀  --litMajorToCtor-->  major₁
           --majorToCtor-->  major (in constructor form)
```

and only then does the stored rule fire.  `rec_rules_fire` is proved
**at the fired form**, so the chain owes its own soundness.  Of its
three links, `whnf` is `WhnfClaimsTT` — already proved — and the other
two are checker functions, so the factoring rule (§8.6) puts an
obligation at each.

Both obligations **return** their reduct's frame conditions alongside
the equation, which is the shape `iota_sound`
(`Setlec/Model/Core/Iota.lean`) independently arrived at and
`ReduceNatStepTT` has now used twice: a reduction step's contract is
"the reduct denotes `Deq`-equally *and* is still well-formed", because
the caller needs both and nothing else can supply the second.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- A reduction step's contract, as every link of the chain states it:
the reduct denotes `Deq`-equally and carries its own frame conditions. -/
def ReductOk {env : Env} (m : EnvTT env) (φ : Name → Nat) (d : Nat)
    (Δ : List VExpr) (e' : Expr) (v : VExpr) : Prop :=
  ∃ w, denote m.cval env φ d e' = some w ∧ Deq Δ v w ∧
    Expr.WScoped d e' ∧ e'.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded e' ∧ CtxOk m.cval env φ d Δ e'

/-- **The string-literal major expansion.**  `litMajorToCtor` replaces
a `String` literal major by its constructor form and is the identity
otherwise. -/
def LitMajorToCtorStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr},
    litMajorToCtorP env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v → ReductOk m φ d Δ e' v

/-- **The stuck-major rescues.**  `majorToCtor` replaces a major that
will not whnf to a constructor by a fabrication, certified by
structure eta (`eta_rescue`) or by proof irrelevance
(`proof_irrel_step`) — both proved; what this obligation still owes is
the dispatch between them and the frame conditions. -/
def MajorToCtorStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {c : Name} {rules : List RecRule}
    {e e' : Expr} {v : VExpr},
    majorToCtorP env fuel d c rules e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v → ReductOk m φ d Δ e' v

/-! ## The chain's first link, and a list fact

`whnf` is the one link already proved, so it is stated in the same
`ReductOk` shape as the other two — three links, one contract. -/

/-- The `whnf` link. -/
theorem whnf_reductOk {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr}
    (ihw : WhnfClaimsTT m φ fuel) (hw : whnf env fuel d e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOk m.cval env φ d Δ e)
    (hv : denote m.cval env φ d e = some v) : ReductOk m φ d Δ e' v := by
  obtain ⟨w, hw', hD⟩ := ihw hw hws hb hLb hC hv
  exact ⟨w, hw', hD, whnf_WScoped m.wf fuel hw hws,
    whnf_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnf_fvarLeaves m.wf fuel hw l hl),
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hw) hC⟩

/-- A spine of length `n + 1` splits at its last entry, which is what
`getD n` selects.  The recursor's major premise is exactly that
entry. -/
theorem list_snoc_of_length {α : Type} : ∀ {xs : List α} {n : Nat},
    xs.length = n + 1 → ∃ ys y, xs = ys ++ [y] ∧ ys.length = n ∧
      ∀ dflt, xs.getD n dflt = y := by
  intro xs
  induction xs with
  | nil => intro n h; exact nomatch h
  | cons x xs ih =>
    intro n h
    match n, xs, h with
    | 0, [], _ => exact ⟨[], x, rfl, rfl, fun _ => rfl⟩
    | n + 1, z :: zs, h =>
      obtain ⟨ys, y, heq, hlen, hgd⟩ := ih (n := n) (by simpa using h)
      refine ⟨x :: ys, y, by rw [List.cons_append, ← heq], by simpa using hlen,
        fun dflt => ?_⟩
      simpa [List.getD, List.getElem?_cons_succ] using hgd dflt

/-- **A stored constant's type denotes, at any level instantiation and
any depth.**  The iota clause needs it for the recursor's and the
constructor's telescopes; the same three lemmas the `.const` inference
clause and the delta step used, in the same order.

Worth naming rather than inlining twice: "the stored type denotes" is
the fact, and it is about the environment invariant, not about
recursors. -/
theorem denote_storedTy {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ)) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (us : List Level) (d : Nat) :
    ∃ T, denote m.cval env φ d
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some T := by
  obtain ⟨t, ht, -⟩ :=
    m.has_type ci (find?_mem hf)
      (Level.substFn φ ci.toConstantVal.levelParams us)
  obtain ⟨hnf, -, -, hbd, -⟩ := m.wf ci (find?_mem hf)
  refine ⟨t, ?_⟩
  rw [denote_instLevels m.val_params,
    denote_lift hcl (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow d
      (Nat.zero_le d)]
  rw [denoteClosed] at ht
  rw [ht]
  simp only [Option.map_some, Nat.sub_zero,
    VExpr.liftN_eq_self_of_closed (denote_closed hcl hnf hbd (by
      rw [denoteClosed]; exact ht))]

/-! ## The assembly, and what it is waiting on

The assembly is `iotaRec_inv` → split the spine at the major → run the
three-link chain on it → `rec_rules_fire` at the constructor form →
reassemble.  Every piece above is built and the plumbing is
mechanical, with **one exception found by writing it**:
`rec_rules_fire` takes the rule's right-hand side's denotation as a
*hypothesis*, and nothing produces it.

**`RecRulesTT` should produce it, as the model's `RecRulesOk` does.**
`RecRulesOk` (`Setlec/Model/Interp.lean`) concludes
`∃ Rv, interpClosed … = some Rv ∧ …` — the interpretation of the
rule's closed right-hand side is part of the invariant, established at
install.  The §8.1 restatement made the bridge's version a hypothesis
instead, which is sound (§8.1's rule permits hypotheses about *stored*
expressions) but leaves the caller with an obligation nothing
discharges: a stored `Expr` being closed and `constsResolve`-clean does
not by itself make its denotation `some` — a `.const` at the wrong
level arity denotes to `none`.

So the next step is a field change rather than a proof:

* `RecRulesTT` gains `∃ R, denote … ((RecRule.rhs rl).instantiateLevelParams
  cv.levelParams us) = some R ∧ …` in place of the `some R` hypothesis;
* `RecRulesTT.cons` transports it **forward** with `Installs.denoteUp`,
  which is easier than the `denoteDown` the hypothesis form needed;
* `rec_rules_fire` loses a hypothesis and `iota_stepTT` gains what it
  is missing.

Recorded rather than done because the field change touches the
invariant, its transport and the fire site together, and those land as
one commit.  **The general shape is §8.1's rule read in the other
direction**: that rule says which facts *may* be hypotheses; it does
not say they *should* be.  A fact about a stored expression that no
caller can establish belongs in the conclusion even though the rule
permits it in the premise — and the model, which had the same choice,
made it the other way.
-/

end Setlec.TTVerify
