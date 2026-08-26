import Setlec.TTVerify.DefEqStep
import Setlec.Verify.Deep

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

/-- A spine application splits at its last argument. -/
theorem VExpr_mkAppN_snoc (f : VExpr) : ∀ (xs : List VExpr) (x : VExpr),
    VExpr.mkAppN f (xs ++ [x]) = .app (VExpr.mkAppN f xs) x := by
  intro xs
  induction xs generalizing f with
  | nil => intro x; rfl
  | cons y ys ih => intro x; exact ih (.app f y) x

/-! ## The assembly

`iotaRec_inv` → split the spine at the major → run the three-link chain
on it → `rec_rules_fire` at the constructor form → reassemble.  The
only step that is not bookkeeping is the last `Deq`: the redex as
written and the redex with its major in constructor form differ in one
spine position, so `VExpr_mkAppN_snoc` and `Deq.appArg` bridge them. -/

/-- **`IotaStepTT`**, modulo the chain's two unproved links. -/
theorem iota_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    (ihw : WhnfClaimsTT m φ fuel)
    (hlitm : LitMajorToCtorStepTT m φ fuel)
    (hmajc : MajorToCtorStepTT m φ fuel) : IotaStepTT m φ fuel := by
  intro d Δ e e'' v h hws hb hLb hC hv
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj,
    cnP, cnF, r, cbinders, cbody, residual, cr, usr,
    hfn, hfc, hlenA, hw0, hl0, hm0, hmfn, hfj, hrule, hlenM,
    -, -, hfire, -, -, hcerts, hmcerts, -, -, -, -, rfl⟩ := iotaRec_inv h
  obtain ⟨args, maj, hsplit, hlenA', hgetd⟩ := list_snoc_of_length hlenA
  have heq : e = Expr.mkAppN (.const c us) (args ++ [maj]) := by
    rw [← hsplit, ← hfn, Expr.mkAppN_getApp]
  have hframe : ∀ x ∈ e.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOk m.cval env φ d Δ x := by
    intro x hx
    exact ⟨hws.getAppArgs x hx, looseBVarsBounded_getAppArgs hb x hx,
      fun l hl => hLb l (fvarLeaves_getAppArgs hx l hl),
      CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hC⟩
  obtain ⟨hwmaj, hbmaj, hLmaj, hCmaj⟩ := hframe maj (by rw [hsplit]; simp)
  rw [heq] at hv
  obtain ⟨vf, vs, hvf, hsp, rfl⟩ := denote_mkAppN_inv hv
  obtain ⟨xs, vmaj, rfl, hspx, hvmaj⟩ := DenoteSpine.snoc_inv hsp
  -- the three-link chain on the major premise
  rw [hgetd (Expr.bvar 0)] at hw0
  obtain ⟨w0, hd0, hD0, hw0s, hb0, hL0, hC0⟩ :=
    whnf_reductOk m φ ihw hw0 hwmaj hbmaj hLmaj hCmaj hvmaj
  obtain ⟨w1, hd1, hD1, hw1s, hb1, hL1, hC1⟩ :=
    hlitm hl0 hw0s hb0 hL0 hC0 hd0
  obtain ⟨w2, hd2, hD2, hw2s, hb2, hL2, hC2⟩ :=
    hmajc hm0 hw1s hb1 hL1 hC1 hd1
  -- the head's arity, and the major's, from their denotations
  rw [denote_const, hfc] at hvf
  simp only [ConstantInfo.toConstantVal] at hvf
  by_cases hlenR : us.length = cv.levelParams.length
  · simp only [hlenR, if_true] at hvf
    obtain rfl : vf = m.cval c (Level.substFn φ cv.levelParams us) :=
      (Option.some.inj hvf).symm
    have hmajEq : major = Expr.mkAppN (.const cj usj) major.getAppArgs := by
      rw [← hmfn, Expr.mkAppN_getApp]
    rw [hmajEq] at hd2
    obtain ⟨vfj, ys, hvfj, hspy, rfl⟩ := denote_mkAppN_inv hd2
    rw [denote_const, hfj] at hvfj
    simp only [ConstantInfo.toConstantVal] at hvfj
    by_cases hlenJ : usj.length = cvj.levelParams.length
    · simp only [hlenJ, if_true] at hvfj
      obtain rfl : vfj = m.cval cj (Level.substFn φ cvj.levelParams usj) :=
        (Option.some.inj hvfj).symm
      -- the rule and its constructor
      have hrl : r ∈ rules := List.mem_of_find?_eq_some hrule
      have hrc : RecRule.ctor r = cj := by
        have := List.find?_some hrule
        simpa using this
      -- the two telescope types denote
      obtain ⟨TR, hTR⟩ := denote_storedTy m φ hcl hfc us d
      obtain ⟨TC, hTC⟩ := denote_storedTy m φ hcl hfj usj d
      simp only [ConstantInfo.toConstantVal] at hTR hTC
      -- the stored types' frame conditions (both are closed)
      obtain ⟨hnfR, -, -, hbdR, -, hrules, -⟩ := m.wf _ (find?_mem hfc)
      obtain ⟨hnfC, -, -, hbdC, -, -, -⟩ := m.wf _ (find?_mem hfj)
      simp only [ConstantInfo.toConstantVal] at hnfR hbdR hnfC hbdC
      obtain ⟨hple, -⟩ := m.rec_rules c cv mI rP rules hfc r hrl hfire
      -- the two spines, as `rec_rules_fire` wants them
      rw [hsplit] at hcerts
      have hmajEq' : Expr.mkAppN (.const (RecRule.ctor r) usj)
          major.getAppArgs = major := by rw [hrc]; exact hmajEq.symm
      have htake : (args ++ [maj]).take mI = args := by
        rw [← hlenA']; exact List.take_left
      have hargsR : ∀ x ∈ args ++ [major], Expr.WScoped d x ∧
          x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
          CtxOk m.cval env φ d Δ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hframe x (by rw [hsplit]; exact List.mem_append_left _ hx')
        · obtain rfl : x = major := by simpa using hx'
          exact ⟨hw2s, hb2, hL2, hC2⟩
      have hargsC : ∀ x ∈ major.getAppArgs, Expr.WScoped d x ∧
          x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
          CtxOk m.cval env φ d Δ x := by
        intro x hx
        exact ⟨hw2s.getAppArgs x hx, looseBVarsBounded_getAppArgs hb2 x hx,
          fun l hl => hL2 l (fvarLeaves_getAppArgs hx l hl),
          CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hC2⟩
      -- the redex's two sides denote
      have hmajD : denote m.cval env φ d major =
          some (VExpr.mkAppN
            (m.cval cj (Level.substFn φ cvj.levelParams usj)) ys) := by
        rw [hmajEq]
        exact denote_mkAppN hspy (by
          rw [denote_const, hfj]
          simp only [ConstantInfo.toConstantVal, hlenJ, if_true])
      have hLd : denote m.cval env φ d
          (Expr.mkAppN (.const c us) (args ++ [major])) =
          some (VExpr.mkAppN (m.cval c (Level.substFn φ cv.levelParams us))
            (xs ++ [VExpr.mkAppN
              (m.cval cj (Level.substFn φ cvj.levelParams usj)) ys])) := by
        refine denote_mkAppN (DenoteSpine.append hspx
          (DenoteSpine.cons hmajD .nil)) ?_
        rw [denote_const, hfc]
        simp only [ConstantInfo.toConstantVal, hlenR, if_true]
      obtain ⟨RH, hRH, -⟩ :=
        (m.rec_rules c cv mI rP rules hfc r hrl hfire).2 φ d us hlenR
      have hRd : denote m.cval env φ d
          (Expr.mkAppN
            ((RecRule.rhs r).instantiateLevelParams cv.levelParams us)
            (args.take rP ++ major.getAppArgs.drop (RecRule.ctorParams r)))
          = some (VExpr.mkAppN RH
            (xs.take rP ++ ys.drop (RecRule.ctorParams r))) :=
        denote_mkAppN (DenoteSpine.append (hspx.take rP)
          (hspy.drop (RecRule.ctorParams r))) hRH
      -- fire
      have hfired := rec_rules_fire m φ hcl ihd ihi hfc hrl hfire
        (hrc ▸ hfj) hlenA' hlenM hlenR hlenJ
        (by rw [htake] at hcerts; rw [hmajEq']; exact hcerts)
        (Expr.WScoped.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hnfR))
        (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbdR)
        (Expr.LeavesBounded.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hnfR))
        (⟨hC.1, fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hnfR)] at hl
          exact nomatch hl⟩)
        hTR (by rw [hmajEq']; exact hargsR) hmcerts
        (Expr.WScoped.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC))
        (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbdC)
        (Expr.LeavesBounded.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC))
        (⟨hC.1, fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC)] at hl
          exact nomatch hl⟩)
        hTC hargsC (by rw [hmajEq']; exact hLd) hRd
      -- the reduct's spine is the redex's prefix, since `rP ≤ mI`
      have htakeR : e.getAppArgs.take rP = args.take rP := by
        rw [hsplit]
        exact List.take_append_of_le_length (by omega)
      obtain ⟨hrhsF, -, -, hrhsB, -⟩ := hrules cv mI rP rules rfl r hrl
      refine ⟨VExpr.mkAppN RH (xs.take rP ++ ys.drop (RecRule.ctorParams r)),
        by rw [htakeR]; exact hRd, ?_, ?_, ?_, ?_, ?_⟩
      · -- the redex as written differs from the fired form in one
        -- spine position
        refine Deq.trans ?_ hfired
        rw [VExpr_mkAppN_snoc, VExpr_mkAppN_snoc]
        exact Deq.appArg ((hD0.trans hD1).trans hD2)
      · exact iotaRec_WScoped m.wf h (heq ▸ hws)
      · refine looseBVarsBounded_mkAppN ?_ ?_
        · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hrhsB
        · intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact (hframe x (List.mem_of_mem_take hx')).2.1
          · exact (hargsC x (List.mem_of_mem_drop hx')).2.1
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hrhsF)] at hl'
          exact nomatch hl'
        · rcases List.mem_append.mp hx with hx' | hx'
          · exact (hframe x (List.mem_of_mem_take hx')).2.2.1 l hlx
          · exact (hargsC x (List.mem_of_mem_drop hx')).2.2.1 l hlx
      · refine ⟨hC.1, fun l hl => ?_⟩
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hrhsF)] at hl'
          exact nomatch hl'
        · rcases List.mem_append.mp hx with hx' | hx'
          · exact (hframe x (List.mem_of_mem_take hx')).2.2.2.2 l hlx
          · exact (hargsC x (List.mem_of_mem_drop hx')).2.2.2.2 l hlx
    · simp [hlenJ] at hvfj
  · simp [hlenR] at hvf

/-- `WhnfCoreClaimsTT` at `fuel + 1` with the iota clause discharged;
only the projection clause remains. -/
theorem whnfCore_claimsTT_iota {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hlitm : LitMajorToCtorStepTT m φ fuel)
    (hmajc : MajorToCtorStepTT m φ fuel)
    (hproj : ProjStepTT m φ fuel)
    (ihwc : WhnfCoreClaimsTT m φ fuel) (ihw : WhnfClaimsTT m φ fuel)
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel) :
    WhnfCoreClaimsTT m φ (fuel + 1) :=
  whnfCore_claimsTT m φ hcl (iota_stepTT m φ hcl ihd ihi ihw hlitm hmajc)
    hproj ihwc ihw ihd ihi

end Setlec.TTVerify
