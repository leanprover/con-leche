import Setlec.TTVerify.DefEqStep
import Setlec.Verify.Denote.OpenRevDenote
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

/- Task #147: this file's lemmas are stated at the TT-lane mode — the
seven gated checks reduce definitionally at `.ttModel`, so the walks
below see the pre-#147 bodies (`CertifiedConfigTT` pins the running
mode to this value). -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- **The string-literal major expansion.**  `litMajorToCtor` replaces
a `String` literal major by its constructor form and is the identity
otherwise. -/
def LitMajorToCtorStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr},
    litMajorToCtorP mode env fuel d e = .ok e' →
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
    majorToCtorP mode env fuel d c rules e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v → ReductOk m φ d Δ e' v

/-! ## A list fact -/

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

/-! ## The assembly

`iotaRec_inv` → split the spine at the major → run the three-link chain
on it → `rec_rules_fire` at the constructor form → reassemble.  The
only step that is not bookkeeping is the last `Deq`: the redex as
written and the redex with its major in constructor form differ in one
spine position, so `VExpr_mkAppN_snoc` and `Deq.appArg` bridge them. -/

/-- **`IotaStepTT`**, modulo the chain's two unproved links. -/
theorem iota_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel)
    (ihw : WhnfClaimsTT mode m φ fuel)
    (hlitm : LitMajorToCtorStepTT m φ fuel)
    (hmajc : MajorToCtorStepTT m φ fuel) : IotaStepTT m φ fuel := by
  intro d Δ e e'' v h hws hb hLb hC hv
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj,
    cnP, cnF, r, cbinders, cbody, residual, cr, usr,
    hfn, hfc, hlenA, hw0, hl0, hm0, hmfn, hfj, hrule, hlenM,
    -, -, hfire, hlev, hdefl, hcerts, hmcerts, -, hresid, -, hidxde, rfl⟩ := iotaRec_inv h
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
      -- **the fire site's parameter test.**  `iotaRec` compares the
      -- constructor's parameters against the rule's comparands — for a
      -- plain rule, the recursor's own leading arguments — and the law
      -- is stated only where that comparison passed.  Discarding this
      -- conjunct (as this proof did until `Quot`) makes the law
      -- quantify over spines no fire site supplies, and `Quot`'s two
      -- eliminators are then not provable at all.
      have hparP : RecRule.fire r = .plain →
          ∀ i, i < RecRule.ctorParams r → i < mI →
            ∀ a b : VExpr,
              denote m.cval env φ d (major.getAppArgs.getD i default)
                = some a →
              denote m.cval env φ d (args.getD i default) = some b →
              Deq Δ a b := by
        intro hplain i hi hiM a b ha hb
        have hcmp : (recFireComparands r cv.levelParams us cvj.levelParams
            e.getAppArgs rP).2
            = e.getAppArgs.take (RecRule.ctorParams r) := by
          simp [recFireComparands, hplain]
        rw [hcmp] at hdefl
        obtain ⟨hlenD, hall⟩ := defEqList_inv hdefl
        have hiM' : i < major.getAppArgs.length := by omega
        have hiA : i < args.length := by omega
        have hiT : i < (major.getAppArgs.take
            (RecRule.ctorParams r)).length := by
          rw [List.length_take]; omega
        have hde := hall ⟨i, hiT⟩
        simp only [Fin.getElem_fin] at hde
        rw [show (major.getAppArgs.take (RecRule.ctorParams r))[i]
            = major.getAppArgs[i] from by simp [List.getElem_take],
          show (e.getAppArgs.take (RecRule.ctorParams r)).getD i default
            = args[i] from by
            rw [hsplit]
            simp [List.getD, hi,
              List.getElem?_append_left hiA,
              List.getElem?_eq_getElem hiA]] at hde
        obtain ⟨hwC', hbC', hLC', hCC'⟩ := hargsC major.getAppArgs[i]
          (List.getElem_mem hiM')
        obtain ⟨hwA', hbA', hLA', hCA'⟩ := hframe args[i] (by
          rw [hsplit]; exact List.mem_append_left _ (List.getElem_mem hiA))
        rw [show major.getAppArgs.getD i default = major.getAppArgs[i] from
          by simp [List.getD, List.getElem?_eq_getElem hiM']] at ha
        rw [show args.getD i default = args[i] from
          by simp [List.getD, List.getElem?_eq_getElem hiA]] at hb
        exact ihd hde hwC' hbC' hLC' hwA' hbA' hLA' hCC' hCA' ha hb
      -- the fire site's **index** test (§15): `iotaRec` compares the
      -- constructor's canonical index tuple against the recursor's own
      -- index arguments, and the inversion already hands both over —
      -- `IotaStep` had been destructuring past them
      rw [hsplit, htake] at hidxde
      have hwCty : Expr.WScoped d
          (cvj.type.instantiateLevelParams cvj.levelParams usj) :=
        Expr.WScoped.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC)
      have hwRes : Expr.WScoped d residual :=
        piResidual_WScoped hresid hwCty (fun x hx => (hargsC x hx).1)
      have hbRes : residual.looseBVarsBounded 0 = true :=
        piResidual_looseBVars hresid
          (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbdC)
          (fun x hx => (hargsC x hx).2.1)
      have hleafRes : ∀ l ∈ residual.fvarLeaves,
          ∃ x ∈ major.getAppArgs, l ∈ x.fvarLeaves := by
        intro l hl
        rcases piResidual_fvarLeaves hresid l hl with h1 | h2
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC)] at h1
          exact nomatch h1
        · exact h2
      have hLRes : Expr.LeavesBounded residual := by
        intro l hl
        obtain ⟨x, hx, hlx⟩ := hleafRes l hl
        exact (hargsC x hx).2.2.1 l hlx
      have hCRes : CtxOk m.cval env φ d Δ residual := by
        refine ⟨hC.1, fun l hl => ?_⟩
        obtain ⟨x, hx, hlx⟩ := hleafRes l hl
        exact (hargsC x hx).2.2.2.2 l hlx
      obtain ⟨hlenD, hall⟩ := defEqList_inv hidxde
      have hlenIdxP : (residual.getAppArgs.drop (RecRule.ctorParams r)).length
          = mI - rP := by
        rw [hlenD, List.length_drop, hlenA']
      have hidxG : ∀ i, i < mI - rP → ∀ a b : VExpr,
          denote m.cval env φ d
            ((residual.getAppArgs.drop (RecRule.ctorParams r)).getD i default)
            = some a →
          denote m.cval env φ d ((args.drop rP).getD i default) = some b →
          Deq Δ a b := by
        intro i hi a b ha hb
        have hiL : i < (residual.getAppArgs.drop
            (RecRule.ctorParams r)).length := by omega
        have hiR : i < (args.drop rP).length := by
          rw [List.length_drop]; omega
        have hde := hall ⟨i, hiL⟩
        simp only [Fin.getElem_fin] at hde
        rw [show (residual.getAppArgs.drop (RecRule.ctorParams r))[i]
            = (residual.getAppArgs.drop (RecRule.ctorParams r)).getD i default
            from by simp [List.getD, List.getElem?_eq_getElem hiL]] at hde
        obtain ⟨hwL, hbL, hLL, hCL⟩ :
            Expr.WScoped d ((residual.getAppArgs.drop
              (RecRule.ctorParams r)).getD i default) ∧
            ((residual.getAppArgs.drop (RecRule.ctorParams r)).getD i
              default).looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded ((residual.getAppArgs.drop
              (RecRule.ctorParams r)).getD i default) ∧
            CtxOk m.cval env φ d Δ ((residual.getAppArgs.drop
              (RecRule.ctorParams r)).getD i default) := by
          have hmem : (residual.getAppArgs.drop
              (RecRule.ctorParams r)).getD i default ∈ residual.getAppArgs := by
            rw [show (residual.getAppArgs.drop (RecRule.ctorParams r)).getD i
                default = (residual.getAppArgs.drop (RecRule.ctorParams r))[i]
                from by simp [List.getD, List.getElem?_eq_getElem hiL]]
            exact List.mem_of_mem_drop (List.getElem_mem hiL)
          exact ⟨hwRes.getAppArgs _ hmem,
            looseBVarsBounded_getAppArgs hbRes _ hmem,
            fun l hl => hLRes l (fvarLeaves_getAppArgs hmem l hl),
            CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hmem l hl) hCRes⟩
        obtain ⟨hwR', hbR', hLR', hCR'⟩ : Expr.WScoped d
            ((args.drop rP).getD i default) ∧
            ((args.drop rP).getD i default).looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded ((args.drop rP).getD i default) ∧
            CtxOk m.cval env φ d Δ ((args.drop rP).getD i default) := by
          have hmem : (args.drop rP).getD i default ∈ e.getAppArgs := by
            rw [hsplit]
            refine List.mem_append_left _ ?_
            rw [show (args.drop rP).getD i default = (args.drop rP)[i] from by
              simp [List.getD, List.getElem?_eq_getElem hiR]]
            exact List.mem_of_mem_drop (List.getElem_mem hiR)
          exact hframe _ hmem
        exact ihd hde hwL hbL hLL hwR' hbR' hLR' hCL hCR' ha hb
      -- **the fire site's nested parameter test** (§17.4): `iotaRec`
      -- compares the constructor's parameters against the stored pins
      -- instantiated at the rule prefix; the law meets it at the
      -- pins' base-0 reverse opening (`denote_openRev`)
      have htakeR0 : e.getAppArgs.take rP = args.take rP := by
        rw [hsplit]
        exact List.take_append_of_le_length (by omega)
      have hparNP : ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          ∀ i, i < RecRule.ctorParams r →
          ∀ (a : VExpr) (vxs : List VExpr),
            denote m.cval env φ d (major.getAppArgs.getD i default)
              = some a →
            DenoteSpine m.cval env φ d (args.take rP) vxs →
            ∀ vp : VExpr,
              denote m.cval env φ rP (openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vp →
              Deq Δ a (VExpr.instRevChain vxs vp) := by
        intro lvls pins hn i hi a vxs ha hvxs vp hvp
        have hcmp : (recFireComparands r cv.levelParams us
            cvj.levelParams e.getAppArgs rP).2 = pins.map (fun p =>
              Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                (p.instantiateLevelParams cv.levelParams us)) := by
          simp [recFireComparands, hn]
        rw [hcmp] at hdefl
        obtain ⟨hlenD, hall⟩ := defEqList_inv hdefl
        rw [List.length_take, List.length_map] at hlenD
        have hpinslen : pins.length = RecRule.ctorParams r := by
          have h0 : major.getAppArgs.length =
              RecRule.ctorParams r + RecRule.nfields r := hlenM
          omega
        -- the stored pin's syntactic facts
        obtain ⟨-, -, -, -, hnested⟩ := hrules cv mI rP rules rfl r hrl
        obtain ⟨-, -, hpinsWf, -⟩ := hnested lvls pins hn
        have hpinmem : pins.getD i default ∈ pins := by
          refine List.mem_of_getElem? (i := i) ?_
          simp [List.getD, List.getElem?_eq_getElem
            (show i < pins.length from by omega)]
        obtain ⟨hpinF, hpinLp, hpinRes, hpinB⟩ := hpinsWf _ hpinmem
        -- the comparand at this position
        have hiT : i < (major.getAppArgs.take
            (RecRule.ctorParams r)).length := by
          rw [List.length_take]
          have h0 : major.getAppArgs.length =
              RecRule.ctorParams r + RecRule.nfields r := hlenM
          omega
        have hde := hall ⟨i, hiT⟩
        simp only [Fin.getElem_fin] at hde
        rw [show (major.getAppArgs.take (RecRule.ctorParams r))[i]
            = major.getAppArgs[i] from by simp [List.getElem_take],
          show (pins.map (fun p => Expr.instSpine
              (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))).getD i
              default = Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us) from by
            simp only [List.getD, List.getElem?_map,
              List.getElem?_eq_getElem
                (show i < pins.length from by omega)]
            rfl] at hde
        -- the argument prefix's facts
        have hargsPre : ∀ x ∈ args.take rP, Expr.WScoped d x ∧
            x.looseBVarsBounded 0 = true ∧ Expr.fvarsBelow d x := by
          intro x hx
          have hx' : x ∈ e.getAppArgs := by
            rw [hsplit]
            exact List.mem_append_left _ (List.mem_of_mem_take hx)
          obtain ⟨hw, hb2, -, -⟩ := hframe x hx'
          exact ⟨hw, hb2, hw.fvarsBelow⟩
        have hprelen : (args.take rP).length = rP := by
          rw [List.length_take]
          omega
        -- the pin, instantiated at the prefix, denotes through the
        -- base-0 reverse opening
        have hpinF' : (Expr.instantiateLevelParams cv.levelParams us
            (pins.getD i default)).hasFvar = false := by
          rw [Expr.hasFvar_instantiateLevelParams]
          exact hpinF
        have hpinB' : (Expr.instantiateLevelParams cv.levelParams us
            (pins.getD i default)).looseBVarsBounded
            (args.take rP).length = true := by
          rw [Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
          exact hpinB
        have hcden := denote_openRev hcl (args.take rP) hargsPre
          ((Expr.WScoped.of_not_hasFvar (d := d) hpinF').fvarsBelow)
          hpinB' hvxs
        rw [hprelen] at hcden
        have hbase := denote_openRev_base (env := env) (φ := φ) hcl
          hpinF' (by
            rw [Expr.looseBVarsBounded_instantiateLevelParams]
            exact hpinB) d
        rw [hbase, hvp] at hcden
        rw [Expr.instSpine_eq_instSeq, htakeR0] at hde
        -- the comparand's frame facts, and the claims
        have hcw : Expr.WScoped d (Expr.instSeq (args.take rP) (rP - 1)
            (Expr.instantiateLevelParams cv.levelParams us
              (pins.getD i default))) := by
          rw [← Expr.instSpine_eq_instSeq]
          exact instSpine_WScoped _
            (Expr.WScoped.of_not_hasFvar hpinF')
            (fun x hx => (hargsPre x hx).1)
        have hcb : (Expr.instSeq (args.take rP) (rP - 1)
            (Expr.instantiateLevelParams cv.levelParams us
              (pins.getD i default))).looseBVarsBounded 0 = true := by
          rw [← Expr.instSpine_eq_instSeq,
            show rP - 1 = (args.take rP).length - 1 from by
              rw [hprelen]]
          exact instSpine_closed (fun x hx => (hargsPre x hx).2.1) hpinB'
        have hcL : Expr.LeavesBounded (Expr.instSeq (args.take rP)
            (rP - 1) (Expr.instantiateLevelParams cv.levelParams us
              (pins.getD i default))) := by
          intro l hl
          rw [← Expr.instSpine_eq_instSeq] at hl
          rcases fvarLeaves_instSpine _ hl with h1 | ⟨x, hx, hlx⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF'] at h1
            exact nomatch h1
          · have hx' : x ∈ e.getAppArgs := by
              rw [hsplit]
              exact List.mem_append_left _ (List.mem_of_mem_take hx)
            exact (hframe x hx').2.2.1 l hlx
        have hcC : CtxOk m.cval env φ d Δ (Expr.instSeq (args.take rP)
            (rP - 1) (Expr.instantiateLevelParams cv.levelParams us
              (pins.getD i default))) := by
          refine ⟨hC.1, fun l hl => ?_⟩
          rw [← Expr.instSpine_eq_instSeq] at hl
          rcases fvarLeaves_instSpine _ hl with h1 | ⟨x, hx, hlx⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF'] at h1
            exact nomatch h1
          · have hx' : x ∈ e.getAppArgs := by
              rw [hsplit]
              exact List.mem_append_left _ (List.mem_of_mem_take hx)
            exact (hframe x hx').2.2.2.2 l hlx
        simp only [Option.map_some] at hcden
        -- the constructor argument's own facts, and the claims
        have hiM2 : i < major.getAppArgs.length := by omega
        obtain ⟨hwA, hbA, hLA, hCA⟩ := hargsC major.getAppArgs[i]
          (List.getElem_mem hiM2)
        rw [show major.getAppArgs.getD i default = major.getAppArgs[i]
          from by simp [List.getD, List.getElem?_eq_getElem hiM2]] at ha
        exact ihd hde hwA hbA hLA hcw hcb hcL hCA hcC ha hcden
      -- fire
      have hfired := rec_rules_fire m φ hcl ihd ihi hfc hrl hfire
        (hrc ▸ hfj) hlenA' hlenM hlenR hlenJ
        (by
          rw [Level.substFn_congr (ks := cvj.levelParams)
              (Level.isEquivList_sound hlev φ),
            recFireComparands_levels r cv.levelParams us cvj.levelParams
              e.getAppArgs [] rP rP])
        hparP hparNP hresid hlenIdxP hidxG
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

/-- **`WhnfCoreClaimsTT` at `fuel + 1`**, with both clauses discharged:
three obligations remain, all at checker functions the chains pass
through. -/
theorem whnfCore_claimsTT_iota {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hlitm : LitMajorToCtorStepTT m φ fuel)
    (hmajc : MajorToCtorStepTT m φ fuel)
    (hlitp : ProjLitToCtorStepTT m φ fuel)
    (ihwc : WhnfCoreClaimsTT mode m φ fuel) (ihw : WhnfClaimsTT mode m φ fuel)
    (ihd : DefEqClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel) :
    WhnfCoreClaimsTT mode m φ (fuel + 1) :=
  whnfCore_claimsTT m φ hcl (iota_stepTT m φ hcl ihd ihi ihw hlitm hmajc)
    (proj_stepTT m φ hcl ihwc ihw ihd ihi hlitp) ihwc ihw ihd ihi

end Setlec.TTVerify
