import Setlec.SetR.Interp2.IndPointKitP
import Setlec.SetR.Interp2.IndProjEtaP

/-!
# The point stage, at the reading (task #161, IND TIER part 5)

`pointS`'s transpose: the checked statement's left-hand side, read at
the fired chain, **is** the redex — the recursor's leaf applied to the
`xs` and to the canonical constructor application at `ys`.

Position by position, exactly as in v1:

* a **prefix** position is a frame opener, and its reading is a `.bvar`
  the chain resolves to the corresponding `xs` slot;
* an **index** position crosses: the recorded index run identifies the
  statement's argument with the constructor residual's, the residual
  crosses to the constructor tower's body along the mixed spine
  (`instPisAt_denoteP_cross`), and the fired `IotaIndexPinP` pins that
  body's trailing arguments to the recursor's own index arguments;
* the **major** is the constructor application, matched up to
  `ErasedEq` (the nested pin's own form) and reconciled through the
  mixed spine's readings.

**The P delta is the index walk's two gradings, and both are
projections.**  `DefEqClaims2P` wants the a-side — an argument of the
statement's left-hand side — and the b-side — an argument of the
constructor residual — graded.  The a-side comes from the statement
side's own grading (`hokLhs`, which the bottom reads off the
`checkIotaSidesTy` inference run `IotaRunsR` records) by
`AnnotOkP_mkAppN_args`; the b-side from `instPisAt_resP_graded` at the
run's completed spine memberships (`hspMem`), again by
`AnnotOkP_mkAppN_args`.  The spine memberships are the zipper's own
position induction read at its top padding, so the stage adds two
premises and no new mathematics.

The other P tax is the one part 4 recorded: a run is a datum about
syntax, so the two comparands' `WScoped`/`looseBVarsBounded`/
`LeavesBounded` frames — which a `DefEqAtW` derivation carried — are
premises here.  They descend from the statement's own
(`Expr.WScoped.getAppArgs` and friends) and from the constructor run's
residual (`instPisAt_WScoped`/`instPisAt_bounded`, residual halves).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  isDefEqCore DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 12800000 in
/-- **The point stage, at the reading** (`pointS`). -/
theorem pointP {m : EnvS2Core V env} {F : Nat} {ψ' : Name → Nat}
    (hclaims : DefEqClaims2P μ m ψ' F)
    {lps : List Name}
    {f : Name → Name} (hroT : RenameOkP m.acval env f)
    {Rn : Name}
    {rP cnP cnF mI : Nat} {xs ys zs : List AVExpr} {ρ : Nat → V}
    (hzs : zs = xs.take rP ++ ys.drop cnP)
    (hrPmI : rP ≤ mI) (hlenX : xs.length = mI)
    (hlenY : ys.length = cnP + cnF)
    {ctor : Name} {cvj : ConstantVal} {usj : List Level}
    {ciRm : ConstantInfo} (hfRnE : env.find? (f Rn) = some ciRm)
    (hRmlps : ciRm.toConstantVal.levelParams = lps)
    -- the statement frame
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hlbFvs : ∀ (i : Nat) (nm : Name) (ty : Expr),
      Expr.fvar i nm ty ∈ fvs → ty.looseBVarsBounded 0 = true)
    {Tstmt : AVExpr} {Γs : List AVExpr} {Rbody : AVExpr}
    (htowerS : PiTeleP (rP + cnF) Tstmt Γs Rbody)
    (hokTst : ∀ σ : Nat → V, AnnotOkP V σ Tstmt)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteP m.acval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    -- the ambient context, and the fired chain in it
    {Δa : List AVExpr} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < rP + cnF →
      Δa[rP + cnF - 1 - i]? = some (Γs.getD (rP + cnF - 1 - i) default))
    (hsat : Sat2 V Δa (chainP V ρ zs))
    -- the statement's left-hand side
    {lhsS : Expr} {vL : AVExpr}
    (hvL : denoteP m.acval env ψ' (rP + cnF) lhsS = some vL)
    (hwsLhs : Expr.WScoped (rP + cnF) lhsS)
    (hbLhs : lhsS.looseBVarsBounded 0 = true)
    (hokLhs : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ vL)
    (hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    {ctorHead : Expr} {sp : List Expr}
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN ctorHead sp))
    (hctorHead : denoteP m.acval env ψ' (rP + cnF) ctorHead
      = some (m.acval ctor (Level.substFn φ cvj.levelParams usj)))
    (hleafLhs : ∀ l ∈ lhsS.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltLhs : ∀ l ∈ lhsS.fvarLeaves, l.1 < rP + cnF)
    -- the constructor's type and run at the statement frame
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : AVExpr}
    (hTVjK : denoteP m.acval env ψ' (rP + cnF) ctyR = some TVj)
    (hokTVj : ∀ σ : Nat → V, AnnotOkP V σ TVj)
    (hTVjcl : ∀ k : Nat, TVj.liftN 1 k = TVj)
    {Γj : List AVExpr} {Rj : AVExpr}
    (htowerJ : PiTeleP (cnP + cnF) TVj Γj Rj)
    (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    -- the run's spine memberships (the zipper's induction, at its top)
    (hspMem : ∀ σ : Nat → V, Sat2 V Δa σ →
      ∀ (q : Nat) (x : Expr), sp[q]? = some x →
        ∃ w, denoteP m.acval env ψ' (rP + cnF) x = some w ∧
          AnnotOkP V σ w ∧
          ∀ dw, denoteP m.acval env ψ' (rP + cnF)
              (cdoms.getD q default) = some dw →
            interp2 V σ w ∈ˢ interp2 V σ dw)
    {vHC : AVExpr} {vArgsC : List AVExpr}
    (hRjdec : Rj = AVExpr.mkAppN vHC vArgsC)
    (hArgsClen : vArgsC.length = cnP + (mI - rP))
    -- the recorded index run
    (hdeIdx : DefEqListOk μ F env (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    {mix : List AVExpr} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denoteP m.acval env ψ' (rP + cnF) x = some w0 ∧
        mix[q]? = some (AVExpr.instSeq zs (rP + cnF - 1) w0))
    (hmixVal : ∀ q, q < cnP + cnF →
      interp2 V ρ (mix.getD q default) = interp2 V ρ (ys.getD q default))
    {restC : AVExpr} (hfitC : TeleFitPA V ρ TVj ys restC)
    (hidx : IotaIndexPinP (V := V) ρ restC cnP mI rP xs) :
    interp2 V (chainP V ρ zs) vL
      = interp2 V ρ
          (AVExpr.mkAppN (m.acval Rn ψ')
            (xs ++ [AVExpr.mkAppN
              (m.acval ctor (Level.substFn φ cvj.levelParams usj))
              ys])) := by
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : zs.length = rP + cnF := by
    rw [hzs, List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hzsPre : ∀ n, n < rP → zs.getD n default = xs.getD n default := by
    intro n hn
    rw [hzs, List.getD, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hn]
    rfl
  -- the openers' gradings at the ambient context
  have hokAll : ∀ i, i < rP + cnF → ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V (fun j => σ (j + (rP + cnF - 1 - i) + 1))
        (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i hi σ hσ
    refine annotOkP_tower_slot (rP + cnF) htowerS (hokTst _)
      (rP + cnF - 1 - i) (by omega) (fun q hq1 hq2 => ?_)
    refine hσ q (Γs.getD q default) ?_
    have h := hΔaent (rP + cnF - 1 - q) (by omega)
    rw [show rP + cnF - 1 - (rP + cnF - 1 - q) = q from by omega] at h
    exact h
  -- shared scattered-spine facts
  have hspFacts : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      (∃ w, denoteP m.acval env ψ' (rP + cnF) x = some w) ∧
        Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨w0, hw0, _⟩ := hmixsp q x hx
    exact ⟨⟨w0, hw0⟩, hspScope q x hx⟩
  have hfbCty : Expr.fvarsBelow (rP + cnF) ctyR := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hl
    exact nomatch hl
  have hfvsLt : ∀ l : Nat × Name × Expr,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨nm', ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1, ← hfvslen]
    exact hql
  -- the residual's syntactic frame
  have hspAll : ∀ a ∈ sp, Expr.WScoped (rP + cnF) a ∧
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    exact hspScope q a hq
  have hwsCres : Expr.WScoped (rP + cnF) cres :=
    (instPisAt_WScoped sp ctyR hcinst
      (Expr.WScoped.of_not_hasFvar hCwR)
      (fun a ha => (hspAll a ha).1)).2
  have hbCres : cres.looseBVarsBounded 0 = true :=
    (instPisAt_bounded sp hcinst hCbR (fun a ha => (hspAll a ha).2)).2
  -- the residual reads, and is graded
  obtain ⟨vCres, hvCres⟩ := instPisAt_denoteP_defined m.acval_closed
    (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
      (fun k' => m.acval_closed n ψ k') y k)
    _ hcinst (D := rP + cnF) hspFacts hfbCty hCbR hTVjK
  have hokCres : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ vCres := by
    intro σ hσ
    exact instPisAt_resP_graded (ρ' := σ) m.acval_closed
      (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
        (fun k' => m.acval_closed n ψ k') y k)
      _ hcinst hspScope hfbCty hCbR hTVjK (hokTVj _) (hspMem σ hσ)
      vCres hvCres
  -- the head of the statement's lhs is the recursor's leaf
  have hconstDen : ∀ (c : Name) (ci : ConstantInfo) (ks : List Name),
      env.find? c = some ci → ci.toConstantVal.levelParams = ks →
      denoteP m.acval env ψ' (rP + cnF) (.const c (ks.map .param))
        = some (m.acval c ψ') := by
    intro c ci ks hf hlp
    rw [denoteP_const hf (by rw [hlp, List.length_map]), hlp,
      show Level.substFn ψ' ks (ks.map .param) = ψ' from
        funext fun _ => Level.substFn_map_param]
  -- decompose the lhs
  have hlhsApp : lhsS = Expr.mkAppN
      (.const (f Rn) (lps.map .param)) lhsS.getAppArgs := by
    rw [← hlhead]
    exact (Expr.mkAppN_getApp lhsS).symm
  rw [hlhsApp] at hvL
  obtain ⟨vLf, vLargs, hvLf, hLspine, rfl⟩ := denoteP_mkAppN_inv hvL
  have hvLargsLen : vLargs.length = mI + 1 := by
    rw [← hLspine.length, hlarity]
  have hvLfEq : vLf = m.acval Rn ψ' := by
    rw [hconstDen (f Rn) ciRm lps hfRnE hRmlps] at hvLf
    rw [hroT.2.2] at hvLf
    exact (Option.some.inj hvLf).symm
  have hokArgs : ∀ σ : Nat → V, Sat2 V Δa σ →
      ∀ a ∈ vLargs, AnnotOkP V σ a := by
    intro σ hσ a ha
    have h := hokLhs σ hσ
    exact AnnotOkP_mkAppN_args vLargs h a ha
  -- reduce to the mapped spine equality
  rw [hvLfEq, interp2_mkAppN_map, interp2_mkAppN_map,
    interp2_closed (V := V)
      (by rw [m.acval_erase]; exact m.base.cval_closed Rn ψ')
      (chainP V ρ zs) ρ]
  suffices hmap : vLargs.map (interp2 V (chainP V ρ zs))
      = (xs ++ [AVExpr.mkAppN
          (m.acval ctor (Level.substFn φ cvj.levelParams usj)) ys]).map
          (interp2 V ρ) by
    rw [hmap]
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i (mI + 1) with hi | hi
  · rcases hai : lhsS.getAppArgs[i]? with _ | ai
    · rw [List.getElem?_eq_none_iff, hlarity] at hai
      omega
    obtain ⟨vi, hvi, hdi⟩ := denoteSpineP_getElem?' hLspine i ai hai
    rw [hvi]
    rcases Nat.lt_or_ge i rP with hiP | hiP
    · -- prefix branch
      have hlargsFv : lhsS.getAppArgs[i]? = fvs[i]? := by
        have h1 := congrArg (fun l => l[i]?) hlpre
        simp only [List.getElem?_take_of_lt hiP] at h1
        exact h1
      obtain ⟨nm, ty, rfl⟩ := hshapeS i ai (by rw [← hlargsFv]; exact hai)
      rw [denoteP_fvar] at hdi
      obtain rfl : vi = .bvar (rP + cnF - 1 - i) :=
        (Option.some.inj hdi).symm
      rw [List.getElem?_append_left (by rw [hlenX]; omega)]
      rcases hx : xs[i]? with _ | xv
      · rw [List.getElem?_eq_none_iff, hlenX] at hx
        omega
      have hgx : xs.getD i default = xv := by
        rw [List.getD, hx]
        rfl
      have hbb : rP + cnF - 1 - i < zs.length := by
        rw [hzslen]
        omega
      rw [Option.map_some, Option.map_some, interp2_bvar, chainP_lt hbb,
        hzslen, show rP + cnF - 1 - (rP + cnF - 1 - i) = i from by omega,
        hzsPre i hiP, hgx]
    · rcases Nat.lt_or_ge i mI with hiM | hiM
      · -- index branch
        have hj : i - rP < mI - rP := by omega
        have hlenL : ((lhsS.getAppArgs.drop rP).take (mI - rP)).length
            = mI - rP := by
          rw [List.length_take, List.length_drop, hlarity]
          omega
        have hLsub : ((lhsS.getAppArgs.drop rP).take (mI - rP)).getD
              (i - rP) default = ai := by
          rw [List.getD, List.getElem?_take_of_lt hj, List.getElem?_drop,
            show rP + (i - rP) = i from by omega, hai]
          rfl
        rcases hbx : cres.getAppArgs[cnP + (i - rP)]? with _ | bx
        · rw [List.getElem?_eq_none_iff, hclen] at hbx
          omega
        have hRsub : (cres.getAppArgs.drop cnP).getD (i - rP) default
            = bx := by
          rw [List.getD, List.getElem?_drop, hbx]
          rfl
        have hrun : isDefEqCore μ env F (rP + cnF) ai bx = .ok true := by
          have h := defEqListOk_getD hdeIdx (i - rP) (by rw [hlenL]; omega)
          rw [hLsub, hRsub] at h
          exact h
        -- leaves of the two subjects
        have hleafA : ∀ l ∈ ai.fvarLeaves,
            Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
          intro l hl
          exact hleafLhs l
            (fvarLeaves_getAppArgs (List.mem_of_getElem? hai) l hl)
        have hltA : ∀ l ∈ ai.fvarLeaves, l.1 < rP + cnF := by
          intro l hl
          exact hltLhs l
            (fvarLeaves_getAppArgs (List.mem_of_getElem? hai) l hl)
        have hleafB : ∀ l ∈ bx.fvarLeaves,
            Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
          intro l hl
          have hlc : l ∈ cres.fvarLeaves :=
            fvarLeaves_getAppArgs (List.mem_of_getElem? hbx) l hl
          rcases instPisAt_leaves _ hcinst l (Or.inr hlc) with
            hty | ⟨a, ha, hla⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hty
            exact nomatch hty
          · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
            exact (hspLeaf q _ hq l hla).1
        have hltB : ∀ l ∈ bx.fvarLeaves, l.1 < rP + cnF := by
          intro l hl
          exact hfvsLt l (hleafB l hl)
        -- the two subjects' syntactic frames
        have hwsA : Expr.WScoped (rP + cnF) ai :=
          hwsLhs.getAppArgs ai (List.mem_of_getElem? hai)
        have hbA : ai.looseBVarsBounded 0 = true :=
          Setlec.looseBVarsBounded_getAppArgs hbLhs ai
            (List.mem_of_getElem? hai)
        have hLA : Expr.LeavesBounded ai := fun l hl =>
          hlbFvs l.1 l.2.1 l.2.2 (hleafA l hl)
        have hwsB : Expr.WScoped (rP + cnF) bx :=
          hwsCres.getAppArgs bx (List.mem_of_getElem? hbx)
        have hbB : bx.looseBVarsBounded 0 = true :=
          Setlec.looseBVarsBounded_getAppArgs hbCres bx
            (List.mem_of_getElem? hbx)
        have hLB : Expr.LeavesBounded bx := fun l hl =>
          hlbFvs l.1 l.2.1 l.2.2 (hleafB l hl)
        -- the residual's read spine
        have hvCres1 : denoteP m.acval env ψ' (rP + cnF)
            (Expr.mkAppN cres.getAppFn cres.getAppArgs)
            = some vCres := by
          rw [Expr.mkAppN_getApp]
          exact hvCres
        obtain ⟨vcH, vcArgs, hvcH, hcsp, hvCresEq⟩ :=
          denoteP_mkAppN_inv hvCres1
        have hvcArgsLen : vcArgs.length = cnP + (mI - rP) := by
          rw [← hcsp.length, hclen]
        obtain ⟨bv', hbv', hdb'⟩ := denoteSpineP_getElem?' hcsp _ bx hbx
        -- fire the recorded index run
        have heqAB := defEqAtP_of_run (m := m) hclaims (k := rP + cnF)
          (fvs := fvs) (Aa := fun i' => Γs.getD (rP + cnF - 1 - i') default)
          (Δa := Δa) hΔalen hshapeS hwsFvs
          (fun i' x hx => hdomsS0 i' x hx) (n := rP + cnF)
          (fun i' hi' => hΔaent i' hi')
          (fun i' hi' σ hσ => hokAll i' hi' σ hσ)
          hrun hwsA hbA hLA hwsB hbB hLB hleafA hltA hleafB hltB
          hdi hdb'
          (fun σ hσ => hokArgs σ hσ vi (List.mem_of_getElem? hvi))
          (fun σ hσ => by
            have h := hokCres σ hσ
            rw [hvCresEq] at h
            exact AnnotOkP_mkAppN_args vcArgs h bv'
              (List.mem_of_getElem? hbv'))
          hsat
        -- the full cross
        have htowFull : PiTeleP sp.length
            (AVExpr.instSeq zs (rP + cnF - 1) TVj) Γj Rj := by
          rw [hsplen, instSeqP_eq_self_of_closed hTVjcl]
          exact htowerJ
        have hcross := instPisAt_denoteP_cross m.acval_closed
          (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
            (fun k' => m.acval_closed n ψ k') y k)
          _ hcinst (D := rP + cnF) (vals := zs) hzslen
          (fun q x hx => (hspFacts q x hx).2) hfbCty hCbR hTVjK hvCres
          (ws := mix) (by rw [hmixlen, hsplen]) hmixsp htowFull
        rw [hvCresEq, instSeqP_mkAppN, hRjdec, instSeqP_mkAppN,
          hmixlen] at hcross
        have hcrossSp := (AVExpr.mkAppN_inj hcross
          (by rw [List.length_map, List.length_map, hvcArgsLen,
            hArgsClen])).2
        rcases hva : vArgsC[cnP + (i - rP)]? with _ | va
        · rw [List.getElem?_eq_none_iff, hArgsClen] at hva
          omega
        have hel : AVExpr.instSeq zs (rP + cnF - 1) bv'
            = AVExpr.instSeq mix (cnP + cnF - 1) va := by
          have h1 := congrArg (fun l => l[cnP + (i - rP)]?) hcrossSp
          simp only [List.getElem?_map, hbv', hva, Option.map_some] at h1
          exact Option.some.inj h1
        -- the fired pin identifies the `ys`-instantiated element
        have hrest : restC = AVExpr.instSeq ys (cnP + cnF - 1) Rj :=
          teleFitPA_rest_eq (cnP + cnF) htowerJ (by rw [hlenY]) hfitC
        obtain ⟨H, cargs, hrestEq, hcarLen, hcarInterp⟩ := hidx
        rcases hcarLen with hcase | hcarLen
        · omega
        have hrest2 : AVExpr.mkAppN H cargs
            = AVExpr.mkAppN (AVExpr.instSeq ys (cnP + cnF - 1) vHC)
                (vArgsC.map (AVExpr.instSeq ys (cnP + cnF - 1))) := by
          rw [← hrestEq, hrest, hRjdec, instSeqP_mkAppN]
        have hcargsSp := (AVExpr.mkAppN_inj hrest2
          (by rw [hcarLen, List.length_map, hArgsClen])).2
        have hcel : cargs.getD (cnP + (i - rP)) default
            = AVExpr.instSeq ys (cnP + cnF - 1) va := by
          have h1 := congrArg (fun l => l[cnP + (i - rP)]?) hcargsSp
          simp only [List.getElem?_map, hva, Option.map_some] at h1
          rw [List.getD, h1]
          rfl
        -- the mixed chain equals the constructor chain
        have hchainEq : chainP V ρ mix = chainP V ρ ys := by
          funext q
          rcases Nat.lt_or_ge q (cnP + cnF) with hq | hq
          · rw [chainP_lt (by rw [hmixlen]; exact hq),
              chainP_lt (by rw [hlenY]; exact hq), hmixlen, hlenY]
            exact hmixVal _ (by omega)
          · rw [chainP_ge (by rw [hmixlen]; exact hq),
              chainP_ge (by rw [hlenY]; exact hq), hmixlen, hlenY]
        -- assemble
        rw [List.getElem?_append_left (by rw [hlenX]; omega)]
        rcases hx : xs[i]? with _ | xv
        · rw [List.getElem?_eq_none_iff, hlenX] at hx
          omega
        rw [Option.map_some, Option.map_some]
        have hgx : xs.getD i default = xv := by
          rw [List.getD, hx]
          rfl
        have hchain : interp2 V (chainP V ρ zs) vi
            = interp2 V ρ (xs.getD i default) := by
          calc interp2 V (chainP V ρ zs) vi
              = interp2 V (chainP V ρ zs) bv' := heqAB
            _ = interp2 V ρ (AVExpr.instSeq zs (zs.length - 1) bv') :=
                (interp2_instSeq zs bv' ρ).symm
            _ = interp2 V ρ (AVExpr.instSeq mix (cnP + cnF - 1) va) := by
                rw [hzslen]
                exact congrArg (interp2 V ρ) hel
            _ = interp2 V (chainP V ρ mix) va := by
                rw [show cnP + cnF - 1 = mix.length - 1 from by
                  rw [hmixlen]]
                exact interp2_instSeq _ va ρ
            _ = interp2 V (chainP V ρ ys) va := by rw [hchainEq]
            _ = interp2 V ρ (AVExpr.instSeq ys (ys.length - 1) va) :=
                (interp2_instSeq ys va ρ).symm
            _ = interp2 V ρ (cargs.getD (cnP + (i - rP)) default) := by
                rw [hlenY, hcel]
            _ = interp2 V ρ (xs.getD (rP + (i - rP)) default) :=
                hcarInterp (i - rP) hj
            _ = interp2 V ρ (xs.getD i default) := by
                rw [show rP + (i - rP) = i from by omega]
        rw [hchain, hgx]
      · -- major branch
        obtain rfl : mI = i := by omega
        have hmajA : Expr.ErasedEq ai (Expr.mkAppN ctorHead sp) := by
          have h1 := hmaj
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
            hlarity, Nat.add_sub_cancel] at h1
          rcases h2 : lhsS.getAppArgs[mI]? with _ | y
          · rw [List.getElem?_eq_none_iff, hlarity] at h2
            omega
          · rw [h2, Option.getD_some] at h1
            rw [hai] at h2
            obtain rfl : ai = y := Option.some.inj h2
            exact h1
        rw [denoteP_erasedEq hmajA (rP + cnF)] at hdi
        obtain ⟨vch, vmargs, hvch, hcspM, hviEq⟩ := denoteP_mkAppN_inv hdi
        have hvchEq : vch = m.acval ctor
            (Level.substFn φ cvj.levelParams usj) := by
          rw [hctorHead] at hvch
          exact (Option.some.inj hvch).symm
        have hmargsLen : vmargs.length = cnP + cnF := by
          rw [← hcspM.length, hsplen]
        rw [List.getElem?_append_right (by rw [hlenX]; omega), hlenX,
          Nat.sub_self]
        rw [show ([AVExpr.mkAppN
            (m.acval ctor (Level.substFn φ cvj.levelParams usj)) ys])[0]?
          = some (AVExpr.mkAppN
              (m.acval ctor (Level.substFn φ cvj.levelParams usj)) ys)
          from rfl]
        rw [Option.map_some, Option.map_some]
        rw [hviEq, interp2_mkAppN_map, interp2_mkAppN_map, hvchEq,
          interp2_closed (V := V)
            (by rw [m.acval_erase]
                exact m.base.cval_closed ctor
                  (Level.substFn φ cvj.levelParams usj))
            (chainP V ρ zs) ρ]
        suffices hsp2 : vmargs.map (interp2 V (chainP V ρ zs))
            = ys.map (interp2 V ρ) by
          rw [hsp2]
        refine List.ext_getElem? fun q => ?_
        rw [List.getElem?_map, List.getElem?_map]
        rcases Nat.lt_or_ge q (cnP + cnF) with hq | hq
        · rcases hxq : sp[q]? with _ | xq
          · rw [List.getElem?_eq_none_iff, hsplen] at hxq
            omega
          obtain ⟨w0, hw0, hmx⟩ := hmixsp q xq hxq
          obtain ⟨vq, hvq, hdq⟩ := denoteSpineP_getElem?' hcspM q _ hxq
          rw [hvq]
          rcases hyq : ys[q]? with _ | yq
          · rw [List.getElem?_eq_none_iff, hlenY] at hyq
            omega
          rw [Option.map_some, Option.map_some]
          have hvqw : vq = w0 := by
            rw [hw0] at hdq
            exact (Option.some.inj hdq).symm
          rw [hvqw]
          have hgy : ys.getD q default = yq := by
            rw [List.getD, hyq]
            rfl
          have hgm : mix.getD q default
              = AVExpr.instSeq zs (rP + cnF - 1) w0 := by
            rw [List.getD, hmx]
            rfl
          have hcalc : interp2 V (chainP V ρ zs) w0
              = interp2 V ρ (ys.getD q default) := by
            calc interp2 V (chainP V ρ zs) w0
                = interp2 V ρ (AVExpr.instSeq zs (zs.length - 1) w0) :=
                  (interp2_instSeq zs w0 ρ).symm
              _ = interp2 V ρ (mix.getD q default) := by
                  rw [hzslen, hgm]
              _ = interp2 V ρ (ys.getD q default) := hmixVal q hq
          rw [hcalc, hgy]
        · rw [List.getElem?_eq_none (by rw [hmargsLen]; omega),
            List.getElem?_eq_none (by rw [hlenY]; omega)]
          rfl
  · rw [List.getElem?_eq_none (by rw [hvLargsLen]; omega),
      List.getElem?_eq_none (by
        rw [List.length_append, hlenX, List.length_cons, List.length_nil]
        omega)]
    rfl

end Setlec.SetR.Interp2
