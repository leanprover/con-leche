module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Model.Inductives.TargetFrame
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Inductives.BlockRuleCaRun

public section

/-!
# The seam's residue conjunct over the target check

`BlockRuleDataB`'s fourth conjunct (`BlockRecData.lean`): the rule's
λ-tower core, read at the fired frame, against the residue at the `ih`
values.  Here it is proved at the TARGET check's
rule data — `ihs := tgtIhsAV`, `Rb0 := tgtRbAV` (`TargetRuleData.lean`)
— from `targetRuleBodyEq_run` (`TargetFrame.lean`) at the `(j, i)`-th
rule run.

The stage record `h` and the target run `R` (with `rs = tgtRs out`) are
taken together: the frame's prefix and field readings, the recursor
types' facts and the callees' leaves are the stage record's kind-free
inversions.  Nothing here reads a field kind.

What crosses:
* the call's `ih` value — the tgt `ih` term `L.inst (bvar (B + K-1-c))`
  at the chain frame is `L` at the callee's chain value (`interp_inst`,
  `chainFrame_apply`), and `L` is bound below `B + 1`
  (`targetRuleBodyEq_run`'s second conclusion), so the chain below the
  frame is invisible;
* the residue's reading IS `tgtRbAV` (the pinning's `tgtAbs`);
* the callee's leaf is typed at its recursor type (`blockRecAV_facts` at
  the family's regime `hpre`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo CheckMode FEnv BlockShape BlockParts
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The recomputed prefix openers are the member-format family's
(`blockRulePrefFvs`). -/
theorem tgtPrefFvs_eq_block (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr))
    (j : Nat) : tgtPrefFvs p out j = blockRulePrefFvs p (tgtRs out) j := by
  have hT : blockRuleRecTy (tgtRs out) j = tgtRecTy out j := by
    simp only [blockRuleRecTy, tgtRecTy, tgtRs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases out[j]? <;> rfl
  rw [tgtPrefFvs, blockRulePrefFvs, hT]
  rfl

/-- The recomputed width `tgtB` at a stored rule. -/
theorem tgtB_at {p : BlockShape} {out : List (ConstantVal × TargetMajor × List Expr)}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA) :
    tgtB p out j i = p.rulePrefixAt j + cA.2 := by
  rw [tgtB, tgtCtorOf_at hr hcA]; rfl

/-! ## `heqP`'s target rows: the level footprint -/

section Params

variable {ps : List Name}

omit [SetTheory V] in
/-- A spine's arguments carry its footprint. -/
theorem lpDefF_mkAppN_args :
    ∀ (as : List Expr) {f : Expr}, lpDefF ps (Expr.mkAppN f as) = true →
      lpDefF ps f = true ∧ ∀ a ∈ as, lpDefF ps a = true
  | [], f, h => ⟨h, fun a ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨h1, h2⟩ := lpDefF_mkAppN_args as (f := Expr.app f a) h
    simp only [lpDefF, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.2
    · exact h2 x hx

omit [SetTheory V] in
/-- A Π-telescope's domains carry the type's footprint. -/
theorem lpDefF_piBinders :
    ∀ (e : Expr), e.allLevelParamsDefined ps = true → ∀ b ∈ e.piBinders.1,
      lpDefF ps b.1 = true := by
  intro e
  induction e with
  | forallE ty body m _ ihb =>
    intro h b hb
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.piBinders, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact lpDefF_of_allLevelParamsDefined _ h.1.1
    · exact ihb h.1.2 b hb
  | _ => intro _ b hb; simp [Expr.piBinders] at hb

omit [SetTheory V] in
theorem lpDefF_mkLamsOf :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) {body : Expr},
      (∀ b ∈ bs, lpDefF ps b.1 = true ∧ b.2.pw.paramsDefined ps = true) →
      lpDefF ps body = true → lpDefF ps (Expr.mkLamsOf bs body) = true
  | [], _, _, hb => hb
  | (ty, m) :: bs, body, hbs, hb => by
    have h0 := hbs (ty, m) List.mem_cons_self
    simp only [Expr.mkLamsOf, lpDefF, h0.1, h0.2,
      lpDefF_mkLamsOf bs (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb, Bool.and_self]

end Params

/-! ## The `ℓ = 0` arm at a rule binding no variable -/

section RuleZero

end RuleZero

end ConLeche.Model
