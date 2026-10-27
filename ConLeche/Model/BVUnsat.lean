module

import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Semantics.Kit
import ConLeche.Model.AxiomMem
import ConLeche.Model.BVQuoteSem

/-!
# `Infer.bvUnsat`'s environment law (task #368)

`Rules.BVUnsatSemLaw`, from the fold's invariant: where the `bv_decide`
closure is the pinned one,

* `unsat_of_verifyBVExpr_eq_true` reads as the point: its stored type
  (pinned) is a Π-type into `Unsat bv`, and `⟦Unsat⟧ ∈ ⟦BVLogicalExpr → Prop⟧`
  (its stored type), so the whole type is a truth value;
* `⟦Unsat E⟧ = ⟦∀ f : Assignment, eval f E = false⟧` (the stored value,
  pinned, through `AcvalDefnInst`), and at every `X ∈ ⟦Assignment⟧` the
  fibre is `eqv ⟦eval X E⟧ ⟦false⟧` (the `Eq` law), which holds: `X` is
  a quoted assignment (`assignQuote_of`, `Model/BVQuoteSem.lean`: the
  stored recursors at a `Prop` motive) and the law's premise equates the
  quoted evaluation with `⟦false⟧`.
-/

public section

namespace ConLeche.Model
open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name CheckMode ConstantInfo)

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

private theorem substFn_nil' (ψ : Name → Nat) : Level.substFn ψ [] [] = ψ :=
  funext fun _ => rfl

private theorem denote_const0 {acval : Name → (Name → Nat) → Term} {φ : Name → Nat}
    {d : Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (hlp : ci.toConstantVal.levelParams = []) :
    denote acval env φ d (.const n []) = some (acval n φ) := by
  have h := denote_const (acval := acval) (φ := φ) (d := d) (us := []) hf (by simp [hlp])
  rw [hlp, substFn_nil'] at h
  exact h

theorem bvUnsatSemLaw_of (mp : EnvModelM V μ env) (φ : Name → Nat)
    (hop : Rules.NatOpRow mp.base2 φ) : Rules.BVUnsatSemLaw mp.base2 φ := by
  intro hpins d E eT ρ hEc hEf heT hwE hmemB hredx hpow
  -- the pinned constants
  obtain ⟨cvU, hfU, hlU, htU⟩ := ConLeche.BVUnsat.pin_U_shape hpins
  obtain ⟨cvS, hS, hfS, hlS, htS⟩ := ConLeche.BVUnsat.pin_Unsat_shape hpins
  obtain ⟨cvB, vB, hB, hfB, hlB, htB⟩ := ConLeche.BVUnsat.pin_BVLE hpins
  obtain ⟨cvE, vE, hE, hfE, hlE, htE⟩ := ConLeche.BVUnsat.pin_eval_shape hpins
  obtain ⟨cvBo, capsBo, hfBo, hlBo, htBo⟩ := ConLeche.BVUnsat.pin_Bool hpins
  obtain ⟨cvF, nP, nF, hfF, hlF, htF⟩ := ConLeche.BVUnsat.pin_BoolFalse hpins
  obtain ⟨ciU, hfU', hcvU⟩ : ∃ ci, env.find? ConLeche.unsatThmName = some ci ∧
      ci.toConstantVal = cvU := by
    rcases hfU with h | h <;> exact ⟨_, h, rfl⟩
  have dU : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.unsatThmName []) =
      some (mp.base2.acval ConLeche.unsatThmName φ) := fun e => denote_const0 hfU' (by rw [hcvU]; exact hlU)
  have dS : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.bvUnsatName []) =
      some (mp.base2.acval ConLeche.bvUnsatName φ) := fun e => denote_const0 hfS hlS
  have dB : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.bvLogicalExprName []) =
      some (mp.base2.acval ConLeche.bvLogicalExprName φ) := fun e => denote_const0 hfB hlB
  have dEv : ∀ e, denote mp.base2.acval env φ e (.const Rules.bvEvalName []) =
      some (mp.base2.acval Rules.bvEvalName φ) := fun e => denote_const0 hfE hlE
  have dBo : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.boolName []) =
      some (mp.base2.acval ConLeche.boolName φ) := fun e => denote_const0 hfBo hlBo
  have dF : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.boolFalseName []) =
      some (mp.base2.acval ConLeche.boolFalseName φ) := fun e => denote_const0 hfF hlF
  have hcl : ∀ (n : Name) (ρ' : Nat → V), interp V ρ' (mp.base2.acval n φ) = interp V ρ (mp.base2.acval n φ) :=
    fun n ρ' => interp_closed V (mp.base2.cval_closed n φ) ρ' ρ
  -- the stored types, as memberships
  have hTyS : interp V ρ (mp.base2.acval ConLeche.bvUnsatName φ) ∈ˢ
      piV (interp V ρ (mp.base2.acval ConLeche.bvLogicalExprName φ)) (fun _ => univ 0) := by
    obtain ⟨tyS, htyS, -, hmS⟩ := mp.constType (φ := φ) d ConLeche.bvUnsatName _ [] hfS
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlS])
    simp only [ConLeche.ConstantInfo.toConstantVal, htS, hlS, substFn_nil'] at htyS hmS
    rw [show ConLeche.unsatTyE.instantiateLevelParams [] [] = ConLeche.unsatTyE from rfl] at htyS
    have h1 : denote mp.base2.acval env φ d ConLeche.unsatTyE =
        some (.pi (mp.base2.acval ConLeche.bvLogicalExprName φ) (.sort 0)) := by
      simp [ConLeche.unsatTyE, denote_forallE, denote_sort, dB, Expr.instantiate1, Level.eval]
    rw [h1] at htyS
    obtain rfl := Option.some.inj htyS
    have := hmS ρ
    simpa [interp_pi, interp_sort] using this
  -- `unsat_of_verifyBVExpr_eq_true` is the point: its type is a truth value
  have hUpt : interp V ρ (mp.base2.acval ConLeche.unsatThmName φ) = pt := by
    obtain ⟨tyU, htyU, -, hmU⟩ := mp.constType (φ := φ) d ConLeche.unsatThmName ciU [] hfU'
      (by rw [hcvU]; simp [hlU])
    simp only [hcvU, htU, hlU, substFn_nil'] at htyU hmU
    rw [show ConLeche.uTyE.instantiateLevelParams [] [] = ConLeche.uTyE from rfl] at htyU
    obtain ⟨BT, R1, hBT, hR1, rfl⟩ := denote_forallE_inv htyU
    rw [dB] at hBT
    obtain rfl := Option.some.inj hBT
    simp [Expr.instantiate1] at hR1
    obtain ⟨ST, R2, -, hR2, rfl⟩ := denote_forallE_inv hR1
    simp [Expr.instantiate1] at hR2
    obtain ⟨HT, R3, -, hR3, rfl⟩ := denote_forallE_inv hR2
    simp [Expr.instantiate1] at hR3
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hR3
    rw [dS] at hfa
    obtain rfl := Option.some.inj hfa
    rw [denote_fvar] at haa
    obtain rfl := Option.some.inj haa
    have hz : interp V ρ (Term.pi (mp.base2.acval ConLeche.bvLogicalExprName φ) (.pi ST (.pi HT
        (.app (mp.base2.acval ConLeche.bvUnsatName φ) (.bvar (d + 1 + 1 + 1 - 1 - d))))))
        ∈ˢ (univZero : V) := by
      simp only [interp_pi, interp_app, interp_bvar]
      refine piV_mem_univZero_of fun b hb => piV_mem_univZero_of fun c _ =>
        piV_mem_univZero_of fun h _ => ?_
      rw [show d + 1 + 1 + 1 - 1 - d = 2 by omega]
      simp only [cons_succ, cons_zero, hcl]
      rw [← univ_zero]
      exact app_mem_piV hTyS hb
    exact eq_pt_of_mem_univZero hz (hmU ρ)
  -- `Assignment` and `Eq`
  have hpA := ConLeche.BVUnsat.pinsOk_model hpins ConLeche.bvPin.Assignment
    (by simp [ConLeche.bvModelPins])
  obtain ⟨vA, hpAe⟩ : ∃ vA, ConLeche.bvPin.Assignment =
      .defn Rules.bvAssignmentName [] (.sort (.succ .zero)) vA := ⟨_, by rfl⟩
  obtain ⟨cvA, hA, hfA, hlA, htA⟩ := ConLeche.BVUnsat.pin_defn hpA hpAe
  have dA : ∀ e, denote mp.base2.acval env φ e (.const Rules.bvAssignmentName []) =
      some (mp.base2.acval Rules.bvAssignmentName φ) := fun e => denote_const0 hfA hlA
  -- the stored value of `Unsat` reads (`AcvalDefnInst`), so `Eq` is stored
  have hdefS := mp.defn_reads φ cvS ConLeche.unsatValE ⟨hS, Env.find?_mem hfS⟩
  have hnS : cvS.name = ConLeche.bvUnsatName := Env.find?_name hfS
  rw [hnS] at hdefS
  obtain ⟨ciEq, hfEq⟩ : ∃ ci, env.find? ConLeche.eqName = some ci := by
    obtain ⟨-, b0, -, hb0, -⟩ := denote_lam_inv hdefS
    simp [Expr.instantiate1] at hb0
    obtain ⟨-, b1, -, hb1, -⟩ := denote_forallE_inv hb0
    simp [Expr.instantiate1] at hb1
    obtain ⟨f1, -, hf1, -, -⟩ := denote_app_inv hb1
    obtain ⟨f2, -, hf2, -, -⟩ := denote_app_inv hf1
    obtain ⟨f3, -, hf3, -, -⟩ := denote_app_inv hf2
    rw [denote] at hf3
    cases hq : env.find? ConLeche.eqName with
    | none => rw [hq] at hf3; exact nomatch hf3
    | some ci => exact ⟨ci, rfl⟩
  have hEqA : env.find? ConLeche.eqName = some ConLeche.eqA := by
    have := (mp.base2.basis_pinned ConLeche.eqName ciEq hfEq (by decide)).1
    rw [hfEq, this]; simp [pinnedInfo]
  have dEq : ∀ e, denote mp.base2.acval env φ e (.const ConLeche.eqName [.succ .zero]) =
      some (mp.base2.acval ConLeche.eqName
        (Level.substFn φ ConLeche.eqA.toConstantVal.levelParams [.succ .zero])) :=
    fun e => denote_const hEqA rfl
  have hval : denote mp.base2.acval env φ 0 ConLeche.unsatValE = some
      (.lam (mp.base2.acval ConLeche.bvLogicalExprName φ)
        (.pi (mp.base2.acval Rules.bvAssignmentName φ)
          (.app (.app (.app (mp.base2.acval ConLeche.eqName
              (Level.substFn φ ConLeche.eqA.toConstantVal.levelParams [.succ .zero]))
            (mp.base2.acval ConLeche.boolName φ))
            (.app (.app (mp.base2.acval Rules.bvEvalName φ) (.bvar 0)) (.bvar 1)))
            (mp.base2.acval ConLeche.boolFalseName φ)))) := by
    simp [ConLeche.unsatValE, denote_lam, denote_forallE, denote_app, denote_fvar,
      Expr.instantiate1, dB, dA, dEq, dBo, dEv, dF]
  rw [hval] at hdefS
  have hSval := (Option.some.inj hdefS).symm
  -- the stored types' memberships
  have hBty : interp V ρ (mp.base2.acval ConLeche.bvLogicalExprName φ) ∈ˢ (univ 1 : V) := by
    obtain ⟨ty, hty, -, hm⟩ := mp.constType (φ := φ) d ConLeche.bvLogicalExprName _ [] hfB
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlB])
    simp only [ConLeche.ConstantInfo.toConstantVal, htB, hlB, substFn_nil'] at hty hm
    rw [show (Expr.sort (.succ .zero)).instantiateLevelParams [] [] = .sort (.succ .zero) from rfl,
      denote_sort] at hty
    obtain rfl := Option.some.inj hty
    simpa [Level.eval] using hm ρ
  have hAty : interp V ρ (mp.base2.acval Rules.bvAssignmentName φ) ∈ˢ (univ 1 : V) := by
    obtain ⟨ty, hty, -, hm⟩ := mp.constType (φ := φ) d Rules.bvAssignmentName _ [] hfA
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlA])
    simp only [ConLeche.ConstantInfo.toConstantVal, htA, hlA, substFn_nil'] at hty hm
    rw [show (Expr.sort (.succ .zero)).instantiateLevelParams [] [] = .sort (.succ .zero) from rfl,
      denote_sort] at hty
    obtain rfl := Option.some.inj hty
    simpa [Level.eval] using hm ρ
  have hBoty : interp V ρ (mp.base2.acval ConLeche.boolName φ) ∈ˢ (univ 1 : V) := by
    obtain ⟨ty, hty, -, hm⟩ := mp.constType (φ := φ) d ConLeche.boolName _ [] hfBo
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlBo])
    simp only [ConLeche.ConstantInfo.toConstantVal, htBo, hlBo, substFn_nil'] at hty hm
    rw [show (Expr.sort (.succ .zero)).instantiateLevelParams [] [] = .sort (.succ .zero) from rfl,
      denote_sort] at hty
    obtain rfl := Option.some.inj hty
    simpa [Level.eval] using hm ρ
  have hFty : interp V ρ (mp.base2.acval ConLeche.boolFalseName φ) ∈ˢ
      interp V ρ (mp.base2.acval ConLeche.boolName φ) := by
    obtain ⟨ty, hty, -, hm⟩ := mp.constType (φ := φ) d ConLeche.boolFalseName _ [] hfF
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlF])
    simp only [ConLeche.ConstantInfo.toConstantVal, htF, hlF, substFn_nil'] at hty hm
    rw [show (Expr.const ConLeche.boolName []).instantiateLevelParams [] [] =
      .const ConLeche.boolName [] from rfl, dBo] at hty
    obtain rfl := Option.some.inj hty
    exact hm ρ
  have hEvty : interp V ρ (mp.base2.acval Rules.bvEvalName φ) ∈ˢ
      piV (interp V ρ (mp.base2.acval Rules.bvAssignmentName φ)) (fun _ =>
        piV (interp V ρ (mp.base2.acval ConLeche.bvLogicalExprName φ)) (fun _ =>
          interp V ρ (mp.base2.acval ConLeche.boolName φ))) := by
    obtain ⟨ty, hty, -, hm⟩ := mp.constType (φ := φ) d Rules.bvEvalName _ [] hfE
      (by simp [ConLeche.ConstantInfo.toConstantVal, hlE])
    simp only [ConLeche.ConstantInfo.toConstantVal, htE, hlE, substFn_nil'] at hty hm
    rw [show ConLeche.evalTyE.instantiateLevelParams [] [] = ConLeche.evalTyE from rfl] at hty
    have h1 : denote mp.base2.acval env φ d ConLeche.evalTyE = some (.pi
        (mp.base2.acval Rules.bvAssignmentName φ) (.pi (mp.base2.acval ConLeche.bvLogicalExprName φ)
          (mp.base2.acval ConLeche.boolName φ))) := by
      simp [ConLeche.evalTyE, denote_forallE, dA, dB, dBo, Expr.instantiate1]
    rw [h1] at hty
    obtain rfl := Option.some.inj hty
    simpa [interp_pi, hcl] using hm ρ
  -- `Bool` holds no proof
  have hBoStrict : Strict (interp V ρ (mp.base2.acval ConLeche.boolName φ)) := by
    have h := mp.indFibLaw φ d ConLeche.boolName cvBo capsBo [] hfBo (by simp [hlBo]) [] 1
      (by
        rw [htBo, hlBo, show (Expr.sort (.succ .zero)).instantiateLevelParams [] [] =
          .sort (.succ .zero) from rfl, denote_sort]
        rfl) ρ [] trivial
    simpa [substFn_nil', hlBo] using h
  have hEB : interp V ρ eT ∈ˢ interp V ρ (mp.base2.acval ConLeche.bvLogicalExprName φ) :=
    hmemB _ (dB d)
  have hψ1 : Level.substFn φ ConLeche.eqA.toConstantVal.levelParams [.succ .zero] uN = 1 := rfl
  -- at every assignment, the formula evaluates to `false`
  have hfib : ∀ X, X ∈ˢ interp V ρ (mp.base2.acval Rules.bvAssignmentName φ) →
      SetTheory.app (SetTheory.app (interp V ρ (mp.base2.acval Rules.bvEvalName φ)) X)
        (interp V ρ eT) = interp V ρ (mp.base2.acval ConLeche.boolFalseName φ) := by
    intro X hX
    obtain ⟨x, qa, hqa, hwq, hiq⟩ := assignQuote_of mp hpins hop hpow (dA d) X hX
    have hrx : denote mp.base2.acval env φ d
        (.app (.app (.const Rules.bvEvalName []) (Rules.quoteAssign x)) E) =
        some (.app (.app (mp.base2.acval Rules.bvEvalName φ) qa) eT) := by
      simp [denote_app, dEv, hqa, heT]
    have hX' : interp V ρ qa ∈ˢ interp V ρ (mp.base2.acval Rules.bvAssignmentName φ) := by
      rw [hiq]; exact hX
    have hm1 := app_mem_piV hEvty hX'
    have hm2 := app_mem_piV hm1 hEB
    have hw1 : WellDenoted V ρ (.app (mp.base2.acval Rules.bvEvalName φ) qa) :=
      WellDenoted_app_of V (Aa := mp.base2.acval Rules.bvAssignmentName φ)
        (Ba := .pi (mp.base2.acval ConLeche.bvLogicalExprName φ) (mp.base2.acval ConLeche.boolName φ))
        (mp.base2.acval_wellDenoted _ _ ρ) hwq
        (by simpa [interp_pi, hcl] using hEvty) hX' (IsTy_of_mem_univ hAty)
    have hw2 : WellDenoted V ρ (.app (.app (mp.base2.acval Rules.bvEvalName φ) qa) eT) :=
      WellDenoted_app_of V (Aa := mp.base2.acval ConLeche.bvLogicalExprName φ)
        (Ba := mp.base2.acval ConLeche.boolName φ) hw1 hwE
        (by simpa [interp_pi, interp_app, hcl] using hm1) hEB (IsTy_of_mem_univ hBty)
    have hne : interp V ρ (.app (.app (mp.base2.acval Rules.bvEvalName φ) qa) eT) ≠ pt :=
      ne_pt_of_mem_strict hBoStrict (by simpa [interp_app] using hm2)
    have := hredx x _ _ hrx hw2 hne (dF d)
    simpa [interp_app, hiq] using this
  refine ⟨_, _, dU d, dS d, mp.base2.acval_wellDenoted _ _ ρ, hUpt, ⟨?_, ?_⟩, ?_⟩
  · exact WellDenoted_app_of V (Aa := mp.base2.acval ConLeche.bvLogicalExprName φ) (Ba := .sort 0)
      (mp.base2.acval_wellDenoted _ _ ρ) hwE (by simpa [interp_pi, interp_sort] using hTyS) hEB
      (IsTy_of_mem_univ hBty)
  · exact IsTy_of_mem_univ (by simpa [interp_app] using app_mem_piV hTyS hEB)
  · rw [interp_app, hSval, interp_lam, app_lamV hEB, interp_pi]
    refine pt_mem_piV_of fun X hX => ?_
    rw [hcl] at hX
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hcl]
    rw [interp_closed V (mp.base2.cval_closed _ _) _ ρ]
    have hlaw := (mp.eq_law hEqA (Level.substFn φ ConLeche.eqA.toConstantVal.levelParams
      [.succ .zero])).1 ρ (interp V ρ (mp.base2.acval ConLeche.boolName φ))
      (SetTheory.app (SetTheory.app (interp V ρ (mp.base2.acval Rules.bvEvalName φ)) X)
        (interp V ρ eT))
      (interp V ρ (mp.base2.acval ConLeche.boolFalseName φ)) (by rw [hψ1]; exact hBoty)
      (app_mem_piV (B := fun _ => interp V ρ (mp.base2.acval ConLeche.boolName φ))
        (app_mem_piV hEvty hX) hEB) hFty
    rw [hlaw, hfib X hX]
    exact ⟨eqv_mem_univZero _ _, pt_mem_eqv_self _⟩

end ConLeche.Model
