import Setlec.Model.DirectExtend
import Setlec.Model.Extend.ProjFn

/-!
# The direct simple-structure install: environment assembly

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`, task #82) installs a
recognised simple structure — the type former, the constructor, the
recursor with its single rule and the `nF` projection functions — from
the reference checks alone, and this module carries the corresponding
model extension, one constant at a time (`extend_basis_one`, then
`extend_rec_swap` for the rule-carrying members).

The values are the constructed ones of `Setlec/Model/DirectInstall.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-! ### Inversions of the direct install stages -/

/-- Inversion for `checkDirectInd` (stage 1). -/
theorem checkDirectInd_inv {env : Env} {p : DirectParts} {F : Nat}
    {v : Env × ConstantVal}
    (h : checkDirectInd (fueledOps F) env p = .ok v) :
    ∃ cvTa bs, checkConstantVal (fueledOps F) env p.cvT = .ok cvTa ∧
      Expr.stripPis p.nP cvTa.type = some (bs, .sort p.resSort) ∧
      v = (⟨.indInfo cvTa (directCaps p) :: env.consts⟩, cvTa) := by
  rw [checkDirectInd] at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨cvTa, hcv, h⟩ := Except.bind_ok h
  refine ⟨cvTa, ?_⟩
  cases hst : Expr.stripPis p.nP cvTa.type with
  | none =>
    rw [hst] at h
    simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | some q =>
    obtain ⟨tbs, tbody⟩ := q
    rw [hst] at h
    simp only [unwrapOr, pure, Except.pure, Except.bind] at h
    by_cases h1 : (tbody == Expr.sort p.resSort) = true
    · obtain rfl : tbody = Expr.sort p.resSort := eq_of_beq h1
      rw [if_pos h1] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨tbs, hcv, rfl, h.symm⟩
    · rw [if_neg h1] at h
      simp only [throw, throwThe, MonadExceptOf.throw] at h
      exact nomatch h

/-! ### Uninstantiating a value-spine fit's levels

The capability laws quantify over a level substitution (`us` for the
constant's own parameters) and state the telescope fit over the
*substituted* type; the constructed values are indexed by the composed
assignment.  This moves the fit back to the raw telescope, exactly as
`TeleFitI.instLev_down` does for expression spines. -/

theorem TeleFit.instLev_down {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {ks : List Name} {lvs : List Level} (hcp : ConstValParams cval env) :
    ∀ {vs : List V} {d : Nat} {ρ : Nat → V} {e : Expr} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ (e.instantiateLevelParams ks lvs) vs d' ρ'
        rest →
      ∃ rest₂, TeleFit V cval env (Level.substFn φ ks lvs) d ρ e vs d' ρ'
        rest₂ := by
  intro vs
  induction vs with
  | nil =>
    intro d ρ e d' ρ' rest hfit
    generalize e.instantiateLevelParams ks lvs = E at hfit
    cases hfit
    exact ⟨e, TeleFit.nil⟩
  | cons x xs ih =>
    intro d ρ e d' ρ' rest hfit
    match e with
    | .forallE n ty body mb =>
      rw [Expr.instantiateLevelParams] at hfit
      cases hfit with
      | @cons _ _ _ _ _ _ _ _ _ _ _ A hity hx hsub =>
        rw [interp_instLevels hcp] at hity
        rw [← instantiateLevelParams_instantiate1] at hsub
        obtain ⟨rest₂, h₂⟩ := ih hsub
        exact ⟨rest₂, TeleFit.cons hity hx h₂⟩
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      rw [Expr.instantiateLevelParams] at hfit
      exact nomatch hfit

/-! ### Stage 1: the type former -/

/-- Extend a model by a direct simple structure's **type former**: an
opaque inductive-kind constant valued by the guarded dependent-pair
tower over the constructor's field telescope (`directTyVal`).

Its membership obligation is unconditional — that is what the guard in
`directTyBody` buys — so the only capability law with content is the
unit-like one, and only for a field-free structure, where the tower is
the singleton. -/
theorem extend_direct_ind {env : Env} (m : EnvModel V env) {p : DirectParts}
    {cvTa : ConstantVal} {F : Nat} {cty : Expr}
    {bs : List (Name × Expr × BinderMeta)}
    (hccv : checkConstantVal (fueledOps F) env p.cvT = .ok cvTa)
    (hstrip : Expr.stripPis p.nP cvTa.type = some (bs, .sort p.resSort))
    (hctyP : cty.allLevelParamsDefined cvTa.levelParams = true)
    -- from `directNoModel`, part of recognition: the block is the
    -- artifact-free route, so the type former has no companion and the
    -- artifact linkage is vacuous for it
    (hnomodel : (env.find? (p.cvT.name.str "_model")).isNone = true) :
    ∃ m₁ : EnvModel V ⟨.indInfo cvTa (directCaps p) :: env.consts⟩,
      (∀ ψ, m₁.val cvTa.name ψ =
        directTyVal V m.val env cvTa.type cty p.nP p.nF p.resSort ψ) ∧
      (∀ n ψ, n ≠ cvTa.name → m₁.val n ψ = m.val n ψ) := by
  obtain ⟨hfind0, hnres0, hmft0, hpshape0, hnd, hlb, hfv, tyA, stype, u,
    hann, hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
  have hnameA : cvTa.name = p.cvT.name := by rw [hcvA]
  have hlpsA : cvTa.levelParams = p.cvT.levelParams := by rw [hcvA]
  have htypeA : cvTa.type = tyA := by rw [hcvA]
  have hfind' : env.find? cvTa.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvTa.name = false := by
    rw [hnameA]; exact hnres0
  have hshapeA : cvTa.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape0
  have htyf : cvTa.type.hasFvar = false := by
    rw [htypeA]
    exact not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvTa.type.looseBVarsBounded 0 = true := by
    rw [htypeA]; exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvTa.type.allLevelParamsDefined cvTa.levelParams = true := by
    rw [htypeA, hlpsA]; exact hlp
  have htres : cvTa.type.constsResolve env = true := by rw [htypeA]; exact hres
  have hAty : ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) cvTa.type := by
    intro ψ
    rw [htypeA]
    exact annotate_sound m _ hann (WScoped.of_not_hasFvar hfv) hlb
      (Expr.LeavesBounded.of_not_hasFvar hfv) (rho0 V)
      (FvarsOk.of_not_hasFvar hfv)
  have htyfA : tyA.hasFvar = false := by rw [← htypeA]; exact htyf
  have hityI : ∀ ψ : Name → Nat, ∃ Tv,
      interpExpr V m.val env ψ 0 (rho0 V) cvTa.type = some Tv := by
    intro ψ
    have hAtyA : AnnotOk V m.val env ψ 0 (rho0 V) tyA := by
      rw [← htypeA]; exact hAty ψ
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ) m F hst
        (WScoped.of_not_hasFvar htyfA)
        (by rw [← htypeA]; exact htyb)
        (Expr.LeavesBounded.of_not_hasFvar htyfA)
        (FvarsOk.of_not_hasFvar htyfA) hAtyA
    exact ⟨v, by rw [htypeA]; exact hvi⟩
  have hsP : p.resSort.allParamsDefined cvTa.levelParams = true := by
    have h := allLevelParamsDefined_stripPis_body p.nP hstrip htlp
    simpa [Expr.allLevelParamsDefined] using h
  have hnresI : reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa (directCaps p)).name = false := hnres
  have hwf : ConstWF ⟨.indInfo cvTa (directCaps p) :: env.consts⟩
      (.indInfo cvTa (directCaps p)) := by
    refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
    · intro cv2 v2 h2 heq; exact nomatch heq
    · intro cv2 mI' rP' rules heq; exact nomatch heq
    · intro cv2 v2 heq; exact nomatch heq
  refine extend_basis_one m (.indInfo cvTa (directCaps p))
    (fun ψ => directTyVal V m.val env cvTa.type cty p.nP p.nF p.resSort ψ)
    hfind' hwf htres (fun cv2 value2 h2 heq => nomatch heq) ?_ ?_ hAty
    (fun cv caps heq hn => absurd (hn ▸ hnresI) (by decide))
    (fun cv nP nF heq _ => nomatch heq)
    (fun cv caps heq hn => absurd (hn ▸ hnresI) (by decide))
    (fun hn => absurd (hn ▸ hnresI) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnresI) (by simp))
    (fun cv mI rP rules heq => nomatch heq)
    (fun val' _ _ cvR mI rP rules heq => nomatch heq)
    (fun cvR mI rP rules heq => nomatch heq)
    (fun _ hk _ => by obtain ⟨cv, cnP, cnF, heq⟩ := hk; exact nomatch heq)
    (fun T j cv mI rP rules hh heq _ => nomatch heq)
    (fun entry heq _ => nomatch heq)
    (fun cv caps heq hcape _ => by
      injection heq with h1 h2
      rw [← h2] at hcape
      exact nomatch hcape)
    (fun cv caps heq hcapu _ => by
      injection heq with h1 h2
      rw [← h2] at hcapu
      exact nomatch hcapu)
    (show modelFamilyTaken env cvTa.name = false by rw [hnameA]; exact hmft0)
    (fun T j cv mI rP rules hh heq => nomatch heq)
    (hnotthm := fun cv2 value2 h => ConstantInfo.noConfusion h)
    (hmodvInd := fun _ _ hms => by
      exfalso
      rw [show (ConstantInfo.indInfo cvTa (directCaps p)).name = p.cvT.name
        from hnameA, Option.isNone_iff_eq_none.mp hnomodel] at hms
      exact nomatch hms)
  · -- `mem_type`
    intro ψ
    obtain ⟨Tv, hTv⟩ := hityI ψ
    exact ⟨Tv, hTv, directTyVal_mem hstrip hTv (hAty ψ)⟩
  · -- `val_params`
    intro ψ₁ ψ₂ hψ
    exact directTyVal_params m.val_params (ps := cvTa.levelParams) hψ
      htlp hctyP hsP

/-- Inversion for `checkDirectParamDoms`. -/
theorem checkDirectParamDoms_inv {env : Env} {F : Nat}
    {cfvs tfvs : List Expr} :
    ∀ (k : Nat),
      checkDirectParamDoms (fueledOps F) env cfvs tfvs k = .ok () →
      ∀ j, j < k → ∀ a b, cfvs[j]? = some a → tfvs[j]? = some b →
        isDefEqCore env F j (Expr.fvarTypeD a) (Expr.fvarTypeD b)
          = .ok true := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro h j hj a b ha hb
    rw [checkDirectParamDoms] at h
    simp only [fueledOps_isDefEq, Bind.bind, Except.bind, unwrapOr] at h
    cases hca : cfvs[k]? with
    | none => rw [hca] at h; exact nomatch h
    | some a₀ =>
      rw [hca] at h
      simp only [pure, Except.pure] at h
      cases hcb : tfvs[k]? with
      | none => rw [hcb] at h; exact nomatch h
      | some b₀ =>
        rw [hcb] at h
        simp only [pure, Except.pure] at h
        cases hde : isDefEqCore env F k (Expr.fvarTypeD a₀)
            (Expr.fvarTypeD b₀) with
        | error _ => rw [hde] at h; exact nomatch h
        | ok v =>
          rw [hde] at h
          cases v with
          | false =>
            simp only [Bool.false_eq_true, if_false, throw, throwThe,
              MonadExceptOf.throw] at h
            exact nomatch h
          | true =>
            simp only [if_true] at h
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · exact ih h j hj' a b ha hb
            · obtain rfl : a₀ = a := Option.some.inj (hca.symm.trans ha)
              obtain rfl : b₀ = b := Option.some.inj (hcb.symm.trans hb)
              exact hde

/-- Inversion for `checkDirectCtor` (stage 2). -/
theorem checkDirectCtor_inv {env₀ env : Env} {p : DirectParts}
    {cvTa : ConstantVal} {F : Nat} {v : Env × ConstantVal}
    (h : checkDirectCtor (fueledOps F) env₀ env p cvTa = .ok v) :
    ∃ cvCa cbs fvsP crest tfvs trest xFvs,
      checkConstantVal (fueledOps F) env p.cvC = .ok cvCa ∧
      Expr.stripPis (p.nP + p.nF) cvCa.type =
        some (cbs, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) ∧
      openPisAtFvars p.nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) ∧
      checkDirectParamDoms (fueledOps F) env fvsP tfvs p.nP = .ok () ∧
      openPisAtFvars p.nF crest p.nP = some (xFvs,
        Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          fvsP) ∧
      (∀ x ∈ xFvs, (Expr.fvarTypeD x).constsResolve env₀ = true) ∧
      checkDirectFieldUniv (fueledOps F) env p.resSort p.nP xFvs p.nF
        = .ok () ∧
      v = (⟨.ctorInfo cvCa p.nP p.nF :: env.consts⟩, cvCa) := by
  rw [checkDirectCtor] at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨cvCa, hcv, h⟩ := Except.bind_ok h
  -- the annotated constructor telescope
  obtain ⟨q1, hq1⟩ : ∃ q, Expr.stripPis (p.nP + p.nF) cvCa.type = some q := by
    cases hh : Expr.stripPis (p.nP + p.nF) cvCa.type with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq1] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  by_cases hb : (q1.2 == directFam p.cvT.name p.cvT.levelParams p.nP p.nF)
      = true
  case neg =>
    rw [if_neg hb] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hb] at h
  have hq1b : Expr.stripPis (p.nP + p.nF) cvCa.type =
      some (q1.1, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) := by
    rw [hq1]
    congr 1
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hb⟩ ▸ rfl
  -- the two openings
  obtain ⟨cq, hcq⟩ : ∃ q, openPisAtFvars p.nP cvCa.type 0 = some q := by
    cases hh : openPisAtFvars p.nP cvCa.type 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hcq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨tq, htq⟩ : ∃ q, openPisAtFvars p.nP cvTa.type 0 = some q := by
    cases hh : openPisAtFvars p.nP cvTa.type 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [htq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  -- the per-frame parameter-domain pins
  obtain ⟨u0, hpins, h⟩ := Except.bind_ok h
  obtain rfl : u0 = () := rfl
  -- the field telescope
  obtain ⟨xq, hxq⟩ : ∃ q, openPisAtFvars p.nF cq.2 p.nP = some q := by
    cases hh : openPisAtFvars p.nF cq.2 p.nP with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hxq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  by_cases hr : (xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1) = true
  case neg =>
    rw [if_neg hr] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hr] at h
  have hxqb : openPisAtFvars p.nF cq.2 p.nP = some (xq.1, Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1) := by
    rw [hxq]
    congr 1
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hr⟩ ▸ rfl
  by_cases hres : (xq.1.all fun x => (Expr.fvarTypeD x).constsResolve env₀)
      = true
  case neg =>
    rw [if_neg hres] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hres] at h
  obtain ⟨u1, hfu, h⟩ := Except.bind_ok h
  obtain rfl : u1 = () := rfl
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvCa, q1.1, cq.1, cq.2, tq.1, tq.2, xq.1, hcv, hq1b, hcq, htq,
    hpins, hxqb, fun x hx => List.all_eq_true.mp hres x hx, hfu, h.symm⟩

end Setlec
