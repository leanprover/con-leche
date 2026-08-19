import Setlec.Kernel.Checker
import Setlec.Model.TypeChecker

/-!
# Consistency of the checker

The headline results:

* `checkDecl_sound`: checking a declaration preserves having a model.
* `checkDecls_sound`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).

Both are parametric in a model `V` of the target set theory: assuming
Tarski–Grothendieck set theory is consistent (i.e. a `SetTheory` instance
exists), no accepted environment can prove `False` — the concrete
"no proof of `Empty` is accepted" corollary lands once `Empty` is in the
supported fragment.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

private theorem find?_none_ne {env : Env} {n : Name} (h : env.find? n = none) :
    ∀ c ∈ env.consts, c.name ≠ n := by
  intro c hc
  have := List.find?_eq_none.mp h c hc
  simpa using this

/-- Checking a declaration preserves having a model. -/
theorem checkDecl_sound {env env' : Env} {d : Declaration}
    (h : checkDecl env d = .ok env') (m : EnvModel V env) : Nonempty (EnvModel V env') := by
  cases d with
  | thmDecl cv value => exact nomatch h
  | axiomDecl cv => exact nomatch h
  | defnDecl cv value =>
    simp only [checkDecl, checkConstantVal, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    -- duplicate-name guard
    by_cases hfind : (env.find? cv.name).isSome = true
    case pos => simp [hfind] at h
    simp only [hfind] at h
    -- nodup / level-param guards
    by_cases hnd : Name.nodup cv.levelParams = true
    case neg => simp [hnd] at h
    simp only [hnd] at h
    by_cases htp : Expr.allLevelParamsDefined cv.levelParams cv.type = true
    case neg => simp [htp] at h
    simp only [htp] at h
    -- no free variables / unknown constants in the type
    by_cases htf : cv.type.hasFvar = true
    case pos => simp [htf] at h
    simp only [htf] at h
    by_cases htr : cv.type.constsResolve env = true
    case neg => simp [htr] at h
    simp only [htr] at h
    -- inferType of the declared type
    cases hst : inferType env 0 cv.type with
    | error e => rw [hst] at h; exact nomatch h
    | ok stype =>
    rw [hst] at h; dsimp only at h
    cases hsort : ensureSort env stype with
    | error e => rw [hsort] at h; exact nomatch h
    | ok u =>
    rw [hsort] at h; dsimp only at h
    -- level params / free variables / constants of the value
    by_cases hvp : Expr.allLevelParamsDefined cv.levelParams value = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvf : value.hasFvar = true
    case pos => simp [hvf] at h
    simp only [hvf] at h
    by_cases hvr : value.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    -- inferType of the value
    cases hvt : inferType env 0 value with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h; dsimp only at h
    -- definitional equality of inferred and declared type
    cases hde : isDefEq env 0 vtype cv.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    -- collected facts
    have htf' : cv.type.hasFvar = false := by simpa using htf
    have hvf' : value.hasFvar = false := by simpa using hvf
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar htf'
    have hwv : WScoped 0 value := WScoped.of_not_hasFvar hvf'
    have hfind' : env.find? cv.name = none := by
      revert hfind
      cases env.find? cv.name <;> simp
    have hfresh := find?_none_ne hfind'
    -- the candidate valuation
    obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n φ =>
        if n = cv.name
        then (interpClosed V m.val env φ value).getD SetTheory.empty
        else m.val n φ := ⟨_, rfl⟩
    -- val' agrees with m.val on names resolvable in env
    have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
        val' n ψ = m.val n ψ := by
      intro n hn ψ
      have : n ≠ cv.name := by
        intro heq; rw [heq, hfind'] at hn; simp at hn
      simp [hval', this]
    -- transfer of closed interpretations from (m.val, env) to (val', env')
    have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
        interpClosed V val' (⟨ConstantInfo.defnInfo cv value :: env.consts⟩ : Env) ψ e =
          interpClosed V m.val env ψ e := by
      intro e hres ψ
      rw [interpClosed_mono (cval := val') (c₀ := ConstantInfo.defnInfo cv value) m.wf hfind' hres]
      exact interp_cval_ext hagree e 0 (rho0 V)
    -- the extended environment is well-formed
    have hwf' : EnvWF ⟨ConstantInfo.defnInfo cv value :: env.consts⟩ := by
      refine EnvWF.cons m.wf ?_
      refine ⟨htf', htp, Expr.constsResolve_mono htr, ?_⟩
      intro cv2 value2 heq
      obtain ⟨rfl, rfl⟩ : cv2 = cv ∧ value2 = value := by
        injection heq with h1 h2
        exact ⟨h1.symm, h2.symm⟩
      exact ⟨hvf', hvp, Expr.constsResolve_mono hvr⟩
    -- semantic facts about the new declaration
    have hsound := fun (ψ : Name → Nat) =>
      inferType_sound (φ := ψ) (ρ := rho0 V) m value hvt hwv
        (FvarsOk.of_not_hasFvar hvf')
    have htsound := fun (ψ : Name → Nat) =>
      inferType_sound (φ := ψ) (ρ := rho0 V) m cv.type hst hwt
        (FvarsOk.of_not_hasFvar htf')
    -- the value's interpretation, membership, and param-dependence
    have hkey : ∀ ψ : Name → Nat, ∃ v T,
        interpClosed V m.val env ψ value = some v ∧
        interpClosed V m.val env ψ cv.type = some T ∧ v ∈ˢ T := by
      intro ψ
      obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hokvt⟩ := hsound ψ
      obtain ⟨⟨T, sT, hT, hsT, -⟩, -, -⟩ := htsound ψ
      have htveq : tv = T :=
        isDefEq_sound (φ := ψ) (ρ := rho0 V) m hde hwvt hwt hokvt
          (FvarsOk.of_not_hasFvar htf') htv hT
      exact ⟨v, T, hv, hT, htveq ▸ hmem⟩
    -- construct the model
    refine ⟨⟨val', hwf', ?_, ?_, ?_⟩⟩
    · -- val_params
      intro n ci hf ψ₁ ψ₂ hψ
      rw [Env.find?_cons] at hf
      split at hf
      · next hn =>
        obtain rfl := Option.some.inj hf
        have hncv : n = cv.name := by rw [← hn]; rfl
        subst hncv
        simp only [hval', if_pos rfl]
        have : interpClosed V m.val env ψ₁ value = interpClosed V m.val env ψ₂ value := by
          unfold interpClosed
          exact interp_params_ext m.wf m.val_params
            (by simpa [ConstantInfo.toConstantVal] using hψ) value 0 (rho0 V) hvp
        rw [this]
      · next hn =>
        have hne : n ≠ cv.name := by
          intro heq
          rw [heq, hfind'] at hf
          exact nomatch hf
        simp only [hval', if_neg hne]
        exact m.val_params n ci hf ψ₁ ψ₂ hψ
    · -- mem_type
      intro c hc ψ
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
        refine ⟨T, ?_, ?_⟩
        · exact (htrans cv.type htr ψ).trans hT
        · show val' cv.name ψ ∈ˢ T
          simp only [hval', if_pos rfl, hv, Option.getD_some]
          exact hmem
      · obtain ⟨t, ht, hmem⟩ := m.mem_type c hc ψ
        obtain ⟨-, -, hres, -⟩ := m.wf c hc
        refine ⟨t, ?_, ?_⟩
        · rw [htrans c.toConstantVal.type hres ψ]
          exact ht
        · have hne : c.name ≠ cv.name := hfresh c hc
          simp [hval', hne, hmem]
    · -- defn_eq
      intro cv2 value2 hmem2 ψ
      rcases List.mem_cons.mp hmem2 with heq | hmem2
      · obtain ⟨rfl, rfl⟩ : cv2 = cv ∧ value2 = value := by
          injection heq with h1 h2
          exact ⟨h1, h2⟩
        obtain ⟨v, T, hv, -, -⟩ := hkey ψ
        rw [htrans _ hvr ψ, hv]
        simp [hval', hv]
      · obtain ⟨-, -, -, hvalwf⟩ := m.wf _ hmem2
        obtain ⟨-, -, hres2⟩ := hvalwf cv2 value2 rfl
        have := m.defn_eq cv2 value2 hmem2 ψ
        rw [htrans value2 hres2 ψ, this]
        have hne : cv2.name ≠ cv.name :=
          hfresh (.defnInfo cv2 value2) hmem2
        simp [hval', hne]

private theorem foldlM_sound {env' : Env} :
    ∀ (ds : List Declaration) (env : Env), Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' → Nonempty (EnvModel V env')
  | [], env, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_sound ds env1 (checkDecl_sound hd m) h

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem checkDecls_sound {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env') : Nonempty (EnvModel V env') :=
  foldlM_sound ds Env.empty ⟨EnvModel.empty V⟩ h

end Setlec
