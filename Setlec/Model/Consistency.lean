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
    -- no free variables in the type
    by_cases htf : cv.type.hasFvar = true
    case pos => simp [htf] at h
    simp only [htf] at h
    -- inferType of the declared type
    cases hst : inferType env 0 cv.type with
    | error e => rw [hst] at h; exact nomatch h
    | ok stype =>
    rw [hst] at h; dsimp only at h
    cases hsort : ensureSort env stype with
    | error e => rw [hsort] at h; exact nomatch h
    | ok u =>
    rw [hsort] at h; dsimp only at h
    -- level params of the value
    by_cases hvp : Expr.allLevelParamsDefined cv.levelParams value = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    -- no free variables in the value
    by_cases hvf : value.hasFvar = true
    case pos => simp [hvf] at h
    simp only [hvf] at h
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
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar (by simpa using htf)
    have hwv : WScoped 0 value := WScoped.of_not_hasFvar (by simpa using hvf)
    have hfind' : env.find? cv.name = none := by
      revert hfind
      cases env.find? cv.name <;> simp
    have hfresh := find?_none_ne hfind'
    -- the interpretation ignores the extension (current fragment)
    have hirr : ∀ (φ : Name → Nat) (e : Expr),
        interpClosed V (⟨ConstantInfo.defnInfo cv value :: env.consts⟩ : Env) φ e =
          interpClosed V env φ e :=
      fun φ e => interpClosed_env_irrel _ env e
    -- construct the extended model
    refine ⟨⟨fun n φ => if n = cv.name
        then (interpClosed V env φ value).getD SetTheory.empty
        else m.val n φ, ?_, ?_⟩⟩
    · intro c hc φ
      rw [hirr]
      rcases List.mem_cons.mp hc with rfl | hc
      · -- the new constant
        obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hokvt⟩ :=
          inferType_sound (V := V) (φ := φ) (ρ := rho0 V) value hvt hwv
            (FvarsOk.of_not_hasFvar (by simpa using hvf))
        obtain ⟨⟨T, sT, hT, hsT, -⟩, -, -⟩ :=
          inferType_sound (V := V) (φ := φ) (ρ := rho0 V) cv.type hst hwt
            (FvarsOk.of_not_hasFvar (by simpa using htf))
        have htveq : tv = T :=
          isDefEq_sound (ρ := rho0 V) hde hwvt hwt hokvt
            (FvarsOk.of_not_hasFvar (by simpa using htf)) htv hT
        subst htveq
        refine ⟨tv, hT, ?_⟩
        simp [ConstantInfo.name, ConstantInfo.toConstantVal, interpClosed, hv, hmem]
      · -- a pre-existing constant
        obtain ⟨t, ht, hmem⟩ := m.mem_type c hc φ
        refine ⟨t, ht, ?_⟩
        have : c.name ≠ cv.name := hfresh c hc
        simp [this, hmem]
    · intro cv2 value2 hmem2 φ
      rw [hirr]
      rcases List.mem_cons.mp hmem2 with heq | hmem2
      · have h12 : cv2 = cv ∧ value2 = value := by
          injection heq with h1 h2; exact ⟨h1, h2⟩
        obtain ⟨⟨v, tv, hv, -, -⟩, -, -⟩ :=
          inferType_sound (V := V) (φ := φ) (ρ := rho0 V) value hvt hwv
            (FvarsOk.of_not_hasFvar (by simpa using hvf))
        rw [h12.1, h12.2]
        simp only [interpClosed] at hv ⊢
        simp [hv]
      · have hne : cv2.name ≠ cv.name :=
          hfresh (.defnInfo cv2 value2) hmem2
        have := m.defn_eq cv2 value2 hmem2 φ
        simp [hne, this]

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
