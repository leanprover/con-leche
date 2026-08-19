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

open SetTheory

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
    -- inferType of the declared type
    cases hst : inferType env cv.type with
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
    -- inferType of the value
    cases hvt : inferType env value with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h; dsimp only at h
    -- definitional equality of inferred and declared type
    cases hde : isDefEq env vtype cv.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    -- construct the extended model
    have hfind' : env.find? cv.name = none := by
      revert hfind
      cases env.find? cv.name <;> simp
    have hfresh := find?_none_ne hfind'
    refine ⟨⟨fun n φ => if n = cv.name
        then (interpExpr V φ value).getD SetTheory.empty
        else m.val n φ, ?_, ?_⟩⟩
    · intro c hc φ
      rcases List.mem_cons.mp hc with rfl | hc
      · -- the new constant
        obtain ⟨v, tv, hv, htv, hmem⟩ := inferType_sound (V := V) hvt φ
        obtain ⟨T, sT, hT, hsT, -⟩ := inferType_sound (V := V) hst φ
        have : tv = T := isDefEq_sound hde φ htv hT
        subst this
        refine ⟨tv, hT, ?_⟩
        simp [ConstantInfo.name, ConstantInfo.toConstantVal, hv, hmem]
      · -- a pre-existing constant
        obtain ⟨t, ht, hmem⟩ := m.mem_type c hc φ
        refine ⟨t, ht, ?_⟩
        have : c.name ≠ cv.name := hfresh c hc
        simp [this, hmem]
    · intro cv2 value2 hmem2 φ
      rcases List.mem_cons.mp hmem2 with heq | hmem2
      · obtain ⟨rfl, rfl⟩ : cv2 = cv ∧ value2 = value := by
          injection heq with h1 h2; exact ⟨h1, h2⟩
        obtain ⟨v, tv, hv, -, -⟩ := inferType_sound (V := V) hvt φ
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
