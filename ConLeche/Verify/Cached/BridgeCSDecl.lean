module

public import ConLeche.Verify.Cached.BridgeCS4

public section

/-!
# Cached shared-state checker: `CheckCM` peels and the extending stages

The `throw`/`ite`/`bind` peels at the cached monad (they are
monad-specific: `rfl` at a concrete `StateT`),
the `_pushC` lemmas taking indexed (`FEnv`) stages to their `Env`
counterparts, and the run-level projection-table stage of a
structure's install.  The `.indDecl` dispatch
(`checkModeledOrNativeSF_run`) is in
`ConLeche/Verify/Cached/TargetRecC.lean`, beside the k-ary block run it
dispatches to.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached


open ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## `CheckCM` peels -/

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem installBasisDeclF_pushC (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckCM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindC] <;> rfl

/-! ### The direct simple-structure path's extending stages (task #175) -/

/-- The projection table's checks at the cached driver: operation-free, the state unchanged, the
verdict the pure stage's. -/
theorem checkStructProjTableS_run {t : ProjTable} (env : Env) {s₀ : CState} {u : Unit}
    {s' : CState} (h : checkStructProjTable (m := CheckCM) t env s₀ = .ok (u, s')) :
    s' = s₀ ∧ checkStructProjTable (m := CheckM) t env = .ok () := by
  unfold checkStructProjTable at h ⊢
  dsimp only at h ⊢
  split at h
  · next hg =>
    rw [ite_eq_left hg]
    split at h
    · next hT =>
      rw [ite_eq_left hT]
      split at h
      · next hn =>
        rw [ite_eq_left hn]
        obtain ⟨-, rfl⟩ := pureC_ok h
        exact ⟨rfl, rfl⟩
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

end ConLeche.Cached
