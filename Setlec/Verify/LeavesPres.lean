import Setlec.Verify.InferLemmas
import Setlec.Verify.Leaves
import Setlec.Verify.InferLeaves

/-!
# Reduction introduces no free-variable leaves

The `LeavesSubCoreF` supplier (ledgered at the head re-basing seal):
`whnfCore`/`whnf` outputs draw every `fvar` leaf from their input.
The proof mirrors `whnfPres_WScoped` clause by clause — the mutual
fuel induction over the core family — with the leaf-subset facts in
place of the scoping facts: rule right-hand sides and stored values
are closed (`EnvWF`), literal expansions are closed (the `WScoped`
facts at depth 0), `majorToCtor`'s fallback carries its leaf subset
in the inversion, and contractions go through
`fvarLeaves_instantiate1`.
-/

namespace Setlec

variable {mode : CheckMode}

open Expr

/-- The nat-literal constructor form is closed. -/
theorem natLitToConstructor_leaves_nil (n : Nat) :
    (natLitToConstructor n).fvarLeaves = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun l hl =>
    absurd (fvarLeaves_lt_of_wscoped
      (natLitToConstructor_WScoped n (d := 0)) l hl)
      (Nat.not_lt_zero _)

/-- The string-literal constructor form is closed. -/
theorem strLitToConstructor_leaves_nil (s : String) :
    (strLitToConstructor s).fvarLeaves = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun l hl =>
    absurd (fvarLeaves_lt_of_wscoped
      (strLitToConstructor_WScoped s 0) l hl)
      (Nat.not_lt_zero _)

/-- The literal-to-constructor conversion introduces no leaves. -/
theorem litToCtorIfNat_leaves {env : Env} {e : Expr} :
    ∀ l ∈ (litToCtorIfNat env e).fvarLeaves, l ∈ e.fvarLeaves := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · intro l hl
      rw [natLitToConstructor_leaves_nil] at hl
      exact absurd hl List.not_mem_nil
    · exact fun l hl => hl
  | .lit (.strVal _) => exact fun l hl => hl
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ =>
    exact fun l hl => hl

/-- Unfolding introduces no leaves (stored values are closed). -/
theorem unfoldDefinition_leaves {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} (h : unfoldDefinition env e = some e₂) :
    ∀ l ∈ e₂.fvarLeaves, l ∈ e.fvarLeaves := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    dsimp only at h
    revert h
    split
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, -, -, hval⟩ := henv _ (find?_mem hf)
      obtain ⟨hvc, -, -, -⟩ := hval cv value rfl
      intro l hl
      rcases fvarLeaves_mkAppN hl with hlh | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [hasFvar_instantiateLevelParams]; exact hvc)] at hlh
        exact absurd hlh List.not_mem_nil
      · exact fvarLeaves_getAppArgs hx l hlx
    · intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨hvc, -, -, -⟩ := hval cv value hint rfl
    intro l hl
    rcases fvarLeaves_mkAppN hl with hlh | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_instantiateLevelParams]; exact hvc)] at hlh
      exact absurd hlh List.not_mem_nil
    · exact fvarLeaves_getAppArgs hx l hlx
  · intro h; exact nomatch h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop introduce no
free-variable leaves. -/
theorem whnfPres_leaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
  | 0 => ⟨(fun {_ _ _} h => nomatch h), (fun {_ _ _} h => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_leaves henv fuel
    constructor
    · -- whnfCore
      intro d e e' h
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | fvar idx n ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | forallE n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | lam n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | lit l =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ (fun l hl => hl)
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE nn tt vv bb =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, whnfCore_def] at h
        intro l hl
        rcases Expr.fvarLeaves_instantiate1 bb 0 (ihCore h l hl)
          with h1 | h1
        · simp only [fvarLeaves]
          exact List.mem_append.2 (.inr h1)
        · simp only [fvarLeaves]
          exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h1)))
      | app f a =>
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hsubf : ∀ l ∈ f'.fvarLeaves, l ∈ f.fvarLeaves :=
          ihCore hwf
        have happ : ∀ l ∈ (Expr.app f' a).fvarLeaves,
            l ∈ (Expr.app f a).fvarLeaves := by
          intro l hl
          simp only [fvarLeaves] at hl ⊢
          rcases List.mem_append.mp hl with h1 | h1
          · exact List.mem_append.2 (.inl (hsubf l h1))
          · exact List.mem_append.2 (.inr h1)
        rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · -- β
          intro l hl
          rcases Expr.fvarLeaves_instantiate1 body 0
              (ihCore hbeta l hl) with h1 | h1
          · refine happ l ?_
            simp only [fvarLeaves]
            exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h1)))
          · simp only [fvarLeaves]
            exact List.mem_append.2 (.inr h1)
        · -- iota
          obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj,
            usj, cvj, cnP, cnF, r, -, -, -, -, -, hfn, hfc, hlen, -, hmaj,
            hlit, hsub, hmfn, hfj, hrule, hml, har1, har2, -, hlev,
            hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ := iotaRec_inv hio
          have hsubM : ∀ l ∈ major.fvarLeaves,
              l ∈ (Expr.app f' a).fvarLeaves := by
            have hsub₀ : ∀ l ∈ major₀.fvarLeaves,
                l ∈ (Expr.app f' a).fvarLeaves := by
              intro l hl
              exact fvarLeaves_getAppArgs (getD_mem (by omega)) l
                (ihLoop hmaj l hl)
            have hsub₁ : ∀ l ∈ major₁.fvarLeaves,
                l ∈ (Expr.app f' a).fvarLeaves := by
              rcases litMajorToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
              · exact fun l hl => hsub₀ l (litToCtorIfNat_leaves l hl)
              · intro l hl
                have hnil := ihLoop hred l hl
                rw [strLitToConstructor_leaves_nil] at hnil
                exact absurd hnil List.not_mem_nil
            rcases majorToCtor_inv hsub with rfl | ⟨-, -, hall, -⟩
            · exact hsub₁
            · intro l hl
              have hcont := List.all_eq_true.mp hall l hl
              exact hsub₁ l (by simpa using hcont)
          intro l hl
          have hl'' := ihCore hwe'' l hl
          refine happ l ?_
          rcases fvarLeaves_mkAppN hl'' with hlh | ⟨x, hx, hlx⟩
          · exfalso
            obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
            obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl r
              (List.mem_of_find?_eq_some hrule)
            rw [fvarLeaves_eq_nil_of_not_hasFvar (by
                rw [hasFvar_instantiateLevelParams]; exact hrf)] at hlh
            exact absurd hlh List.not_mem_nil
          · rcases List.mem_append.mp hx with hx | hx
            · exact fvarLeaves_getAppArgs
                (List.mem_of_mem_take hx) l hlx
            · exact hsubM l (fvarLeaves_getAppArgs
                (List.mem_of_mem_drop hx) l hlx)
        · -- stuck
          exact happ
      | proj sn i pe =>
        obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
        have hsub₂ : ∀ l ∈ e₂.fvarLeaves, l ∈ pe.fvarLeaves :=
          ihLoop he
        have hsub₃ : ∀ l ∈ e₃.fvarLeaves, l ∈ pe.fvarLeaves := by
          rcases projLitToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
          · exact hsub₂
          · intro l hl
            have hnil := ihLoop hred l hl
            rw [strLitToConstructor_leaves_nil] at hnil
            exact absurd hnil List.not_mem_nil
        rcases hcase with rfl |
          ⟨us, entry, hfn2, hf2, hnat, hi, hlen2, hus, hred2, -⟩
        · intro l hl
          simp only [fvarLeaves] at hl ⊢
          exact hsub₃ l hl
        · intro l hl
          have hl2 := ihCore hred2 l hl
          have hl3 := fvarLeaves_getAppArgs (getD_mem (by omega)) l hl2
          simp only [fvarLeaves]
          exact hsub₃ l hl3
    · -- whnf loop
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
        intro n
        induction n with
        | zero => intro _ _ _ h; exact nomatch h
        | succ n ihN =>
          intro d e e' h
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have hsub₁ : ∀ l ∈ e₁.fvarLeaves, l ∈ e.fvarLeaves :=
            ihCore hwc
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ |
            ⟨-, -, rfl⟩
          · intro l hl
            have hl2 := ihN hcont l hl
            rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
              simp [fvarLeaves] at hl2
          · exact fun l hl => hsub₁ l
              (unfoldDefinition_leaves henv hu l (ihN hcont l hl))
          · exact hsub₁
      intro d e e' h
      exact hloop whnfLoopFuel h

/-- Head normalization introduces no leaves. -/
theorem whnfCore_leaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore mode env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_leaves henv fuel).1 h

/-- The reduction loop introduces no leaves. -/
theorem whnf_leaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_leaves henv fuel).2 h

end Setlec
