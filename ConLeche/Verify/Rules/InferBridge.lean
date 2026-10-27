module

public import ConLeche.Verify.Rules.Defs
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferIOLemmas
import ConLeche.Verify.Rules.BVUnsatBridge

public section

/-!
# The inference bridges (task #305)

`inferTypeCore` (full grade) and `inferTypeCoreIO` (io grade) at
`fuel + 1` from the five bridges at `fuel`.  Eleven shapes each:

| clause | full inversion | io inversion | rule |
|---|---|---|---|
| `.sort` | inline | `inferTypeCoreIO_sort_eq` | `Infer.sort` |
| `.bvar` | throws | throws | — |
| `.fvar` | inline | `inferTypeCoreIO_fvar_eq` | `Infer.fvar` |
| `.const` | `inferTypeCore_const_inv_full` | `inferTypeCoreIO_const_eq` | `Infer.const` |
| `.lit` | `inferTypeCore_natLit_inv'` / `_strLit_inv'` | `inferTypeCoreIO_lit_eq` | `Infer.natLit` / `strLit` |
| `.forallE` | `inferTypeCore_forall_inv` | `inferTypeCoreIO_forall_inv` | `Infer.forallE` (+ `ensureSortCore_inv`) |
| `.lam` | `inferTypeCore_lam_inv` | `inferTypeCoreIO_lam_inv` | `Infer.lam` |
| `.app` | `inferTypeCore_app_inv` | `inferTypeCoreIO_app_inv` | `Infer.app` |
| `.proj` | `inferTypeCore_proj_inv` | `inferTypeCoreIO_proj_inv` | `Infer.proj` |
| `.letE` | `inferTypeCore_letE_inv` | `inferTypeCoreIO_letE_inv` | — |

The io body recurses through `pureFnsIO`, whose `whnf`/`defeq` are the
full knot's at the same fuel (`pureFnsIO_whnf`, `pureFnsIO_defeq`) and
whose `infer` is the lane at `fuel` (`inferIO_def`).
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {env : Env} {fuel : Nat}

/-! ## The leaf clauses' inversions

`Verify/InferLemmas.lean` inverts the four recursive clauses; the six
leaves (`.sort`, `.fvar`, `.const`'s arity, the two literals, the
`.bvar` throw) have no inversion there; they are stated here (the
rules tier may not import `Model/*`, whose `Tiers.lean` has the two
literal ones) with the io twins.  Each is one `simp only [inferBody, …]`
deep. -/

variable {mode : CheckMode}

/-- The `.sort` clause: the successor sort, no run. -/
theorem inferTypeCore_sort_inv {d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- The `.fvar` clause: the scope guard and the stored annotation. -/
theorem inferTypeCore_fvar_inv {d idx : Nat} {ty t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.fvar idx ty) = .ok t) :
    idx < d ∧ t = ty := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hlt : idx < d
  · rw [ite_eq_left hlt] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hlt, h.symm⟩
  · rw [ite_eq_right hlt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `.bvar` clause throws. -/
theorem inferTypeCore_bvar_inv {d i : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.bvar i) = .ok t) : False := by
  rw [inferTypeCore_succ] at h
  simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h

/-- The `.const` clause, whole: the stored constant, the level arity
and the instantiated type
(`inferTypeCore_const_inv` drops the arity — it is consumed inside its
own `split`). -/
theorem inferTypeCore_const_inv_full {d : Nat} {n : Name} {us : List Level}
    {t : Expr} (h : inferTypeCore mode env (fuel + 1) d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  revert h
  cases hf : env.find? n with
  | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    intro h
    dsimp only at h
    by_cases hlen : us.length = ci.toConstantVal.levelParams.length
    · rw [ite_eq_left hlen] at h
      simp only [Except.ok.injEq] at h
      exact ⟨ci, rfl, hlen, h.symm⟩
    · rw [ite_eq_right hlen] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `Nat`-literal clause: the support guard and `Nat`. -/
theorem inferTypeCore_natLit_inv' {d k : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    natLitSupported env = true ∧ t = .const natName [] := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hg : natLitSupported env = true
  · rw [ite_eq_left hg] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [ite_eq_right hg] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The string-literal clause: the support guard and `String`. -/
theorem inferTypeCore_strLit_inv' {d : Nat} {s : String} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.strVal s)) = .ok t) :
    strLitSupported env = true ∧ t = .const stringName [] := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hg : strLitSupported env = true
  · rw [ite_eq_left hg] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [ite_eq_right hg] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The io lane's `.bvar` clause throws too. -/
theorem inferTypeCoreIO_bvar_inv {d i : Nat} {t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.bvar i) = .ok t) : False := by
  rw [inferTypeCoreIO_succ] at h
  simp [inferBodyIO, throw, throwThe, MonadExceptOf.throw] at h

/-- **`inferTypeCore` at `fuel + 1`**, full grade. -/
theorem infer_bridge_succ (hw : WhnfBridge μ env fuel) (hd : DefEqBridge μ env fuel)
    (hdE : DefEqBridge μ.toEager env fuel) (hi : InferBridge μ env fuel) :
    InferBridge μ env (fuel + 1) := by
  intro d e t h
  match e, h with
  | .bvar _, h => exact (inferTypeCore_bvar_inv h).elim
  | .letE _ _ _, h =>
    obtain ⟨tty, u, tv, hty, hes, hv, hde, hb⟩ := inferTypeCore_letE_inv h
    exact .letE (fun _ => hi hty) (fun _ => hw (ensureSortCore_inv hes)) (fun _ => hi hv)
      (fun _ => hd hde) (hi hb)
  | .sort u, h =>
    obtain rfl := inferTypeCore_sort_inv h
    exact .sort
  | .fvar idx ty, h =>
    obtain ⟨hlt, rfl⟩ := inferTypeCore_fvar_inv h
    exact .fvar hlt
  | .const n us, h =>
    obtain ⟨ci, hf, hlen, rfl⟩ := inferTypeCore_const_inv_full h
    exact .const hf hlen
  | .lit (.natVal k), h =>
    obtain ⟨hg, rfl⟩ := inferTypeCore_natLit_inv' h
    exact .natLit hg
  | .lit (.strVal s), h =>
    obtain ⟨hg, rfl⟩ := inferTypeCore_strLit_inv' h
    exact .strLit hg
  | .forallE ty body, h =>
    obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, rfl⟩ :=
      inferTypeCore_forall_inv h
    exact .forallE (hi hty) (hw hwt) (hi hbt) (hw (ensureSortCore_inv hes))
  | .app f a, h =>
    obtain ⟨tf, ty', body', htf, hwf, rfl, hrest⟩ :=
      inferTypeCore_app_inv h
    rcases hrest with hsk | ⟨ta, hta, hde⟩
    · -- Task #368: the skipped argument check
      exact bvUnsat_bridge (hi htf) (hw hwf) hsk
    -- an `eagerReduce _ _` argument was compared in the eager tower
    -- (task #353): the same rule, from that tower's bridge
    have hD : DefEq env d ta ty' := by
      unfold CheckMode.argMode at hde
      split at hde
      · exact hdE hde
      · exact hd hde
    exact .app (hi htf) (hw hwf) (fun _ => hi hta) (fun _ => hD)
  | .proj sn i pe, h =>
    obtain ⟨tpe, te, T, us, entry, hpe, hwpe, hfn, hentry, hlen, hlvl, hprop,
      rfl, rfl⟩ := inferTypeCore_proj_inv h
    simp only [beq_iff_eq] at hprop
    exact .proj (hi hpe) (hw hwpe) hfn hentry hlen hlvl hprop
  | .lam ty body, h =>
    obtain ⟨tty, u, bt, hty, hwt, hbt, rfl⟩ :=
      inferTypeCore_lam_inv h
    exact .lam (fun _ => hi hty) (fun _ => hw hwt) (hi hbt)

/-- **`inferTypeCoreIO` at `fuel + 1`**, io grade. -/
theorem inferIO_bridge_succ (hw : WhnfBridge μ env fuel)
    (hio : InferIOBridge μ env fuel) :
    InferIOBridge μ env (fuel + 1) := by
  intro d e t h
  match e, h with
  | .bvar _, h => exact (inferTypeCoreIO_bvar_inv h).elim
  | .letE _ _ _, h =>
    exact .letE (s := .bvar 0) (u := .zero) (tv := .bvar 0)
      (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
      (hio (inferTypeCoreIO_letE_inv h))
  | .sort u, h =>
    rw [inferTypeCoreIO_sort_eq] at h
    obtain rfl := inferTypeCore_sort_inv h
    exact .sort
  | .fvar idx ty, h =>
    rw [inferTypeCoreIO_fvar_eq] at h
    obtain ⟨hlt, rfl⟩ := inferTypeCore_fvar_inv h
    exact .fvar hlt
  | .const n us, h =>
    rw [inferTypeCoreIO_const_eq] at h
    obtain ⟨ci, hf, hlen, rfl⟩ := inferTypeCore_const_inv_full h
    exact .const hf hlen
  | .lit (.natVal k), h =>
    rw [inferTypeCoreIO_lit_eq] at h
    obtain ⟨hg, rfl⟩ := inferTypeCore_natLit_inv' h
    exact .natLit hg
  | .lit (.strVal s), h =>
    rw [inferTypeCoreIO_lit_eq] at h
    obtain ⟨hg, rfl⟩ := inferTypeCore_strLit_inv' h
    exact .strLit hg
  | .forallE ty body, h =>
    obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, rfl⟩ :=
      inferTypeCoreIO_forall_inv h
    exact .forallE (hio hty) (hw hwt) (hio hbt) (hw (ensureSortCore_inv hes))
  | .proj sn i pe, h =>
    obtain ⟨tpe, te, T, us, entry, hpe, hwpe, hfn, hentry, hlen, hlvl, hprop,
      rfl, rfl⟩ := inferTypeCoreIO_proj_inv h
    simp only [beq_iff_eq] at hprop
    exact .proj (hio hpe) (hw hwpe) hfn hentry hlen hlvl hprop
  | .app f a, h =>
    obtain ⟨tf, ty', body', htf, hwf, rfl⟩ :=
      inferTypeCoreIO_app_inv h
    exact .app (ta := a) (hio htf) (hw hwf) (fun hg => nomatch hg)
      (fun hg => nomatch hg)
  | .lam ty body, h =>
    obtain ⟨bt, hbt, rfl⟩ := inferTypeCoreIO_lam_inv h
    exact .lam (s := ty) (u := .zero) (fun hg => nomatch hg) (fun hg => nomatch hg)
      (hio hbt)

end ConLeche.Rules
