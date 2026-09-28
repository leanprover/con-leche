module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# A container's type former at a key, inverted

`nestInstType` (`Kernel/Inductives/Positivity.lean`) instantiates a
container's stored type former at a key: its parameters a syntactic
telescope, its index telescope at the key hole-free, its sort, and the
key's level count.  Read back at the pure monad; used by the class
check's key inversion (`ClassInv`) and the positivity walk's container
case (`NestContInv`).
-/

namespace ConLeche

/-- **The container's type former, inverted.** -/
theorem nestInstType_inv {ctx : NestCtx} {hi : Nat} {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty)) :
    ∃ cvC caps, ctx.find? key.cname = some (.indInfo cvC caps) ∧
      (cvC.type.stripPis key.ds.length).isSome = true ∧
      cty = cvC.type.instantiateLevelParams cvC.levelParams key.lvls ∧
      ∃ ty s, instPisWith key.ds (cvC.type.instantiateLevelParams cvC.levelParams key.lvls)
          = some ty ∧ ty.piBinders.2 = .sort s ∧
        (ty.piBinders.1.any fun b => b.1.nestOcc ctx.names ctx.nP hi) = false ∧
        nI = ty.piBinders.1.length ∧ Level.isEquiv s ctx.sort = some true := by
  unfold nestInstType at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i cvC hcv
  have hcv' := unwrapOr_ok hcv
  split at hcv'
  · rename_i cv caps hf
    simp only [Option.some.injEq] at hcv'
    subst hcv'
    split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · rename_i hstrip
      split at h
      · simp at h
      rename_i ty hty
      split at h
      · simp at h
      rename_i s hs
      have hs' := unwrapOr_ok hs
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      rename_i hocc
      split at h
      · simp at h
      rename_i bl hbl
      split at h
      · rename_i hbt
        have hlev : Level.isEquiv s ctx.sort = some true := by
          unfold liftFueled at hbl
          split at hbl
          · rename_i a ha; simp only [pure, Except.pure, Except.ok.injEq] at hbl; subst hbl
            simpa using ha.trans (congrArg some hbt)
          · simp [throw, throwThe, MonadExceptOf.throw] at hbl
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨cv, caps, hf, by simpa using hstrip, rfl, _, s, unwrapOr_ok hty, ?_,
          by simpa using hocc, rfl, by simpa using hlev⟩
        split at hs'
        · rename_i s' he; rw [he]; simp only [Option.some.injEq] at hs'; rw [hs']
        · exact nomatch hs'
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · exact nomatch hcv'

/-- **The container is applied at its own level count** (official's
`infer_constant`). -/
theorem nestInstType_lvls {ctx : NestCtx} {hi : Nat} {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty)) :
    ∃ cvC caps, ctx.find? key.cname = some (.indInfo cvC caps) ∧
      key.lvls.length = cvC.levelParams.length := by
  obtain ⟨cvC, caps, hf, -⟩ := nestInstType_inv h
  refine ⟨cvC, caps, hf, ?_⟩
  unfold nestInstType at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i cv hcv
  have hcv' := unwrapOr_ok hcv
  rw [hf] at hcv'
  simp only [Option.some.injEq] at hcv'
  subst hcv'
  split at h
  · assumption
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end ConLeche
