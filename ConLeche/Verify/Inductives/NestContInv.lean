module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The container case of the positivity walk, inverted (lane CONTSEM)

`nestCont` and the frame machinery below it
(`Kernel/Inductives/Positivity.lean`) read back at the pure monad: what
a successful run checked, piece by piece — the container's type former
(`nestInstType`: its parameters a syntactic telescope, its index
telescope at the key hole-free (N2), its sort), the key's parameters,
and the instantiation's lookup.  The semantic side
(`Model/Inductives/ContSem.lean`) consumes these facts.
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
        nI = ty.piBinders.1.length := by
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
      · rename_i hlev
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨cv, caps, hf, by simpa using hstrip, rfl, _, s, unwrapOr_ok hty, ?_,
          by simpa using hocc, rfl⟩
        split at hs'
        · rename_i s' he; rw [he]; simp only [Option.some.injEq] at hs'; rw [hs']
        · exact nomatch hs'
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · exact nomatch hcv'

end ConLeche
