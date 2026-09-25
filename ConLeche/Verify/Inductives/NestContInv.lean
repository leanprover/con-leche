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

end ConLeche

namespace ConLeche

/-- **The container case's checks, inverted.** -/
theorem nestCont_inv {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}
    {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level} {args : List Expr}
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestCont ctx ops env rec syn prog kb n us args st = .ok (k, st')) :
    ∃ nPc L, (nestContainerC ctx st n).1 = some (nPc, L) ∧ nPc ≤ args.length ∧
      ((args.drop nPc).all fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) = true ∧
      n ≠ quotName ∧
      ((args.take nPc).all fun x => x.bvarB == 0 && decide (x.fvarB ≤ ctx.hiAt prog.length))
        = true ∧
      ∃ nI cty, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, args.take nPc⟩
          = .ok (nI, cty) ∧ args.length = nPc + nI ∧
        nestContKey ctx ops env rec syn prog kb n us (args.take nPc) nPc (nestContainerC ctx st n).2
          = .ok (k, st') := by
  simp only [nestCont, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i q hq
  have hq' := unwrapOr_ok hq
  obtain ⟨nPc, L⟩ := q
  dsimp only at h
  by_cases h2 : (decide (args.length < nPc) ||
      !(List.drop nPc args).all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x)
        = true
  · rw [if_pos h2] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg h2] at h
  by_cases h3 : (n == quotName) = true
  · rw [if_pos h3] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg h3] at h
  have h4 : ((List.take nPc args).all fun x => x.bvarB == 0 &&
      decide (x.fvarB ≤ ctx.hiAt prog.length)) = true := by
    cases hc : ((List.take nPc args).all fun x => x.bvarB == 0 &&
      decide (x.fvarB ≤ ctx.hiAt prog.length))
    · rw [hc] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    · rfl
  rw [if_pos h4] at h
  split at h
  · simp at h
  rename_i ni hni
  obtain ⟨nI, cty⟩ := ni
  dsimp only at h
  have h5 : (args.length == nPc + nI) = true := by
    cases hc : (args.length == nPc + nI)
    · rw [hc] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    · rfl
  rw [if_pos h5] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at h2
  refine ⟨nPc, L, hq', by omega, by simpa using h2.2, by simpa using h3, h4,
    nI, cty, hni, by simpa using h5, h⟩

end ConLeche
