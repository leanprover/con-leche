module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# The container case of the positivity walk, inverted

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
      instPisWith key.ds (cvC.type.instantiateLevelParams cvC.levelParams key.lvls)
        = some cty ∧
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
        refine ⟨cv, caps, hf, by simpa using hstrip, unwrapOr_ok hty, _, s, unwrapOr_ok hty, ?_,
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

/-- The occurrence test is monotone in the hole range's upper end. -/
theorem Expr.nestOcc_mono_hi {names : List Name} {lo hi hi' : Nat} (hle : hi' ≤ hi) :
    ∀ e : Expr, e.nestOcc names lo hi' = true → e.nestOcc names lo hi = true
  | .bvar _, h | .sort _, h | .lit _, h => by simp [Expr.nestOcc] at h
  | .const _ _, h => h
  | .fvar _ _, h => by simp only [Expr.nestOcc, decide_eq_true_eq] at h ⊢; omega
  | .app f a, h => by
    simp only [Expr.nestOcc, Bool.or_eq_true] at h ⊢
    exact h.imp (nestOcc_mono_hi hle f) (nestOcc_mono_hi hle a)
  | .lam ty b _, h | .forallE ty b _, h => by
    simp only [Expr.nestOcc, Bool.or_eq_true] at h ⊢
    exact h.imp (nestOcc_mono_hi hle ty) (nestOcc_mono_hi hle b)
  | .letE ty v b, h => by
    simp only [Expr.nestOcc, Bool.or_eq_true] at h ⊢
    exact h.imp (Or.imp (nestOcc_mono_hi hle ty) (nestOcc_mono_hi hle v)) (nestOcc_mono_hi hle b)
  | .proj _ _ x, h => by
    simp only [Expr.nestOcc] at h ⊢
    exact nestOcc_mono_hi hle x h

/-- **The container's type former, from its facts** (`nestInstType_inv`'s
converse). -/
theorem nestInstType_of {ctx : NestCtx} {hi : Nat} {key : NestKey} {cvC : ConstantVal}
    {caps : IndCaps} {ty : Expr} {s : Level}
    (hf : ctx.find? key.cname = some (.indInfo cvC caps))
    (hl : key.lvls.length = cvC.levelParams.length)
    (hstrip : (cvC.type.stripPis key.ds.length).isSome = true)
    (hty : instPisWith key.ds (cvC.type.instantiateLevelParams cvC.levelParams key.lvls) = some ty)
    (hs : ty.piBinders.2 = .sort s)
    (hocc : (ty.piBinders.1.any fun b => b.1.nestOcc ctx.names ctx.nP hi) = false)
    (hlev : Level.isEquiv s ctx.sort = some true) :
    nestInstType (m := CheckM) ctx hi key = .ok (ty.piBinders.1.length, ty) := by
  unfold nestInstType
  simp [bind, Except.bind, hf, unwrapOr, hl, hstrip, hty, hs, hocc, liftFueled, hlev, pure,
    Except.pure]

/-- **The type former's checks hold at a smaller hole range**: only the
index telescope's occurrence test (N2) reads `hi`, and it is monotone. -/
theorem nestInstType_mono_hi {ctx : NestCtx} {hi hi' : Nat} (hle : hi' ≤ hi) {key : NestKey}
    {nI : Nat} {cty : Expr} (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty)) :
    nestInstType (m := CheckM) ctx hi' key = .ok (nI, cty) := by
  obtain ⟨cvC, caps, hf, hstrip, hcty, ty, s, hty, hs, hocc, rfl, hlev⟩ := nestInstType_inv h
  obtain rfl : cty = ty := by simpa [hty] using hcty.symm
  obtain ⟨cvC', caps', hf', hl⟩ := nestInstType_lvls h
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cvC = cvC' ∧ caps = caps' := by simpa using hf'
  refine nestInstType_of hf hl hstrip hty hs ?_ hlev
  rw [List.any_eq_false] at hocc ⊢
  intro b hb hb'
  exact hocc b hb (Expr.nestOcc_mono_hi hle _ hb')

end ConLeche

namespace ConLeche

/-- **The container case's checks, inverted.** -/
theorem nestCont_inv {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level} {args : List Expr}
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestCont ctx ops env rec prog kb n us args st = .ok (k, st')) :
    ∃ nPc L, nestContainer ctx n = some (nPc, L) ∧ nPc ≤ args.length ∧
      ((args.drop nPc).all fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) = true ∧
      n ≠ quotName ∧
      ((args.take nPc).all fun x => x.bvarB == 0 && decide (x.fvarB ≤ ctx.hiAt prog.length))
        = true ∧
      ∃ nI cty, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, args.take nPc⟩
          = .ok (nI, cty) ∧ args.length = nPc + nI ∧
        nestContKey ctx ops env rec prog kb n us (args.take nPc) nPc cty st
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
  · rw [ite_eq_left h2] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right h2] at h
  by_cases h3 : (n == quotName) = true
  · rw [ite_eq_left h3] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right h3] at h
  have h4 : ((List.take nPc args).all fun x => x.bvarB == 0 &&
      decide (x.fvarB ≤ ctx.hiAt prog.length)) = true := by
    cases hc : ((List.take nPc args).all fun x => x.bvarB == 0 &&
      decide (x.fvarB ≤ ctx.hiAt prog.length))
    · rw [hc] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    · rfl
  rw [ite_eq_left h4] at h
  split at h
  · simp at h
  rename_i ni hni
  obtain ⟨nI, cty⟩ := ni
  dsimp only at h
  have h5 : (args.length == nPc + nI) = true := by
    cases hc : (args.length == nPc + nI)
    · rw [hc] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    · rfl
  rw [ite_eq_left h5] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at h2
  refine ⟨nPc, L, hq', by omega, by simpa using h2.2, by simpa using h3, h4,
    nI, cty, hni, by simpa using h5, h⟩

end ConLeche
