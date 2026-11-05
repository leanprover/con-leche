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

/-- A family's telescope is its stored type, or a closed reduct of it. -/
theorem familyTelescope_cases {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr} (h : familyTelescope ops env cv caps = .ok ty) :
    (formerDefHeaded cv = false ∧ ty = cv.type) ∨
    (formerDefHeaded cv = true ∧ ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true ∧
      ∃ cvR, reducedFormer ops env cv (caps.nparams + caps.nIdx) = .ok cvR ∧ ty = cvR.type) := by
  unfold familyTelescope at h
  split at h
  · rename_i hd
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    rename_i cvR hr
    split at h
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact .inr ⟨hd, hc.1, hc.2, cvR, hr, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hd
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact .inl ⟨by simpa using hd, h.symm⟩

/-- A family's telescope is closed where its stored type is. -/
theorem familyTelescope_hasFvar {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr} (h : familyTelescope ops env cv caps = .ok ty)
    (hc : cv.type.hasFvar = false) : ty.hasFvar = false := by
  rcases familyTelescope_cases h with ⟨-, rfl⟩ | ⟨-, hf, -⟩
  · exact hc
  · exact hf

/-- A family's telescope is scoped where its stored type is. -/
theorem familyTelescope_bounded {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr} (h : familyTelescope ops env cv caps = .ok ty)
    (hc : cv.type.looseBVarsBounded 0 = true) : ty.looseBVarsBounded 0 = true := by
  rcases familyTelescope_cases h with ⟨-, rfl⟩ | ⟨-, -, hb, -⟩
  · exact hc
  · exact hb

/-- **The container's type former, inverted.** -/
theorem nestInstType_inv {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi : Nat}
    {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx ops env hi key = .ok (nI, cty)) :
    ∃ cvC caps tyC, ctx.find? key.cname = some (.indInfo cvC caps) ∧
      familyTelescope ops env cvC caps = .ok tyC ∧
      key.lvls.length = cvC.levelParams.length ∧
      (tyC.stripPis key.ds.length).isSome = true ∧
      ∃ s, instPisWith key.ds (tyC.instantiateLevelParams cvC.levelParams key.lvls) = some cty ∧
        cty.piBinders.2 = .sort s ∧
        (cty.piBinders.1.any fun b => b.nestOcc ctx.names ctx.nP hi) = false ∧
        nI = cty.piBinders.1.length ∧ Level.isEquiv s ctx.sort = some true := by
  unfold nestInstType at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i q hq
  obtain ⟨cvC, capsC⟩ := q
  have hq' := unwrapOr_ok hq
  split at hq'
  · rename_i cv caps hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    dsimp only at h
    split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hl
    split at h
    · simp at h
    rename_i tyC hfam
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
        refine ⟨cv, caps, tyC, hf, hfam, by simpa using hl, by simpa using hstrip, s,
          unwrapOr_ok hty, ?_, by simpa using hocc, rfl, by simpa using hlev⟩
        split at hs'
        · rename_i s' he; rw [he]; simp only [Option.some.injEq] at hs'; rw [hs']
        · exact nomatch hs'
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · exact nomatch hq'

/-- The occurrence test is monotone in the hole range's upper end. -/
theorem Expr.nestOcc_mono_hi {names : List Name} {lo hi hi' : Nat} (hle : hi' ≤ hi) :
    ∀ e : Expr, e.nestOcc names lo hi' = true → e.nestOcc names lo hi = true
  | .bvar _, h | .sort _, h | .lit _, h => by simp [Expr.nestOcc] at h
  | .const _ _, h => h
  | .fvar _ _, h => by simp only [Expr.nestOcc, decide_eq_true_eq] at h ⊢; omega
  | .app f a, h => by
    simp only [Expr.nestOcc, Bool.or_eq_true] at h ⊢
    exact h.imp (nestOcc_mono_hi hle f) (nestOcc_mono_hi hle a)
  | .lam ty b, h | .forallE ty b, h => by
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
theorem nestInstType_of {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi : Nat}
    {key : NestKey} {cvC : ConstantVal} {caps : IndCaps} {tyC ty : Expr} {s : Level}
    (hf : ctx.find? key.cname = some (.indInfo cvC caps))
    (hfam : familyTelescope ops env cvC caps = .ok tyC)
    (hl : key.lvls.length = cvC.levelParams.length)
    (hstrip : (tyC.stripPis key.ds.length).isSome = true)
    (hty : instPisWith key.ds (tyC.instantiateLevelParams cvC.levelParams key.lvls) = some ty)
    (hs : ty.piBinders.2 = .sort s)
    (hocc : (ty.piBinders.1.any fun b => b.nestOcc ctx.names ctx.nP hi) = false)
    (hlev : Level.isEquiv s ctx.sort = some true) :
    nestInstType (m := CheckM) ctx ops env hi key = .ok (ty.piBinders.1.length, ty) := by
  unfold nestInstType
  simp [bind, Except.bind, hf, hfam, unwrapOr, hl, hstrip, hty, hs, hocc, liftFueled, hlev, pure,
    Except.pure]

/-- **The type former's checks hold at a smaller hole range**: only the
index telescope's occurrence test (N2) reads `hi`, and it is monotone. -/
theorem nestInstType_mono_hi {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi hi' : Nat}
    (hle : hi' ≤ hi) {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx ops env hi key = .ok (nI, cty)) :
    nestInstType (m := CheckM) ctx ops env hi' key = .ok (nI, cty) := by
  obtain ⟨cvC, caps, tyC, hf, hfam, hl, hstrip, s, hty, hs, hocc, rfl, hlev⟩ := nestInstType_inv h
  refine nestInstType_of hf hfam hl hstrip hty hs ?_ hlev
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
      ∃ nI cty, nestInstType (m := CheckM) ctx ops env (ctx.hiAt prog.length) ⟨n, us, args.take nPc⟩
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
