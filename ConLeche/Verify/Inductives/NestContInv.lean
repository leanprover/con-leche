module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Abstract
public import ConLeche.Verify.Shift

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

open Expr

/-- A former's reduct is the former but for its type. -/
theorem reducedFormer_cv {ops : CheckerOps CheckM} {env : Env} {cv cvR : ConstantVal} {n : Nat}
    (h : reducedFormer ops env cv n = .ok cvR) : cvR = { cv with type := cvR.type } := by
  unfold reducedFormer at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

/-- The telescope's domains are scoped where its type is, at `ops` whose whnf keeps terms
scoped. -/
theorem whnfTelescope_wscoped {ops : CheckerOps CheckM} {env : Env}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w) :
    ∀ (n i : Nat) (e : Expr) (bs : List Expr) (s : Level),
      whnfTelescope ops env i n e = .ok (bs, s) → WScoped i e →
      ∀ (k : Nat) (nd : Expr), bs[k]? = some nd → WScoped (i + k) nd
  | 0, i, e, bs, s, h, _, k, nd, hk => by
    simp only [whnfTelescope, bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp at hk
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, i, e, bs, s, h, hws, k, nd, hk => by
    simp only [whnfTelescope, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i w hwh
    split at h
    · rename_i dom body
      split at h
      · simp at h
      rename_i q hq
      obtain ⟨bs', s'⟩ := q
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hW := hw i e _ hwh hws
      simp only [WScoped] at hW
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact hW.1
      | succ k =>
        rw [show i + (k + 1) = i + 1 + k by omega]
        exact whnfTelescope_wscoped hw n (i + 1) _ bs' s' hq (WScoped.instantiate1 hW.1 0 hW.2) k nd
          (by simpa using hk)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The telescope's domains have no loose bound variable where its type has none, at `ops` whose
whnf keeps that. -/
theorem whnfTelescope_bounded {ops : CheckerOps CheckM} {env : Env}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true) :
    ∀ (n i : Nat) (e : Expr) (bs : List Expr) (s : Level),
      whnfTelescope ops env i n e = .ok (bs, s) → e.looseBVarsBounded 0 = true →
      ∀ nd ∈ bs, nd.looseBVarsBounded 0 = true
  | 0, i, e, bs, s, h, _, nd, hk => by
    simp only [whnfTelescope, bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp at hk
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, i, e, bs, s, h, hb, nd, hk => by
    simp only [whnfTelescope, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i w hwh
    split at h
    · rename_i dom body
      split at h
      · simp at h
      rename_i q hq
      obtain ⟨bs', s'⟩ := q
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hB := hw i e _ hwh hb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hB.1
      · exact whnfTelescope_bounded hw n (i + 1) _ bs' s' hq
          (looseBVarsBounded_instantiate1 (d := i) (ty := dom) body 0 hB.2) nd hk
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A former's reduct has no free variable where its stored type has none. -/
theorem reducedFormer_hasFvar {ops : CheckerOps CheckM} {env : Env} {cv cvR : ConstantVal} {n : Nat}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w)
    (h : reducedFormer ops env cv n = .ok cvR) (hc : cv.type.hasFvar = false) :
    cvR.type.hasFvar = false := by
  unfold reducedFormer at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i q hq
  obtain ⟨bs, s⟩ := q
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow ?_)
  exact closeTelescope_wscoped bs 0 _ (whnfTelescope_wscoped hw n 0 _ bs s hq
    (WScoped.of_not_hasFvar hc)) (by simp [WScoped])

/-- A former's reduct has no loose bound variable where its stored type has none. -/
theorem reducedFormer_looseBVars {ops : CheckerOps CheckM} {env : Env} {cv cvR : ConstantVal}
    {n : Nat}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true)
    (h : reducedFormer ops env cv n = .ok cvR) (hc : cv.type.looseBVarsBounded 0 = true) :
    cvR.type.looseBVarsBounded 0 = true := by
  unfold reducedFormer at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i q hq
  obtain ⟨bs, s⟩ := q
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact closeTelescope_bounded bs 0 _ (whnfTelescope_bounded hw n 0 _ bs s hq hc) rfl

/-- A family's telescope is its stored type, or its reduct. -/
theorem familyTelescope_cases {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr} (h : familyTelescope ops env cv caps = .ok ty) :
    (formerDefHeaded cv = false ∧ ty = cv.type) ∨
    (formerDefHeaded cv = true ∧
      ∃ cvR, reducedFormer ops env cv (caps.nparams + caps.nIdx) = .ok cvR ∧ ty = cvR.type) := by
  unfold familyTelescope at h
  split at h
  · rename_i hd
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    rename_i cvR hr
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .inr ⟨hd, cvR, hr, rfl⟩
  · rename_i hd
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact .inl ⟨by simpa using hd, h.symm⟩

/-- A family's telescope is closed where its stored type is. -/
theorem familyTelescope_hasFvar {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w)
    (h : familyTelescope ops env cv caps = .ok ty)
    (hc : cv.type.hasFvar = false) : ty.hasFvar = false := by
  rcases familyTelescope_cases h with ⟨-, rfl⟩ | ⟨-, cvR, hr, rfl⟩
  · exact hc
  · exact reducedFormer_hasFvar hw hr hc

/-- A family's telescope is scoped where its stored type is. -/
theorem familyTelescope_bounded {ops : CheckerOps CheckM} {env : Env} {cv : ConstantVal}
    {caps : IndCaps} {ty : Expr}
    (hw : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true)
    (h : familyTelescope ops env cv caps = .ok ty)
    (hc : cv.type.looseBVarsBounded 0 = true) : ty.looseBVarsBounded 0 = true := by
  rcases familyTelescope_cases h with ⟨-, rfl⟩ | ⟨-, cvR, hr, rfl⟩
  · exact hc
  · exact reducedFormer_looseBVars hw hr hc

/-- **What `nestInstType` checks of a telescope**: the container is applied at its own level count,
the telescope binds its parameters, its instantiation at the key is `cty`, a telescope ending in a
sort, its index binders name no member and no hole below `hi`, and its sort is the block's. -/
structure NestInstFacts (ctx : NestCtx) (hi : Nat) (key : NestKey) (lps : List Name) (tyC : Expr)
    (nI : Nat) (cty : Expr) : Prop where
  lvls : key.lvls.length = lps.length
  strip : (tyC.stripPis key.ds.length).isSome = true
  inst : instPisWith key.ds (tyC.instantiateLevelParams lps key.lvls) = some cty
  sort : ∃ s, cty.piBinders.2 = .sort s ∧ Level.isEquiv s ctx.sort = some true
  occ : (cty.piBinders.1.any fun b => b.nestOcc ctx.names ctx.nP hi) = false
  count : nI = cty.piBinders.1.length

/-- **The container's type former, inverted.** -/
theorem nestInstType_inv {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi : Nat}
    {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx ops env hi key = .ok (nI, cty)) :
    ∃ cvC caps tyC, ctx.find? key.cname = some (.indInfo cvC caps) ∧
      familyTelescope ops env cvC caps = .ok tyC ∧
      NestInstFacts ctx hi key cvC.levelParams tyC nI cty := by
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
        refine ⟨cv, caps, tyC, hf, hfam, by simpa using hl, by simpa using hstrip,
          unwrapOr_ok hty, ⟨s, ?_, by simpa using hlev⟩, by simpa using hocc, rfl⟩
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
    {key : NestKey} {cvC : ConstantVal} {caps : IndCaps} {tyC cty : Expr} {nI : Nat}
    (hf : ctx.find? key.cname = some (.indInfo cvC caps))
    (hfam : familyTelescope ops env cvC caps = .ok tyC)
    (h : NestInstFacts ctx hi key cvC.levelParams tyC nI cty) :
    nestInstType (m := CheckM) ctx ops env hi key = .ok (nI, cty) := by
  obtain ⟨hl, hstrip, hty, ⟨s, hs, hlev⟩, hocc, rfl⟩ := h
  unfold nestInstType
  simp [bind, Except.bind, hf, hfam, unwrapOr, hl, hstrip, hty, hs, hocc, liftFueled, hlev, pure,
    Except.pure]

/-- The checks of a telescope hold at a smaller hole range: only the index telescope's occurrence
test (N2) reads `hi`, and it is monotone. -/
theorem NestInstFacts.mono_hi {ctx : NestCtx} {hi hi' : Nat} (hle : hi' ≤ hi) {key : NestKey}
    {lps : List Name} {tyC cty : Expr} {nI : Nat} (h : NestInstFacts ctx hi key lps tyC nI cty) :
    NestInstFacts ctx hi' key lps tyC nI cty := by
  obtain ⟨hl, hstrip, hty, hs, hocc, hc⟩ := h
  refine ⟨hl, hstrip, hty, hs, ?_, hc⟩
  rw [List.any_eq_false] at hocc ⊢
  intro b hb hb'
  exact hocc b hb (Expr.nestOcc_mono_hi hle _ hb')

/-- **The type former's checks hold at a smaller hole range**. -/
theorem nestInstType_mono_hi {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi hi' : Nat}
    (hle : hi' ≤ hi) {key : NestKey} {nI : Nat} {cty : Expr}
    (h : nestInstType (m := CheckM) ctx ops env hi key = .ok (nI, cty)) :
    nestInstType (m := CheckM) ctx ops env hi' key = .ok (nI, cty) := by
  obtain ⟨cvC, caps, tyC, hf, hfam, hF⟩ := nestInstType_inv h
  exact nestInstType_of hf hfam (hF.mono_hi hle)

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
