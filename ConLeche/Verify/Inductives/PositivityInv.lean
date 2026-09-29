module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.UniformOcc
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The install's positivity stage, inverted

`checkBlockPositivity` (`Kernel/Inductives/BlockInstall.lean`) read back
constructor by constructor: the canonical parameters are the head
former's opened telescope, the holes are the members' stored types at
`nP + t`, and every stored constructor went through the ROOT frame
(`nestRoot`: its member-abstracted type `instPisWith params
(nestAbstract ctx holes cty)` inferred at the holes' context — the
typing the monotonicity premises read — and walked, read once into its
derivation by `checkBlockPositivity_deriv`; its monotonicity is
`posD_mono`), after official's uniform-occurrence check (`nestUniform`,
which yields M2′ here and the normal forms' `holesApplied`,
`HolesApplied.lean`), then the fields' universes at the holes.
-/

namespace ConLeche

/-- The context `checkBlockPositivity` builds. -/
@[expose] def BlockParts.nestCtx (p : BlockParts) (fvsP : List Expr)
    (find? : Name → Option ConstantInfo) : NestCtx :=
  ⟨p.memberNames, p.lps, p.nP, p.nIdxs, fvsP, p.resSort, find?⟩

/-- **A frame's constructor list, run**: one output per constructor, and
every constructor's instantiated type typed at the frame's depth. -/
theorem nestCtors_typed {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr} {nPc : Nat}
    {sub : Name → List Level → Option Expr} :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestState} {os : List (List NestFieldKind × Expr)}
      {st' : NestState},
      nestCtors ctx ops env rec prog hi us ds nPc sub cs st = .ok (os, st') →
      os.length = cs.length ∧ ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ty, instPisWith ds
            ((cA.1.type.instantiateLevelParams cA.1.levelParams us).replaceConsts sub) = some crest ∧ ops.inferType env hi crest = .ok ty
  | [], st, os, st', h => by
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, fun _ _ hj => by simp at hj⟩
  | (cv, nF) :: cs, st, os, st', h => by
    simp only [nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    split at h
    · simp at h
    rename_i crest hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h
      · simp at h
      rename_i r hr
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hl, hall⟩ := nestCtors_typed hr
      refine ⟨by simp [hl], fun j cA hj => ?_⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact ⟨crest, ty, unwrapOr_ok hcrest, hty⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        exact hall j cA hj
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The root frame, run**: every member's constructors through the one
constructor loop at the root key, the state threaded; its output per
member. -/
theorem nestRoot_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr} :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestState}
      {outs : List (List (List NestFieldKind × Expr))} {st' : NestState},
      nestRoot ops env ctx holes css st = .ok (outs, st') →
      outs.length = css.length ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs → ∃ st₀ os st₁,
        nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
          (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.nP (nestRootSub ctx holes) cs st₀
          = .ok (os, st₁) ∧ outs[c]? = some os
  | [], _, _, _, h => by
    simp only [nestRoot, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, fun _ _ hc => by simp at hc⟩
  | cs₀ :: css, st, outs, st', h => by
    simp only [nestRoot, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨o, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨os₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hl, hall⟩ := nestRoot_inv hr₂
    refine ⟨by simp [hl], fun c cs hc => ?_⟩
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨st, o, st₁, hr₁, rfl⟩
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact hall c cs hc

/-- **The fields' universes at the holes at one member**, inverted. -/
theorem checkAbsCtorSorts_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {cs : List (ConstantVal × Nat)} {os : List (List NestFieldKind × Expr)},
      checkAbsCtorSorts ops env ctx cs os = .ok () →
      ∀ (j : Nat) (cA : ConstantVal × Nat) (o : List NestFieldKind × Expr), cs[j]? = some cA →
        os[j]? = some o →
        o.2.allLevelParamsDefined ctx.lps = true ∧
        ∃ xq sorts, openPisAtFvars cA.2 o.2 (ctx.hiAt 0) = some xq ∧
          checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
            ctx.sort (ctx.hiAt 0) xq.1 [] cA.2 = .ok sorts
  | [], _, _, j, cA, _, hj, _ => by simp at hj
  | _ :: _, [], _, j, cA, _, _, ho => by simp at ho
  | c :: cs, o :: os, h, j, cA, o', hj, ho => by
    simp only [checkAbsCtorSorts, bind, Except.bind] at h
    by_cases hlp' : o.2.allLevelParamsDefined ctx.lps = true
    case neg =>
      simp [hlp', throw, throwThe, MonadExceptOf.throw] at h
    simp only [hlp', ↓reduceIte] at h
    split at h
    · simp at h
    rename_i xq hxq
    split at h
    · simp at h
    rename_i sorts hsorts
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj ho
      subst hj ho
      exact ⟨hlp', xq, sorts, unwrapOr_ok hxq, hsorts⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ho
      exact checkAbsCtorSorts_inv h j cA o' hj ho

theorem checkAbsCtorSortsAll_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {css : List (List (ConstantVal × Nat))} {oss : List (List (List NestFieldKind × Expr))},
      checkAbsCtorSortsAll ops env ctx css oss = .ok () →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)),
        css[c]? = some cs → oss[c]? = some os → checkAbsCtorSorts ops env ctx cs os = .ok ()
  | [], _, _, c, cs, _, hc, _ => by simp at hc
  | _ :: _, [], _, c, cs, _, _, ho => by simp at ho
  | cs₀ :: css, os₀ :: oss, h, c, cs, os, hc, ho => by
    simp only [checkAbsCtorSortsAll, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i u hu
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc ho
      subst hc ho
      exact hu
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ho
      exact checkAbsCtorSortsAll_inv h c cs os hc ho

/-- **The walk's context, inverted** (`blockNestCtx`): the first
former's parameter telescope opened at the canonical variables, the
context at them, its holes. -/
theorem blockNestCtx_inv {p : BlockShape} {cvTas : List ConstantVal}
    {find? : Name → Option ConstantInfo} {ctx : NestCtx}
    {holes : List Expr}
    (h : blockNestCtx (m := CheckM) p cvTas find? = .ok (ctx, holes)) :
    ∃ cvTa0 fvsP rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      ctx = p.nestCtx fvsP find? ∧ nestHoles ctx = some holes := by
  simp only [blockNestCtx, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i cvTa0 hcv
  split at h
  · simp at h
  rename_i pq hpq
  split at h
  · simp at h
  rename_i holes' hholes
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨cvTa0, pq.1, pq.2, unwrapOr_ok hcv, unwrapOr_ok hpq, rfl, unwrapOr_ok hholes⟩

/-- **The install's positivity stage, inverted into its parts**: the
walk's context, official's uniform check, the root frame's run (from the
empty state), the fields' universes — and the outputs are its kinds and
normal forms, its final state the stage's. -/
theorem checkBlockPositivity_inv {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (h : checkBlockPositivity ops env₁ find? p cvTas ctorsAs = .ok (kinds, nfs, pos)) :
    ∃ cvTa0 fvsP rest holes outs, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find?) = some holes ∧
      nestUniform (m := CheckM) (p.nestCtx fvsP find?) holes ctorsAs = .ok () ∧
      nestRoot ops env₁ (p.nestCtx fvsP find?) holes ctorsAs {} = .ok (outs, pos) ∧
      checkAbsCtorSortsAll ops env₁ (p.nestCtx fvsP find?) ctorsAs outs = .ok () ∧
      kinds = outs.map (·.map (·.1)) ∧ nfs = outs.map (·.map (·.2)) := by
  simp only [checkBlockPositivity, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r₀ hr₀
  obtain ⟨ctx, holes⟩ := r₀
  obtain ⟨cvTa0, fvsP, rest, hcv', hpq', rfl, hh⟩ := blockNestCtx_inv hr₀
  simp only at h
  split at h
  · simp at h
  rename_i u hL
  cases u
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨outs, st⟩ := r
  simp only at h
  split at h
  · simp at h
  rename_i u hA
  cases u
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨cvTa0, fvsP, rest, holes, outs, hcv', hpq', hh, hL, hr, hA, rfl, rfl⟩

/-- The root's substitution at a constructor of the block's own levels is
the member abstraction. -/
theorem rootCrest_eq (ctx : NestCtx) (holes : List Expr) {cv : ConstantVal}
    (hlps : cv.levelParams = ctx.lps) :
    (cv.type.instantiateLevelParams cv.levelParams (ctx.lps.map .param)).replaceConsts
      (nestRootSub ctx holes) = nestAbstract ctx holes cv.type := by
  rw [hlps, Expr.instantiateLevelParams_self, nestAbstract_eq]

/-- An output list's entry, read by `getD`. -/
theorem outs_getD {α β : Type} [Inhabited β] {outs : List (List α)} {f : α → β} {c j : Nat}
    {os : List α} {o : α} (hc : outs[c]? = some os) (hj : os[j]? = some o) (d : β) :
    ((outs.map (·.map f)).getD c []).getD j d = f o := by
  simp [List.getD_eq_getElem?_getD, hc, hj]

/-- **M2′ at every stored constructor** (official's uniform check): its
member-abstracted declared type mentions no member constant. -/
theorem checkBlockPositivity_m2 {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (h : checkBlockPositivity ops env₁ find? p cvTas ctorsAs = .ok (kinds, nfs, pos)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find?) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
          (nestAbstract (p.nestCtx fvsP find?) holes cA.1.type).nestOcc
            (p.nestCtx fvsP find?).names 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, outs, hcv', hpq', hh, hU, -, -, -, -⟩ :=
    checkBlockPositivity_inv h
  refine ⟨cvTa0, fvsP, rest, holes, hcv', hpq', hh, fun c cs hc j cA hj => ?_⟩
  refine nestAbstract_nestOcc_zero (fun x hx => ?_) (Verify.openPisAtFvars_length _ hpq')
    (nestUniform_inv hU cs (List.mem_of_getElem? hc) cA (List.mem_of_getElem? hj))
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ hpq' i x hi
  exact ⟨_, _, rfl⟩

/-- **The install's positivity stage, constructor by constructor**: the
member-abstracted crest `crest` (the root frame's instantiation, at a
constructor of the block's own levels) walked to its normal form `tyN`
(the run's output list's entry), the crest typed, the normal form's
fields' sorts and level parameters, M2′.  The walk itself is read once,
into its derivation (`checkBlockPositivity_deriv`, `PosDerivInv.lean`). -/
theorem checkBlockPositivity_inv_gen {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (h : checkBlockPositivity ops env₁ find? p cvTas ctorsAs = .ok (kinds, nfs, pos))
    (hlps : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = p.lps) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find?) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs → ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest tyN, instPisWith fvsP (nestAbstract (p.nestCtx fvsP find?) holes cA.1.type)
            = some crest ∧
          (nfs.getD c []).getD j default = tyN ∧
          (∃ ty, ops.inferType env₁ ((p.nestCtx fvsP find?).hiAt 0) crest = .ok ty) ∧
          tyN.allLevelParamsDefined p.lps = true ∧
          (∃ xq sorts, openPisAtFvars cA.2 tyN ((p.nestCtx fvsP find?).hiAt 0) = some xq ∧
            checkStructFieldSortsI ops env₁ (Level.isEquiv p.resSort .zero == some true) false
              p.resSort ((p.nestCtx fvsP find?).hiAt 0) xq.1 [] cA.2 = .ok sorts) ∧
          (nestAbstract (p.nestCtx fvsP find?) holes cA.1.type).nestOcc
            (p.nestCtx fvsP find?).names 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, outs, hcv', hpq', hh, hU, hr, hA, rfl, rfl⟩ :=
    checkBlockPositivity_inv h
  refine ⟨cvTa0, fvsP, rest, holes, hcv', hpq', hh, fun c cs hc j cA hj => ?_⟩
  obtain ⟨-, hall⟩ := nestRoot_inv hr
  obtain ⟨st₀, os, st₁, hms, hoc⟩ := hall c cs hc
  obtain ⟨hlen, htyped⟩ := nestCtors_typed hms
  obtain ⟨crest, ty, hcrest, hty⟩ := htyped j cA hj
  rw [rootCrest_eq _ _ (hlps c cs hc cA (List.mem_of_getElem? hj))] at hcrest
  obtain ⟨o, hoj⟩ : ∃ o, os[j]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)⟩
  have hocc := nestAbstract_nestOcc_zero (ctx := p.nestCtx fvsP find?) (holes := holes)
    (fun x hx => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ hpq' i x hi
      exact ⟨_, _, rfl⟩) (Verify.openPisAtFvars_length _ hpq')
    (nestUniform_inv hU cs (List.mem_of_getElem? hc) cA (List.mem_of_getElem? hj))
  obtain ⟨hlp, xq, sorts, hxq, hsorts⟩ :=
    checkAbsCtorSorts_inv (checkAbsCtorSortsAll_inv hA c cs os hc hoc) j cA o hj hoj
  exact ⟨crest, o.2, hcrest, outs_getD hoc hoj default, ⟨ty, hty⟩, hlp, ⟨xq, sorts, hxq, hsorts⟩,
    hocc⟩

end ConLeche
