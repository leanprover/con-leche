module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The install's positivity stage, inverted (lane HOLE2, checkpoint (c))

`checkBlockPositivity` (`Kernel/Inductives/BlockInstall.lean`) read back
constructor by constructor: the canonical parameters are the head
former's opened telescope, the holes are the members' stored types at
`nP + t`, and every stored constructor's member-abstracted type
(`instPisWith params (nestAbstract ctx holes cty)`)

* went through `nestMemberCtor` with only flat kinds (the walk the
  monotonicity theorem `nestMemberCtor_sem` inverts, at the flat kinds'
  ContSem provider `contSem_flat`), and
* was inferred at the holes' context (U2, the typing that theorem's
  premises read).
-/

namespace ConLeche

/-- The context `checkBlockPositivity` builds. -/
@[expose] def BlockParts.nestCtx (p : BlockParts) (fvsP : List Expr)
    (find? : Name → Option ConstantInfo) (consts : List ConstantInfo) : NestCtx :=
  ⟨p.memberNames, p.lps, p.nP, p.nIdxs, fvsP, p.resSort, find?, consts⟩

/-- **One member's constructors through the walk**, inverted. -/
theorem nestMemberCtors_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} {stable : Bool} :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestState} {kss : List (List NestFieldKind)}
      {nss : List Expr} {st' : NestState},
      nestMemberCtors ops env ctx holes stable cs st = .ok (kss, nss, st') →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest st₀ ks tyN st₁,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
        nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) ∧ kss[j]? = some ks ∧
        (stable = true → tyN = crest) ∧
        (nestAbstract ctx holes cA.1.type).nestOcc ctx.names 0 0 = false
  | [], _, _, _, _, _, j, cA, hj => by simp at hj
  | c :: cs, st, kss, nss, st', h, j, cA, hj => by
    simp only [nestMemberCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i crest hcrest
    split at h
    · simp at h
    rename_i cq hcq
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨ks, tyN, st₁⟩ := r₁
    simp only at h
    have hstab : stable = true → tyN = crest := by
      intro hs
      split at h
      · simp at h
      · rename_i hne
        simpa [hs] using hne
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i u hnm
    have hnm' : (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false := by
      unfold nestNoMemberConst at hnm
      split at hnm
      · simp [throw, throwThe, MonadExceptOf.throw] at hnm
      · rename_i hn; simpa using hn
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨kss₂, nss₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hc : instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest :=
        unwrapOr_ok hcrest
      exact ⟨crest, st, ks, tyN, st₁, hc, hr₁, rfl, hstab, hnm'⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact nestMemberCtors_inv hr₂ j cA hj

/-- **Every member's constructors through the walk**, inverted. -/
theorem nestBlockCtors_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} {stable : Bool} :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestState}
      {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {st' : NestState},
      nestBlockCtors ops env ctx holes stable css st = .ok (ksss, nsss, st') →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs → ∃ st₀ kss nss st₁,
        nestMemberCtors ops env ctx holes stable cs st₀ = .ok (kss, nss, st₁) ∧
          ksss[c]? = some kss
  | [], _, _, _, _, _, c, cs, hc => by simp at hc
  | cs₀ :: css, st, ksss, nsss, st', h, c, cs, hc => by
    simp only [nestBlockCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨kss, nss, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨ksss₂, nsss₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨st, kss, nss, st₁, hr₁, rfl⟩
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact nestBlockCtors_inv hr₂ c cs hc

/-- **U2 at one member's constructors**, inverted. -/
theorem checkAbsCtorTys_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {cs : List (ConstantVal × Nat)}, checkAbsCtorTys ops env ctx holes cs = .ok () →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ty,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
        ops.inferType env (ctx.hiAt 0) crest = .ok ty ∧
        ∃ xq sorts, openPisAtFvars cA.2 crest (ctx.hiAt 0) = some xq ∧
          checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
            ctx.sort (ctx.hiAt 0) xq.1 [] cA.2 = .ok sorts
  | [], _, j, cA, hj => by simp at hj
  | c :: cs, h, j, cA, hj => by
    simp only [checkAbsCtorTys, bind, Except.bind] at h
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
    rename_i xq hxq
    split at h
    · simp at h
    rename_i sorts hsorts
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hc : instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest :=
        unwrapOr_ok hcrest
      exact ⟨crest, ty, hc, hty, xq, sorts, unwrapOr_ok hxq, hsorts⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      exact checkAbsCtorTys_inv h j cA hj

/-- **U2 at every member's constructors**, inverted. -/
theorem checkAbsCtorTysAll_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {css : List (List (ConstantVal × Nat))}, checkAbsCtorTysAll ops env ctx holes css = .ok () →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs → checkAbsCtorTys ops env ctx holes cs = .ok ()
  | [], _, c, cs, hc => by simp at hc
  | cs₀ :: css, h, c, cs, hc => by
    simp only [checkAbsCtorTysAll, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i u hu
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact hu
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      exact checkAbsCtorTysAll_inv h c cs hc

/-- **The install's positivity stage, constructor by constructor.** -/
theorem checkBlockPositivity_inv {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok kinds) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs → ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest, instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
            = some crest ∧
          (∃ st₀ ks st₁,
            nestMemberCtor ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest st₀
              = .ok (ks, crest, st₁) ∧ ∀ k ∈ ks, k.flat = true) ∧
          (∃ ty, ops.inferType env₁ ((p.nestCtx fvsP find? consts).hiAt 0) crest = .ok ty) ∧
          (∃ xq sorts, openPisAtFvars cA.2 crest ((p.nestCtx fvsP find? consts).hiAt 0) = some xq ∧
            checkStructFieldSortsI ops env₁ (Level.isEquiv p.resSort .zero == some true) false
              p.resSort ((p.nestCtx fvsP find? consts).hiAt 0) xq.1 [] cA.2 = .ok sorts) ∧
          (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type).nestOcc
            (p.nestCtx fvsP find? consts).names 0 0 = false := by
  simp only [checkBlockPositivity, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i cvTa0 hcv
  have hcv' : cvTas.head? = some cvTa0 := unwrapOr_ok hcv
  split at h
  · simp at h
  rename_i pq hpq
  have hpq' : openPisAtFvars p.nP cvTa0.type 0 = some pq := unwrapOr_ok hpq
  split at h
  · simp at h
  rename_i holes hholes
  have hh : nestHoles (p.nestCtx pq.1 find? consts) = some holes := unwrapOr_ok hholes
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨kinds', normals, st⟩ := r
  simp only at h
  by_cases hall : kinds'.all (fun x => x.all fun x => x.all NestFieldKind.flat) = true
  case neg =>
    rw [if_neg hall] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_pos hall] at h
  split at h
  · simp at h
  rename_i u hA
  cases u
  refine ⟨cvTa0, pq.1, pq.2, holes, hcv', hpq', hh, fun c cs hc j cA hj => ?_⟩
  obtain ⟨st₀, kss, nss, st₁, hms, hk⟩ := nestBlockCtors_inv hr c cs hc
  obtain ⟨crest, st₂, ks, tyN, st₃, hcrest, hm, hks, hstab, hocc⟩ :=
    nestMemberCtors_inv hms j cA hj
  obtain rfl := hstab rfl
  obtain ⟨crest', ty, hcrest', hty, xq, sorts, hxq, hsorts⟩ :=
    checkAbsCtorTys_inv (checkAbsCtorTysAll_inv hA c cs hc) j cA hj
  rw [hcrest] at hcrest'
  obtain rfl := Option.some.inj hcrest'
  refine ⟨tyN, hcrest, ⟨st₂, ks, st₃, hm, fun k hk' => ?_⟩, ⟨ty, hty⟩,
    ⟨xq, sorts, hxq, hsorts⟩, hocc⟩
  simp only [List.all_eq_true] at hall
  exact hall kss (List.mem_of_getElem? hk) ks (List.mem_of_getElem? hks) k hk'

end ConLeche
