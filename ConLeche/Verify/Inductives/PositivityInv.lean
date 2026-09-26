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
    {holes : List Expr} :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestState} {kss : List (List NestFieldKind)}
      {nss : List Expr} {st' : NestState},
      nestMemberCtors ops env ctx holes cs st = .ok (kss, nss, st') →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest st₀ ks tyN st₁,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
        nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) ∧ kss[j]? = some ks ∧
        nss[j]? = some tyN ∧
        (nestAbstract ctx holes cA.1.type).nestOcc ctx.names 0 0 = false
  | [], _, _, _, _, _, j, cA, hj => by simp at hj
  | c :: cs, st, kss, nss, st', h, j, cA, hj => by
    simp only [nestMemberCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i crest hcrest
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨ks, tyN, st₁⟩ := r₁
    simp only at h
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
    obtain ⟨rfl, rfl, -⟩ := h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hc : instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest :=
        unwrapOr_ok hcrest
      exact ⟨crest, st, ks, tyN, st₁, hc, hr₁, rfl, rfl, hnm'⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact nestMemberCtors_inv hr₂ j cA hj

/-- **Every member's constructors through the walk**, inverted. -/
theorem nestBlockCtors_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestState}
      {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {st' : NestState},
      nestBlockCtors ops env ctx holes css st = .ok (ksss, nsss, st') →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs → ∃ st₀ kss nss st₁,
        nestMemberCtors ops env ctx holes cs st₀ = .ok (kss, nss, st₁) ∧
          ksss[c]? = some kss ∧ nsss[c]? = some nss
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
    obtain ⟨rfl, rfl, -⟩ := h
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨st, kss, nss, st₁, hr₁, rfl, rfl⟩
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact nestBlockCtors_inv hr₂ c cs hc

/-- **U2 at one member's constructors**, inverted: the declared crest
inferred, the normal form's fields' sorts, the normal form's level
parameters the block's. -/
theorem checkAbsCtorTys_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {cs : List (ConstantVal × Nat)} {ns : List Expr}, checkAbsCtorTys ops env ctx holes cs ns = .ok () →
      ∀ (j : Nat) (cA : ConstantVal × Nat) (tyN : Expr), cs[j]? = some cA → ns[j]? = some tyN →
        ∃ crest ty,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
        ops.inferType env (ctx.hiAt 0) crest = .ok ty ∧
        tyN.allLevelParamsDefined ctx.lps = true ∧
        ∃ xq sorts, openPisAtFvars cA.2 tyN (ctx.hiAt 0) = some xq ∧
          checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
            ctx.sort (ctx.hiAt 0) xq.1 [] cA.2 = .ok sorts
  | [], _, _, j, cA, _, hj, _ => by simp at hj
  | _ :: _, [], _, j, cA, _, _, hn => by simp at hn
  | c :: cs, n :: ns, h, j, cA, tyN, hj, hn => by
    simp only [checkAbsCtorTys, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i crest hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    by_cases hlp' : n.allLevelParamsDefined ctx.lps = true
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
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hn
      subst hj hn
      have hc : instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest :=
        unwrapOr_ok hcrest
      exact ⟨crest, ty, hc, hty, hlp', xq, sorts, unwrapOr_ok hxq, hsorts⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj hn
      exact checkAbsCtorTys_inv h j cA tyN hj hn

/-- **U2 at every member's constructors**, inverted. -/
theorem checkAbsCtorTysAll_inv {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {css : List (List (ConstantVal × Nat))} {nss : List (List Expr)},
      checkAbsCtorTysAll ops env ctx holes css nss = .ok () →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)) (ns : List Expr), css[c]? = some cs →
        nss[c]? = some ns → checkAbsCtorTys ops env ctx holes cs ns = .ok ()
  | [], _, _, c, cs, _, hc, _ => by simp at hc
  | _ :: _, [], _, c, cs, _, _, hn => by simp at hn
  | cs₀ :: css, ns₀ :: nss, h, c, cs, ns, hc, hn => by
    simp only [checkAbsCtorTysAll, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i u hu
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hn
      subst hc hn
      exact hu
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc hn
      exact checkAbsCtorTysAll_inv h c cs ns hc hn

/-- **The install's positivity stage, constructor by constructor**, at
either position of the route switch: the declared crest `crest` walked
to its normal form `tyN` (the run's output list's entry), the crest
typed, the normal form's fields' sorts and level parameters, M2′.  The
walk itself is read once, into its derivation (`checkBlockPositivity_deriv`,
`PosDerivInv.lean`). -/
theorem checkBlockPositivity_inv_gen {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs → ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest tyN, instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
            = some crest ∧
          (nfs.getD c []).getD j default = tyN ∧
          (∃ ty, ops.inferType env₁ ((p.nestCtx fvsP find? consts).hiAt 0) crest = .ok ty) ∧
          tyN.allLevelParamsDefined p.lps = true ∧
          (∃ xq sorts, openPisAtFvars cA.2 tyN ((p.nestCtx fvsP find? consts).hiAt 0) = some xq ∧
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
  split at h
  · simp at h
  rename_i u hA
  cases u
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨cvTa0, pq.1, pq.2, holes, hcv', hpq', hh, fun c cs hc j cA hj => ?_⟩
  obtain ⟨st₀, kss, nss, st₁, hms, hk, hn⟩ := nestBlockCtors_inv hr c cs hc
  obtain ⟨crest, st₂, ks, tyN, st₃, hcrest, hm, hks, hnj, hocc⟩ :=
    nestMemberCtors_inv hms j cA hj
  obtain ⟨crest', ty, hcrest', hty, hlp, xq, sorts, hxq, hsorts⟩ :=
    checkAbsCtorTys_inv (checkAbsCtorTysAll_inv hA c cs nss hc hn) j cA tyN hj hnj
  rw [hcrest] at hcrest'
  obtain rfl := Option.some.inj hcrest'
  refine ⟨crest, tyN, hcrest, ?_, ⟨ty, hty⟩, hlp, ⟨xq, sorts, hxq, hsorts⟩, hocc⟩
  have hg : normals.getD c [] = nss := by rw [List.getD_eq_getElem?_getD, hn]; rfl
  rw [hg, List.getD_eq_getElem?_getD, hnj]; rfl

/-! ## The walk's state, threaded (lane NESTKERN, session 2)

The block's constructors share ONE walk state (the container cache),
threaded from the empty state through every member's constructors in
order.  An invariant of the state that every block constructor's run
keeps (`nestMemberCtor_sem_cont`'s `CacheInv`) therefore holds at every
constructor's entry. -/

/-- **One member's constructors, the state threaded**: an invariant kept
by each of this member's runs holds at every run's entry and at the
exit. -/
theorem nestMemberCtors_inv_I {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} {I : NestState → Prop} {R : NestState → NestState → Prop}
    (hRr : ∀ s, R s s) (hRt : ∀ a b c, R a b → R b c → R a c) :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestState} {kss : List (List NestFieldKind)}
      {nss : List Expr} {st' : NestState},
      nestMemberCtors ops env ctx holes cs st = .ok (kss, nss, st') → I st →
      (∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest →
        ∀ st₀ ks tyN st₁, nss[j]? = some tyN → I st₀ →
          nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) → I st₁ ∧ R st₀ st₁) →
      I st' ∧ R st st' ∧ ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest st₀ ks tyN st₁,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧ I st₀ ∧
        nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) ∧ nss[j]? = some tyN ∧
        kss[j]? = some ks ∧ R st₁ st'
  | [], _, _, _, _, h, hI, _ => by
    simp only [nestMemberCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨hI, hRr _, fun j cA hj => by simp at hj⟩
  | c :: cs, st, kss, nss, st', h, hI, hstep => by
    simp only [nestMemberCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i crest hcrest
    have hc : instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest :=
      unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨ks, tyN, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨kss₂, nss₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hI₁, hR₁⟩ := hstep 0 c rfl crest hc st ks tyN st₁ rfl hI hr₁
    obtain ⟨hI', hR', hall⟩ := nestMemberCtors_inv_I hRr hRt hr₂ hI₁
      (fun j cA hj crest' hc' st₀ ks' tyN' st₁' hn hI₀ hm =>
        hstep (j + 1) cA (by simpa using hj) crest' hc' st₀ ks' tyN' st₁' (by simpa using hn)
          hI₀ hm)
    refine ⟨hI', hRt _ _ _ hR₁ hR', fun j cA hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨crest, st, ks, tyN, st₁, hc, hI, hr₁, rfl, rfl, hR'⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact hall j cA hj

/-- **Every member's constructors, the state threaded.** -/
theorem nestBlockCtors_inv_I {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} {I : NestState → Prop} {R : NestState → NestState → Prop}
    (hRr : ∀ s, R s s) (hRt : ∀ a b c, R a b → R b c → R a c) :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestState}
      {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {st' : NestState},
      nestBlockCtors ops env ctx holes css st = .ok (ksss, nsss, st') → I st →
      (∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
        instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest →
        ∀ st₀ ks tyN st₁, (nsss.getD c []).getD j default = tyN → I st₀ →
          nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) → I st₁ ∧ R st₀ st₁) →
      I st' ∧ R st st' ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest st₀ ks tyN st₁,
          instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧ I st₀ ∧
          nestMemberCtor ops env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) ∧
          (nsss.getD c []).getD j default = tyN ∧ (ksss.getD c []).getD j [] = ks ∧ R st₁ st'
  | [], st, ksss, nsss, st', h, hI, _ => by
    simp only [nestBlockCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨hI, hRr _, fun c cs hc => by simp at hc⟩
  | cs₀ :: css, st, ksss, nsss, st', h, hI, hstep => by
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
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hI₁, hR₁, hall₁⟩ := nestMemberCtors_inv_I hRr hRt hr₁ hI
      (fun j cA hj crest hc' st₀ ks tyN st₁' hn hI₀ hm =>
        hstep 0 cs₀ rfl j cA hj crest hc' st₀ ks tyN st₁' (by
          simp only [List.getD_cons_zero]
          rw [List.getD_eq_getElem?_getD, hn]; rfl) hI₀ hm)
    obtain ⟨hI₂, hR₂, hall₂⟩ := nestBlockCtors_inv_I hRr hRt hr₂ hI₁
      (fun c' cs' hc' j' cA' hj' crest hcr st₀ ks tyN st₁' hn hI₀ hm =>
        hstep (c' + 1) cs' (by simpa using hc') j' cA' hj' crest hcr st₀ ks tyN st₁'
          (by simpa using hn) hI₀ hm)
    refine ⟨hI₂, hRt _ _ _ hR₁ hR₂, fun c cs hc => ?_⟩
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      intro j cA hj
      obtain ⟨crest, st₀, ks, tyN, st₁', h1, h2, h3, h4, h5, h6⟩ := hall₁ j cA hj
      refine ⟨crest, st₀, ks, tyN, st₁', h1, h2, h3, ?_, ?_, hRt _ _ _ h6 hR₂⟩
      · simp only [List.getD_cons_zero]
        rw [List.getD_eq_getElem?_getD, h4]; rfl
      · simp only [List.getD_cons_zero]
        rw [List.getD_eq_getElem?_getD, h5]; rfl
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      intro j cA hj
      simpa using hall₂ c cs hc j cA hj

/-- **The install's positivity stage, the walk's state threaded**
(lane NESTKERN, session 2): at either position of the route switch, an
invariant of the walk's state that holds of the empty state and that
every block constructor's run (the one the stage ran, to its output
normal form) keeps holds at every constructor's entry. -/
theorem checkBlockPositivity_inv_I {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      ∀ (I : NestState → Prop) (R : NestState → NestState → Prop), I {} → (∀ s, R s s) →
        (∀ a b c, R a b → R b c → R a c) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
          instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
            = some crest →
          ∀ st₀ ks tyN st₁, (nfs.getD c []).getD j default = tyN → I st₀ →
            nestMemberCtor ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest st₀
              = .ok (ks, tyN, st₁) → I st₁ ∧ R st₀ st₁) →
        ∃ stF : NestState, I stF ∧ nodes.keys = stF.nodes.toList ∧
          nodes.ctors = nestMemberNfs (p.nestCtx fvsP find? consts) ctorsAs nfs ++
            stF.ctorNfs.toList ∧
        ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest st₀ ks tyN st₁,
            instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
              = some crest ∧ I st₀ ∧
            nestMemberCtor ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest st₀
              = .ok (ks, tyN, st₁) ∧
            (nfs.getD c []).getD j default = tyN ∧ (kinds.getD c []).getD j [] = ks ∧
            R st₁ stF := by
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
  split at h
  · simp at h
  rename_i u hA
  cases u
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨cvTa0, pq.1, pq.2, holes, hcv', hpq', hh, fun I R hI hRr hRt hstep => ?_⟩
  obtain ⟨hIF, -, hall⟩ := nestBlockCtors_inv_I hRr hRt hr hI hstep
  refine ⟨st, hIF, rfl, rfl, fun c cs hc j cA hj => ?_⟩
  obtain ⟨crest, st₀, ks, tyN, st₁, h1, h2, h3, h4, h5, h6⟩ := hall c cs hc j cA hj
  exact ⟨crest, st₀, ks, tyN, st₁, h1, h2, h3, h4, h5, h6⟩

end ConLeche
