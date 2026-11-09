module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# The positivity twins are the specification at the shared operations (task #498)

The cached twins of `ConLeche/Cached/IndPositivity.lean` mirror their
specifications (`ConLeche/Kernel/Inductives/Positivity.lean`, the
positivity stage of `BlockInstall.lean`, `classSeeds`) step by step, at
the cached walks where the specification runs the plain ones; so each is
the specification at the shared operations `sharedOpsC` (an `…C_eq`
equation, closed by rewriting with the walks' specifications and the
callees' equations, then `rfl`: the shared operations ARE the cached
core).  The simulation triples (`NestPosC.lean`) and the driver lemmas
(`checkBlockPassS_run`, `checkBlockPassS_push`, `checkBlockPassS_twin`)
are entered through `checkBlockPositivityC_eq`, `nestSeedsC_eq`,
`blockNestCtxC_eq` and `classSeedsC_eq`.

The new walk of this lane, `replaceAppsC`, verifies itself against its
plain descent (`replaceAppsP`); `replaceAppsP_spec` reads the descent as
`Expr.replaceApps`.
-/

namespace ConLeche.Expr

theorem appHoleAt?_eq (f : Name → List Level → Option Expr) (b n : Nat) (a x : Expr) :
    appHoleAt? f b n a x = (Expr.app a x).appHole? f b n := by
  unfold appHoleAt? Expr.appHole?
  cases n <;> cases x <;> simp [Expr.phApp?]
  split <;> simp_all

theorem constHoleAt?_eq (f : Name → List Level → Option Expr) (b n : Nat) (c : Name)
    (us : List Level) : constHoleAt? f n c us = (Expr.const c us).appHole? f b n := by
  unfold constHoleAt? Expr.appHole?
  cases n <;> simp [Expr.phApp?]

/-- **The plain descent computes `Expr.replaceApps`.** -/
theorem replaceAppsP_spec {f : Name → List Level → Option Expr} {b n : Nat} :
    ∀ e : Expr, replaceAppsP f b n e = e.replaceApps f b n := by
  intro e
  induction e <;>
    simp_all [replaceAppsP, Expr.replaceApps, appHoleAt?_eq, constHoleAt?_eq (b := b)]

/-- **The cached whole-application replacement computes `Expr.replaceApps`.** -/
theorem replaceAppsC_spec {f : Name → List Level → Option Expr} {b n : Nat} {e : Expr} :
    replaceAppsC f b n e = e.replaceApps f b n := by
  rw [replaceAppsC, resTerm_eq, replaceAppsP_spec]

end ConLeche.Expr

namespace ConLeche.Cached

open ConLeche

/-- `replaceFVarsC_spec` unapplied (the specification maps `(·.replaceFVars f)`). -/
theorem replaceFVarsC_fun (f : Nat → Option Expr) :
    Expr.replaceFVarsC f = fun e => e.replaceFVars f := by
  funext e; exact Expr.replaceFVarsC_spec

/-- `replaceAppsC_spec` unapplied. -/
theorem replaceAppsC_fun (f : Name → List Level → Option Expr) (b n : Nat) :
    Expr.replaceAppsC f b n = fun e => e.replaceApps f b n := by
  funext e; exact Expr.replaceAppsC_spec

variable (mode : CheckMode) (fe : FEnv)

theorem checkSpineAtC_eq (d : Nat) : ∀ (t : Expr) (as : List Expr),
    checkSpineAtC mode fe d t as = checkSpineAt (sharedOpsC mode fe) fe.env d t as
  | _, [] => rfl
  | t, a :: as => by
    cases t <;> simp only [checkSpineAtC, checkSpineAt, Expr.instantiate1C_spec,
      checkSpineAtC_eq d _ as] <;> rfl

theorem familyKeyCheckC_eq (find? : Name → Option ConstantInfo) (d : Nat) (c : Name)
    (us : List Level) (ds : List Expr) :
    familyKeyCheckC mode fe find? d c us ds =
      familyKeyCheck (sharedOpsC mode fe) fe.env find? d c us ds := by
  simp only [familyKeyCheckC, familyKeyCheck, familyTelescopeC_eq, checkSpineAtC_eq,
    Expr.instLevelParams_spec] <;> rfl

theorem nestHoleImgC_eq (ctx : NestCtx) : ∀ prog, nestHoleImgC ctx prog = nestHoleImg ctx prog
  | [] => by funext i; rfl
  | h :: prog => by
    funext i
    simp only [nestHoleImgC, nestHoleImg, nestHoleImgC_eq ctx prog,
      replaceFVarsC_fun]

theorem nestCanonCrestC_eq (names : List Name) (us : List Level) (n : Nat) (cty : Expr) :
    nestCanonCrestC names us n cty = nestCanonCrest names us n cty := by
  simp only [nestCanonCrestC, nestCanonCrest, Expr.instPisWithC_eq, replaceAppsC_fun]

theorem nestCrestC_eq (names : List Name) (us : List Level) (ds holes : List Expr) (cty : Expr) :
    nestCrestC names us ds holes cty = nestCrest names us ds holes cty := by
  simp only [nestCrestC, nestCrest, nestCanonCrestC_eq, replaceFVarsC_fun]

theorem nestInstTypeC_eq (ctx : NestCtx) (hi : Nat) (key : NestKey) :
    nestInstTypeC mode ctx fe hi key = nestInstType ctx (sharedOpsC mode fe) fe.env hi key := by
  simp only [nestInstTypeC, nestInstType, familyTelescopeC_eq, Expr.instPisWithC_eq,
    Expr.instLevelParams_spec, Expr.nestOccC_spec] <;> rfl

theorem nestFieldsC_eq
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState),
      nestFieldsC rec prog base err nF j cur st = nestFields rec prog base err nF j cur st
  | 0, _, _, _ => rfl
  | nF + 1, j, cur, st => by
    cases cur <;> simp only [nestFieldsC, nestFields, Expr.instantiate1C_spec,
      nestFieldsC_eq rec prog base err nF]

theorem structUsedLaterC_eq (cty : Expr) (nP j : Nat) :
    structUsedLaterC cty nP j = structUsedLater cty nP j := by
  simp only [structUsedLaterC, structUsedLater, hasLooseBVarBC_spec] <;> rfl

theorem nestCtorsC_eq (ctx : NestCtx) (fuelOf : Expr → Nat)
    (rec : Nat → List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) : ∀ (cs : List (ConstantVal × Nat)) (st : NestState),
      nestCtorsC mode ctx fe fuelOf rec prog hi us ds names holes cs st =
        nestCtors ctx (sharedOpsC mode fe) fe.env (fun crest => rec (fuelOf crest)) prog hi us ds
          names holes cs st
  | [], _ => rfl
  | (cv, nF) :: cs, st => by
    simp only [nestCtorsC, nestCtors, nestCrestC_eq, Expr.instLevelParams_spec, nestFieldsC_eq,
      Expr.closeTelescopeC_eq, structUsedLaterC_eq, Expr.getAppArgsC_spec, Expr.nestOccC_spec,
      nestCtorNfC, nestCtorNf, nestHoleImgC_eq, Expr.replaceFVarsC_spec, replaceFVarsC_fun,
      nestCtorsC_eq ctx fuelOf rec prog hi us ds names holes cs]
    rfl

theorem nestGrowGroupC_eq (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr) :
    ∀ (cs : List Name) (grp : List (Name × Expr)),
      nestGrowGroupC mode ctx fe hi us ds cs grp =
        nestGrowGroup ctx (sharedOpsC mode fe) fe.env hi us ds cs grp
  | [], _ => rfl
  | c :: cs, grp => by
    simp only [nestGrowGroupC, nestGrowGroup, nestInstTypeC_eq, nestGrowGroupC_eq ctx hi us ds cs]

theorem nestFrameC_eq (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) :
    nestFrameC mode ctx fe rec prog hi us ds nPc grp st =
      nestFrame ctx (sharedOpsC mode fe) fe.env rec prog hi us ds nPc grp st := by
  simp only [nestFrameC, nestFrame, familyKeyCheckC_eq, nestCtorsC_eq]

theorem nestContNewC_eq (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) :
    nestContNewC mode ctx fe rec prog kb n us ds nPc cty st =
      nestContNew ctx (sharedOpsC mode fe) fe.env rec prog kb n us ds nPc cty st := by
  simp only [nestContNewC, nestContNew, nestGrowGroupC_eq, nestFrameC_eq]

theorem nestContKeyC_eq (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) :
    nestContKeyC mode ctx fe rec prog kb n us ds nPc cty st =
      nestContKey ctx (sharedOpsC mode fe) fe.env rec prog kb n us ds nPc cty st := by
  simp only [nestContKeyC, nestContKey, nestContNewC_eq]

theorem nestContC_eq (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) :
    nestContC mode ctx fe rec prog kb n us args st =
      nestCont ctx (sharedOpsC mode fe) fe.env rec prog kb n us args st := by
  simp only [nestContC, nestCont, Expr.nestOccC_spec, nestInstTypeC_eq, nestContKeyC_eq]

/-- **The cached positivity function is `nestPos` at the shared operations.** -/
theorem nestPosC_eq (ctx : NestCtx) :
    ∀ fuel, nestPosC mode fe ctx fuel = nestPos (sharedOpsC mode fe) fe.env ctx fuel
  | 0 => rfl
  | fuel + 1 => by
    funext prog dep kb e st
    simp only [nestPosC, nestPos, Expr.nestOccC_spec, Expr.instantiate1C_spec,
      Expr.abstract1C_spec, Expr.getAppArgsC_spec, nestContC_eq, nestPosC_eq ctx fuel]
    rfl

theorem nestHolesC_eq (ctx : NestCtx) : nestHolesC ctx = nestHoles ctx := by
  simp only [nestHolesC, nestHoles, Expr.instPisWithC_eq] <;> rfl

theorem nestRootCanonC_eq (ctx : NestCtx) (cv : ConstantVal) :
    nestRootCanonC ctx cv = nestRootCanon ctx cv := by
  simp only [nestRootCanonC, nestRootCanon, nestCanonCrestC_eq, Expr.instLevelParams_spec]

theorem piDomsOccC_eq (names : List Name) (lo hi : Nat) :
    ∀ (n : Nat) (e : Expr), piDomsOccC names lo hi n e = e.piDomsOcc names lo hi n
  | 0, _ => rfl
  | n + 1, e => by
    cases e <;> simp only [piDomsOccC, Expr.piDomsOcc, Expr.nestOccC_spec,
      piDomsOccC_eq names lo hi n]

theorem nestUniformOkC_eq (ctx : NestCtx) : nestUniformOkC ctx = nestUniformOk ctx := by
  funext cv
  simp only [nestUniformOkC, nestUniformOk, piDomsOccC_eq, nestRootCanonC_eq,
    Expr.nestOccC_spec] <;> rfl

theorem nestUniformC_eq (ctx : NestCtx) (ctorss : List (List (ConstantVal × Nat))) :
    nestUniformC ctx ctorss = nestUniform ctx ctorss := by
  simp only [nestUniformC, nestUniform, nestUniformOkC_eq] <;> rfl

theorem whnfWalkFuelC_eq : whnfWalkFuelC = whnfWalkFuel := by
  funext e
  simp only [whnfWalkFuelC, whnfWalkFuel, Expr.depthC_spec]

theorem nestRootC_eq (ctx : NestCtx) (holes : List Expr) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState),
      nestRootC mode fe ctx holes css st = nestRoot (sharedOpsC mode fe) fe.env ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    simp only [nestRootC, nestRoot, whnfWalkFuelC_eq, nestPosC_eq, nestCtorsC_eq,
      nestRootC_eq ctx holes css]

theorem nestSeedOfC_eq (ctx : NestCtx) : nestSeedOfC ctx = nestSeedOf ctx := by
  funext holes I us ds nPc
  simp only [nestSeedOfC, nestSeedOf, Expr.replaceAppsC_spec, Expr.replaceFVarsC_spec]

theorem nestSeedsC_eq (ctx : NestCtx) : ∀ (ks : List (NestKey × Nat)) (st : NestState),
    nestSeedsC mode fe ctx ks st = nestSeeds (sharedOpsC mode fe) fe.env ctx ks st
  | [], _ => rfl
  | (key, nPc) :: ks, st => by
    simp only [nestSeedsC, nestSeeds, whnfWalkFuelC_eq, nestInstTypeC_eq, nestPosC_eq,
      nestContKeyC_eq, nestSeedsC_eq ctx ks]

theorem checkStructFieldSortsIC_eq (isProp large : Bool) (s : Level) (nP : Nat)
    (fvs idxArgs : List Expr) : ∀ j,
      checkStructFieldSortsIC mode fe isProp large s nP fvs idxArgs j =
        checkStructFieldSortsI (sharedOpsC mode fe) fe.env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIC, checkStructFieldSortsI,
      checkStructFieldSortsIC_eq isProp large s nP fvs idxArgs j]
    rfl

theorem checkAbsCtorSortsC_eq (ctx : NestCtx) : ∀ (cs : List (ConstantVal × Nat))
    (os : List (List NestFieldKind × Expr)),
    checkAbsCtorSortsC mode fe ctx cs os = checkAbsCtorSorts (sharedOpsC mode fe) fe.env ctx cs os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, o :: os => by
    simp only [checkAbsCtorSortsC, checkAbsCtorSorts, Expr.allLevelParamsDefinedC_spec,
      openPisAtFvarsC_eq, checkStructFieldSortsIC_eq, checkAbsCtorSortsC_eq ctx cs os]

theorem checkAbsCtorSortsAllC_eq (ctx : NestCtx) : ∀ (css : List (List (ConstantVal × Nat)))
    (oss : List (List (List NestFieldKind × Expr))),
    checkAbsCtorSortsAllC mode fe ctx css oss =
      checkAbsCtorSortsAll (sharedOpsC mode fe) fe.env ctx css oss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | cs :: css, os :: oss => by
    simp only [checkAbsCtorSortsAllC, checkAbsCtorSortsAll, checkAbsCtorSortsC_eq,
      checkAbsCtorSortsAllC_eq ctx css oss]

/-- **The cached walk's context is `blockNestCtx`.** -/
theorem blockNestCtxC_eq (p : BlockShape) (find? : Name → Option ConstantInfo) :
    blockNestCtxC p find? = blockNestCtx (m := CheckCM) p find? := by
  simp only [blockNestCtxC, blockNestCtx, openPisAtFvarsC_eq, nestHolesC_eq]

/-- **The cached seeds are `classSeeds`.** -/
theorem classSeedsC_eq (ctx : NestCtx) (holes : List Expr) (Ms : List TargetMajor) :
    classSeedsC ctx holes Ms = classSeeds ctx holes Ms := by
  simp only [classSeedsC, classSeeds, nestSeedOfC_eq]

/-- **The cached positivity stage is `checkBlockPositivity` at the shared
operations.** -/
theorem checkBlockPositivityC_eq (find? : Name → Option ConstantInfo) (p : BlockShape) :
    checkBlockPositivityC mode fe find? p =
      checkBlockPositivity (sharedOpsC mode fe) fe.env find? p := by
  simp only [checkBlockPositivityC, checkBlockPositivity, blockNestCtxC_eq, nestUniformC_eq,
    nestRootC_eq, checkAbsCtorSortsAllC_eq]

end ConLeche.Cached
