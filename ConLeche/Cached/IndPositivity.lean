module

public import ConLeche.Cached.CoreC
public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Kernel.Inductives.BlockInstall

@[expose] public section

/-!
# The cached twin of the inductive check: positivity (task #498)

The production twins of `ConLeche/Kernel/Inductives/Positivity.lean` and
of the positivity stage of `BlockInstall.lean` (`checkBlockPositivity`,
`blockNestCtx`) with the seeds (`classSeeds`, `GenRec.lean`):
monomorphic `CheckCM` definitions at a mode and an environment index,
calling the cached core (`coreKnotI`) directly and the cached walks of
`ConLeche/Cached/ExprOpsC.lean` where the specification runs the plain
ones (`instantiate1C`, `abstract1C`, `nestOccC`, `replaceFVarsC`,
`closeTelescopeC`, `instLevelParams`, `depthC`, and `replaceAppsC`
below).  Definitions that walk no `Expr` (`nestContainer`,
`nestGroupCtors`, `nestWalkStack`, `nestHoleAt`, …) are shared.  Each
twin is the specification at the shared operations
(`whnfTelescopeC_eq`, `reducedFormerC_eq`,
`ConLeche/Verify/Cached/WalkersC.lean`; the positivity twins'
equations in `ConLeche/Verify/Cached/IndPositivityC.lean`), so the
simulation triples of `NestPosC.lean` are entered through them.
-/

/-! ## `replaceAppsC`: the whole-application abstraction, memoised

`Expr.replaceApps` (`Positivity.lean`) at the walks' conventions
(`ConLeche/Cached/ExprOpsC.lean`): a pre-order replacement of every
whole application `f` maps, the shared compound nodes memoised by
address.  No cutoff (no field records the constants of a node).  The
hole test of an application node reads its spine in place
(`appHoleAt?`, no node rebuilt to ask).  `replaceAppsP_spec` and
`replaceAppsC_spec` (`ConLeche/Verify/Cached/IndPositivityC.lean`) read
the descent as the specification. -/

namespace ConLeche.Expr

/-- `(Expr.app a x).appHole? f b n` without building the node. -/
@[inline] def appHoleAt? (f : Name → List Level → Option Expr) (b n : Nat) (a x : Expr) :
    Option Expr :=
  match n, x with
  | k + 1, .fvar j .. => if j = b + k then (a.phApp? b k).bind fun p => f p.1 p.2 else none
  | _, _ => none

/-- `(Expr.const c us).appHole? f b n` without building the node. -/
@[inline] def constHoleAt? (f : Name → List Level → Option Expr) (n : Nat) (c : Name)
    (us : List Level) : Option Expr :=
  match n with
  | 0 => f c us
  | _ + 1 => none

/-- The plain descent of `replaceAppsC`. -/
def replaceAppsP (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) : Expr :=
  match e with
  | .app a x .. =>
    (appHoleAt? f b n a x).getD (mkApp (replaceAppsP f b n a) (replaceAppsP f b n x))
  | .const c us .. => (constHoleAt? f n c us).getD e
  | .lam ty body .. => mkLam (replaceAppsP f b n ty) (replaceAppsP f b n body)
  | .forallE ty body .. => mkForallE (replaceAppsP f b n ty) (replaceAppsP f b n body)
  | .letE ty val body .. =>
    mkLetE (replaceAppsP f b n ty) (replaceAppsP f b n val) (replaceAppsP f b n body)
  | .proj sn i sub .. => mkProj sn i (replaceAppsP f b n sub)
  | .bvar .. | .fvar .. | .sort .. | .lit .. => e

/-- The child step of `replaceAppsXP`: the compound test, then the
exclusivity read. -/
@[inline] def enterRA (f : @& Name → List Level → Option Expr) (b n : Nat) (e : @& Expr)
    (memo : MemoXP0 (replaceAppsP f b n))
    (rec : Unit → Squash (ResXP0 (replaceAppsP f b n) e)) :
    Squash (ResXP0 (replaceAppsP f b n) e) :=
  if !isCompound e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()

/-- The walk of `replaceAppsC`. -/
def replaceAppsXP (f : @& Name → List Level → Option Expr) (b n : Nat)
    (memo : MemoXP0 (replaceAppsP f b n)) (e : @& Expr) :
    Squash (ResXP0 (replaceAppsP f b n) e) :=
  match e with
  | .bvar j .. => Squash.mk (⟨.bvar j, by rw [replaceAppsP]⟩, memo)
  | .fvar i ty .. => Squash.mk (⟨.fvar i ty, by rw [replaceAppsP]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [replaceAppsP]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [replaceAppsP]⟩, memo)
  | .const c us .. =>
    Squash.mk (⟨(constHoleAt? f n c us).getD (.const c us), by rw [replaceAppsP]⟩, memo)
  | .app a x .. =>
    match h : appHoleAt? f b n a x with
    | some r => Squash.mk (⟨r, by rw [replaceAppsP, h]; rfl⟩, memo)
    | none =>
      enterRA f b n a memo (fun _ => replaceAppsXP f b n memo a) |>.lift fun (⟨a', ha⟩, memo) =>
      enterRA f b n x memo (fun _ => replaceAppsXP f b n memo x) |>.lift fun (⟨x', hx⟩, memo) =>
      Squash.mk (⟨mkApp a' x', by rw [replaceAppsP, h, ha, hx]; rfl⟩, memo)
  | .lam ty body .. =>
    enterRA f b n ty memo (fun _ => replaceAppsXP f b n memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRA f b n body memo (fun _ => replaceAppsXP f b n memo body) |>.lift
      fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [replaceAppsP, ht, hb]⟩, memo)
  | .forallE ty body .. =>
    enterRA f b n ty memo (fun _ => replaceAppsXP f b n memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRA f b n body memo (fun _ => replaceAppsXP f b n memo body) |>.lift
      fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [replaceAppsP, ht, hb]⟩, memo)
  | .letE ty val body .. =>
    enterRA f b n ty memo (fun _ => replaceAppsXP f b n memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRA f b n val memo (fun _ => replaceAppsXP f b n memo val) |>.lift fun (⟨v', hv⟩, memo) =>
    enterRA f b n body memo (fun _ => replaceAppsXP f b n memo body) |>.lift
      fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [replaceAppsP, ht, hv, hb]⟩, memo)
  | .proj sn i sub .. =>
    enterRA f b n sub memo (fun _ => replaceAppsXP f b n memo sub) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [replaceAppsP, hs]⟩, memo)

/-- The cached `Expr.replaceApps f b n` (one memoized DAG walk). -/
def replaceAppsC (f : Name → List Level → Option Expr) (b n : Nat) (e : @& Expr) : Expr :=
  resTerm (replaceAppsXP f b n none e)

end ConLeche.Expr

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- The cached `whnfTelescope`: official's telescope loop, the residual
reduced by the cached core and each binder opened by `instantiate1C`. -/
def whnfTelescopeC (fe : FEnv) : Nat → Nat → Expr → CheckCM (List Expr × Level)
  | i, 0, e => do
    let e' ← (coreKnotI mode false fe checkFuel).whnf i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← (coreKnotI mode false fe checkFuel).whnf i e
    match e' with
    | .forallE dom body =>
      let (bs, s) ← whnfTelescopeC fe (i + 1) n (Expr.instantiate1C body (.fvar i dom))
      pure (dom :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- The cached `reducedFormer`: the reduced telescope closed by
`closeTelescopeC` (each domain abstracted once). -/
def reducedFormerC (fe : FEnv) (cv : ConstantVal) (n : Nat) : CheckCM ConstantVal := do
  let (bs, s) ← whnfTelescopeC mode fe 0 n cv.type
  pure { cv with type := Expr.closeTelescopeC bs 0 (.sort s) }

/-- The cached `familyTelescope`: a definition-headed former's reduct
by `reducedFormerC` (`familyTelescopeC_eq`). -/
def familyTelescopeC (fe : FEnv) (cv : ConstantVal) (caps : IndCaps) : CheckCM Expr :=
  if formerDefHeaded cv then do
    let cvR ← reducedFormerC mode fe cv (caps.nparams + caps.nIdx)
    pure cvR.type
  else pure cv.type

/-- The cached `checkSpineAt`: the cached core's `infer` and `defeq`,
the telescope instantiated by `instantiate1C`. -/
def checkSpineAtC (fe : FEnv) (d : Nat) : Expr → List Expr → CheckCM Unit
  | _, [] => pure ()
  | t, a :: as =>
    match t with
    | .forallE ty body => do
      let ta ← (coreKnotI mode false fe checkFuel).infer d a
      unless ← (coreKnotI mode false fe checkFuel).defeq d ta ty do
        throw (.invalid "application type mismatch at a family's parameters")
      checkSpineAtC fe d (Expr.instantiate1C body a) as
    | _ => throw (.invalid "function expected at a family's parameters")

/-- The cached `familyKeyCheck`. -/
def familyKeyCheckC (fe : FEnv) (find? : Name → Option ConstantInfo) (d : Nat)
    (c : Name) (us : List Level) (ds : List Expr) : CheckCM Unit :=
  match find? c with
  | some (.indInfo cv caps) => do
    unless us.length = cv.levelParams.length do
      throw (.invalid "incorrect number of universe levels at a family's key")
    let ty ← familyTelescopeC mode fe cv caps
    checkSpineAtC mode fe d (Expr.instLevelParams cv.levelParams us ty) ds
  | _ => throw (.invalid "a family's key is no stored family")

/-! ## Positivity through containers -/

/-- The cached `whnfWalkFuel`: the depth by `depthC`. -/
def whnfWalkFuelC (e : Expr) : Nat := Expr.depthC e + fuelSlack

/-- The cached `nestHoleImg`: the frames' parameters read back by
`replaceFVarsC`. -/
def nestHoleImgC (ctx : NestCtx) : List NestHole → Nat → Option Expr
  | [], i =>
    if ctx.nP ≤ i ∧ i < ctx.hiAt 0 then
      some (Expr.mkAppN (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param))
        ctx.params)
    else none
  | h :: prog, i =>
    if i = ctx.hiAt prog.length then
      some (Expr.mkAppN (.const h.key.cname h.key.lvls)
        (h.key.ds.map (Expr.replaceFVarsC (nestHoleImgC ctx prog))))
    else nestHoleImgC ctx prog i

/-- The cached `nestCanonCrest`: `Expr.instPisWithC`, then `replaceAppsC`. -/
def nestCanonCrestC (names : List Name) (us : List Level) (n : Nat) (cty : Expr) :
    Option Expr :=
  (Expr.instPisWithC (nestPhs n) cty).map (Expr.replaceAppsC (nestCanonSub names us n) 0 n)

/-- The cached `nestCrest`: `nestCanonCrestC`, then `replaceFVarsC`. -/
def nestCrestC (names : List Name) (us : List Level) (ds holes : List Expr) (cty : Expr) :
    Option Expr :=
  (nestCanonCrestC names us ds.length cty).map (Expr.replaceFVarsC (nestKeyMap ds holes))

/-- The cached `nestInstType`: the container's telescope by
`familyTelescopeC`, instantiated by `instLevelParams` and `Expr.instPisWithC`,
its binders read once. -/
def nestInstTypeC (ctx : NestCtx) (fe : FEnv) (hi : Nat) (key : NestKey) :
    CheckCM (Nat × Expr) := do
  let (cvC, capsC) ← unwrapOr (match ctx.find? key.cname with
      | some (.indInfo cv caps) => some (cv, caps)
      | _ => none)
    (.internal "nested positivity: container vanished")
  unless key.lvls.length = cvC.levelParams.length do
    throw (.invalid "nested positivity: incorrect number of universe levels for a nested \
      inductive datatype (official: incorrect number of universe levels)")
  let tyC ← familyTelescopeC mode fe cvC capsC
  unless (tyC.stripPis key.ds.length).isSome do
    throw (.invalid "nested positivity: invalid nested inductive datatype, its type does \
      not bind its parameters (official: ill-formed inductive type)")
  let ty ← unwrapOr (Expr.instPisWithC key.ds
      (Expr.instLevelParams cvC.levelParams key.lvls tyC))
    (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind \
      its parameters (official: ill-formed inductive type)")
  let pb := ty.piBinders
  let s ← unwrapOr (match pb.2 with
      | .sort s => some s
      | _ => none)
    (.invalid "nested positivity: invalid nested inductive datatype, its type is not a \
      telescope ending in a sort (official: type expected)")
  if pb.1.any (fun b => Expr.nestOccC ctx.names ctx.nP hi b) then
    throw (.invalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)")
  unless ← liftFueled "level comparison" (Level.isEquiv s ctx.sort) do
    throw (.invalid "nested positivity: mutually inductive types must live in the \
      same universe")
  pure (pb.1.length, ty)

/-- The cached `nestFields`: each field opened by `instantiate1C`. -/
def nestFieldsC
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    Nat → Nat → Expr → NestState →
      CheckCM (List NestFieldKind × List Expr × Expr × NestState)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, j, cur, st =>
    match cur with
    | .forallE a b => do
      let (k, nd, st) ← rec prog (base + j) 0 a st
      let (ks, nds, res, st) ← nestFieldsC rec prog base err nF (j + 1)
        (Expr.instantiate1C b (.fvar (base + j) a)) st
      pure (k :: ks, nd :: nds, res, st)
    | _ => throw err

/-- The cached `nestCtorNf`, at the walked telescope `tel` closed once
by the caller (`closeTelescopeC`). -/
def nestCtorNfC (ctx : NestCtx) (prog : List NestHole) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (tel : Expr) : NestCtorNf :=
  ⟨cv.name, us, ds.map (Expr.replaceFVarsC (nestHoleImgC ctx prog)),
    Expr.replaceFVarsC (nestHoleImgC ctx prog) tel⟩

/-- The cached `structUsedLater`: the occurrence by `hasLooseBVarBC`. -/
def structUsedLaterC (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => Expr.hasLooseBVarBC 0 rest
  | none => false

/-- The cached `nestCtors`: the constructor's crest by `nestCrestC`,
typed by the cached core, its fields by `nestFieldsC`, the walked
telescope closed ONCE (`closeTelescopeC`) for the U4 test, the record
and the output.  The walk of the fields is `rec` at the fuel
`fuelOf crest`, computed once per constructor before its fields are
walked (the specification's `rec crest`, `fun crest => nestPos … (whnfWalkFuel
crest)` at the root, is applied anew at every field). -/
def nestCtorsC (ctx : NestCtx) (fe : FEnv) (fuelOf : Expr → Nat)
    (rec : Nat → List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) :
    List (ConstantVal × Nat) → NestState →
      CheckCM (List (List NestFieldKind × Expr) × NestState)
  | [], st => pure ([], st)
  | (cv, nF) :: cs, st => do
    unless Name.nodup cv.levelParams do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    let crest ← unwrapOr
      (nestCrestC names us ds holes (Expr.instLevelParams cv.levelParams us cv.type))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind the parameters (official: ill-formed constructor)")
    let ty ← (coreKnotI mode false fe checkFuel).infer hi crest
    let _ ← ensureSortI (coreKnotI mode false fe checkFuel) hi ty
    let F := fuelOf crest
    let (ks, nds, cur, st) ← nestFieldsC (rec F) prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    let tel := Expr.closeTelescopeC nds hi cur
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLaterC tel 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result depends on a recursive or nested field)")
    unless nestResHead cur && (Expr.getAppArgsC cur).all
        (fun x => !Expr.nestOccC ctx.names ctx.nP hi x) do
      throw (.invalid "nested positivity: invalid return type — a constructor's result \
        index mentions the block")
    let st := { st with ctorNfs := st.ctorNfs.push (nestCtorNfC ctx prog us ds cv tel) }
    let (os, st) ← nestCtorsC ctx fe fuelOf rec prog hi us ds names holes cs st
    pure ((ks, tel) :: os, st)

/-- The cached `nestGrowGroup`. -/
def nestGrowGroupC (ctx : NestCtx) (fe : FEnv) (hi : Nat) (us : List Level)
    (ds : List Expr) : List Name → List (Name × Expr) → CheckCM (List (Name × Expr))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstTypeC mode ctx fe hi ⟨c, us, ds⟩
    nestGrowGroupC ctx fe hi us ds cs (grp ++ [(c, cty)])

/-- The cached `nestFrame`. -/
def nestFrameC (ctx : NestCtx) (fe : FEnv)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) : CheckCM NestState := do
  familyKeyCheckC mode fe ctx.find? hi (grp.headD default).1 us ds
  let prog' := (grp.mapIdx fun _ (c, ty) =>
    ({ key := ⟨c, us, ds⟩, base := hi, nIdx := ty.piBinders.1.length } : NestHole)).reverse ++ prog
  let ctors ← nestGroupCtors ctx nPc (grp.map (·.1))
  let (_, st) ← nestCtorsC mode ctx fe (fun _ => 0) (fun _ => rec) prog' (hi + grp.length) us ds
    (grp.map (·.1)) (grp.mapIdx fun i (_, ty) => Expr.fvar (hi + i) ty) ctors st
  pure st

/-- The cached `nestContNew`. -/
def nestContNewC (ctx : NestCtx) (fe : FEnv)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : CheckCM (NestFieldKind × NestState) := do
  let wp := nestWalkStack ctx prog ds
  let grp ← nestGrowGroupC mode ctx fe (ctx.hiAt wp.length) us ds (nestFrameMates ctx n)
    [(n, cty)]
  let act := st.active
  let st := { st with
    active := grp.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey)) ++ act }
  let st ← nestFrameC mode ctx fe rec wp (ctx.hiAt wp.length) us ds nPc grp st
  return (.nested (kb != 0),
    { st with active := act,
              keys := if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then
                nestAcceptGroup us ds grp st.keys else st.keys })

/-- The cached `nestContKey`. -/
def nestContKeyC (ctx : NestCtx) (fe : FEnv)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : CheckCM (NestFieldKind × NestState) :=
  if st.active.contains ⟨n, us, ds⟩ then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  else if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) && st.keys.contains ⟨n, us, ds⟩ then
    pure (.nested (kb != 0), st)
  else nestContNewC mode ctx fe rec prog kb n us ds nPc cty st

/-- The cached `nestCont`. -/
def nestContC (ctx : NestCtx) (fe : FEnv)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : CheckCM (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainer ctx n) nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !Expr.nestOccC ctx.names ctx.nP (ctx.hiAt prog.length) x) then
    throw nestNonValid
  if n == quotName then throw nestNonValid
  unless (args.take q.1).all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt prog.length) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  let ni ← nestInstTypeC mode ctx fe (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKeyC mode ctx fe rec prog kb n us (args.take q.1) q.1 ni.2 st

/-- **The cached positivity function** (`nestPos`): the cached core's
`whnf`, the occurrence tests by `nestOccC`, the binder opened by
`instantiate1C` and closed by `abstract1C`, the spine by `getAppArgsC`. -/
def nestPosC (fe : FEnv) (ctx : NestCtx) :
    Nat → List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← (coreKnotI mode false fe checkFuel).whnf dep e
    if !Expr.nestOccC ctx.names ctx.nP hi w then
      return (.ordinary, (if Expr.nestOccC ctx.names ctx.nP hi e then w else e), st)
    match w with
    | .forallE a b =>
      if Expr.nestOccC ctx.names ctx.nP hi a then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ←
        nestPosC fe ctx fuel prog (dep + 1) (kb + 1) (Expr.instantiate1C b (.fvar dep a)) st
      pure (k, .forallE a (Expr.abstract1C nb dep), st)
    | _ =>
      let args := Expr.getAppArgsC w
      match w.getAppFn with
      | .fvar i _ =>
        match nestHoleAt ctx prog i with
        | some h =>
          if args.all (fun x => !Expr.nestOccC ctx.names ctx.nP hi x) && args.length == h.nIdx then
            return (if i < ctx.hiAt 0 then
                (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
              else .inProgress, w, st)
          else throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        if ctx.names.contains n then throw nestNonValid
        let (k, st) ← nestContC mode ctx fe (nestPosC fe ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- The cached `nestHoles`: the formers instantiated by `Expr.instPisWithC`. -/
def nestHolesC (ctx : NestCtx) : Option (List Expr) :=
  (List.range ctx.names.length).mapM fun mm =>
    match ctx.formers[mm]? with
    | some cv => (Expr.instPisWithC ctx.params cv.type).map (.fvar (ctx.nP + mm) ·)
    | none => none

/-- The cached `nestRootCanon`. -/
def nestRootCanonC (ctx : NestCtx) (cv : ConstantVal) : Option Expr :=
  nestCanonCrestC ctx.names (ctx.lps.map .param) ctx.nP
    (Expr.instLevelParams cv.levelParams (ctx.lps.map .param) cv.type)

/-- The cached `Expr.piDomsOcc`. -/
def piDomsOccC (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE d b => Expr.nestOccC names lo hi d || piDomsOccC names lo hi n b
  | _ + 1, _ => false

/-- The cached `nestUniformOk`. -/
def nestUniformOkC (ctx : NestCtx) (cv : ConstantVal) : Bool :=
  !piDomsOccC ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type &&
    match nestRootCanonC ctx cv with
    | some crest => !Expr.nestOccC ctx.names 0 0 crest
    | none => false

/-- The cached `nestUniform`. -/
def nestUniformC (ctx : NestCtx) (ctorss : List (List (ConstantVal × Nat))) : CheckCM Unit :=
  match ctorss.findSome? (·.find? (!nestUniformOkC ctx ·.1)) with
  | some c => throw (.invalid s!"invalid occurrence of a datatype being declared in the \
      type of {c.1.name}: it must be applied to the parameters and universe levels of the \
      mutual declaration")
  | none => pure ()

/-- The cached `nestRoot`: each constructor walked at the fuel
`whnfWalkFuelC` of its crest. -/
def nestRootC (fe : FEnv) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestState →
      CheckCM (List (List (List NestFieldKind × Expr)) × NestState)
  | [], st => pure ([], st)
  | cs :: css, st => do
    let (o, st) ← nestCtorsC mode ctx fe whnfWalkFuelC (nestPosC mode fe ctx) [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st
    let (os, st) ← nestRootC fe ctx holes css st
    pure (o :: os, st)

/-- The cached `nestSeedOf`. -/
def nestSeedOfC (ctx : NestCtx) (holes : List Expr) (I : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) : NestKey × Nat :=
  (⟨I, us, ds.map fun x =>
      Expr.replaceFVarsC (nestKeyMap ctx.params holes)
        (Expr.replaceAppsC (nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0 ctx.nP x)⟩,
    nPc)

/-- The cached `nestSeeds`. -/
def nestSeedsC (fe : FEnv) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → CheckCM NestState
  | [], st => pure st
  | (key, nPc) :: ks, st => do
    let F := key.ds.foldl (fun a d => max a (whnfWalkFuelC d)) fuelSlack
    let (_, cty) ← nestInstTypeC mode ctx fe (ctx.hiAt 0) key
    let (_, st) ← nestContKeyC mode ctx fe (nestPosC mode fe ctx F) [] 0 key.cname key.lvls
      key.ds nPc cty st
    nestSeedsC fe ctx ks st

/-! ## The positivity stage -/

/-- The cached `checkStructFieldSortsI`: each field's sort by the cached
core's `infer` and `ensureSortI`. -/
def checkStructFieldSortsIC (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← (coreKnotI mode false fe checkFuel).infer (nP + j) fv.fvarTypeD
    let u ← ensureSortI (coreKnotI mode false fe checkFuel) (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    checkStructFieldSortsIC fe isProp large s nP fvs idxArgs j

/-- The cached `checkAbsCtorSorts`: the scoping assertion by
`allLevelParamsDefinedC`, the normal form opened by `openPisAtFvarsC`. -/
def checkAbsCtorSortsC (fe : FEnv) (ctx : NestCtx) :
    List (ConstantVal × Nat) → List (List NestFieldKind × Expr) → CheckCM Unit
  | c :: cs, o :: os => do
    unless Expr.allLevelParamsDefinedC ctx.lps o.2 do
      throw (.internal "direct rec: a positivity normal form outside the block's level \
        parameters")
    let xq ← unwrapOr (openPisAtFvarsC c.2 o.2 (ctx.hiAt 0))
      (.internal "direct rec: abstracted constructor fields")
    checkStructFieldSortsIC mode fe (Level.isEquiv ctx.sort .zero == some true)
      false ctx.sort (ctx.hiAt 0) xq.1 [] c.2
    checkAbsCtorSortsC fe ctx cs os
  | _, _ => pure ()

/-- The cached `checkAbsCtorSortsAll`. -/
def checkAbsCtorSortsAllC (fe : FEnv) (ctx : NestCtx) :
    List (List (ConstantVal × Nat)) → List (List (List NestFieldKind × Expr)) → CheckCM Unit
  | cs :: css, os :: oss => do
    checkAbsCtorSortsC mode fe ctx cs os
    checkAbsCtorSortsAllC fe ctx css oss
  | _, _ => pure ()

/-- The cached `blockNestCtx`: the head former opened by
`openPisAtFvarsC`, the holes by `nestHolesC`. -/
def blockNestCtxC (p : BlockShape) (find? : Name → Option ConstantInfo) :
    CheckCM (NestCtx × List Expr) := do
  let cvTa0 ← unwrapOr p.formers.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (openPisAtFvarsC p.nP cvTa0.type 0)
    (.internal "direct rec: type former telescope")
  let ctx := p.nestCtx pq.1 find?
  let holes ← unwrapOr (nestHolesC ctx) (.internal "direct rec: a member is not a stored former")
  pure (ctx, holes)

/-- The cached `classSeeds`. -/
def classSeedsC (ctx : NestCtx) (holes : List Expr) (Ms : List TargetMajor) :
    List (NestKey × Nat) :=
  Ms.filterMap fun M =>
    if M.member.isNone then some (nestSeedOfC ctx holes M.ind M.lvls M.ds M.nPc) else none

/-- **The cached positivity stage** (`checkBlockPositivity`): the
uniform-occurrence check, the root frame, the fields' universes. -/
def checkBlockPositivityC (fe : FEnv) (find? : Name → Option ConstantInfo) (p : BlockShape) :
    CheckCM (List (List (List NestFieldKind × Expr)) × NestState) := do
  let (ctx, holes) ← blockNestCtxC p find?
  nestUniformC ctx p.memberCtors
  let (outs, st) ← nestRootC mode fe ctx holes p.memberCtors {}
  checkAbsCtorSortsAllC mode fe ctx p.memberCtors outs
  pure (outs, st)

end ConLeche.Cached
