module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Cached.IndPositivity

@[expose] public section

/-!
# The cached twin of the inductive check: the block pass and the classes (task #498)

The production twins of the pass's stages (`checkBlockIndsF`,
`checkBlockCtorsF`, `ConLeche/Kernel/Inductives/BlockInstallF.lean`,
`SumInstallF.lean`, `StructInstallF.lean`) and of the classes
(`checkBlockClasses`, `GenRec.lean`, with `classRead`, `ClassRead.lean`,
and the major's resolution, `RecCheck.lean`): monomorphic `CheckCM`
definitions at a mode and an environment index, calling the cached core
(`coreKnotI`) directly and the cached walks of
`ConLeche/Cached/ExprOpsC.lean` (`openPisAtFvarsC`, `constsResolveFC`,
`getAppArgsC`, `instantiate1C`, `replaceFVarsC`, `nestOccC`,
`instPisWithC`) where the specification runs the plain ones.  Each
mirrors its specification at the shared operations, so the relation is
an equation (`checkBlockIndsC_eq`, `checkBlockCtorsC_eq`,
`checkBlockClassesC_eq`, `ConLeche/Verify/Cached/IndPassC.lean`); the
cached driver (`checkBlockPassS`) runs them.  The constant check
`checkConstantValC`, which the members' reduction runs too, opens the
file.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## The constant check -/

/-- The cached `unresolvedConstsErrorL`: the `sorryAx` test by the
memoized `mentionsAnyConstC` (`unresolvedConstsErrorLC_eq`). -/
def unresolvedConstsErrorLC (strOk : Bool) (where_ : String) (e : Expr) : CheckError :=
  if !strOk && (Expr.hasStrLitGo {} e).1 then
    .notImplemented "string literals before the String support declarations"
  else if Expr.mentionsAnyConstC [sorryAxName] e then
    .notImplemented s!"use of the sorryAx axiom in {where_}"
  else .invalid s!"unknown constant in {where_}"

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode false fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorLC (strLitStoredF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

/-! ## Stage 1: the formers -/

/-- The cached `checkBlockTeleF`. -/
def checkBlockTeleC (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    CheckCM (ConstantVal × Level) := do
  checkConstantValC mode fe ms.cvT
  let (cvTa, s) ← checkSumTele (nP + ms.nIdx) ms.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + ms.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  pure (cvTa, s)

/-- The cached `checkBlockTelesF`. -/
def checkBlockTelesC (fe : FEnv) (nP : Nat) :
    List MemberShape → CheckCM (List (ConstantVal × Level))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTeleC mode fe nP ms
    let rs ← checkBlockTelesC fe nP rest
    pure (r :: rs)

/-- The cached `checkBlockDomsAtF`. -/
def checkBlockDomsAtC (fe : FEnv) (off : Nat) (fvs doms : List Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    unless ← (coreKnotI mode false fe checkFuel).defeq (off + j) a.fvarTypeD b do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtC fe off fvs doms j

/-- The cached `checkBlockAgreeF`: the telescopes opened by
`openPisAtFvarsC`. -/
def checkBlockAgreeC (fe : FEnv) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    List (ConstantVal × Level) → CheckCM Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (openPisAtFvarsC nP cvTa0.type 0)
      (.internal "block: type former telescope")
    let tq ← unwrapOr (openPisAtFvarsC nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq0.1.length do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtC mode fe 0 tq.1 (tq0.1.map Expr.fvarTypeD) nP
    unless ← liftFueled "level comparison" (Level.isEquiv s s0) do
      throw (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgreeC fe nP cvTa0 s0 rest

/-- The cached `checkBlockIndsF`; the formers are consed by the shared
`consBlockIndsF`. -/
def checkBlockIndsC (fe : FEnv) (p : BlockShape) (isRec : Bool) :
    CheckCM (FEnv × BlockShape) :=
  match p.members with
  | [] => throw (.internal "block: no type former")
  | ms0 :: rest => do
    let (cvTa0, s0) ← checkBlockTeleC mode fe p.nP ms0
    let cvs ← checkBlockTelesC mode fe p.nP rest
    checkBlockAgreeC mode fe p.nP cvTa0 s0 cvs
    let p₁ := p.withSort s0
    pure (consBlockIndsF p₁ isRec (p.members.map (·.declared)) 0 fe, p₁)

/-! ## Stage 1b: the constructors -/

/-- The cached `checkStructDomsAtFA`. -/
def checkStructDomsAtC (fe : FEnv) (off : Nat) (fvs doms : Array Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← (coreKnotI mode false fe checkFuel).defeq (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtC fe off fvs doms j

/-- The cached `checkStructFieldSortsIFA`. -/
def checkStructFieldSortsC (fe : FEnv) (isProp large : Bool) (s : Level) (nP : Nat)
    (fvs : Array Expr) (idxArgs : List Expr) : Nat → CheckCM Unit
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
    checkStructFieldSortsC fe isProp large s nP fvs idxArgs j

/-- The cached `checkSumCtorF`: the telescopes opened by
`openPisAtFvarsC`, the residual's spine read once by `getAppArgsC`,
the resolution gates by `constsResolveFC`. -/
def checkSumCtorC (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) : CheckCM Unit := do
  checkConstantValC mode fe cvC
  let (_, cbody) ← unwrapOr (cvC.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvarsC nP cvC.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsC nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAtC mode fe 0 cq.1.toArray (tq.1.map Expr.fvarTypeD).toArray nP
  let xq ← unwrapOr (openPisAtFvarsC nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  let args := Expr.getAppArgsC xq.2
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      args.take nP == cq.1 && args.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  unless xq.1.all fun x => constsResolveFC fe₀ x.fvarTypeD do
    throw (.notImplemented "direct sum: field domain after the block")
  unless (args.drop nP).all fun e => constsResolveFC fe₀ e do
    throw (.invalid "direct sum: index expression mentions the block")
  checkStructFieldSortsC mode fe isProp large resSort nP xq.1.toArray (args.drop nP) nF

/-- The cached `checkSumCtorsF`. -/
def checkSumCtorsC (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → CheckCM Unit
  | [] => pure ()
  | c :: cs => do
    checkSumCtorC mode fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    checkSumCtorsC fe₀ fe T lps nP nIdx resSort isProp large cvTa cs

/-- The cached `checkBlockCtorsF`. -/
def checkBlockCtorsC (fe₀ fe : FEnv) (p : BlockShape) : List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    checkSumCtorsC mode fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx
      p.resSort p.isProp p.large ms.cvT ms.ctors
    checkBlockCtorsC fe₀ fe p rest

/-- The cached `checkBlockIdxSortsF` (the tail's index sorts), over the
array walk (`checkStructFieldSortsIFA_eq`). -/
def checkBlockIdxSortsC (fe₁ : FEnv) (p : BlockShape) : List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    let tq ← unwrapOr (openPisAtFvarsC (p.nP + ms.nIdx) ms.cvT.type 0)
      (.internal "direct rec: type former telescope")
    checkStructFieldSortsC mode fe₁ true false p.resSort p.nP (tq.1.drop p.nP).toArray []
      ms.nIdx
    checkBlockIdxSortsC fe₁ p rest

/-! ## The classes: the pre-pass -/

/-- The cached `classReadMinor`: the minor's telescope opened by
`openPisAtFvarsC`, the spines read by `getAppArgsC`. -/
def classReadMinorC (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    Option ClassSlot := do
  let n := dom.piBinders.1.length
  let (fvs, concl) ← openPisAtFvarsC n dom d
  let .fvar p _ := concl.getAppFn | none
  let c ← classOfMotiveVar nP motPos p
  let .const C _ := (← (Expr.getAppArgsC concl).getLast?).getAppFn | none
  let ihs := (List.range fvs.length).filterMap fun q =>
    match (fvs.getD q default).fvarTypeD.piResult.getAppFn with
    | .fvar p' _ =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match (Expr.getAppArgsC (fvs.getD q default).fvarTypeD.piResult).getLast? with
        | some a =>
          match a.getAppFn with
          | .fvar f _ => if d ≤ f then some (f - d, t) else none
          | _ => none
        | none => none
      | none => none
    | _ => none
  pure (.minor c C ihs)

/-- The cached `classReadSlots`: each binder opened by `instantiate1C`. -/
def classReadSlotsC (nPc : Name → Nat) (np : Nat) :
    Nat → List Nat → Nat → Expr → Option (List ClassSlot)
  | 0, _, _, _ => some []
  | n + 1, motPos, d, .forallE dom body => do
    let slot ← match dom.piResult with
      | .sort _ => do
        let (bs, _) := dom.piBinders
        let mdom ← bs.getLast?
        let .const I us := mdom.getAppFn | none
        pure (ClassSlot.motive ⟨I, us, (Expr.getAppArgsC mdom).take (nPc I)⟩)
      | _ => classReadMinorC np motPos d dom
    let motPos' := match slot with | .motive _ => motPos ++ [d - np] | _ => motPos
    let rest ← classReadSlotsC nPc np n motPos' (d + 1) (Expr.instantiate1C body (.fvar d dom))
    pure (slot :: rest)
  | _ + 1, _, _, _ => none

/-- The cached `classRead` (the UNVERIFIED pre-pass, `ClassRead.lean`):
the recursor types opened by `openPisAtFvarsC`. -/
def classReadC (nP : Nat) (nPc : Name → Nat) (recs : List RecShape) : Option ClassRead := do
  let rc0 ← recs.head?
  let (_, body) ← openPisAtFvarsC nP rc0.cvR.type 0
  let slots ← classReadSlotsC nPc nP (rc0.rP - nP) [] nP body
  let motPos := (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false
  let recCls ← recs.mapM fun rc => do
    let (_, concl) ← openPisAtFvarsC (rc.mI + 1) rc.cvR.type 0
    let .fvar p _ := concl.getAppFn | none
    classOfMotiveVar nP motPos p
  pure ⟨slots, recCls⟩

/-! ## The classes: the keys and the majors -/

/-- The cached `targetCanonParams`, by `replaceFVarsC`. -/
def targetCanonParamsC (pfvs : List Expr) (e : Expr) : Expr :=
  Expr.replaceFVarsC (fun i => pfvs[i]?) e

/-- The cached `classKeyCanon`. -/
def classKeyCanonC (params : List Expr) (k : ClassKey) : ClassKey :=
  { k with ds := k.ds.map (targetCanonParamsC params) }

/-- The cached `classKeyOf`. -/
def classKeyOfC (nP : Nat) (params : List Expr) (k : ClassKey) : CheckCM ClassKey := do
  let k := classKeyCanonC params k
  unless k.ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ nP) do
    throw (.invalid "target rec: the major's parameters mention more than the \
      recursor's parameters")
  pure k

/-- The cached `targetOutsideInst`: the former's telescope by
`familyTelescopeC`, at the class's levels by `instLevelParams` and its
parameters by `instPisWithC`. -/
def targetOutsideInstC (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr) :
    CheckCM (Nat × Level) := do
  let some (.indInfo cvI capsI) := fe.find? I
    | throw (.invalid "target rec: the recursor's major is not a stored inductive")
  let tyI ← familyTelescopeC mode fe cvI capsI
  let some ty := instPisWithC ds (Expr.instLevelParams cvI.levelParams us tyI)
    | throw (.invalid "target rec: the major's type former does not bind its parameters \
        (official: ill-formed inductive type)")
  let (ibs, s) := ty.piBinders
  let .sort s := s
    | throw (.invalid "target rec: the major's type former is not a telescope ending in a \
        sort (official: type expected)")
  pure (ibs.length, s)

/-- The cached `targetMajorOf`: the spine read by `getAppArgsC`, the
auxiliary-type test by `nestOccC`. -/
def targetMajorOfC (fe : FEnv) (p : BlockShape) (pfvs fvs : List Expr) (mty : Expr) :
    CheckCM TargetMajor := do
  let args := Expr.getAppArgsC mty
  match mty.getAppFn with
  | .const I us =>
    match p.memberNames.findIdx? (· == I) with
    | some t => do
      let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
      unless us == p.lps.map .param && args.take p.nP == fvs.take p.nP do
        throw (.invalid "target rec: the recursor's major premise is not the member at its \
          parameters and its index binders")
      pure { ind := I, lvls := us, ds := fvs.take p.nP, nPc := p.nP, nIdx := ms.nIdx,
             ctors := ms.ctors, member := some t, pfvs := pfvs : TargetMajor }
    | none => do
      if I == quotName then
        throw (.invalid "target rec: the recursor's major is Quot, which is no inductive")
      let some (nPc, ctors) := targetCtorsOf fe I
        | throw (.invalid "target rec: the recursor's major is not a stored inductive")
      let ds := args.take nPc
      unless ds.length == nPc &&
          ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ p.nP) do
        throw (.invalid "target rec: the major's parameters mention more than the \
          recursor's parameters")
      unless ds.any (fun x => Expr.nestOccC p.memberNames 0 0 x) do
        throw (.invalid "target rec: the recursor's major is an outside inductive at an \
          instantiation that is no auxiliary type of the block (official generates no such \
          auxiliary recursor: `elim_nested_inductive`, `is_nested`)")
      let (nIdx, sI) ← targetOutsideInstC mode fe I us ds
      unless ← liftFueled "level comparison" (Level.isEquiv sI p.resSort) do
        throw (.invalid "target rec: the recursor's major lives in another universe than \
          the block (Q1)")
      pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx, ctors := ctors,
             member := none, pfvs := pfvs }
  | _ => throw (.invalid "target rec: the recursor's major premise is not an inductive's \
      application")

/-- The cached `targetPinTys`. -/
def targetPinTysC (fe : FEnv) (d : Nat) : List Expr → CheckCM Unit
  | [] => pure ()
  | x :: xs => do
    let _ ← (coreKnotI mode false fe checkFuel).infer d x
    targetPinTysC fe d xs

/-- The cached `targetMajorPins`. -/
def targetMajorPinsC (fe : FEnv) (rP : Nat) (M : TargetMajor) : CheckCM Unit :=
  if M.member.isNone then do
    targetPinTysC mode fe rP M.ds
    familyKeyCheckC mode fe fe.find? rP M.ind M.lvls M.ds
  else pure ()

/-- The cached `classMajors`. -/
def classMajorsC (fe : FEnv) (p : BlockShape) (pfvs : List Expr) :
    List ClassKey → CheckCM (List TargetMajor)
  | [] => pure []
  | key :: keys => do
    let M ← targetMajorOfC mode fe p pfvs pfvs (Expr.mkAppN (.const key.ind key.lvls) key.ds)
    targetMajorPinsC mode fe p.nP M
    let Ms ← classMajorsC fe p pfvs keys
    pure (M :: Ms)

/-- The cached `checkBlockClasses`. -/
def checkBlockClassesC (fe₁ : FEnv) (p : BlockShape) (params : List Expr) :
    CheckCM (ClassRead × List TargetMajor) := do
  -- [UNVERIFIED] the pre-pass: the classes, the layout, each recursor's class
  let rd ← unwrapOr (classReadC p.nP (classNPcOf p fe₁) p.recs)
    (.invalid "generated recursor: the recursor family is not of the generated shape \
      (official: invalid recursor)")
  let keys ← rd.classes.mapM (classKeyOfC p.nP params)
  let Ms ← classMajorsC mode fe₁ p params keys
  unless (List.range p.k).all (fun t => (Ms.filter (·.member == some t)).length == 1) do
    throw (.invalid "generated recursor: the recursor family does not have exactly one class \
      per member (official: invalid recursor)")
  pure (rd, Ms)

end ConLeche.Cached
