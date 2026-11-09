module

public import ConLeche.Cached.IndPass
public import ConLeche.Kernel.Inductives.GenRec

@[expose] public section

/-!
# The cached twin of the inductive check: the recursor stage (task #498)

The production twins of `ConLeche/Kernel/Inductives/GenRec.lean` and of
the class kit of `ConLeche/Kernel/Inductives/RecCheck.lean` it runs:
monomorphic `CheckCM` definitions at a mode and an environment index,
calling the cached core (`coreKnotI`) directly and the cached walks of
`ConLeche/Cached/ExprOpsC.lean` where the specification runs the plain
ones — the member abstraction `targetAbsC`, the free-variable
replacement `replaceFVarsC` (the canonical parameters, the erased
annotations), `nestOccC`, the openers `openPisAtFvarsC`/`instPisWithC`/
`targetPiDomsWithC`, the closers `closeTelescopeC`/`closeLamsC` (each
domain abstracted once) and the guards `allLevelParamsDefinedC`/
`constsResolveFC`.  The generators (`ClassGen.majorC` …
`classGenRuleC`) are pure.

Each twin is the specification at the shared operations
(`genRecCheckC_eq : genRecCheckC mode fe … = genRecCheck (shadowOpsC
mode) fe …`, `ConLeche/Verify/Cached/IndRecC.lean`); the rule stage's
inference runs at the rule-less recursors' environment with
`sharedOpsRuleR`'s two flushes inline (`classRuleCheckC`).  The
rule-less recursors are an overlay sharing the constructors' index
(`classFeROvl`).
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The rule-less recursors, as an overlay -/

/-- The records `consBlockRecsBareF` pushes, in push order. -/
def blockRecInfosBare (p : BlockShape) : Nat → List (ConstantVal × Nat) → List ConstantInfo
  | _, [] => []
  | m, (cvRa, _nIdx) :: rest =>
    .recInfo cvRa (p.majorIdxAt m) (p.rulePrefixAt m) false [] :: blockRecInfosBare p (m + 1) rest

/-- **`classFeR` as an overlay** (task #329): the rule-less generated
recursors consed onto `fe` WITHOUT entering its index (`FEnv.overlay`,
newest first).  The rule stage needs `fe` and `classFeR … fe` at once,
so `classFeR`'s pushes ran on a shared index and copied its whole bucket
array, once per inductive block; the overlay shares it.  Same `find?`
and `env` as `classFeR` on an `fe` without an overlay
(`classFeROvl_find?`, `ConLeche/Verify/Cached/BlockOverlay.lean`). -/
def classFeROvl (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (fe : FEnv) : FEnv :=
  fe.overlay (blockRecInfosBare p 0
    ((cvGs.zip recCls).map fun (cv, c) => (cv, (Ms.getD c default).nIdx))).reverse

/-! ## The generator -/

/-- The cached `targetCtorAt`: an outside class's constructor at its
levels by the cached `instLevelParams`. -/
def targetCtorAtC (M : TargetMajor) (c : ConstantVal) : Expr :=
  match M.member with
  | some _ => c.type
  | none => Expr.instLevelParams c.levelParams M.lvls c.type

/-- The cached `ClassGen.major`. -/
def _root_.ConLeche.ClassGen.majorC (g : ClassGen) (c : Nat) (d : Nat) :
    Option (List Expr × Expr) := do
  let ci := g.cls.getD c default
  let ty ← Expr.instPisWithC ci.ds (g.formerTys.getD c default)
  let (ifs, _) ← openPisAtFvarsC ci.nIdx ty d
  pure (ifs, Expr.mkAppN (.const ci.ind ci.lvls) (ci.ds ++ ifs))

/-- The cached `ClassGen.motiveTy`. -/
def _root_.ConLeche.ClassGen.motiveTyC (g : ClassGen) (c d : Nat) : Option Expr := do
  let (ifs, maj) ← g.majorC c d
  pure (Expr.closeTelescopeC (ifs.map classBinder) d (.forallE maj (.sort g.elim)))

/-- The cached `ClassGen.ihParts`. -/
def _root_.ConLeche.ClassGen.ihPartsC (g : ClassGen) (t : Nat) (tele : Nat) (w : Expr) (d : Nat) :
    Option (List Expr × List Expr) := do
  let (xs, leaf) ← openPisAtFvarsC tele w d
  pure (xs, (Expr.getAppArgsC leaf).drop (g.cls.getD t default).nPc)

/-- The cached `ClassGen.minorTy`. -/
def _root_.ConLeche.ClassGen.minorTyC (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) :
    Option Expr := do
  let ci := g.cls.getD c default
  let (fvs, res) ← openPisAtFvarsC x.nF x.tyD d
  let ws ← Expr.targetPiDomsWithC fvs x.tyN
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let ihs ← (List.range recs.length).mapM fun l => do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let (xs, idx) ← g.ihPartsC t tele (ws.getD i default) e
    pure (Expr.closeTelescopeC (xs.map g.binder) e
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs])))
  let concl := Expr.mkAppN (g.motVar c)
    ((Expr.getAppArgsC res).drop ci.nPc ++
      [Expr.mkAppN (.const x.cv.name ci.lvls) (ci.ds ++ fvs)])
  pure (Expr.closeTelescopeC (fvs.map g.binder ++ ihs) d concl)

/-- The cached `ClassGen.prefixBinders`. -/
def _root_.ConLeche.ClassGen.prefixBindersC (g : ClassGen) : Option (List Expr) := do
  let slotBs ← (List.range g.slots.length).mapM fun s => do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      g.motiveTyC c d
    | .minor c C _ =>
      let x ← (g.ctors.getD c []).find? (·.cv.name == C)
      g.minorTyC c x d
  pure (g.params.map g.binder ++ slotBs)

/-- The cached `classGenRecTy`. -/
def classGenRecTyC (g : ClassGen) (c : Nat) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.majorC c rP
  let t : Expr := .fvar (rP + ifs.length) maj
  pure (Expr.closeTelescopeC (pre ++ ifs.map g.binder ++ [maj]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [t])))

/-- The cached `classGenRule`. -/
def classGenRuleC (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level) (c : Nat)
    (x : ClassCtor) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (s, _) ← (List.range g.slots.length).zip g.slots |>.find? fun (_, sl) =>
    match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false
  let (fvs, _) ← openPisAtFvarsC x.nF x.tyD rP
  let ws ← Expr.targetPiDomsWithC fvs x.tyN
  let pvars := (List.range rP).map fun i => if i < g.nP then g.params.getD i default else
    g.slotVar (i - g.nP)
  let ihs ← (List.range x.nF).filterMapM fun i =>
    match x.kinds.getD i .ordinary with
    | .ordinary => some none
    | .recursive t tele => do
      let f := fvs.getD i default
      let (xs, idx) ← g.ihPartsC t tele (ws.getD i default) (rP + x.nF)
      let r ← recOf t
      pure (some (Expr.closeLamsC (xs.map g.binder) (rP + x.nF)
        (Expr.mkAppN (.const r rlvls) (pvars ++ idx ++ [Expr.mkAppN f xs]))))
  pure (Expr.closeLamsC (pre ++ fvs.map g.binder) 0 (Expr.mkAppN (g.slotVar s) (fvs ++ ihs)))

variable (mode : CheckMode)

/-! ## The class match -/

/-- The cached `targetCanonParams`. -/
def targetCanonParamsC (pfvs : List Expr) (e : Expr) : Expr :=
  Expr.replaceFVarsC (fun i => pfvs[i]?) e

/-- The cached `Expr.eraseFVarTys`. -/
def eraseFVarTysC (e : Expr) : Expr :=
  Expr.replaceFVarsC (fun i => some (.fvar i (.sort .zero))) e

/-- The cached `targetParamsDefEq`, its member abstraction the cached
`targetAbsC names lvls holes`. -/
def targetParamsDefEqC (fe : FEnv) (d : Nat) (names : List Name) (lvls : List Level)
    (holes : List Expr) (pfvs : List Expr) : List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if a.bvarB == 0 && b.bvarB == 0 && a.fvarB ≤ pfvs.length && b.fvarB ≤ pfvs.length then
      let a' := Expr.targetAbsC names lvls holes (targetCanonParamsC pfvs a)
      let b' := Expr.targetAbsC names lvls holes (targetCanonParamsC pfvs b)
      if a' == b' then targetParamsDefEqC fe d names lvls holes pfvs as bs
      else
        let _ ← (coreKnotI mode false fe checkFuel).infer d a'
        let _ ← (coreKnotI mode false fe checkFuel).infer d b'
        if ← (coreKnotI mode false fe checkFuel).defeq d a' b' then
          targetParamsDefEqC fe d names lvls holes pfvs as bs
        else pure false
    else pure false
  | _, _ => pure false

/-- The cached `targetClassMatch`. -/
def targetClassMatchC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) :
    CheckCM Bool := do
  unless Level.isEquivList us lvls == some true do return false
  targetParamsDefEqC mode fe (pfvs.length + formerTys.length) p.memberNames (p.lps.map .param)
    (targetHoles formerTys pfvs.length) pfvs ds eds

/-- The cached `targetMajorNfs`. -/
def targetMajorNfsC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat)) :
    List NestCtorNf → CheckCM (List NestCtorNf)
  | [] => pure []
  | e :: es => do
    let rest ← targetMajorNfsC fe p formerTys pfvs us ds ctors es
    if ctors.any (·.1.name == e.ctor) then
      if ← targetClassMatchC mode fe p formerTys pfvs us ds e.lvls e.ds then pure (e :: rest)
      else pure rest
    else pure rest

/-- The cached `targetK53`. -/
def targetK53C (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr) : CheckCM Bool :=
  match f.stripPis tele.length with
  | none => pure false
  | some (teleW, leafW) =>
    if teleW.map eraseFVarTysC != tele.map eraseFVarTysC
    then pure false
    else
      match leafW.getAppFn, majDom.getAppFn with
      | .const I' us', .const I _ =>
        if I' == I && (Expr.getAppArgsC leafW).length == (Expr.getAppArgsC majDom).length &&
            ((Expr.getAppArgsC leafW).drop Mc.nPc).map eraseFVarTysC
              == ((Expr.getAppArgsC majDom).drop Mc.nPc).map eraseFVarTysC &&
            Expr.nestOccC p.memberNames 0 0
              (Expr.mkAppN (.const I' us') ((Expr.getAppArgsC leafW).take Mc.nPc)) then
          targetClassMatchC mode fe p formerTys Mc.pfvs Mc.lvls Mc.ds us'
            ((Expr.getAppArgsC leafW).take Mc.nPc)
        else pure false
      | _, _ => pure false

/-! ## The classes' constructors -/

/-- The cached `classFieldsOf`. -/
def classFieldsOfC (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) :
    Nat → List Expr → CheckCM (List ClassField)
  | _, [] => pure []
  | i, f :: fs => do
    let w := f.fvarTypeD
    let k' ← match Expr.nestOccC p.memberNames 0 0 w, ihs.filter (·.1 == i) with
      | false, [] => pure ClassField.ordinary
      | true, [(_, t)] => pure (.recursive t w.piBinders.1.length)
      | _, _ =>
        throw (.invalid s!"generated recursor: the inductive hypotheses of {ctor}'s minor \
          premise are not its recursive fields (official: invalid recursor)")
    let ks' ← classFieldsOfC p ctor ihs (i + 1) fs
    pure (k' :: ks')

/-- The cached `classNodesAgree`. -/
def classNodesAgreeC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (leaf : Expr) (fvs : List Expr)
    (i : Nat) (ctor : Name) : List NestCtorNf → CheckCM Unit
  | [] => pure ()
  | e :: es => do
    let some f := ((Expr.targetPiDomsWithC fvs e.ty).getD [])[i]?
      | throw (.invalid s!"generated recursor: a recorded normal form of {ctor} is too short")
    unless ← targetK53C mode fe p formerTys Mc tele leaf f do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not land at its inductive \
        hypothesis's class at every node of the positivity check (official: invalid recursor)")
    classNodesAgreeC fe p formerTys Mc tele leaf fvs i ctor es

/-- The cached `classFieldsAgree`. -/
def classFieldsAgreeC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) :
    Nat → List ClassField → CheckCM Unit
  | _, [] => pure ()
  | i, .ordinary :: ks => classFieldsAgreeC fe p formerTys Ms fvs ctor E (i + 1) ks
  | i, .recursive t tele :: ks => do
    let (teleB, leaf) ← unwrapOr ((fvs.getD i default).fvarTypeD.stripPis tele)
      (.internal "generated recursor: field telescope")
    unless classLeafAt (Ms.getD t default) leaf do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not end in its inductive \
        hypothesis's class (official: invalid recursor)")
    classNodesAgreeC mode fe p formerTys (Ms.getD t default) teleB leaf fvs i ctor E
    classFieldsAgreeC fe p formerTys Ms fvs ctor E (i + 1) ks

/-- The cached `classCtorOf`. -/
def classCtorOfC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (ctor : ConstantVal × Nat) :
    CheckCM ClassCtor := do
  let E := (Ms.getD c default).nfs.filter (·.ctor == ctor.1.name)
  let e0 ← unwrapOr E.head? (.internal s!"generated recursor: the constructor {ctor.1.name} of a \
    class has no entry in the positivity check's table")
  let (_, ihs) ← classMinorSlot rd c ctor.1.name
  let (fvs, _) ← unwrapOr (openPisAtFvarsC ctor.2 e0.ty (p.nP + p.k))
    (.internal "generated recursor: datum telescope")
  let kinds ← classFieldsOfC p ctor.1.name ihs 0 fvs
  classFieldsAgreeC mode fe p formerTys Ms fvs ctor.1.name E 0 kinds
  let M := Ms.getD c default
  let tyD ← unwrapOr (Expr.instPisWithC M.ds (targetCtorAtC M ctor.1))
    (.internal "generated recursor: constructor parameter telescope")
  pure ⟨ctor.1, ctor.2, kinds, tyD, e0.ty⟩

/-- The cached `classCtorsOf`. -/
def classCtorsOfC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) :
    List (ConstantVal × Nat) → CheckCM (List ClassCtor)
  | [] => pure []
  | ctor :: cs => do
    let x ← classCtorOfC mode fe p formerTys rd Ms c ctor
    let xs ← classCtorsOfC fe p formerTys rd Ms c cs
    pure (x :: xs)

/-- The cached `classesCtors`. -/
def classesCtorsC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) : Nat → List TargetMajor →
    CheckCM (List (List ClassCtor))
  | _, [] => pure []
  | c, M :: rest => do
    let xs ← classCtorsOfC mode fe p formerTys rd Ms c M.ctors
    let xss ← classesCtorsC fe p formerTys rd Ms (c + 1) rest
    pure (xs :: xss)

/-- The cached `classesNfs`. -/
def classesNfsC (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) : List TargetMajor → CheckCM (List TargetMajor)
  | [] => pure []
  | M :: Ms => do
    let es ← targetMajorNfsC mode fe p formerTys M.pfvs M.lvls M.ds M.ctors tbl
    let rest ← classesNfsC fe p formerTys tbl Ms
    pure ({ M with nfs := es } :: rest)

/-- The cached `classFormerTy`. -/
def classFormerTyC (fe : FEnv) (formers : List ConstantVal) (M : TargetMajor) : CheckCM Expr :=
  match M.member with
  | some t => pure (formers.getD t default).type
  | none => match fe.find? M.ind with
    | some (.indInfo cv caps) => do
      let ty ← familyTelescopeC mode fe cv caps
      pure (Expr.instLevelParams cv.levelParams M.lvls ty)
    | _ => throw (.internal "generated recursor: a class's former vanished")

/-! ## The generated types and rules, checked -/

/-- The cached `classConstOk`. -/
def classConstOkC (fe : FEnv) (cv : ConstantVal) : CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.internal s!"generated recursor: loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.internal s!"generated recursor: free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorLC true s!"type of {cv.name}" cv.type)
  let stype ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← ensureSortI (coreKnotI mode false fe checkFuel) 0 stype

/-- The cached `classRecTyCheck`. -/
def classRecTyCheckC (fe : FEnv) (cvRi cvG : ConstantVal) : CheckCM Unit := do
  classConstOkC mode fe cvG
  unless ← (coreKnotI mode false fe checkFuel).defeq 0 cvRi.type cvG.type do
    throw (.invalid s!"generated recursor: the type of {cvG.name} is not the generated one \
      (official: invalid recursor)")

/-- The cached `classRecTyOk`. -/
def classRecTyOkC (fe : FEnv) (g : ClassGen)
    (k : Nat) (rc : RecShape) (cvRi : ConstantVal) (c : Nat) : CheckCM ConstantVal := do
  let ci := g.cls.getD c default
  unless rc.tgt == ci.member.getD k do
    throw (.invalid "generated recursor: the recursor record's member is not its class's")
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    throw (.invalid "generated recursor: the recursor record's rule prefix or major index is \
      not the generated one")
  let gty ← unwrapOr (classGenRecTyC g c) (.internal "generated recursor: recursor type")
  let cvG := { rc.cvR with type := gty }
  classRecTyCheckC mode fe cvRi cvG
  pure cvG

/-- The cached `classRecTysOk`. -/
def classRecTysOkC (fe : FEnv) (g : ClassGen)
    (k : Nat) : List RecShape → List ConstantVal → List Nat → CheckCM (List ConstantVal)
  | rc :: rcs, cvRi :: cvs, c :: cs => do
    let x ← classRecTyOkC mode fe g k rc cvRi c
    let xs ← classRecTysOkC fe g k rcs cvs cs
    pure (x :: xs)
  | [], _, _ => pure []
  | _, _, _ => throw (.internal "generated recursor: recursor list")

/-- The cached `classRuleCheck`: the rule typed at the rule-less
recursors' environment `feR`, a flush entering and leaving it
(`sharedOpsRuleR`'s inference, inline). -/
def classRuleCheckC (feT feR : FEnv) (cvR : ConstantVal) (n : Nat) (gen : Expr) :
    CheckCM Unit := do
  unless gen.looseBVarsBounded 0 && !gen.hasFvar do
    throw (.internal s!"generated recursor: a rule of {cvR.name} is not closed")
  unless Expr.allLevelParamsDefinedC cvR.levelParams gen do
    throw (.internal s!"generated recursor: a rule of {cvR.name} names an undeclared universe \
      parameter")
  unless constsResolveFC feR gen do
    throw (unresolvedConstsErrorLC true s!"generated rule of {cvR.name}" gen)
  -- the flush entering the `feR` half
  flushC
  let _ ← (coreKnotI mode false feR checkFuel).infer 0 gen
  flushC
  let (rbs, _) ← unwrapOr (gen.stripLams n)
    (.internal s!"generated recursor: a rule of {cvR.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  unless rbs.all (fun b => constsResolveFC feT b) do
    throw (unresolvedConstsErrorLC true s!"the domains of a generated rule of {cvR.name}" gen)

/-- The cached `classRulesOk` (the rule returned as generated after its
check: `classRuleOk`). -/
def classRulesOkC (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (c : Nat) : List ClassCtor → CheckCM (List Expr)
  | [] => pure []
  | x :: xs => do
    let gen ← unwrapOr (classGenRuleC g recOf (cvR.levelParams.map .param) c x)
      (.invalid s!"generated recursor: the rule of {x.cv.name} calls a class whose recursor the \
        stream omits (official: unknown constant)")
    classRuleCheckC mode feT feR cvR (g.nP + g.slots.length + x.nF) gen
    let rs ← classRulesOkC feT feR g recOf cvR c xs
    pure (gen :: rs)

/-- The cached `classRecsRulesOk`. -/
def classRecsRulesOkC (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name) :
    List ConstantVal → List Nat → CheckCM (List (ConstantVal × TargetMajor × List Expr))
  | cvG :: cvs, c :: cs => do
    let rhss ← classRulesOkC mode feT feR g recOf cvG c (g.ctors.getD c [])
    let xs ← classRecsRulesOkC feT feR g recOf cvs cs
    pure ((cvG, g.cls.getD c default, rhss) :: xs)
  | _, _ => pure []

/-- The cached `classStreamRecs`. -/
def classStreamRecsC (fe : FEnv) : List RecShape → CheckCM (List ConstantVal)
  | [] => pure []
  | rc :: rcs => do
    checkConstantValC mode fe rc.cvR
    let cvs ← classStreamRecsC fe rcs
    pure (rc.cvR :: cvs)

/-! ## The stage -/

/-- **The cached generated recursor stage**: `genRecCheck` at the
cached core and walks (`genRecCheckC_eq`), the rule-less recursors an
overlay on the constructors' index `fe` (`classFeROvl`), a flush
entering and leaving the rule stage. -/
def genRecCheckC (fe : FEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (block : List ConstantInfo) :
    CheckCM (List (ConstantVal × TargetMajor × List Expr)) := do
  targetRecPins p block
  -- the stream's recursor types, checked: the generated types are compared with them
  let cvRis ← classStreamRecsC mode fe p.recs
  -- the elimination guard
  unless 0 < p.k do
    throw (.invalid "generated recursor: the block declares no family")
  if p.large && !blockLargeElimAllowed p (nestedBit || Ms.any (·.member.isNone)) then
    throw (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
      (official: elim_only_at_universe_zero)")
  let formerTys := p.formers.map (·.type)
  let Ms ← classesNfsC mode fe p formerTys tbl Ms
  -- per class and constructor: the datum, the inductive hypotheses, node agreement
  let ctors ← classesCtorsC mode fe p formerTys rd Ms 0 Ms
  unless (rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum do
    throw (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  -- generation
  let formerTysC ← Ms.mapM (classFormerTyC mode fe p.formers)
  let elim := structElimLevel p.elim p.large
  let g0 : ClassGen := ⟨p.nP, params, Ms, formerTysC, rd.slots, ctors, elim, []⟩
  let pre ← unwrapOr g0.prefixBindersC (.internal "generated recursor: recursor prefix")
  let g := { g0 with pre := pre }
  let cvGs ← classRecTysOkC mode fe g p.k p.recs cvRis rd.recCls
  let feR := classFeROvl p Ms cvGs rd.recCls fe
  flushC
  let out ← classRecsRulesOkC mode fe feR g (classRecOf rd.recCls cvGs) cvGs rd.recCls
  flushC
  pure out

end ConLeche.Cached
