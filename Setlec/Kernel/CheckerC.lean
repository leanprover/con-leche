import Setlec.Kernel.Env
import Setlec.Kernel.TypeChecker
import Setlec.Kernel.TypeCheckerC

/-!
# The executable checker

The cached twin of `Setlec.Kernel.Checker`: identical declaration
checking, running on the memoized checker core (`TypeCheckerC`).  The
pure module remains the specification the verification reasons about;
the planned refinement bridge relates the two (see DESIGN.md).
-/

namespace Setlec

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared
parameters.  Returns the constant with its type **annotated**
(`annotateC`); the guards run on the annotated type. -/
def checkConstantValC (env : Env) (cv : ConstantVal) : CheckM ConstantVal := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← annotateC env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolve env do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← inferTypeC env 0 type
  let _u ← ensureSortC env 0 stype
  pure { cv with type := type }

/-- Build the expected statement of the model's `iota_j` theorem for one
recursor rule (non-indexed, single motive): the rule's λ-telescope,
domains renamed to the `_model` family, closing over
`R._model p⃗ M m⃗ (C._model p⃗ x⃗) = rhs-body`. -/
def buildIotaStmtC (f : Name → Name) (recName ctorName : Name)
    (recLPs ctorLPs : List Name) (nP nM nm nF : Nat)
    (recTy ctorTy : Expr) (ruleRhs : Expr) : Option Expr := do
  let (binders, body) ← ruleRhs.stripLams (nP + nM + nm + nF)
  -- binder infos follow the recursor's telescope (then the
  -- constructor's fields), not the rule's λs
  let bisR ← recTy.piBinderInfos (nP + nM + nm)
  let bisC ← ctorTy.piBinderInfos (nP + nF)
  let bis := bisR ++ bisC.drop nP
  let binders := (binders.zip bis).map fun (b, bi) => (b.1, b.2.1, bi)
  let (_, mdom, _) ← binders[nP]?
  let ℓ ← mdom.resultSort
  let depth := nP + nM + nm + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let mmArgs := (List.range (nM + nm)).map fun k =>
    Expr.bvar (depth - 1 - nP - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let ctorApp := Expr.mkAppN (.const (f ctorName) (ctorLPs.map .param))
    (pArgs ++ xArgs)
  let lhs := Expr.mkAppN (.const (f recName) (recLPs.map .param))
    (pArgs ++ mmArgs ++ [ctorApp])
  let motiveBVar := Expr.bvar (nF + nm + (nM - 1))
  let α := Expr.app motiveBVar ctorApp
  let rhs := body.renameConsts f
  let eqApp := Expr.mkAppN (.const eqName [ℓ]) [α, lhs, rhs]
  pure (binders.foldr
    (fun (b : Name × Expr × BinderInfo) acc =>
      .forallE b.1 (b.2.1.renameConsts f) acc ⟨b.2.2, none⟩) eqApp)

/-- Compare binder domains at offsets `o₁`/`o₂` for `n` positions, the
right side viewed through `g` (identity, lifting, or renaming). -/
def domsMatchAuxC (g : Nat → Expr → Expr)
    (bs₁ bs₂ : List (Name × Expr × BinderMeta)) (o₁ o₂ n : Nat) : Bool :=
  (List.range n).all fun i =>
    match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
    | some b₁, some b₂ => b₁.2.1 == g i b₂.2.1
    | _, _ => false

/-- Check a modeled recursor's rules against the model's `iota`
theorems (the loop of `checkIndDeclC`'s recursor arm, lifted for
verification). -/
def checkIotaRulesC (env' envSelf : Env) (f : Name → Name)
    (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm : Nat) : Nat → List RecRule → CheckM (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let some (.ctorInfo cvj cnP cnF) := env'.find? r.ctor
      | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
    unless cnP = nP do
      throw (.notImplemented "constructor/recursor parameter mismatch")
    unless r.nfields = cnF do
      throw (.invalid "rule field count mismatch")
    unless r.rhs.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in rule of {cvName}")
    if r.rhs.hasFvar then
      throw (.invalid s!"free variable in rule of {cvName}")
    let rhsA ← annotateC envSelf 0 r.rhs
    unless rhsA.allLevelParamsDefined lps do
      throw (.invalid s!"undeclared universe parameter in rule of {cvName}")
    unless rhsA.constsResolve envSelf do
      throw (.invalid s!"unknown constant in rule of {cvName}")
    -- the rule's λ-domains pin down what the model's iota
    -- theorem quantifies over; they must match the recursor
    -- type's domains (prefix) and the constructor type's field
    -- domains (lifted past motive and minors) — the same
    -- telescopes the iota certificates certify the spines
    -- against
    let some (rbinders, rbody) := rhsA.stripLams (nP + nM + nm + cnF)
      | throw (.notImplemented s!"rule of {cvName} is not a lambda telescope")
    let some (tbinders, _) := tyA.stripPis (nP + nM + nm + 1)
      | throw (.notImplemented s!"type of {cvName} is not a pi telescope")
    let some (cbinders, _) := cvj.type.stripPis (cnP + cnF)
      | throw (.notImplemented s!"type of {r.ctor} is not a pi telescope")
    unless domsMatchAuxC (fun _ e => e) rbinders tbinders 0 0
        (nP + nM + nm) do
      throw (.notImplemented s!"rule domain mismatch with recursor type for {cvName}")
    unless domsMatchAuxC (fun i e => e.liftLooseBVars (nM + nm) i)
        rbinders cbinders (nP + nM + nm) cnP cnF do
      throw (.notImplemented s!"rule field domain mismatch with constructor type for {cvName}")
    -- infer the rule's type: soundness interprets the (λ-tower)
    -- right-hand side through this inference
    let _rhsTy ← inferTypeC envSelf 0 rhsA
    let some stmtRaw := buildIotaStmtC f cvName r.ctor
        lps cvj.levelParams nP nM nm cnF
        tyA cvj.type r.rhs
      | throw (.notImplemented "iota statement construction")
    let stmtA ← annotateC env' 0 stmtRaw
    let thmName := (cvName.str "_model").str s!"iota_{j}"
    let some (.thmInfo cvt _) := env'.find? thmName
      | throw (.notImplemented s!"missing iota theorem {thmName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch {thmName}")
    unless cvt.type == stmtA do
      throw (.notImplemented s!"iota statement mismatch for {thmName}")
    -- the theorem's telescope domains and equation body are
    -- additionally pinned to the rule's annotated data: soundness
    -- walks the statement with exactly these facts
    let some (sbinders, sbody) := cvt.type.stripPis (nP + nM + nm + cnF)
      | throw (.notImplemented
          s!"iota statement of {thmName} is not a pi telescope")
    unless domsMatchAuxC (fun _ e => e.renameConsts f) sbinders rbinders
        0 0 (nP + nM + nm + cnF) do
      throw (.notImplemented
        s!"iota statement domain mismatch for {thmName}")
    let some (_, mdomA, _) := rbinders[nP]?
      | throw (.notImplemented "iota statement motive")
    let some ℓA := mdomA.resultSort
      | throw (.notImplemented "iota statement motive sort")
    let depthS := nP + nM + nm + cnF
    let pArgsS := (List.range nP).map fun k => Expr.bvar (depthS - 1 - k)
    let mmArgsS := (List.range (nM + nm)).map fun k =>
      Expr.bvar (depthS - 1 - nP - k)
    let xArgsS := (List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)
    let ctorAppS := Expr.mkAppN
      (.const (f r.ctor) (cvj.levelParams.map .param)) (pArgsS ++ xArgsS)
    let lhsS := Expr.mkAppN
      (.const (f cvName) (lps.map .param))
      (pArgsS ++ mmArgsS ++ [ctorAppS])
    let motiveBVarS := Expr.bvar (cnF + nm + (nM - 1))
    unless sbody == Expr.mkAppN (.const eqName [ℓA])
        [.app motiveBVarS ctorAppS, lhsS, rbody.renameConsts f] do
      throw (.notImplemented
        s!"iota statement body mismatch for {thmName}")
    let rest' ← checkIotaRulesC env' envSelf f cvName lps tyA nP nM nm
      (j + 1) rest
    pure ({ r with rhs := rhsA } :: rest')

/-- Check and install one member of a modeled inductive block against
its `_model` counterpart (the step of `checkIndDeclC`'s fold, lifted
for verification).  `caps` is the capability record the block earned
(recorded on the inductive type former). -/
def checkIndMemberC (blockNames : List Name) (caps : IndCaps) (env' : Env)
    (ci : ConstantInfo) : CheckM Env := do
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  let cvA ← checkConstantValC env' ci.toConstantVal
  -- a member may not itself be shaped like a model companion, so the
  -- block renaming can never map onto a member
  if cvA.name.isModelSuffix then
    throw (.invalid s!"model-shaped member name {cvA.name}")
  -- the model counterpart
  let some (.defnInfo cvm _mval) := env'.find? (cvA.name.str "_model")
    | throw (.notImplemented s!"missing model for {cvA.name}")
  unless cvm.levelParams = cvA.levelParams do
    throw (.notImplemented s!"model level parameters mismatch for {cvA.name}")
  unless (cvA.type.renameConsts f) == cvm.type do
    throw (.notImplemented s!"model type mismatch for {cvA.name}")
  match ci with
  | .indInfo _ _ => pure (⟨.indInfo cvA caps :: env'.consts⟩ : Env)
  | .ctorInfo _ nP nF => pure ⟨.ctorInfo cvA nP nF :: env'.consts⟩
  | .recInfo _ nP nM nm ni rules => do
    unless ni = 0 do throw (.notImplemented "indexed recursor")
    unless nM = 1 do throw (.notImplemented "multiple motives")
    -- the recursor comes last: with every other member installed the
    -- block renaming is exactly "installed members and the recursor"
    unless blockNames.all (fun n =>
        n == cvA.name || (env'.find? n).isSome) do
      throw (.notImplemented "recursor before other block members")
    -- iota statements are equations: pin the pinned equality former
    unless env'.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    -- provisional self with *no* rules: rule right-hand sides may
    -- mention the recursor, but nothing during their annotation may
    -- depend on its (yet unchecked) rules
    let envSelf : Env := ⟨.recInfo cvA nP nM nm ni [] :: env'.consts⟩
    let rules' ← checkIotaRulesC env' envSelf f cvA.name cvA.levelParams cvA.type nP nM nm 0 rules
    pure ⟨.recInfo cvA nP nM nm ni rules' :: env'.consts⟩
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Rename a model-side projection type back to public names. -/
def projBackC (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T.str "_model" then T
  else if n = ctor.str "_model" then ctor
  else
    match (List.range nF).find? (fun j => n == projModelName T j) with
    | some j => projFnName T j
    | none => n

/-- The forward (public → model) map on the projection family. -/
def projFwdC (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T then T.str "_model"
  else if n = ctor then ctor.str "_model"
  else
    match (List.range nF).find? (fun j => n == projFnName T j) with
    | some j => projModelName T j
    | none => n

/-- Stage 1 of `checkProjFnC`: the stored constants the projection
depends on — the single constructor (arity-matched), the model's
`proj_i` definition (level-matched), the parent type, and the pinned
equality former; the projection's own name must be free. -/
def checkProjLookupsC (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckM (ConstantVal × ConstantVal) := do
  let some (.ctorInfo cvj cnP cnF) := env'.find? ctorName
    | throw (.notImplemented "projection constructor not stored")
  unless cnP = nP ∧ cnF = nF do
    throw (.notImplemented "projection constructor arity mismatch")
  let some (.defnInfo mcv _) := env'.find? (projModelName T i)
    | throw (.notImplemented "missing projection model")
  unless mcv.levelParams = lps do
    throw (.notImplemented "projection model level mismatch")
  unless (env'.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  unless (env'.find? T).isSome do
    throw (.notImplemented "projection parent not stored")
  unless env'.find? eqName = some eqA do
    throw (.notImplemented "projection iota requires the pinned Eq basis")
  pure (cvj, mcv)

/-- Stage 2: the public projection type — the model's, renamed back
(pinned by the renaming roundtrip), well-formed and parameter-led. -/
def checkProjTyC (env' : Env) (T ctorName : Name) (lps : List Name)
    (mty : Expr) (nP nF : Nat) : CheckM Expr := do
  let pty := mty.renameConsts (projBackC T ctorName nF)
  unless (pty.renameConsts (projFwdC T ctorName nF)) == mty do
    throw (.notImplemented "projection type roundtrip")
  unless pty.constsResolve env' do
    throw (.notImplemented "projection type resolution")
  unless pty.looseBVarsBounded 0 && !pty.hasFvar &&
      pty.allLevelParamsDefined lps do
    throw (.notImplemented "projection type wellformedness")
  unless (pty.stripPis (nP + 1)).isSome do
    throw (.notImplemented "projection type telescope")
  pure pty

/-- Stage 3: the reduction rule — λ over the constructor telescope
returning field `i`, annotated; its λ-domains stay the constructor's. -/
def checkProjRuleC (env' : Env) (cvj : ConstantVal) (lps : List Name)
    (nP nF i : Nat) : CheckM Expr := do
  let some rhs := Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i))
    | throw (.notImplemented "projection rule telescope")
  unless !rhs.hasFvar && rhs.looseBVarsBounded 0 do
    throw (.notImplemented "projection rule scoping")
  let rhsA ← annotateC env' 0 rhs
  unless rhsA.allLevelParamsDefined lps && rhsA.constsResolve env' &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "projection rule wellformedness")
  let some (rbinders, rrbody) := rhsA.stripLams (nP + nF)
    | throw (.notImplemented "projection rule telescope")
  unless rrbody == Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection rule body")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAuxC (fun _ e => e) rbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  pure rhsA

/-- Stage 4: the model's `proj_i.iota` theorem pins the rule — the
statement's telescope domains are the constructor's (renamed to the
model side) and its body equates the projected constructor spine with
field `i`.  The equality's type slot needs no pin (the collapse
ignores it). -/
def checkProjIotaC (env' : Env) (T ctorName : Name) (lps : List Name)
    (cvj : ConstantVal) (nP nF i : Nat) : CheckM Unit := do
  let some (.thmInfo tcv _) := env'.find? ((projModelName T i).str "iota")
    | throw (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    throw (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) := tcv.type.stripPis (nP + nF)
    | throw (.notImplemented "projection iota telescope")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAuxC
      (fun _ e => e.renameConsts (projFwdC T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection iota domain mismatch")
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let mkSpine := Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param))
    (pArgs ++ xArgs)
  let lhsS := Expr.mkAppN
    (.const (projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
    unless c = eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")

/-- Check and install the public projection function for field `i` of
a modeled single-constructor structure, against the model's
`T._model.proj_i` definition and its `iota` theorem.  The function is
stored as a degenerate recursor (no motive, no minors) carrying one
rule, so the generic iota machinery reduces it. -/
def checkProjFnC (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckM Env := do
  let (cvj, mcv) ← checkProjLookupsC env' T ctorName lps nP nF i
  let pty ← checkProjTyC env' T ctorName lps mcv.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleC env' cvj lps nP nF i
  checkProjIotaC env' T ctorName lps cvj nP nF i
  pure ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
    [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩

/-- Does the model document structural eta for this single-constructor
block — a `T._model.eta` theorem with the pinned statement
`∀ p⃗ (x : T._model p⃗), x = C._model p⃗ (T._model.proj_0 p⃗ x) …`?
Checked before install; a positive answer records the eta capability
on the stored inductive.  (`Bool`-valued: an absent or differently
shaped artifact just means no capability.)  The parameter telescope is
pinned against the constructor *model*'s (both live on the model side
and are annotated by the same pipeline), and the equality's type slot
is not pinned (the collapse ignores it). -/
def checkEtaThmC (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "eta"),
      env'.find? (T.str "_model"),
      env'.find? (ctorName.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _),
      some (.defnInfo cvmC _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps && cvmC.levelParams == lps &&
    -- the projection models exist at the family's level parameters
    (List.range nF).all (fun j =>
      match env'.find? (projModelName T j) with
      | some (.defnInfo cvmj _) => cvmj.levelParams == lps
      | _ => false) &&
    (match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAuxC (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 0 &&
          rhsC == Expr.mkAppN
            (.const (ctorName.str "_model") (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (lps.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0]))
        | _ => false)
     | _, _ => false)
  | _, _, _, _ => false

/-- Does the model document unit-likeness for this block — a
`T._model.unitlike` theorem with the pinned statement
`∀ p⃗ (x y : T._model p⃗), x = y`?  Checked before install; a positive
answer records the unit-like capability on the stored inductive. -/
def checkUnitThmC (env' : Env) (T : Name) (lps : List Name)
    (nP : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "unitlike"),
      env'.find? (T.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps &&
    (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAuxC (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbinders[nP + 1]? with
        | some (_, ydom, _) =>
          ydom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0
        | _ => false)
     | _, _ => false)
  | _, _, _ => false

/-- The result sort of a syntactic pi telescope (the sort the type
former's type ends in), if it ends in a sort at all. -/
def piResultSortC (e : Expr) : Option Level :=
  match e.piResult with
  | .sort u => some u
  | _ => none

/-- Check and install a modeled inductive block: every member is
checked against its `_model` counterpart (type up to the public↔model
renaming, iota rules against the model's `iota_j` theorems), then
stored as a real inductive-kind constant.  Single-constructor blocks
determine their capability record first (recorded on the inductive)
and additionally install the projection functions the model documents
(skipped where the artifacts are absent).  The K flag is computed from
shape exactly as the official kernel does — an inductive proposition
with a single constructor taking only the parameters; the reduction
site carries the semantic load (proof irrelevance), so no model
theorem backs the flag. -/
def checkIndDeclC (env : Env) (block : List ConstantInfo) : CheckM Env := do
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps : IndCaps :=
      { eta := cvC.levelParams = cvT.levelParams &&
          checkEtaThmC env cvT.name cvC.name cvT.levelParams nP nF,
        etaCtor := cvC.name, etaParams := nP, etaFields := nF,
        unitlike := checkUnitThmC env cvT.name cvT.levelParams nP,
        unitParams := nP,
        ruleK := nF == 0 && piResultIsProp cvT.type }
    let env₂ ← block.foldlM
      (checkIndMemberC (block.map (·.name)) caps) env
    -- the whole projection name family must be ours to install
    unless (List.range nF).all
        (fun j => (env₂.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    (List.range nF).foldlM (fun e i =>
      if (e.find? (projModelName cvT.name i)).isSome then
        checkProjFnC e cvT.name cvC.name cvT.levelParams nP nF i
      else pure e) env₂
  | _, _ =>
    block.foldlM (checkIndMemberC (block.map (·.name)) {}) env

/-- Check a single declaration, extending the environment on success. -/
def checkDeclC (env : Env) (d : Declaration) : CheckM Env := do
  match d with
  | .defnDecl cv value =>
    let cv ← checkConstantValC env cv
    unless value.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    let value ← annotateC env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferTypeC env 0 value
    unless ← isDefEqC env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in definition {cv.name}")
    pure ⟨.defnInfo cv value :: env.consts⟩
  | .thmDecl cv value =>
    let cv ← checkConstantValC env cv
    -- the type of a theorem must be a proposition
    let stype ← inferTypeC env 0 cv.type
    let u ← ensureSortC env 0 stype
    unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
      throw (.invalid s!"type of theorem {cv.name} is not a proposition")
    unless value.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    let value ← annotateC env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferTypeC env 0 value
    unless ← isDefEqC env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in theorem {cv.name}")
    pure ⟨.thmInfo cv value :: env.consts⟩
  | .axiomDecl cv => throw (.notImplemented s!"axiom declaration ({cv.name})")
  | .basisDecl kind =>
    -- Install the pinned (pre-annotated) basis block; the frontend has
    -- already matched the incoming record against the pinned shapes.
    kind.declsA.foldlM (fun env ci => do
      unless (env.find? ci.name).isNone do
        throw (.invalid s!"duplicate declaration {ci.name}")
      pure (⟨ci :: env.consts⟩ : Env)) env
  | .indDecl block => checkIndDeclC env block

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDeclsC (ds : List Declaration) : CheckM Env :=
  ds.foldlM checkDeclC Env.empty

end Setlec
