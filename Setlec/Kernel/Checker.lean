import Setlec.Kernel.Env
import Setlec.Kernel.StdAxioms
import Setlec.Kernel.TypeChecker
import Setlec.Kernel.TypeCheckerC

/-!
# The checker

`checkDecl` checks one declaration against the current environment and, on
success, returns the extended environment.  `checkDecls` folds it over a list
of declarations, starting from the empty environment.

Currently supported: `def` declarations in the sort fragment.  Axioms and
theorems are declined.  Verification: `Setlec.Verify.Checker` and
`Setlec.Model.Consistency`.
-/

namespace Setlec

/-- The core entry points the declaration checker runs on: the checker
is written once against this record, monad-polymorphically, and
instantiated with the pure knot (`fueledOps`/`pureOps`, the
verification's subject) and with the memoized knot (`cachedOps`, what
the binary executes). -/
structure CheckerOps (m : Type → Type) where
  annotate : Env → Nat → Expr → m Expr
  inferType : Env → Nat → Expr → m Expr
  isDefEq : Env → Nat → Expr → Expr → m Bool
  ensureSort : Env → Nat → Expr → m Level
  whnf : Env → Nat → Expr → m Expr

/-- The pure instantiation, at an arbitrary fuel. -/
def fueledOps (F : Nat) : CheckerOps CheckM where
  annotate env d e := annotateCore env F d e
  inferType env d e := inferTypeCore env F d e
  isDefEq env d a b := isDefEqCore env F d a b
  ensureSort env d e := ensureSortCore env F d e
  whnf env d e := Setlec.whnf env F d e

/-- The pure instantiation, at the standard fuel. -/
def pureOps : CheckerOps CheckM := fueledOps checkFuel

/-- The memoized instantiation, at the standard fuel; each call starts
from a fresh cache (the environment differs between calls). -/
def cachedOps : CheckerOps CheckM where
  annotate env d e := ((cachedFns env checkFuel).annotate d e).run' {}
  inferType env d e := ((cachedFns env checkFuel).infer d e).run' {}
  isDefEq env d a b := ((cachedFns env checkFuel).defeq d a b).run' {}
  ensureSort env d e :=
    (ensureSort (cachedFns env checkFuel) env d e).run' {}
  whnf env d e := ((cachedFns env checkFuel).whnf d e).run' {}

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared
parameters.  Returns the constant with its type **annotated**
(`annotate`); the guards run on the annotated type. -/
def checkConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) : m ConstantVal := do
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
  let type ← ops.annotate env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolve env do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← ops.inferType env 0 type
  let _u ← ops.ensureSort env 0 stype
  pure { cv with type := type }

/-- Compare binder domains at offsets `o₁`/`o₂` for `n` positions, the
right side viewed through `g` (identity, lifting, or renaming). -/
def domsMatchAux (g : Nat → Expr → Expr)
    (bs₁ bs₂ : List (Name × Expr × BinderMeta)) (o₁ o₂ n : Nat) : Bool :=
  (List.range n).all fun i =>
    match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
    | some b₁, some b₂ => b₁.2.1 == g i b₂.2.1
    | _, _ => false

/-- Open the first `n` `∀`-binders at fresh free variables `0..n-1`
(each fvar's type is the binder domain, instantiated with the earlier
fvars).  Returns the fvars and the opened body. -/
def openPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e)
  | n + 1, .forallE nm dom body _, i =>
    let fv : Expr := .fvar i nm dom
    match openPisAtFvars n (body.instantiate1 fv) (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none

/-- Is the expression the pinned equality former at one level? -/
def isEqHead : Expr → Bool
  | .const c [_ℓ] => c == eqName
  | _ => false

/-- Pairwise definitional-equality check of two spines (throws on any
mismatch, including a length difference). -/
def checkDefEqList (ops : CheckerOps m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Unit
  | [], [] => pure ()
  | a :: as, b :: bs => do
    unless ← ops.isDefEq env depth a b do
      throw (.notImplemented "iota statement component mismatch")
    checkDefEqList ops env depth as bs
  | _, _ => throw (.notImplemented "iota statement component arity")

/-- Check a *canonical* recursor rule's `iota_j` theorem,
*semantically*: the stored theorem's telescope is opened at free
variables, its body must be an `Eq`, the equation's left side is
structurally the renamed recursor applied to the opened variables and
a canonical major (its index arguments definitionally the
constructor's canonical index tuple), and the right side is
definitionally the rule's applied right-hand side.  The opened
telescope's domains are definitionally the recursor's prefix and the
constructor's field domains (renamed), and the rule's own λ-domains
definitionally the public ones — the memberships the fold fact
quantifies over transfer along these equalities.  Definitional
comparison makes the checks insensitive to hygienic binder names and
reducible wrappers (`optParam` etc.) in the stored types. -/
def checkIotaThm (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m Unit := do
    let some (.thmInfo cvt _) :=
        env'.find? ((cvName.str "_model").str s!"iota_{j}")
      | throw (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    -- open the theorem's telescope: params, motives, minors, fields
    let depth := nP + nM + nm + cnF
    let some (fvs, tbody) := openPisAtFvars depth cvt.type 0
      | throw (.notImplemented s!"iota statement shape mismatch for {cvName}")
    -- the body is an equation (at one level, like the pinned `Eq`)
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    -- the equation's left side: structurally the renamed recursor
    -- applied to the opened prefix variables, `ni` index arguments
    -- (checked below against the constructor's canonical tuple),
    -- and the constructor at its own level parameters applied to
    -- the leading parameter variables and the field variables
    let xFvs := fvs.drop (nP + nM + nm)
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = nP + nM + nm + ni + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take (nP + nM + nm) == fvs.take (nP + nM + nm) do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    unless major == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    -- the constructor's telescope (renamed), instantiated at the
    -- major's arguments: field domains and the canonical index tuple
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let some (cdoms, cres) :=
        Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f)
      | throw (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + ni do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops envSelf depth ((largs.drop (nP + nM + nm)).take ni)
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops envSelf depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    -- the statement's prefix domains are the recursor's (renamed)
    let some (rdoms, _) :=
        Expr.instPisAt (fvs.take (nP + nM + nm)) (tyA.renameConsts f)
      | throw (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops envSelf depth
      ((fvs.take (nP + nM + nm)).map Expr.fvarTypeD) rdoms
    -- the rule's λ-domains are the public recursor prefix and
    -- constructor field domains (the fold fact's value spines fit
    -- the public telescopes; these equalities let them fit the λs)
    let some (fvsP, _) := openPisAtFvars (nP + nM + nm) tyA 0
      | throw (.notImplemented s!"iota recursor telescope for {cvName}")
    let some (_, crestP) := Expr.instPisAt (fvsP.take cnP) cvj.type
      | throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let some (xFvsP, _) := openPisAtFvars cnF crestP (nP + nM + nm)
      | throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let some (ldoms, _) := Expr.instLamsAt (fvsP ++ xFvsP) rhsA
      | throw (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops envSelf depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    -- the right side: definitionally the rule's applied rhs
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq envSelf depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")

/-- Check one modeled recursor rule: generic well-formedness of the
right-hand side, then — for canonical rules — the model's `iota_j`
theorem (`checkIotaThm`).  A rule that is not canonical
(`Expr.recRulePlain`; nested auxiliary constructors) is stored *inert*
after the well-formedness checks: `iotaRec` never fires on it, so no
model theorem is consulted. -/
def checkIotaRule (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni j : Nat) (r : RecRule) : m RecRule := do
    let some (.ctorInfo cvj cnP cnF) := env'.find? r.ctor
      | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
    unless r.nfields = cnF do
      throw (.invalid "rule field count mismatch")
    unless r.rhs.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in rule of {cvName}")
    if r.rhs.hasFvar then
      throw (.invalid s!"free variable in rule of {cvName}")
    let rhsA ← ops.annotate envSelf 0 r.rhs
    unless rhsA.allLevelParamsDefined lps do
      throw (.invalid s!"undeclared universe parameter in rule of {cvName}")
    unless rhsA.constsResolve envSelf do
      throw (.invalid s!"unknown constant in rule of {cvName}")
    -- the rule's rhs must be a λ-telescope over the recursor prefix
    -- and the constructor fields (so it can be applied positionally)
    unless (rhsA.stripLams (nP + nM + nm + cnF)).isSome do
      throw (.notImplemented s!"rule shape mismatch for {cvName}")
    -- infer the rule's type: soundness interprets the (λ-tower)
    -- right-hand side through this inference
    let _rhsTy ← ops.inferType envSelf 0 rhsA
    if Expr.recRulePlain tyA nP nM nm ni cnP then
      checkIotaThm ops env' envSelf f cvName lps tyA nP nM nm ni j r
        cvj cnP cnF rhsA
    pure { r with rhs := rhsA }

/-- The per-rule check, folded over a modeled recursor's rules. -/
def checkIotaRules (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name)
    (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni : Nat) : Nat → List RecRule → m (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRule ops env' envSelf f cvName lps tyA nP nM nm ni j r
    let rest' ← checkIotaRules ops env' envSelf f cvName lps tyA nP nM nm ni
      (j + 1) rest
    pure (r' :: rest')

/-- Check a block member's constant against its `_model` counterpart:
`checkConstantVal`, the member may not itself be model-shaped, and its
type is the model's under the block renaming. -/
def checkMemberVal (ops : CheckerOps m) (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) : m ConstantVal := do
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  let cvA ← checkConstantVal ops env' cv
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
  pure cvA

/-- Check and install one non-recursor member of a modeled inductive
block against its `_model` counterpart (the step of `checkIndDecl`'s
fold, lifted for verification).  `caps` is the capability record the
block earned (recorded on the inductive type former).  Recursors are
handled by `checkIndRecs`. -/
def checkIndMember (ops : CheckerOps m) (blockNames : List Name)
    (caps : IndCaps) (env' : Env) (ci : ConstantInfo) : m Env := do
  let cvA ← checkMemberVal ops blockNames env' ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (⟨.indInfo cvA caps :: env'.consts⟩ : Env)
  | .ctorInfo _ nP nF => pure ⟨.ctorInfo cvA nP nF :: env'.consts⟩
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group: check each recursor's constant and
provision it *rule-less* on top of the previous ones.  Returns the
fully provisioned environment together with the checked constants (in
order).  Rule right-hand sides may mention any recursor of the block
(mutual and nested blocks), so they are annotated only against the
fully provisioned environment. -/
def provisionRecs (ops : CheckerOps m) (blockNames : List Name) :
    Env → List ConstantInfo →
    m (Env × List (ConstantVal × Nat × Nat × Nat × Nat × List RecRule))
  | envAcc, [] => pure (envAcc, [])
  | envAcc, ci :: rest =>
    match ci with
    | .recInfo _ nP nM nm ni rules => do
      let cvA ← checkMemberVal ops blockNames envAcc ci.toConstantVal
      let (envSelf, others) ← provisionRecs ops blockNames
        ⟨.recInfo cvA nP nM nm ni [] :: envAcc.consts⟩ rest
      pure (envSelf, (cvA, nP, nM, nm, ni, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- Check and install a block's recursors *as a group*: every rule
right-hand side may mention any of them, so all are provisioned
rule-less together (`envSelf`) and installed together — no
intermediate environment stores a recursor whose rules mention a
missing sibling. -/
def checkIndRecs (ops : CheckerOps m) (blockNames : List Name)
    (env₂ : Env) (recs : List ConstantInfo) : m Env := do
  if recs.isEmpty then
    pure env₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    -- iota statements are equations: pin the pinned equality former
    unless env₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (envSelf, checked) ← provisionRecs ops blockNames env₂ recs
    checked.foldlM (fun (acc : Env) c => do
        let rules' ← checkIotaRules ops env₂ envSelf f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1
          0 c.2.2.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1
          rules' :: acc.consts⟩ : Env))
      env₂

/-- Rename a model-side projection type back to public names. -/
def projBack (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T.str "_model" then T
  else if n = ctor.str "_model" then ctor
  else
    match (List.range nF).find? (fun j => n == projModelName T j) with
    | some j => projFnName T j
    | none => n

/-- The forward (public → model) map on the projection family. -/
def projFwd (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T then T.str "_model"
  else if n = ctor then ctor.str "_model"
  else
    match (List.range nF).find? (fun j => n == projFnName T j) with
    | some j => projModelName T j
    | none => n

/-- Stage 1 of `checkProjFn`: the stored constants the projection
depends on — the single constructor (arity-matched), the model's
`proj_i` definition (level-matched), the parent type, and the pinned
equality former; the projection's own name must be free. -/
def checkProjLookups (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m (ConstantVal × ConstantVal) := do
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
def checkProjTy (env' : Env) (T ctorName : Name) (lps : List Name)
    (mty : Expr) (nP nF : Nat) : m Expr := do
  let pty := mty.renameConsts (projBack T ctorName nF)
  unless (pty.renameConsts (projFwd T ctorName nF)) == mty do
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
def checkProjRule (ops : CheckerOps m) (env' : Env) (cvj : ConstantVal) (lps : List Name)
    (nP nF i : Nat) : m Expr := do
  let some rhs := Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i))
    | throw (.notImplemented "projection rule telescope")
  unless !rhs.hasFvar && rhs.looseBVarsBounded 0 do
    throw (.notImplemented "projection rule scoping")
  let rhsA ← ops.annotate env' 0 rhs
  unless rhsA.allLevelParamsDefined lps && rhsA.constsResolve env' &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "projection rule wellformedness")
  let some (rbinders, rrbody) := rhsA.stripLams (nP + nF)
    | throw (.notImplemented "projection rule telescope")
  unless rrbody == Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection rule body")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  pure rhsA

/-- Stage 4: the model's `proj_i.iota` theorem pins the rule — the
statement's telescope domains are the constructor's (renamed to the
model side) and its body equates the projected constructor spine with
field `i`.  The equality's type slot needs no pin (the collapse
ignores it). -/
def checkProjIota (env' : Env) (T ctorName : Name) (lps : List Name)
    (cvj : ConstantVal) (nP nF i : Nat) : m Unit := do
  let some (.thmInfo tcv _) := env'.find? ((projModelName T i).str "iota")
    | throw (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    throw (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) := tcv.type.stripPis (nP + nF)
    | throw (.notImplemented "projection iota telescope")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
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
def checkProjFn (ops : CheckerOps m) (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m Env := do
  let (cvj, mcv) ← checkProjLookups env' T ctorName lps nP nF i
  let pty ← checkProjTy env' T ctorName lps mcv.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRule ops env' cvj lps nP nF i
  checkProjIota env' T ctorName lps cvj nP nF i
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
def checkEtaThm (env' : Env) (T ctorName : Name) (lps : List Name)
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
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
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
def checkUnitThm (env' : Env) (T : Name) (lps : List Name)
    (nP : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "unitlike"),
      env'.find? (T.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps &&
    (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
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
def piResultSort (e : Expr) : Option Level :=
  match e.piResult with
  | .sort u => some u
  | _ => none

/-- One projection-function install step (skipped where the model's
projection artifact is absent). -/
def installProjFnStep (ops : CheckerOps m) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) : m Env :=
  if (e.find? (projModelName T i)).isSome then
    checkProjFn ops e T ctorName lps nP nF i
  else pure e

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env := do
  unless (env.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env)

/-- The capabilities recorded for a single-constructor modeled block. -/
def indBlockCaps (env : Env) (cvT cvC : ConstantVal) (nP nF : Nat) :
    IndCaps where
  eta := (cvC.levelParams = cvT.levelParams) &&
    checkEtaThm env cvT.name cvC.name cvT.levelParams nP nF
  etaCtor := cvC.name
  etaParams := nP
  etaFields := nF
  unitlike := checkUnitThm env cvT.name cvT.levelParams nP
  unitParams := nP
  ruleK := nF == 0 && piResultIsProp cvT.type

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
def checkIndDecl (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) : m Env := do
  -- the recursors must form a suffix of the block: their rules may
  -- mention each other, so they install as a group after everything
  -- else
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ _ _ => false | _ => true)
  unless block = nonrecs ++ recs do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCaps env cvT cvC nP nF)
    let env₂ ← nonrecs.foldlM
      (checkIndMember ops blockNames caps) env
    let env₃ ← checkIndRecs ops blockNames env₂ recs
    -- the whole projection name family must be ours to install
    unless (List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    (List.range nF).foldlM
      (installProjFnStep ops cvT.name cvC.name cvT.levelParams nP nF) env₃
  | _, _ => do
    let env₂ ← nonrecs.foldlM (checkIndMember ops blockNames {}) env
    checkIndRecs ops blockNames env₂ recs

/-- Check a `def` declaration's value against its checked constant. -/
def checkDefnVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure ⟨.defnInfo cv value :: env.consts⟩

/-- Check a `theorem` declaration's value against its checked constant
(whose type must additionally be a proposition). -/
def checkThmVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  -- the type of a theorem must be a proposition
  let stype ← ops.inferType env 0 cv.type
  let u ← ops.ensureSort env 0 stype
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid s!"type of theorem {cv.name} is not a proposition")
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure ⟨.thmInfo cv value :: env.consts⟩

/-- Check an `opaque` declaration's value against its checked
constant: exactly the theorem check without the is-a-proposition
requirement.  The result is stored as a `thmInfo` — "checked value,
never delta-unfolded" is precisely opaque semantics. -/
def checkOpaqueVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure ⟨.thmInfo cv value :: env.consts⟩
/-- Certify a list of recurrence equations by definitional equality
(at depth 2: the equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (ops : CheckerOps m) (env : Env) :
    List (Expr × Expr) → m Bool
  | [] => pure true
  | eq :: rest => do
    if ← ops.isDefEq env 2 eq.1 eq.2 then
      certifyNatEqs ops env rest
    else pure false

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : CheckerOps m) (env : Env) (d : Declaration) : m Env := do
  match d with
  | .defnDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value
    -- Structural-Nat pins: the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked
    -- by definitional equality here, once, so the literal fast path's
    -- reduction-time certification never fails on an accepted
    -- environment.  A nonstandard definition under one of these names
    -- is positively unsupported.  The equations are certified in the
    -- *pre-insertion* environment with the operation's self-references
    -- replaced by its stored value (see `Setlec/Kernel/Core.lean`:
    -- certifying after insertion would let the operation's own fast
    -- path discharge its all-literal equations vacuously), and the
    -- operation's and its dependencies' stored types are pinned.
    if natOpNames.contains cv.name then
      unless natOpGuard env2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match env2.find? cv.name with
      | some (.defnInfo _ value') =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal s!"structural Nat operation not stored ({cv.name})")
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkOpaqueVal ops env cv value
  | .axiomDecl cv => do
    -- Only the two standard axioms the preprocessor's generated routes
    -- use are accepted, with their types and the shapes of the
    -- inductives they quantify over pinned (up to the exporter's
    -- unstable hygienic binder names); both are true in the set model
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice).
    let cvA ← checkConstantVal ops env cv
    if stdAxiomOk env cvA then
      pure ⟨.axiomInfo cvA :: env.consts⟩
    else
      throw (.notImplemented s!"axiom declaration ({cv.name})")
  | .basisDecl kind => do
    -- Install the pinned (pre-annotated) basis block; the frontend has
    -- already matched the incoming record against the pinned shapes.
    -- The quotient block's types mention the pinned equality former.
    if kind = .quotK then
      unless env.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDecl env
  | .indDecl block => checkIndDecl ops env block

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ops : CheckerOps m) (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl ops) Env.empty

end Setlec
