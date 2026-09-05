import Setlec.Kernel.Modeled
import Setlec.Kernel.TrustAxioms

/-!
# The checker

`checkDecl` checks one declaration against the current environment and,
on success, returns the extended environment.  `checkDecls` folds it
over a list of declarations, starting from the empty environment.  The
entry-point records (`CheckerOps` and its instantiations) and the
common `checkConstantVal` live in `Setlec/Kernel/CheckerBase.lean`;
the modeled-inductive install in `Setlec/Kernel/Modeled.lean`.
Verification: `Setlec.Verify.*`, `Setlec.SetR.Main` (the set route)
and `Setlec.TTVerify.Main` (the declarative route).
-/

namespace Setlec

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-! ## The direct simple-structure path (task #82)

A block recognised by `directParts?` (`Setlec/Kernel/Direct.lean`)
installs *directly*: no `_model` artifact is consumed, and the
set-theoretic model was constructed from the constructor telescope by
the retired direct model (`Setlec/Model/*`, deleted at task #148 T7;
the route ships `false`).  What is left for this layer are the
reference checks that need inference and definitional equality — the
per-field universe bound and the definitional pins of the recursor's
binder domains against the constructor's.
-/

/-- The capabilities a direct simple structure earns (task #175 W4c,
the user's ruling that the direct route carries every feature).

* `eta`: the tower's own elimination law (`towerSet_elim`) — the
  kernel's eta arms fabricate the projections as `.proj T j` nodes
  when every slot holds a tower entry (`etaProjs`), and the P tier's
  eta law is discharged from the tower at the install;
* `unitlike`: the fieldless tower is a singleton;
* `ruleK`: exactly the official `isKTarget` (a `Prop` result, a single
  constructor taking only the parameters; lean4lean
  `Inductive/Add.lean:289-296`) — the reduction site carries the
  semantic load (proof irrelevance), as on the modeled path. -/
def directCaps (p : DirectParts) : IndCaps where
  eta := true
  etaCtor := p.cvC.name
  etaParams := p.nP
  etaFields := p.nF
  unitlike := p.nF == 0
  unitParams := p.nP
  ruleK := p.nF == 0 && p.isProp

/-- The fields' sorts over the opened constructor telescope, with the
official per-field universe bound unless the structure is
propositional: every field's sort must be `≤` the structure's result
sort (lean4lean `Inductive/Add.lean:225-228`, nanoda `check_ctor`,
`checker/src/inductive.rs:809`; the `Prop` escape hatch is `isProp`,
task #175 W4c/O4).  Walks the fields from the last to the first and
returns the sorts in field order — the projection guards'
(`directProjGuards`) input. -/
def checkDirectFieldSorts (ops : CheckerOps m) (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    -- each field's domain is inferred at *its own* frame: the variable
    -- `fvs[j]` sits at index `nP + j`, so everything below it is in
    -- scope and nothing above is
    let ty ← ops.inferType env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct structure: field universe too large")
    else if large then
      -- a propositional structure's large eliminator exists only when
      -- every field is a proposition (lean4lean `Add.lean:257-259`);
      -- the squash model reads that as `FieldsBound 0`, so it is
      -- re-checked here on the annotated constants
      unless Level.isEquiv u .zero == some true do
        throw (.notImplemented
          "direct structure: large eliminator with a non-propositional field")
    let rest ← checkDirectFieldSorts ops env isProp large s nP fvs j
    pure (rest ++ [u])

/-- The reference kernels' binder-domain comparisons, run binder by
binder **at its own frame**: the `j`-th opened variable's annotation
against the `j`-th expected domain, at frame `off + j`.

Domain `j` is scoped at `off + j` — it mentions the binders before it
and nothing else — so that frame is exactly the context the references
compare it in, with those binders in scope and no more.  Because each
telescope is opened at its **own** variables, neither side's
annotations are borrowed from the other, which is what lets the model's
walks carry their own frame conditions at every stage.  Walks from the
last binder to the first, like `checkDirectFieldUniv`. -/
def checkDirectDomsAt (ops : CheckerOps m) (env : Env) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAt ops env off fvs doms j

/-- Stage 1: the type former.  The ordinary constant check plus a
re-verification of the *annotated* shape — the model reads the
parameter telescope and the result sort off the stored type. -/
def checkDirectInd (ops : CheckerOps m) (env : Env) (p : DirectParts) :
    m (Env × ConstantVal) := do
  let cvTa ← checkConstantVal ops env p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis p.nP)
    (.notImplemented "direct structure: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct structure: type former result sort")
  pure (⟨.indInfo cvTa (directCaps p) :: env.consts⟩, cvTa)

/-- Stage 2: the constructor — the ordinary constant check, the
annotated result shape, and the per-field universe bound.

`env₀` is the **pre-block** environment and `env` the one carrying the
type former.  The opened field domains are re-checked to resolve in
`env₀`: `directNonRec` says that of the *raw* domains (it is the
recognition filter), and the model needs it of the *annotated* ones,
because the type former's value — fixed one install earlier, before its
own constructor existed — is built from those domains' interpretations
in `env₀`.  Same discipline as `directShape`: a skeleton fact checked
on the raw block for recognition and re-checked on the annotated
constants at install. -/
def checkDirectCtor (ops : CheckerOps m) (env₀ env : Env) (p : DirectParts)
    (cvTa : ConstantVal) : m (Env × ConstantVal × List Level) := do
  let cvCa ← checkConstantVal ops env p.cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (p.nP + p.nF))
    (.notImplemented "direct structure: constructor telescope")
  unless cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF do
    throw (.notImplemented "direct structure: constructor result")
  -- Each parameter telescope is opened at its **own** variables: the
  -- constructor's is the frame the model's fits arrive at (the field
  -- types' interpretations, the dependent-pair tower and the
  -- constructor value are all read off it), and the type former's is
  -- the frame its own value's λ-tower was built at, so a parameter
  -- value's membership carries from one to the other and the family's
  -- value folds at the very same parameters.
  let cq ← unwrapOr (openPisAtFvars p.nP cvCa.type 0)
    (.notImplemented "direct structure: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars p.nP cvTa.type 0)
    (.notImplemented "direct structure: type former telescope")
  checkDirectDomsAt ops env 0 cq.1 (tq.1.map Expr.fvarTypeD) p.nP
  let xq ← unwrapOr (openPisAtFvars p.nF cq.2 p.nP)
    (.notImplemented "direct structure: constructor field telescope")
  -- the opened residual is the family at the opened parameter variables
  unless xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1 do
    throw (.notImplemented "direct structure: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolve env₀ do
    throw (.notImplemented "direct structure: field domain after the block")
  -- the fields' sorts, with the official `Prop` escape hatch on the
  -- universe bound (lean4lean `Add.lean:225`; task #175 W4c/O4 — a
  -- propositional structure's model is the squash, which needs none)
  let sorts ← checkDirectFieldSorts ops env p.isProp p.large p.resSort p.nP
    xq.1 p.nF
  pure (⟨.ctorInfo cvCa p.nP p.nF :: env.consts⟩, cvCa, sorts)

/-- Stage 3: the recursor's type is the generated shape.  The skeleton
(motive dependent over the family, one minor over the constructor's
field telescope ending in `motive (C p⃗ f⃗)`, no indices, major, body
`motive t`) is pinned syntactically by `directShape`; the binder
*domains* are pinned definitionally against the type former's and the
constructor's over one shared opening — exactly the equalities the
model's telescope walks consume. -/
def checkDirectRecTy (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvTa cvCa cvRa : ConstantVal) : m Unit := do
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  unless directShape T p.cvC.name lps p.elim p.large p.nP p.nF
      cvTa.type cvCa.type cvRa.type do
    throw (.notImplemented "direct structure: annotated recursor shape")
  let (fvsP, rest) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let ps := fvsP.take p.nP
  let famApp := Expr.mkAppN (.const T (lps.map .param)) ps
  -- the parameters: definitionally the constructor's parameter domains,
  -- domain `j` at frame `j`
  let (cdomsP, crest) ← unwrapOr (Expr.instPisAt ps cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  checkDirectDomsAt ops env 0 ps cdomsP p.nP
  -- the motive: `∀ (t : T p⃗), Sort elim`
  let mfv ← unwrapOr fvsP[p.nP]?
    (.internal "direct structure: motive index")
  let (mbs, mbody) ← unwrapOr (mfv.fvarTypeD.stripPis 1)
    (.notImplemented "direct structure: motive telescope")
  let mdom ← unwrapOr ((mbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: motive telescope")
  unless ← ops.isDefEq env p.nP mdom famApp do
    throw (.notImplemented "direct structure: motive domain")
  unless mbody == Expr.sort (if p.large then .param p.elim else .zero) do
    throw (.notImplemented "direct structure: motive codomain")
  -- the minor premise: the constructor's field telescope, ending in
  -- the motive applied to the canonical constructor spine
  let minfv ← unwrapOr fvsP[p.nP + 1]?
    (.internal "direct structure: minor index")
  let (xFvs, minBody) ← unwrapOr
    (openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2))
    (.notImplemented "direct structure: minor telescope")
  let (cdomsF, crest2) ← unwrapOr (Expr.instPisAt xFvs crest)
    (.notImplemented "direct structure: constructor field telescope")
  checkDirectDomsAt ops env (p.nP + 2) xFvs cdomsF p.nF
  unless crest2 == famApp do
    throw (.notImplemented "direct structure: constructor residual")
  unless minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (lps.map .param)) (ps ++ xFvs)) do
    throw (.notImplemented "direct structure: minor conclusion")
  -- the major premise and the conclusion `motive t`
  let (jbs, jbody) ← unwrapOr (rest.stripPis 1)
    (.notImplemented "direct structure: major telescope")
  let jdom ← unwrapOr ((jbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: major telescope")
  unless ← ops.isDefEq env (p.nP + 2) jdom famApp do
    throw (.notImplemented "direct structure: major domain")
  unless jbody == Expr.app mfv (.bvar 0) do
    throw (.notImplemented "direct structure: recursor conclusion")

/-- Stage 4: the single rule's right-hand side — `λ p⃗ motive minor f⃗,
minor f⃗` (lean4lean `Inductive/Add.lean:441-447`), annotated and
checked exactly like a projection rule: the body is the canonical
application and the λ-domains are definitionally the recursor's own and
the constructor's field domains. -/
def checkDirectRule (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvCa cvRa : ConstantVal) : m Expr := do
  unless !p.rhs.hasFvar && p.rhs.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: rule scoping")
  let rhsA ← ops.annotate env 0 p.rhs
  unless rhsA.allLevelParamsDefined cvRa.levelParams && rhsA.constsResolve env &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "direct structure: rule wellformedness")
  let (_, rbody) ← unwrapOr (rhsA.stripLams (p.nP + 2 + p.nF))
    (.notImplemented "direct structure: rule telescope")
  unless rbody == directRuleBody p.nF do
    throw (.notImplemented "direct structure: rule body")
  let depth := p.nP + 2 + p.nF
  let (fvsP, _) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsP.take p.nP) cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  -- The frame is the **rule tower's own** (`ruleLhsParts`): the
  -- constructor's field telescope opened at the rule prefix, not the
  -- minor premise's opening of the same binders.  The two are pinned
  -- definitionally equal by `checkDirectRecTy`, but only this one is
  -- the frame the stored rule's total λ-equality is stated over, and
  -- the model has no way to cross a definitional step it was not
  -- handed — the same "route (X), at the stage's own frames"
  -- discipline the projection stage follows.
  let (xFvs, _) ← unwrapOr (openPisAtFvars p.nF crest (p.nP + 2))
    (.notImplemented "direct structure: constructor field telescope")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvs) rhsA)
    (.notImplemented "direct structure: rule telescope")
  checkDefEqList ops env depth ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms
  let _rhsTy ← ops.inferType env 0 rhsA
  pure rhsA

/-- Install the **native tower-backed projection entry** for field `i`
of a direct simple structure (task #175 wiring; supersedes the
degenerate-recursor install).  The stored `ty` is the generated
projection type in `.proj`-node spelling (`directProjTyP`), reduction
is `whnfCore`'s generic structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`,
and the definitional re-checks below (subject domain, residual) are
exactly the interpretation pins the model consumes.  The **O4
per-field branch**: the entry is installed iff the levelwise bound
`ψ(structSort) = 0 → ψ(fieldSort) = 0` is decidably discharged —
`resSort.isNonZero` (today's whole recognised class) or
`Level.leq fieldSort resSort` (the monotone case); a field failing it
gets NO entry and its `.proj` uses stay per-use checked.  Fields are
installed in order: field `i`'s type spells the earlier projections as
`.proj` nodes, whose annotation reads the earlier entries. -/
def checkDirectProjEntry (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (resSort guard : Level) (cvCa : ConstantVal)
    (pty : Expr) (env : Env) (i : Nat) : m Env := do
  unless !pty.hasFvar && pty.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: projection type scoping")
  let ptyA ← ops.annotate env 0 pty
  unless ptyA.allLevelParamsDefined lps && ptyA.constsResolve env &&
      ptyA.looseBVarsBounded 0 && !ptyA.hasFvar do
    throw (.notImplemented "direct structure: projection type wellformedness")
  unless (ptyA.stripPis (nP + 1)).isSome do
    throw (.notImplemented "direct structure: projection type telescope")
  let sty ← ops.inferType env 0 ptyA
  let _u ← ops.ensureSort env 0 sty
  unless (env.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  checkProjShape ptyA cvCa.type nP nF
  -- The **annotated** projection type's own frame walk.  The model
  -- reads the stored (annotated) type, and annotation is not
  -- interpretation-preserving — the raw `directProjTy` output is not
  -- even interpretable, since its binders carry no codomain sort — so
  -- the two facts the model needs are re-checked here, exactly as
  -- `checkDirectInd`/`checkDirectCtor`/`checkDirectRecTy` re-check
  -- their skeletons on the annotated constants: the subject's domain is
  -- the family at the opened parameters, and the residual is the
  -- constructor's `i`-th field domain at those parameters and at the
  -- earlier projections.  Both comparands are built here from *closed*
  -- arguments (the opened variables), so `Expr.instPisAt` suffices and
  -- `directProjTy` becomes a **validated generator**: a failure here is
  -- a generator bug, and declining is the right verdict.
  let (fvsP, prest) ← unwrapOr (openPisAtFvars nP ptyA 0)
    (.notImplemented "direct structure: projection type telescope")
  let famApp := Expr.mkAppN (.const T (lps.map .param)) fvsP
  let (sbs, _) ← unwrapOr (prest.stripPis 1)
    (.notImplemented "direct structure: projection subject telescope")
  let sdom ← unwrapOr ((sbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: projection subject telescope")
  unless ← ops.isDefEq env nP sdom famApp do
    throw (.notImplemented "direct structure: projection subject domain")
  let (tFvs, resid) ← unwrapOr (openPisAtFvars 1 prest nP)
    (.notImplemented "direct structure: projection subject telescope")
  let tfv ← unwrapOr tFvs[0]?
    (.internal "direct structure: projection subject index")
  let projArgs := (List.range i).map fun j => Expr.proj T j tfv
  let (_, cresid) ← unwrapOr (Expr.instPisAt (fvsP ++ projArgs) cvCa.type)
    (.notImplemented "direct structure: projection field telescope")
  let fdom ← unwrapOr (match cresid with
      | .forallE _ d _ _ => some d
      | _ => none)
    (.notImplemented "direct structure: projection field telescope")
  unless ← ops.isDefEq env (nP + 1) resid fdom do
    throw (.notImplemented "direct structure: projection residual")
  -- the entry's `fieldSort` slot carries the projection's `Prop`
  -- guard level (`directProjGuards`), the datum the tower infer
  -- branch checks at every use of a `Prop`-declared structure
  pure ⟨.projInfo ⟨T, i, lps, nP, C, nF, ptyA, guard, resSort,
    true, false, true⟩ :: env.consts⟩

/-- The projection slot for field `i` (task #175 W4c/O4): the entry
decision `directProjSlotOk` — a function of the block's input data —
says whether an entry installs at all; a skipped slot is a plain
fall-through, never a verdict (the block installs; a `.proj` use of
the field declines at its own site).  Otherwise the entry is installed
with its guard level. -/
def checkDirectProj (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa cvCa : ConstantVal) (guards : List Level) (env : Env) (i : Nat) :
    m Env := do
  let pty ← unwrapOr (directProjTyP T lps nP nF i cvTa.type cvCa.type)
    (.notImplemented "direct structure: projection type")
  if directProjSlotOk T isProp large pty then
    checkDirectProjEntry ops T C lps nP nF resSort (guards.getD i .zero)
      cvCa pty env i
  else pure env

/-- Check and install a **direct simple structure** (task #82): the
type former, the constructor, the recursor with its single rule, and
the `nF` projection **functions** (`checkDirectProj` — real degenerate
recursors in the `projFnName` slot family, *not* the Prop-fallback
elimination templates, which cannot express a dependent field's
projection; see DESIGN.md, "Projections compose with the existing
table").  No `_model` artifact is read and none is written; the model
was constructed at install by the retired direct model (deleted at
task #148 T7; the route ships `false`).  Recognition
happened in `directParts?`; everything here is a genuine check of the
declaration, so a failure is a verdict, not a fall-through. -/
def checkDirectStruct (ops : CheckerOps m) (env : Env) (p : DirectParts) :
    m Env := do
  let (env₁, cvTa) ← checkDirectInd ops env p
  let (env₂, cvCa, sorts) ← checkDirectCtor ops env env₁ p cvTa
  let cvRa ← checkConstantVal ops env₂ p.cvR
  checkDirectRecTy ops env₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRule ops env₂ p cvCa cvRa
  let env₃ : Env :=
    ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
          .plain else .inert,
        rhsA⟩] :: env₂.consts⟩
  unless (List.range p.nF).all
      (fun j => (env₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  (List.range p.nF).foldlM
    (checkDirectProj ops p.cvT.name p.cvC.name p.cvT.levelParams
      p.nP p.nF p.resSort p.isProp p.large cvTa cvCa
      (directProjGuards cvCa.type p.nP p.nF sorts)) env₃

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env := do
  unless (env.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env)

/-- Check a `def` declaration's value against its checked constant.
The reducibility hint is stored untouched: it steers only the lazy
delta unfolding order in `isDefEq`, never a verdict, so nothing about
it needs checking. -/
def checkDefnVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : m Env := do
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
  pure ⟨.defnInfo cv value hint :: env.consts⟩

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
requirement.  The result is stored as an `axiomInfo` — the checked
value is a *realizability witness*, consumed by the model extension
and then discarded: the official kernel's `is_delta` never unfolds an
opaque (unlike theorems, task #66), so storing the value in an
unfoldable kind would be a reduction-strategy superset (it would
e.g. compute `Lean.reduceBool b` where the reference kernels are
stuck; the task-#95 honest limit relies on that stuckness). -/
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
  pure ⟨.axiomInfo cv :: env.consts⟩
/-- Certify a list of recurrence equations by definitional equality
(at depth 2: the equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (ops : CheckerOps m) (env : Env) :
    List (Expr × Expr) → m Bool
  | [] => pure true
  | eq :: rest => do
    if ← ops.isDefEq env 2 eq.1 eq.2 then
      certifyNatEqs ops env rest
    else pure false

/-- The pinned defining expression of a pin-certified WF-recursive op
(`Setlec/Kernel/NatOpPins.lean`, generated at build time from the toolchain's own
prelude). -/
def divModDeclPin (c : Name) : Expr :=
  if c = natDivName then natDivDeclPin
  else if c = natGcdName then natGcdDeclPin
  else if c = natLandName then natLandDeclPin
  else if c = natLorName then natLorDeclPin
  else if c = natXorName then natXorDeclPin
  else if c = natShiftLeftName then natShiftLeftDeclPin
  else if c = natShiftRightName then natShiftRightDeclPin
  else if c = natLog2Name then natLog2DeclPin
  else natModDeclPin

/-- The vendored certificate proof terms of a pin-certified
WF-recursive op (`Setlec/Kernel/NatOpPins.lean`), one per statement of
`divModCertStmts`. -/
def divModCertProofs (c : Name) : List Expr :=
  if c = natDivName then natDivCertProofs
  else if c = natGcdName then natGcdCertProofs
  else if c = natLandName then natLandCertProofs
  else if c = natLorName then natLorCertProofs
  else if c = natXorName then natXorCertProofs
  else if c = natShiftLeftName then natShiftLeftCertProofs
  else if c = natShiftRightName then natShiftRightCertProofs
  else if c = natLog2Name then natLog2CertProofs
  else natModCertProofs

/-- The pinned characterization statements of a pin-certified
WF-recursive op, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOpsOk` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored annotated
value before checking (all statement components are application
spines, so `Expr.substConst0` applies). -/
def divModCertStmts (c : Name) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar 0 (.str .anonymous "x") natTy
  let y : Expr := .fvar 1 (.str .anonymous "y") natTy
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natMulName []) a) b
  let op1 : Expr → Expr := fun a => .app (.const c []) a
  let s1 : Expr → Expr := fun a => .app (.const natSuccName []) a
  if c = natGcdName then
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natShiftLeftName then
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natShiftRightName then
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natLog2Name then
    -- unary: `2 ≤ x → log2 x = succ (log2 (x/2))`, `x < 2 → log2 x = 0`
    -- (the statement frame still has both variables; `y` is unused)
    [([eqB (ble2 two x) bT], eqN (op1 x) (s1 (op1 (div2 x two)))),
     ([eqB (ble2 two x) bF], eqN (op1 x) z)]
  else if c = natLandName then
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
    -- `x = 0 → x &&& y = 0`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c = natLorName then
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
    -- `x = 0 → x ||| y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natXorName then
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
    -- `x = 0 → x ^^^ y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- The vendored proof applied to the statement's free variables
(`x`, `y`, then one `fvar` per hypothesis, carrying the hypothesis
*type* as its `fvar` annotation — the checker's implicit local
context). -/
def divModCertApplied (proofS : Expr) (hyps : List Expr) : Expr :=
  let base : Expr :=
    .app (.app proofS (.fvar 0 (.str .anonymous "x") (.const natName [])))
      (.fvar 1 (.str .anonymous "y") (.const natName []))
  match hyps with
  | [h1] => .app base (.fvar 2 (.str .anonymous "h1") h1)
  | [h1, h2] =>
    .app (.app base (.fvar 2 (.str .anonymous "h1") h1))
      (.fvar 3 (.str .anonymous "h2") h2)
  | _ => base

/-- The syntactic guards of one certificate check: the substituted
proof is closed, level-monomorphic and resolving, and the substituted
statement components resolve. -/
def divModCertGuard (env : Env) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolve env &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolve env) &&
  (Expr.substConst0 c annVal eqE).constsResolve env

/-- Check the pinned certificates of op `c`: per certificate, the
vendored proof (with the op's self-references replaced by the stored
annotated value — the checks run in the *pre-insertion* environment,
exactly like the structural-Nat certification: post-insertion the op's
own just-enabled fast path would participate in checking the very
certificates that justify it) is applied to free variables typed by
the pinned open statement, its type inferred, and compared against the
pinned characteristic equation.  This checks each certificate exactly
like a theorem declaration over an opened telescope — nothing is
installed. -/
def checkDivModCerts (ops : CheckerOps m) (env : Env) (c : Name)
    (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if divModCertGuard env c annVal hyps eqE proof then
      let appliedA ← ops.annotate env 4
        (divModCertApplied (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal)))
      let tp ← ops.inferType env 4 appliedA
      if ← ops.isDefEq env 4 tp (Expr.substConst0 c annVal eqE) then
        checkDivModCerts ops env c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- Environment prerequisites of a certified `Nat.div`/`Nat.mod`:
dependency guard, pinned dependencies, the pinned `Eq` basis (the
certificate statements are equations in the pinned equality), and the
`Bool` constructors stored at the type `Bool` itself (the guards'
`true`/`false` must inhabit the `Bool` value semantically). -/
def divModEnvGuard (env2 : Env) (c : Name) : Bool :=
  natOpGuard env2 c && (natOpDeps c).all (natOpStoredOk env2) &&
  env2.find? eqName == some eqA &&
  (match env2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- Syntactic guards on the vendored pin (generated; checked once at
install rather than proven about the blob). -/
def divModPinGuard (env : Env) (c : Name) : Bool :=
  (divModDeclPin c).looseBVarsBounded 0 && !(divModDeclPin c).hasFvar &&
  (divModDeclPin c).allLevelParamsDefined [] &&
  (divModDeclPin c).constsResolve env

/-- All certificates' syntactic guards at once.  Checked *before* the
pin comparison and declined on failure: a stream may legitimately stop
short of the constants the vendored proofs mention, which is an
unsupported environment, not an internal inconsistency. -/
def divModCertsGuard (env : Env) (c : Name) (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs c)).all
    (fun p => divModCertGuard env c annVal p.1.1 p.1.2 p.2)

/-- The `Nat.div`/`Nat.mod` install gate, run after the ordinary
definition check (`env2` is the already-extended environment, `env`
the pre-insertion one all checks run in): dependency and pinned-`Eq`
guards, then definitional equality of the stored value against the
vendored pin of the toolchain's own helper-unfolded definition —
elaborator drift surfaces as a decline (exit 2), never silently — and
on a match the pinned certificates (`checkDivModCerts`).  A
certificate failure after a pin match is an internal inconsistency
(exit 3). -/
def checkDivModPin (ops : CheckerOps m) (env env2 : Env) (c : Name) :
    m Unit := do
  if divModEnvGuard env2 c then
    match env2.find? c with
    | some (.defnInfo _ value' _) =>
      if divModPinGuard env c && divModCertsGuard env c value' then do
        let pinA ← ops.annotate env 0 (divModDeclPin c)
        let okPin ← ops.isDefEq env 0 value' pinA
        if okPin then do
          let ok ← checkDivModCerts ops env c value'
            (divModCertStmts c) (divModCertProofs c)
          if ok then pure ()
          else throw (.internal
            s!"pinned Nat.div/mod certificate failed after pin match ({c})")
        else throw (.notImplemented
          s!"unsupported Nat.div/mod spelling ({c})")
      else throw (.notImplemented
        s!"unsupported Nat.div/mod spelling ({c}: pin ground constants absent)")
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the
ordinary opaque check (`env2` is the already-extended environment,
`env` the pre-insertion one the comparisons run in; `value` the
declaration's raw witness value, annotated again here — the stored
constant is an `axiomInfo`, which carries no value):

* the stored constant must carry the pinned type;
* the witness value must be definitionally equal to the build-time pin
  of the toolchain's own defining expression
  (`Setlec/Kernel/TrustPins.lean`) — toolchain drift surfaces as a
  decline (exit 2), never silently;
* the *identity certificate*: `value x ≡ x` over an opened `fvar` at
  the element type.  This is what the model consumes
  (`EnvModel.reduce_ops`): with the operation interpreted as the
  identity, the `ofReduce*` axioms' types are trivially inhabited.  A
  certificate failure after the pin matched is an internal
  inconsistency (the pin *is* the identity function). -/
def checkReducePin (ops : CheckerOps m) (env env2 : Env) (c : Name)
    (value : Expr) : m Unit := do
  if reduceStoredOk env2 c && reduceElemOk env c then
    if reducePinGuard env c then do
      let valA ← ops.annotate env 0 value
      let pinA ← ops.annotate env 0 (reduceDeclPin c)
      let okPin ← ops.isDefEq env 0 valA pinA
      if okPin then do
        let x := reduceCertVar c
        let ok ← ops.isDefEq env 1 (.app valA x) x
        if ok then pure ()
        else throw (.internal
          s!"pinned compiler-trust opaque is not the identity ({c})")
      else throw (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({c})")
    else throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  else throw (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({c})")

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : CheckerOps m) (env : Env) (d : Declaration) : m Env := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value hint
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
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal s!"structural Nat operation not stored ({cv.name})")
    -- WF-recursive Nat pins (`Nat.div`/`Nat.mod`): the stored value must
    -- be definitionally equal to the vendored pin of the toolchain's own
    -- (helper-unfolded) definition — elaborator drift surfaces as a
    -- decline (exit 2), never silently.  On a match, the pinned
    -- `Nat.ble`-guarded characterization certificates are checked (in
    -- the pre-insertion environment, self-references substituted; see
    -- `checkDivModCerts`) but not installed; their success is what the
    -- model side consumes for the literal fast path.  A certificate
    -- failure after a pin match is an internal inconsistency (exit 3).
    if natDivModNames.contains cv.name then
      checkDivModPin ops env env2 cv.name
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkOpaqueVal ops env cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`,
    -- task #95): the stored value must be definitionally equal to the
    -- build-time pin of the toolchain's own defining expression — the
    -- gate that lets the `ofReduce*` axioms' identity certificates
    -- never fail on an accepted environment.
    if reduceOpNames.contains cv.name then
      checkReducePin ops env env2 cv.name value
    pure env2
  | .axiomDecl cv => do
    -- Pinned axioms are *installed*: the two standard axioms
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice) and the `Init` compiler-trust
    -- family (task #95: `Lean.trustCompiler` as an opaque with value
    -- `True.intro`; `Lean.ofReduceNat`/`Lean.ofReduceBool` over the
    -- pinned identity opaques, trivially true).  All types and the
    -- shapes of the inductives they quantify over are pinned (up to
    -- the exporter's unstable hygienic binder names).  The tolerated
    -- whitelist (`toleratedAxiomNames` — exactly `sorryAx`, user
    -- ruling) is well-formedness-checked but not stored; the run
    -- continues and the frontend positively declines any later
    -- declaration that references the skipped axiom.  Any other axiom
    -- is a positive decline at its own record; a *pinned name* with a
    -- non-pinned shape likewise (the pin would otherwise shadow).
    let cvA ← checkConstantVal ops env cv
    if stdAxiomOk env cvA then
      pure ⟨.axiomInfo cvA :: env.consts⟩
    else if cvA.name = trustCompilerName then
      -- `Lean.trustCompiler : True` is trivially realizable (task
      -- #95): installed exactly like a checked `opaque` with witness
      -- value `True.intro` over the pinned `True` family — the pin
      -- guarantees everything the ordinary opaque check would have
      -- checked for that value, and the model interprets the constant
      -- by `True.intro`'s interpretation.
      if trustCompilerOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      -- The pinned `ofReduce*` axioms (task #95): over the pinned
      -- `Eq` basis, the element inductive and the identity-certified
      -- reduce opaque, `∀ a b, reduce a = b → a = b` interprets to an
      -- inhabited proposition (the hypothesis *is* the conclusion).
      if ofReduceAxOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure env
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    -- Install the pinned (pre-annotated) basis block; the frontend has
    -- already matched the incoming record against the pinned shapes.
    -- The quotient block's types mention the pinned equality former.
    if kind = .quotK then
      unless env.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDecl env
  | .indDecl block =>
    -- Task #82: an *artifact-free* recognised simple structure is
    -- installed directly, from the reference checks alone
    -- (`Setlec/Kernel/Direct.lean`).  `directParts?` is a conservative
    -- filter that also requires the block's `_model` companions to be
    -- absent, so every preprocessed stream keeps today's route byte for
    -- byte; the module split (`CheckerBase ← Modeled ← Checker`) is why
    -- the dispatch lives here and not inside `checkIndDecl`.
    match directParts? env block with
    | some p => checkDirectStruct ops env p
    | none => checkIndDecl mode ops env block

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ops : CheckerOps m) (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl mode ops) Env.empty

end Setlec
