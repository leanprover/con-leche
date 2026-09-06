import Setlec.Kernel.Modeled
import Setlec.Kernel.TrustAxioms

/-!
# The direct simple-structure install (pure fueled checker)

The install stages of a block recognised by `directParts?`
(`Setlec/Kernel/Direct/Parts.lean`): former, constructor, recursor
type and rule, projection entries, assembled by `checkDirectStruct`.
Extracted verbatim from `Setlec/Kernel/Checker.lean` on 2026-09-06
(cleanup pass A); `checkDecl`'s `.indDecl` clause dispatches here.
The index-threaded twins are `Setlec/Kernel/Direct/InstallF.lean`.
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
  -- structure eta is claimed for the non-`Prop` families only (task
  -- #175 W4c/O4): at a `Prop`-declared structure every proof is
  -- already definitionally equal by proof irrelevance, and the tower
  -- eta fabrication's `.proj` nodes at a data field would be untyped
  eta := !p.isProp
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

/-- Stage 5: **the projection table** (task #175 S1).  One constant
per structure: the fields' result-type bodies read off the
*annotated* constructor type by substitution alone
(`directProjBodies`), the per-field guard levels
(`directProjGuards`), the constructor and the counts.  Nothing is
annotated, inferred or pinned here — a `.proj T i e` use instantiates
`bodies[i]` at its own arguments (`ProjEntry.typeAt`) after the
official `infer_proj` guard test, and a slot with no legal
instantiation (a used-later data field of a `Prop` structure) simply
fails that guard at every use (`invalid`, as official).  The body
walk cannot fail on a constructor type `checkDirectCtor` accepted
(it peels exactly `nP + nF` binders), so its failure is internal. -/
def checkDirectProjTable (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (cvCa : ConstantVal) (env : Env) :
    m Env := do
  let bodies ← unwrapOr (directProjBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  unless (env.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure ⟨.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, true⟩ :: env.consts⟩

/-- Check and install a **direct simple structure** (task #82): the
type former, the constructor, the recursor with its single rule, and
the structure's projection **table** (`checkDirectProjTable` — the
fields' bodies, one constant; task #175 S1).  No `_model` artifact is
read and none is written; the model was constructed at install by the
retired direct model (deleted at task #148 T7; the route ships
`false`).  Recognition happened in `directParts?`; everything here is
a genuine check of the declaration, so a failure is a verdict, not a
fall-through. -/
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
  checkDirectProjTable p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
    p.resSort (directProjGuards cvCa.type p.nP p.nF sorts) cvCa env₃

end Setlec
