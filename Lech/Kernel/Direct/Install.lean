import Lech.Kernel.Modeled
import Lech.Kernel.TrustAxioms

/-!
# The direct simple-structure install (pure fueled checker)

The install stages of a block recognised by `directParts?`
(`Lech/Kernel/Direct/Parts.lean`): former, constructor, recursor
type and rule, projection entries, assembled by `checkDirectStruct`.
Extracted verbatim from `Lech/Kernel/Checker.lean` on 2026-09-06
(cleanup pass A); `checkDecl`'s `.indDecl` clause dispatches here.
The index-threaded twins are `Lech/Kernel/Direct/InstallF.lean`.
-/

namespace Lech

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-! ## The direct simple-structure path (task #82)

A block recognised by `directParts?` (`Lech/Kernel/Direct.lean`)
installs *directly*: no `_model` artifact is consumed, and the
set-theoretic model was constructed from the constructor telescope by
the retired direct model (`Lech/Model/*`, deleted at task #148 T7;
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

/-- Stage 3: **the recursor, generated and compared** (task #175 S2).
The recursor type and its rule are *fabricated* from the annotated
type former and constructor types (`directRecTy`/`directRecRhs`,
`Lech/Kernel/Direct/Parts.lean`), exactly as the reference kernels
generate theirs; the stream's recursor is admitted by the ordinary
constant check (`checkConstantVal` — freshness, reservation, level
parameters, annotate + infer) and then compared against the generated
type by **one closed `isDefEq`** — the gap official's `whnf`-peeled
domains leave is definitional, and this is the one place it is
crossed.  What is *stored* is the generated recursor (its type and its
rule), as official stores its own: the model reads the stored forms
syntactically, and the comparison carries no proof obligation.

The generated forms are validated once: the recursor type is inferred
(a sort; in verified mode this also validates every binder datum the
generator wrote) and the rule's right-hand side is inferred (the
reading's grading), and both pass the scoping guards `EnvWF` records
(fvar-free, level parameters within the recursor's, resolving, closed)
— those cannot fail on a block the earlier stages accepted, so their
failure is internal.  Returns the stored recursor's `ConstantVal` and
the rule's right-hand side. -/
def checkDirectRec (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvTa cvCa : ConstantVal) : m (ConstantVal × Expr) := do
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := [(p.cvC.name, p.nF, cvCa.type)]
  let recTy ← unwrapOr (directRecTy T lps p.elim p.large p.nP cvTa.type ctors)
    (.internal "direct structure: recursor type")
  let rhs ← unwrapOr (directRecRhs T lps p.elim p.large p.nP cvTa.type ctors 0)
    (.internal "direct structure: recursor rule")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct structure: recursor type scoping")
  unless rhs.allLevelParamsDefined p.cvR.levelParams && rhs.constsResolve env &&
      rhs.looseBVarsBounded 0 && !rhs.hasFvar do
    throw (.internal "direct structure: recursor rule scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    throw (.notImplemented "direct structure: recursor type")
  let _rhsTy ← ops.inferType env 0 rhs
  pure (⟨p.cvR.name, p.cvR.levelParams, recTy⟩, rhs)

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
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && b.constsResolve env &&
      b.looseBVarsBounded (nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the projection-function name family (the modeled route's, the key
  -- of its η-family predicate) must be free too: a direct family has
  -- no projection functions, and the model's η law for the block is
  -- discharged by the tower, never by `EtaFamilyStored`
  unless (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) do
    throw (.invalid "projection name family taken")
  unless (env.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure ⟨.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards⟩ :: env.consts⟩

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
  let (cvRa, rhsA) ← checkDirectRec ops env₂ p cvTa cvCa
  let env₃ : Env :=
    ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
          .plain else .inert,
        rhsA⟩] :: env₂.consts⟩
  checkDirectProjTable p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
    p.resSort (directProjGuards cvCa.type p.nP p.nF sorts) cvCa env₃

end Lech
