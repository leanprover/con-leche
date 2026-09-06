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
  -- the guard's zeroing instantiation (`directGuardSigma`): the
  -- entry's type is validated where the entry is usable
  let σ := directGuardSigma resSort lps guard
  let ptyσ := pty.instantiateLevelParams lps σ
  let ctyσ := cvCa.type.instantiateLevelParams lps σ
  let ptyA ← ops.annotate env 0 ptyσ
  unless ptyA.allLevelParamsDefined lps && ptyA.constsResolve env &&
      ptyA.looseBVarsBounded 0 && !ptyA.hasFvar do
    throw (.notImplemented "direct structure: projection type wellformedness")
  unless (ptyA.stripPis (nP + 1)).isSome do
    throw (.notImplemented "direct structure: projection type telescope")
  let sty ← ops.inferType env 0 ptyA
  let _u ← ops.ensureSort env 0 sty
  unless (env.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  checkProjShape ptyA ctyσ nP nF
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
  let famApp := Expr.mkAppN (.const T σ) fvsP
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
  -- the entry's parameter domains are the constructor's at the opened
  -- parameters (task #175 W4c, P3 module 7): the model identifies the
  -- entry's parameter frame with the block's through this pin, exactly
  -- as `checkDirectCtor` pins the constructor's to the former's
  let (cdomsP, _) ← unwrapOr (Expr.instPisAt fvsP ctyσ)
    (.notImplemented "direct structure: projection parameter telescope")
  checkDirectDomsAt ops env 0 fvsP cdomsP nP
  let projArgs := (List.range i).map fun j => Expr.proj T j tfv
  let (_, cresid) ← unwrapOr (Expr.instPisAt (fvsP ++ projArgs) ctyσ)
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
decision `slots` (`directProjSlots`, a function of the block's raw
types) says whether an entry installs at all; a skipped slot is a
plain fall-through, never a verdict (the block installs; a `.proj` use
of the field declines at its own site).  Otherwise the entry is
installed, from the annotated types, with its guard level. -/
def checkDirectProj (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (resSort : Level) (slots : List Bool)
    (guards : List Level) (cvTa cvCa : ConstantVal) (env : Env) (i : Nat) :
    m Env :=
  if slots.getD i false then do
    let pty ← unwrapOr (directProjTyP T lps nP nF i cvTa.type cvCa.type)
      (.notImplemented "direct structure: projection type")
    if directSlotAdmit resSort lps cvCa.type nP guards i then
      checkDirectProjEntry ops T C lps nP nF resSort (guards.getD i .zero)
        cvCa pty env i
    else do
      -- the inert entry (`directInertEntry`): the slot is held, the
      -- field's projections decline at their own sites
      unless (env.find? (projFnName T i)).isNone do
        throw (.invalid "projection name taken")
      pure ⟨.projInfo (directInertEntry T i lps nP C nF (guards.getD i .zero) resSort)
        :: env.consts⟩
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
      p.nP p.nF p.resSort (directProjSlots p)
      (directProjGuards cvCa.type p.nP p.nF sorts) cvTa cvCa) env₃

end Setlec
