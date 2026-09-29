module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Kernel.Inductives.ClassRead

@[expose] public section

/-!
# The recursor family, GENERATED (charter item 5, amended 2026-09-29)

The recursor stage in official's shape (`mk_rec_infos`/`mk_rec_rules`,
`inductive.cpp`): the checker GENERATES the block's recursor family —
types and rules — from the CLASSES the stream's family eliminates and
the positivity check's recorded constructor normal forms, compares each
generated TYPE with the stream's by `isDefEq`, and INSTALLS the generated
recursors.  The stream's recursor rules are never read.

* **The classes.**  An UNVERIFIED pre-pass (`ClassRead.lean`) reads the
  classes (one per motive), the prefix layout (motives, minor premises,
  their inductive hypotheses) and every recursor's class off the stream's
  recursor TYPES.  Every class is then checked as a major
  (`targetMajorOf`: a member at the block's levels and parameters, or a
  stored inductive at an auxiliary type of the block, `is_nested`), with
  exactly one class per member.
* **The seeds.**  Every outside class seeds the positivity check
  (`nestSeeds`), so every class is a node of the walk by construction; the
  walk's recorded constructor normal forms (the TABLE, `NestCtorNf`, with
  their readings) are the generator's input.
* **Per class and constructor** the entries of the table at a key the
  class matches per component (`targetMajorNfs`); the first is the
  generator's DATUM (its telescope and field kinds).  The minor premise's
  inductive hypotheses must be exactly the datum's recursive fields, one
  each (the classes they name come from the pre-pass); and — NODE
  AGREEMENT (K.53′) — at EVERY entry of the pair, every recursive field
  has the datum's telescope, the same leaf head and indices, and a leaf
  class matching the inductive hypothesis's class per component
  (`targetK53`).  Only a class with two or more nodes gives the second
  half work.
* **Generation** (`ClassGen`): the shared prefix (parameters, motives,
  minor premises in the stream's order), each recursor's type
  (`classGenRecTy`) and each rule (`classGenRule`: the minor premise
  applied to the fields and, per recursive field, `λ a⃗, rec_t p⃗ e⃗ (f a⃗)`
  at the recursor of the class the field lands at).
* **Installation.**  Each generated type is checked as a constant
  (`checkConstantValF`) under the stream's name and level parameters and
  must be `isDefEq` to the stream's (checked) type; each generated rule is
  annotated, resolved and typed at the environment holding the rule-less
  generated recursors.  What is stored is the generated family.
-/

namespace ConLeche

/-! ## The generator -/

/-- A field of a class's constructor, as the generator reads it:
ordinary, or recursive at class `cls` with a telescope of `tele` binders
(the inductive hypothesis's). -/
inductive ClassField where
  | ordinary
  | recursive (cls : Nat) (tele : Nat)
  deriving DecidableEq, Inhabited

/-- A class's constructor as the generator reads it (official's
`mk_rec_infos` shape): its DECLARED type at the class's levels and
parameters `tyD` — the minor premise's fields and conclusion, the rule's
fields — and the datum entry's WALKED telescope `tyN` (read back, over the
canonical parameters) — every inductive hypothesis's telescope and
indices (official: `whnf (infer_type u_i)`) — with the field count and
the fields' kinds. -/
structure ClassCtor where
  cv : ConstantVal
  nF : Nat
  kinds : List ClassField
  tyD : Expr
  tyN : Expr
  deriving Inhabited

/-- Close a telescope of `λ`s (`closeTelescope`'s twin). -/
def closeLams : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body => .lam dom ((closeLams bs (i + 1) body).abstract1 i 0) bm

/-- What generation reads: the block, the classes, the layout, the
constructors, the elimination level. -/
structure ClassGen where
  nP : Nat
  params : List Expr
  cls : List TargetMajor
  /-- per class, the former's type (its own levels instantiated) -/
  formerTys : List Expr
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  elim : Level
  /-- the generated prefix binders (`ClassGen.prefixBinders`), computed once -/
  pre : List (Expr × BinderMeta) := []

/-- The binder of an opened variable. -/
def classBinder (x : Expr) : Expr × BinderMeta := (x.fvarTypeD, default)

/-- The prefix variable of slot `s`. -/
def ClassGen.slotVar (g : ClassGen) (s : Nat) : Expr := .fvar (g.nP + s) (.sort .zero)

/-- Class `c`'s motive variable. -/
def ClassGen.motVar (g : ClassGen) (c : Nat) : Expr :=
  g.slotVar ((ClassRead.motiveSlot ⟨g.slots, []⟩ c).getD 0)

/-- Class `c`'s index telescope opened at `d`, and its major domain. -/
def ClassGen.major (g : ClassGen) (c : Nat) (d : Nat) : Option (List Expr × Expr) := do
  let ci := g.cls.getD c default
  let ty ← instPisWith ci.ds (g.formerTys.getD c default)
  let (ifs, _) ← openPisAtFvars ci.nIdx ty d
  pure (ifs, Expr.mkAppN (.const ci.ind ci.lvls) (ci.ds ++ ifs))

/-- Class `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`. -/
def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : Option Expr := do
  let (ifs, maj) ← g.major c d
  pure (closeTelescope (ifs.map classBinder) d (.forallE maj (.sort g.elim) default))

/-- The inductive hypothesis of a recursive field whose WALKED type is `w`
(`∀ a⃗, J E⃗ e⃗`, landing at class `t`), opened at `d`: its telescope and its
index arguments. -/
def ClassGen.ihParts (g : ClassGen) (t : Nat) (tele : Nat) (w : Expr) (d : Nat) :
    Option (List Expr × List Expr) := do
  let (xs, leaf) ← openPisAtFvars tele w d
  pure (xs, leaf.getAppArgs.drop (g.cls.getD t default).nPc)

/-- Constructor `x`'s minor premise type at depth `d`, of class `c`: its
declared fields, then per recursive field `f` (walked type `w`) the
inductive hypothesis `∀ a⃗, motive_t e⃗ (f a⃗)`, over the motive at the
declared result indices and the constructor applied. -/
def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) : Option Expr := do
  let ci := g.cls.getD c default
  let (fvs, res) ← openPisAtFvars x.nF x.tyD d
  let ws ← targetPiDomsWith fvs x.tyN
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let ihs ← (List.range recs.length).mapM fun l => do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let (xs, idx) ← g.ihParts t tele (ws.getD i default) e
    pure (closeTelescope (xs.map classBinder) e
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs])),
      (default : BinderMeta))
  let concl := Expr.mkAppN (g.motVar c)
    (res.getAppArgs.drop ci.nPc ++ [Expr.mkAppN (.const x.cv.name ci.lvls) (ci.ds ++ fvs)])
  pure (closeTelescope (fvs.map classBinder ++ ihs) d concl)

/-- The prefix binders (parameters, then every slot in the stream's
order). -/
def ClassGen.prefixBinders (g : ClassGen) : Option (List (Expr × BinderMeta)) := do
  let slotBs ← (List.range g.slots.length).mapM fun s => do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      pure ((← g.motiveTy c d), (default : BinderMeta))
    | .minor c C _ =>
      let x ← (g.ctors.getD c []).find? (·.cv.name == C)
      pure ((← g.minorTy c x d), (default : BinderMeta))
  pure (g.params.map classBinder ++ slotBs)

/-- **The generated recursor type** at class `c`. -/
def classGenRecTy (g : ClassGen) (c : Nat) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.major c rP
  let t : Expr := .fvar (rP + ifs.length) maj
  pure (closeTelescope (pre ++ ifs.map classBinder ++ [(maj, default)]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [t])))

/-- **The generated rule** of a recursor at class `c` for its constructor
`x`: `λ p⃗ (prefix) f⃗, minor f⃗ (λ a⃗, rec_t p⃗ (prefix) e⃗ (f a⃗))…`, the
callee `rec_t` the family's recursor at the landing class `t`
(`recOf`). -/
def classGenRule (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level) (c : Nat)
    (x : ClassCtor) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (s, _) ← (List.range g.slots.length).zip g.slots |>.find? fun (_, sl) =>
    match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false
  let (fvs, _) ← openPisAtFvars x.nF x.tyD rP
  let ws ← targetPiDomsWith fvs x.tyN
  let pvars := (List.range rP).map fun i => if i < g.nP then g.params.getD i default else
    g.slotVar (i - g.nP)
  let ihs ← (List.range x.nF).filterMapM fun i =>
    match x.kinds.getD i .ordinary with
    | .ordinary => some none
    | .recursive t tele => do
      let f := fvs.getD i default
      let (xs, idx) ← g.ihParts t tele (ws.getD i default) (rP + x.nF)
      let r ← recOf t
      pure (some (closeLams (xs.map classBinder) (rP + x.nF)
        (Expr.mkAppN (.const r rlvls) (pvars ++ idx ++ [Expr.mkAppN f xs]))))
  pure (closeLams (pre ++ fvs.map classBinder) 0 (Expr.mkAppN (g.slotVar s) (fvs ++ ihs)))

/-! ## The stage -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A minor premise's slot. -/
def ClassSlot.isMinor : ClassSlot → Bool
  | .minor .. => true
  | .motive _ => false

/-- The minor premise slot of class `c`'s constructor `C`: exactly one. -/
def classMinorSlot (rd : ClassRead) (c : Nat) (C : Name) : m (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap fun s =>
    match (rd.slots[s]? : Option ClassSlot) with
    | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
    | _ => none
  match hits with
  | [x] => pure x
  | _ => throw (.invalid s!"generated recursor: the recursors' prefix does not have exactly one \
      minor premise for {C} (official: invalid recursor)")

/-- **The minor premise's inductive hypotheses are the datum's recursive
fields**, one each (`ihs` the pre-pass's `(field, class)` pairs; `fvs` the
datum's opened fields from field `i` on): a field is RECURSIVE when its
walked type names a member of the block (the positivity check classifies
every such field as recursive or nested; the others are ordinary), and
then it has exactly one inductive hypothesis, an ordinary one none.
Returns the generator's kinds (a recursive field at its `ih`'s class, with
its walked telescope's length). -/
def classFieldsOf (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) :
    Nat → List Expr → m (List ClassField)
  | _, [] => pure []
  | i, f :: fs => do
    let w := f.fvarTypeD
    let k' ← match w.nestOcc p.memberNames 0 0, ihs.filter (·.1 == i) with
      | false, [] => pure ClassField.ordinary
      | true, [(_, t)] => pure (.recursive t w.piBinders.1.length)
      | _, _ =>
        throw (.invalid s!"generated recursor: the inductive hypotheses of {ctor}'s minor \
          premise are not its recursive fields (official: invalid recursor)")
    let ks' ← classFieldsOf p ctor ihs (i + 1) fs
    pure (k' :: ks')

/-- **Node agreement at one recursive field** (K.53′): at every entry
`E` of the constructor, field `i` (opened at the datum's variables `fvs`)
has the datum's telescope `tele`, the datum's leaf head and indices, and
a leaf class matching the inductive hypothesis's class `Mc` per component
(`targetK53`). -/
def classNodesAgree (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (leaf : Expr) (fvs : List Expr)
    (i : Nat) (ctor : Name) : List NestCtorNf → m Unit
  | [] => pure ()
  | e :: es => do
    let some f := ((targetPiDomsWith fvs e.ty).getD [])[i]?
      | throw (.invalid s!"generated recursor: a recorded normal form of {ctor} is too short")
    unless ← targetK53 ops env p formerTys Mc tele leaf f do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not land at its inductive \
        hypothesis's class at every node of the positivity check (official: invalid recursor)")
    classNodesAgree ops env p formerTys Mc tele leaf fvs i ctor es

/-- A walked field's leaf is headed by class `M`'s inductive. -/
def classLeafAt (M : TargetMajor) (leaf : Expr) : Bool :=
  match leaf.getAppFn with
  | .const I _ => I == M.ind
  | _ => false

/-- Node agreement at every recursive field of the datum (`ks` from field
`i` on). -/
def classFieldsAgree (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) :
    Nat → List ClassField → m Unit
  | _, [] => pure ()
  | i, .ordinary :: ks => classFieldsAgree ops env p formerTys Ms fvs ctor E (i + 1) ks
  | i, .recursive t tele :: ks => do
    let (teleB, leaf) ← unwrapOr ((fvs.getD i default).fvarTypeD.stripPis tele)
      (.internal "generated recursor: field telescope")
    unless classLeafAt (Ms.getD t default) leaf do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not end in its inductive \
        hypothesis's class (official: invalid recursor)")
    classNodesAgree ops env p formerTys (Ms.getD t default) teleB leaf fvs i ctor E
    classFieldsAgree ops env p formerTys Ms fvs ctor E (i + 1) ks

/-- **One constructor of class `c`, read for the generator**: its entries
`E` in the class's table (`M.nfs`), the first the DATUM; the minor
premise's inductive hypotheses against the datum's recursive fields
(`classFieldsOf`); node agreement at every entry (`classFieldsAgree`). -/
def classCtorOf (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (cA : ConstantVal × Nat) :
    m ClassCtor := do
  let E := (Ms.getD c default).nfs.filter (·.ctor == cA.1.name)
  let e0 ← unwrapOr E.head? (.internal s!"generated recursor: the constructor {cA.1.name} of a \
    class has no entry in the positivity check's table")
  let (_, ihs) ← classMinorSlot rd c cA.1.name
  let (fvs, _) ← unwrapOr (openPisAtFvars cA.2 e0.ty (p.nP + p.k))
    (.internal "generated recursor: datum telescope")
  let kinds ← classFieldsOf p cA.1.name ihs 0 fvs
  classFieldsAgree ops env p formerTys Ms fvs cA.1.name E 0 kinds
  let M := Ms.getD c default
  let tyD ← unwrapOr (instPisWith M.ds (targetCtorAt M cA.1))
    (.internal "generated recursor: constructor parameter telescope")
  pure ⟨cA.1, cA.2, kinds, tyD, e0.ty⟩

/-- Every constructor of class `c` (`classCtorOf`). -/
def classCtorsOf (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) :
    List (ConstantVal × Nat) → m (List ClassCtor)
  | [] => pure []
  | cA :: cs => do
    let x ← classCtorOf ops env p formerTys rd Ms c cA
    let xs ← classCtorsOf ops env p formerTys rd Ms c cs
    pure (x :: xs)

/-- Every class's constructors, from class `c` on. -/
def classesCtors (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) : Nat → List TargetMajor → m (List (List ClassCtor))
  | _, [] => pure []
  | c, M :: rest => do
    let xs ← classCtorsOf ops env p formerTys rd Ms c M.ctors
    let xss ← classesCtors ops env p formerTys rd Ms (c + 1) rest
    pure (xs :: xss)

/-- Every class checked as a major (`targetMajorOf`, `targetMajorPins`),
over the stream's first recursor's parameter openers `pfvs`. -/
def classMajors (ops : CheckerOps m) (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs : List Expr) :
    List ClassKey → m (List TargetMajor)
  | [] => pure []
  | key :: keys => do
    let M ← targetMajorOf fe p ctorsAs pfvs pfvs (Expr.mkAppN (.const key.ind key.lvls) key.ds)
    targetMajorPins ops fe.env p.nP M
    let Ms ← classMajors ops fe p ctorsAs pfvs keys
    pure (M :: Ms)

/-- Every class with its entries of the table `tbl` (`targetMajorNfs`). -/
def classesNfs (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) : List TargetMajor → m (List TargetMajor)
  | [] => pure []
  | M :: Ms => do
    let es ← targetMajorNfs ops env p formerTys M.pfvs M.lvls M.ds M.ctors tbl
    let rest ← classesNfs ops env p formerTys tbl Ms
    pure ({ M with nfs := es } :: rest)

/-- A class's former type: a member's own, an outside class's stored
former at the class's levels. -/
def classFormerTy (fe : FEnv) (cvTas : List ConstantVal) (M : TargetMajor) : m Expr :=
  match M.member with
  | some t => pure (cvTas.getD t default).type
  | none => match fe.find? M.ind with
    | some (.indInfo cv _) => pure (cv.type.instantiateLevelParams cv.levelParams M.lvls)
    | _ => throw (.internal "generated recursor: a class's former vanished")

/-- **One recursor's generated type, checked and compared**: the record's
member, rule prefix and major index are the generated ones; the generated
type is checked as a constant under the record's name and level
parameters (`checkConstantValF`) and must be `isDefEq` to the stream's
checked type `cvRi`.  Returns the generated constant (what is stored). -/
def classRecTyOk (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) : m ConstantVal := do
  let ci := g.cls.getD c default
  unless rc.tgt == ci.member.getD k do
    throw (.invalid "generated recursor: the recursor record's member is not its class's")
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    throw (.invalid "generated recursor: the recursor record's rule prefix or major index is \
      not the generated one")
  let gty ← unwrapOr (classGenRecTy g c) (.internal "generated recursor: recursor type")
  let cvG ← checkConstantValF ops fe { rc.cvR with type := gty }
  unless ← ops.isDefEq fe.env 0 cvRi.type cvG.type do
    throw (.invalid s!"generated recursor: the type of {rc.cvR.name} is not the generated one \
      (official: invalid recursor)")
  pure cvG

/-- Every recursor's generated type, pairwise with the stream's checked
types and the recursors' classes. -/
def classRecTysOk (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) :
    List RecShape → List ConstantVal → List Nat → m (List ConstantVal)
  | rc :: rcs, cvRi :: cvs, c :: cs => do
    let x ← classRecTyOk ops fe g k rc cvRi c
    let xs ← classRecTysOk ops fe g k rcs cvs cs
    pure (x :: xs)
  | [], _, _ => pure []
  | _, _, _ => throw (.internal "generated recursor: recursor list")

/-- **One generated rule, installed**: annotated, resolved and typed at the
rule-less recursors' environment `feR` (its level parameters the
recursor's), its λ-telescope over the prefix and the fields `n` long,
its λ-domains resolving at the constructors' environment `feT` and
annotated with the family's elimination datum `pw`.  Returns the
annotated rule (stored). -/
def classRuleOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (cvR : ConstantVal)
    (pw : PropWhen) (n : Nat) (gen : Expr) : m Expr := do
  unless gen.looseBVarsBounded 0 && !gen.hasFvar do
    throw (.internal s!"generated recursor: a rule of {cvR.name} is not closed")
  let genA ← ops.annotate feR.env 0 gen
  unless genA.allLevelParamsDefined cvR.levelParams do
    throw (.internal s!"generated recursor: a rule of {cvR.name} names an undeclared universe \
      parameter")
  unless w.resolve feR genA do
    throw (unresolvedConstsError s!"generated rule of {cvR.name}" genA)
  let _ ← ops.inferType feR.env 0 genA
  let (rbs, _) ← unwrapOr (genA.stripLams n)
    (.internal s!"generated recursor: a rule of {cvR.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  unless rbs.all (fun b => w.resolve feT b.1) do
    throw (unresolvedConstsError s!"the domains of a generated rule of {cvR.name}" genA)
  unless rbs.all (fun b => b.2.pw == pw) do
    throw (.internal s!"generated recursor: a rule of {cvR.name} does not annotate its \
      λ-binders with the family's elimination datum")
  pure genA

/-- A recursor's generated rules, one per constructor of its class. -/
def classRulesOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (pw : PropWhen) (c : Nat) :
    List ClassCtor → m (List Expr)
  | [] => pure []
  | x :: xs => do
    let gen ← unwrapOr (classGenRule g recOf (cvR.levelParams.map .param) c x)
      (.invalid s!"generated recursor: the rule of {x.cv.name} calls a class whose recursor the \
        stream omits (official: unknown constant)")
    let r ← classRuleOk ops w feT feR cvR pw (g.nP + g.slots.length + x.nF) gen
    let rs ← classRulesOk ops w feT feR g recOf cvR pw c xs
    pure (r :: rs)

/-- Every recursor's generated rules, at the rule-less recursors'
environment `feR`, with its class. -/
def classRecsRulesOk (ops : CheckerOps m) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (pw : PropWhen) :
    List ConstantVal → List Nat → m (List (ConstantVal × TargetMajor × List Expr))
  | cvG :: cvs, c :: cs => do
    let rhss ← classRulesOk ops w feT feR g recOf cvG pw c (g.ctors.getD c [])
    let xs ← classRecsRulesOk ops w feT feR g recOf pw cvs cs
    pure ((cvG, g.cls.getD c default, rhss) :: xs)
  | _, _ => pure []

/-- The stream's recursor constants, checked (`checkConstantValF`): what
the pre-pass reads and the generated types are compared with. -/
def classStreamRecs (ops : CheckerOps m) (fe : FEnv) : List RecShape → m (List ConstantVal)
  | [] => pure []
  | rc :: rcs => do
    let cv ← checkConstantValF ops fe rc.cvR
    let cvs ← classStreamRecs ops fe rcs
    pure (cv :: cvs)

/-- A class key moved to the block's canonical parameter variables
`params` (the pre-pass reads it over the stream recursor's own openers). -/
def classKeyCanon (params : List Expr) (k : ClassKey) : ClassKey :=
  { k with ds := k.ds.map (targetCanonParams params) }

/-- An inductive's parameter count as the pre-pass reads it: the block's
at a member, the stored `IndCaps`' otherwise. -/
def classNPcOf (p : BlockShape) (fe : FEnv) (I : Name) : Nat :=
  if p.memberNames.contains I then p.nP else
    match fe.find? I with
    | some (.indInfo _ caps) => caps.nparams
    | _ => 0

/-- The seeds: every OUTSIDE class in the positivity check's
representation (`nestSeedOf`), in order. -/
def classSeeds (ctx : NestCtx) (holes : List Expr) (Ms : List TargetMajor) :
    List (NestKey × Nat) :=
  Ms.filterMap fun M =>
    if M.member.isNone then some (nestSeedOf ctx holes M.ind M.lvls M.ds M.nPc) else none

/-- The recursor a call at class `t` names: the family's first recursor
at that class (`recCls` the pre-pass's reading, `cvGs` the generated
constants). -/
def classRecOf (recCls : List Nat) (cvGs : List ConstantVal) (t : Nat) : Option Name :=
  ((List.range cvGs.length).find? fun r => recCls.getD r 0 == t).map fun r =>
    (cvGs.getD r default).name

/-- The rule-less generated recursors consed onto the constructors'
environment `fe`. -/
def classFeR (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (fe : FEnv) : FEnv :=
  consBlockRecsBareF p 0 ((cvGs.zip recCls).map fun (cv, c) => (cv, (Ms.getD c default).nIdx)) fe

/-- **The generated recursor stage** (charter item 5, see the module
header), at the constructors' environment `fe`; the seeds walk at the
formers' environment `fe₁`/`env₁`, continuing the positivity check's
state `pos` after its root frame (the members' constructors, whose
entries the table holds already); `nestedBit` is the elimination guard's
container bit as the caller reads it (`blockNestedBit`), to which every
outside class adds.  Returns every recursor, generated, with its class
and its generated annotated rules (what the install stores). -/
def genRecCheck (so : ShadowOps m) (fe₁ : FEnv) (env₁ : Env) (fe : FEnv) (p : BlockShape)
    (nestedBit : Bool) (pos : NestState) (cvTas : List ConstantVal) (block : List ConstantInfo)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr)) := do
  targetRecPins p block
  let ops := so.opsAt fe
  -- the stream's recursor types, checked: the pre-pass reads them, the
  -- generated types are compared with them
  let cvRis ← classStreamRecs ops fe p.recs
  -- [UNVERIFIED] the pre-pass: the classes, the layout, each recursor's class
  let rd ← unwrapOr (classRead p.nP (classNPcOf p fe)
      ((p.recs.zip cvRis).map fun (rc, cv) => { rc with cvR := cv }))
    (.invalid "generated recursor: the recursor family is not of the generated shape \
      (official: invalid recursor)")
  -- the classes, each checked as a major over the block's canonical
  -- parameters (the generated prefix's); one per member
  let (ctx, holes) ← blockNestCtx p cvTas fe₁.find? env₁.consts
  let Ms ← classMajors ops fe p ctorsAs ctx.params (rd.classes.map (classKeyCanon ctx.params))
  unless (List.range p.k).all (fun t => (Ms.filter (·.member == some t)).length == 1) do
    throw (.invalid "generated recursor: the recursor family does not have exactly one class \
      per member (official: invalid recursor)")
  -- the elimination guard
  unless 0 < p.k do
    throw (.invalid "generated recursor: the block declares no family")
  if p.large && !blockLargeElimAllowed p (nestedBit || Ms.any (·.member.isNone)) then
    throw (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
      (official: elim_only_at_universe_zero)")
  -- the seeds, at the formers' environment: every class a node
  so.flush
  let st ← nestSeeds (so.opsAt fe₁) env₁ ctx (classSeeds ctx holes Ms) pos
  so.flush
  let formerTys := cvTas.map (·.type)
  let Ms ← classesNfs ops fe.env p formerTys st.ctorNfs.toList Ms
  -- per class and constructor: the datum, the inductive hypotheses, node agreement
  let ctors ← classesCtors ops fe.env p formerTys rd Ms 0 Ms
  unless (rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum do
    throw (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  -- generation
  let formerTysC ← Ms.mapM (classFormerTy fe cvTas)
  let elim := structElimLevel p.elim p.large
  let g0 : ClassGen := ⟨p.nP, ctx.params, Ms, formerTysC, rd.slots, ctors, elim, []⟩
  let pre ← unwrapOr g0.prefixBinders (.internal "generated recursor: recursor prefix")
  let g := { g0 with pre := pre }
  let cvGs ← classRecTysOk ops fe g p.k p.recs cvRis rd.recCls
  let feR := classFeR p Ms cvGs rd.recCls fe
  so.flush
  let out ← classRecsRulesOk (so.opsRuleR feR) so.walkers fe feR g
    (classRecOf rd.recCls cvGs) (Level.zeronessOf elim) cvGs rd.recCls
  so.flush
  pure out

end ConLeche
