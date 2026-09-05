import Setlec.Kernel.Core

/-!
# The direct simple-structure class: recognition

A **simple structure** is a non-recursive, single-constructor,
index-free inductive with a provably nonzero result sort — parameters
and dependent fields allowed.  Such a block needs no preprocessor
`_model` artifact: its set-theoretic model is the iterated dependent
pair over the field types (modeled by the retired `Setlec/Model/*`,
deleted at task #148 T7), so the kernel installs it *directly*, from
the reference checks alone.

This module holds the **pure** recognition layer.  It is a conservative
filter: a block that does not match falls through to the modeled path
unchanged, so a `false` here never costs a verdict.

The checks mirror what the reference kernels do when *adding* an
inductive declaration, restricted to this class (line numbers:
lean4lean `Lean4Lean/Inductive/Add.lean`, a line-by-line port of the
official `src/kernel/inductive/inductive.cpp`; nanoda
`checker/src/inductive.rs`):

* the type former's type is a `∀`-telescope of exactly `numParams`
  binders ending in a `Sort` — `checkInductiveTypes` (`Add.lean:60-116`,
  nanoda `check_inductive_spec_0th`, `inductive.rs:375`); *index-free* means the
  telescope ends there.
* the result level may be anything (task #175 W4c/O4, the user's
  ruling that every supported `.proj` is served directly): a provably
  `Prop` result (`isProp`) selects the squash-regime install — the
  official kernel's `Prop` escape hatch on the field-universe bound
  (`Add.lean:225`), projection entries only for the `Prop`-prefix of
  the fields (a data field of a `Prop` structure is not projectable,
  `infer_proj`'s restriction), K for the fieldless case.
* the constructor's type is a `∀`-telescope whose first `numParams`
  binder domains are the type former's, ending in the type former
  applied to **exactly** those parameters at the declaration's own
  level parameters — `checkConstructors` (`Add.lean:218-223`) and
  `isValidIndAppIdx` (`Add.lean:157-165`, nanoda `is_valid_ind_app`, `inductive.rs:711`).
* no recursive occurrence: every binder domain of the constructor
  resolves already in the *pre-block* environment, which subsumes
  `checkPositivity`/`hasIndOcc` (`Add.lean:184-199`) for this class and
  is exactly what the model construction needs (the type former's value
  is defined from the field types' interpretations in the old
  environment).
* the recursor's type is **exactly** the generated shape
  (`Add.lean:477-483`): params → one motive → one minor → no indices →
  major → `motive t`, with the motive dependent
  (`∀ (t : T p⃗), Sort ℓ`, `Add.lean:326`), the minor the constructor's
  field telescope ending in `motive (C p⃗ f⃗)` (`Add.lean:384-388`), and
  either a fresh elimination level parameter in front
  (`getRecLevelParams`, `Add.lean:416-417`) — the large eliminator
  (`isLargeEliminator`, `Add.lean:257-259`) — or, for a propositional
  structure with a non-`Prop` field, the small eliminator (motive into
  `Prop`, the block's own level parameters).  Both shapes are
  recognised (`DirectParts.large`).
* the single rule's right-hand side is
  `λ p⃗ motive minor f⃗, minor f⃗` (`mkRecRules`, `Add.lean:441-447`).

The per-field universe bound (`Add.lean:225-228`,
nanoda `check_ctor`, `inductive.rs:809`) and the definitional pins of the
recursor's binder domains against the constructor's need inference and
`isDefEq`, so they live in the monadic `checkDirectStruct`
(`Setlec/Kernel/Checker.lean`).

The direct path installs **native tower-backed projection entries**
(`checkDirectProj`, task #175 wiring): `.proj T i` nodes are typed by
the entry's stored type and reduced by the structural rule, and the
model reads them by the uniform tower projection.  The capability
record (`directCaps`) claims structure eta (the tower's own law),
unit-likeness for the fieldless case, and K for the fieldless
propositional case.
-/

namespace Setlec

/-- The type former applied to its parameter variables, `bvar` indices
offset by `o` (the number of binders crossed since the parameters). -/
def directFam (T : Name) (lps : List Name) (nP o : Nat) : Expr :=
  Expr.mkAppN (.const T (lps.map .param))
    ((List.range nP).map fun k => Expr.bvar (o + nP - 1 - k))

/-- The constructor applied to the parameter and field variables, as
spelled inside the recursor's minor premise (parameters sit above the
motive binder). -/
def directCtorSpine (C : Name) (lps : List Name) (nP nF : Nat) : Expr :=
  Expr.mkAppN (.const C (lps.map .param))
    (((List.range nP).map fun i => Expr.bvar (nF + nP - i)) ++
     (List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- The recursor rule's right-hand side body: the minor premise applied
to the field variables. -/
def directRuleBody (nF : Nat) : Expr :=
  Expr.mkAppN (.bvar nF) ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- The pieces of a recognised simple-structure block. -/
structure DirectParts where
  /-- the type former -/
  cvT : ConstantVal
  /-- the single constructor -/
  cvC : ConstantVal
  /-- parameter count -/
  nP : Nat
  /-- field count -/
  nF : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the structure's result sort -/
  resSort : Level
  /-- the single rule's right-hand side (as exported) -/
  rhs : Expr
  /-- **large eliminator** (task #175 W4c/O4): the recursor carries a
  fresh elimination level parameter in front and its motive lands in
  `Sort elim`; `false` is the small eliminator (`motive : T p⃗ → Prop`,
  the recursor's level parameters are the block's own) that Lean
  generates for a propositional structure with a non-`Prop` field. -/
  large : Bool
  /-- **propositional result** (task #175 W4c/O4): the result sort is
  provably `Prop` (`Level.isEquiv resSort .zero`).  Selects the
  squash-regime install: no field-universe bound (the official
  kernel's `Prop` escape hatch), entries only for the `Prop`-prefix of
  the fields, K for the fieldless case. -/
  isProp : Bool
  deriving Repr

/-- The *shape* facts the model reads off the stored (annotated)
types — everything that annotation cannot change, checked on both the
raw block (recognition) and the annotated constants (install).

The binder-domain correspondences are deliberately **not** here: the
reference kernels compare the constructor's parameter domains to the
type former's by `isDefEq` (`Add.lean:220-222`) and build the
recursor's telescope from `whnf`-peeled domains (`Add.lean:79-95`), so
a syntactic pin would wrongly reject; `checkDirectStruct` pins them
definitionally over the opened telescopes instead. -/
def directShape (T C : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nF : Nat) (tty cty rty : Expr) : Bool :=
  match tty.stripPis nP, cty.stripPis (nP + nF), rty.stripPis (nP + 3) with
  | some (_, .sort _), some (_, cbody), some (rbs, rbody) =>
    cbody == directFam T lps nP nF &&
    rbody == Expr.app (.bvar 2) (.bvar 0) &&
    (match rbs[nP]? with
     | some (_, .forallE _ mmaj (.sort s') _, _) =>
       -- the motive's codomain: `Sort elim` for the large eliminator,
       -- `Prop` for the small one (task #175 W4c/O4)
       (if large then s' == .param elim else s' == .zero) &&
         mmaj == directFam T lps nP 0
     | _ => false) &&
    (match rbs[nP + 1]? with
     | some (_, mindom, _) =>
       match mindom.stripPis nF with
       | some (_, mbody) =>
         mbody == Expr.app (.bvar nF) (directCtorSpine C lps nP nF)
       | none => false
     | none => false) &&
    (match rbs[nP + 2]? with
     | some (_, majdom, _) => majdom == directFam T lps nP 2
     | none => false)
  | _, _, _ => false

/-- Recognise a direct simple-structure block (see the module docs).
`none` means "not this class" — the caller falls through to the modeled
path, so this is never an error source. -/
def directPartsCore? (block : List ConstantInfo) : Option DirectParts :=
  match block with
  | [.indInfo cvT _, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] =>
    let T := cvT.name
    let C := cvC.name
    let lps := cvT.levelParams
    -- the shape facts common to both eliminator shapes
    if cvR.name == T.str "rec" && cvC.levelParams == lps &&
        reservedBasisNames.contains T == false &&
        reservedBasisNames.contains C == false &&
        reservedBasisNames.contains cvR.name == false &&
        mI == nP + 2 && rP == nP + 2 &&
        rule.ctor == C && rule.nfields == nF &&
        (match rule.rhs.stripLams (nP + 2 + nF) with
         | some (_, rbody) => rbody == directRuleBody nF
         | none => false) then
      match cvT.type.stripPis nP with
      | some (_, .sort s) =>
        let isProp := Level.isEquiv s .zero == some true
        -- the large eliminator: a fresh elimination level parameter in
        -- front of the block's own; else the small eliminator at the
        -- block's own level parameters (task #175 W4c/O4)
        let large? : Option Name :=
          match cvR.levelParams with
          | elim :: relps =>
            if relps == lps && !lps.contains elim &&
                directShape T C lps elim true nP nF cvT.type cvC.type
                  cvR.type then
              some elim
            else none
          | [] => none
        match large? with
        | some elim =>
          some ⟨cvT, cvC, nP, nF, cvR, elim, s, rule.rhs, true, isProp⟩
        | none =>
          if cvR.levelParams == lps &&
              directShape T C lps .anonymous false nP nF cvT.type cvC.type
                cvR.type then
            some ⟨cvT, cvC, nP, nF, cvR, .anonymous, s, rule.rhs, false,
              isProp⟩
          else none
      | _ => none
    else none
  | _ => none

/-- The parameter spine of the generated projection types, spelled at
the frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar
(nP - k)` (the `instPisAtLift` walk lowers each entry once per
substitution step, landing them at `bvar (nP - 1 - k)` under the
subject binder). -/
def directProjPs (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (nP - k)

/-- The `j`-th earlier-projection substitute in a generated projection
type: `T.proj.j p⃗ t`, at the same final frame. -/
def directProjArg (T : Name) (lps : List Name) (nP j : Nat) : Expr :=
  Expr.mkAppN (.const (projFnName T j) (lps.map .param))
    (directProjPs nP ++ [Expr.bvar 0])

/-- The constructor telescope peeled at the parameters and the first
`i` earlier-projection substitutes —
`Expr.instPisAtLift (directProjPs nP ++ (List.range i).map
(directProjArg T lps nP)) cty` (`directProjResid_eq`), but computed
*incrementally*: step `i → i + 1` is a single `instantiate1Lift`, so a
projection loop that threads this residual does one telescope pass per
projection instead of redoing all earlier substitutions. -/
def directProjResid (T : Name) (lps : List Name) (nP : Nat)
    (cty : Expr) : Nat → Option Expr
  | 0 => Expr.instPisAtLift (directProjPs nP) cty
  | i + 1 => (directProjResid T lps nP cty i).bind
      (Expr.instPisAtLift [directProjArg T lps nP i])

/-- The projection type for field `i` read off the peeled residual
(`directProjTy_eq_resid`: at `directProjResid T lps nP cty i` this is
exactly `directProjTy`). -/
def directProjTyR (T : Name) (lps : List Name) (nP nF i : Nat)
    (tty : Expr) : Option Expr → Option Expr
  | some (.forallE _ fdom _ _) =>
    if i < nF then
      Expr.replacePiBody nP tty
        (.forallE (.str .anonymous "t") (directFam T lps nP 0) fdom
          ⟨.default, .never⟩)
    else none
  | _ => none

/-- The projection function's generated type for field `i`:

    ∀ p⃗ (t : T p⃗), F_i[p⃗ ; f_j := T.proj.j p⃗ t  (j < i)]

read off the constructor telescope — the direct-recognition counterpart
of the modeled path's `T._model.proj_i` artifact type. -/
def directProjTy (T : Name) (lps : List Name) (nP nF i : Nat)
    (tty cty : Expr) : Option Expr :=
  let args := directProjPs nP ++ (List.range i).map (directProjArg T lps nP)
  directProjTyR T lps nP nF i tty (Expr.instPisAtLift args cty)

/-- The `j`-th earlier-field substitute in a **tower entry's**
generated type (task #175 wiring): the first-class node `t.j`
(`.proj T j` of the subject), at `directProjArg`'s frame (subject
`t = bvar 0`).  No `projFnName` chain — each field's entry stands
alone, which is what makes O4's per-field entry branch real. -/
def directProjArgP (T : Name) (j : Nat) : Expr :=
  Expr.proj T j (Expr.bvar 0)

/-- `directProjResid` in the `.proj`-node spelling: the constructor
telescope peeled at the parameters and the first `i` subject
projections, threaded incrementally (step `i → i + 1` is a single
`instantiate1Lift`). -/
def directProjResidP (T : Name) (nP : Nat) (cty : Expr) : Nat → Option Expr
  | 0 => Expr.instPisAtLift (directProjPs nP) cty
  | i + 1 => (directProjResidP T nP cty i).bind
      (Expr.instPisAtLift [directProjArgP T i])

/-- The tower entry's projection type for field `i` —
`∀ p⃗ (t : T p⃗), F_i[p⃗ ; f_j := t.j  (j < i)]`: `directProjTy` with
earlier fields spelled as `.proj` nodes (the native-entry `ty`
discipline recorded at `ProjEntry`). -/
def directProjTyP (T : Name) (lps : List Name) (nP nF i : Nat)
    (tty cty : Expr) : Option Expr :=
  let args := directProjPs nP ++ (List.range i).map (directProjArgP T)
  directProjTyR T lps nP nF i tty (Expr.instPisAtLift args cty)

/-- Every `.proj s j` node of `e` satisfies `P s j` (not through fvar
type annotations). -/
def Expr.projNodesOk (P : Name → Nat → Bool) : Expr → Bool
  | .proj s j e => P s j && projNodesOk P e
  | .app f a => projNodesOk P f && projNodesOk P a
  | .lam _ ty b _ => projNodesOk P ty && projNodesOk P b
  | .forallE _ ty b _ => projNodesOk P ty && projNodesOk P b
  | .letE _ t v b => projNodesOk P t && projNodesOk P v && projNodesOk P b
  | _ => true

/-- **The projection guard levels** (task #175 W4c/O4): for field `i`,
its own sort joined with the sorts of **every** earlier field — the
level a `.proj T i` use on a `Prop`-declared structure must
instantiate to `Prop`.  `sorts` are the fields' sorts in order
(`checkDirectFieldSorts`).

The official `infer_proj` joins only the earlier fields *used by a
later field* (`has_loose_bvars(binding_body(r))`).  The join over all
earlier fields is a strict restriction (a recorded finding, task #175
W4c P3 module 7): at a squash instance the structure's members are
one point, so a field's projection law needs its type at the
all-point prefix to be inhabited, which the coarse guard gives by
proof irrelevance of every earlier field, while the official guard
additionally needs the type's *invariance* in the unused earlier
slots — a syntactic-to-semantic transport (`Expr.hasLooseBVar`
against the reading's environment) the battery does not carry.  The
two guards differ only on a `Prop`-declared structure with a data
field that no later field mentions, projected at a later `Prop`
field; the init-full census records no such use. -/
def directProjGuards (_cty : Expr) (_nP nF : Nat) (sorts : List Level) :
    List Level :=
  (List.range nF).map fun i =>
    (List.range i).foldl
      (fun acc j => .max acc (sorts.getD j .zero))
      (sorts.getD i .zero)

/-- **The entry decision of a projection slot** (task #175 W4c/O4), a
function of the block's input data alone (the agreement floor reads
nothing a core computes): every field of a non-propositional
structure, and of a propositional structure with the large eliminator
— Lean generates it exactly when every field is a proposition, which
`checkDirectFieldSorts` re-checks; at a propositional structure with
the small eliminator (some field is data) the **first field only**:
the squash model reads the structure's members as the point, so a
field's projection law needs the field's type not to depend on the
earlier fields' values, which the first field's cannot (P3 module 5
records the restriction; widening to every field whose type mentions
no earlier field needs the annotation pass's variable-preservation
lemma, not yet in the battery).  A skipped slot is a fall-through,
never a verdict. -/
def directProjSlotOk (isProp large : Bool) (i : Nat) : Bool :=
  !isProp || large || i == 0

/-- **The entry decisions of a recognised block**, one per field,
computed on the block's RAW types (the agreement floor's currency:
input data, nothing a core computed) — the annotated types' generated
projection type can only mention *fewer* earlier fields (annotation
zeta-reduces `let`s and adds no field variable), and an annotated
entry type that still mentions a data field of a propositional
structure fails its own inference, which declines the block. -/
def directProjSlots (p : DirectParts) : List Bool :=
  (List.range p.nF).map fun i =>
    match directProjTyP p.cvT.name p.cvT.levelParams p.nP p.nF i p.cvT.type
        p.cvC.type with
    | some _ => directProjSlotOk p.isProp p.large i
    | none => false

/-- **Non-recursive**: every binder domain of the constructor already
resolves in the *pre-block* environment.  This subsumes the reference
positivity check (`checkPositivity`/`hasIndOcc`, lean4lean
`Inductive/Add.lean:184-199`) for a single-inductive block, and it is
exactly what the model construction needs — the type former's value is
built from the field types' interpretations in the environment *before*
the block, so a self-reference would make it circular. -/
def directNonRec (env : Env) (p : DirectParts) : Bool :=
  match p.cvC.type.stripPis (p.nP + p.nF) with
  | some (cbs, _) => cbs.all fun b => b.2.1.constsResolve env
  | none => false

/-- Recognise a direct simple-structure block against an environment:
`directPartsCore?` and non-recursiveness.  **Priority gate** (task
#175 W4c, the user's ruling that every supported `.proj` is served by
a direct-installed model): every recognised block installs directly,
whether or not the stream carries `_model` artifacts for it — those
artifacts are then ordinary, unconsumed declarations.  The modeled
path keeps the blocks recognition rejects (recursive, indexed,
mutual, multi-constructor) and carries no projection machinery for
them.  (The former master switch `directStructsEnabled` and the
artifact-absence conjunct `directNoModel` are gone with the flip.) -/
def directParts? (env : Env) (block : List ConstantInfo) :
    Option DirectParts :=
  match directPartsCore? block with
  | some p => if directNonRec env p then some p else none
  | none => none

end Setlec
