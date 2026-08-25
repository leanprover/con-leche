import Setlec.Kernel.Core

/-!
# The direct simple-structure class: recognition

A **simple structure** is a non-recursive, single-constructor,
index-free inductive with a provably nonzero result sort — parameters
and dependent fields allowed.  Such a block needs no preprocessor
`_model` artifact: its set-theoretic model is the iterated dependent
pair over the field types (`Setlec/Model/DirectTower.lean`), so the
kernel installs it *directly*, from the reference checks alone.

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
* the result level is `isNeverZero` (`Add.lean:101`); we **require** it
  (see `DESIGN.md`, "Direct install of simple structures": the class is
  narrowed to non-`Prop` structures so that `sigmaSet`'s `Prop`
  collapse — which breaks `proj_i (mk f⃗) = f_i` for a `Prop` structure
  with data fields — never arises).  A `Prop` structure simply stays on
  the modeled path.
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
  a fresh elimination level parameter in front (`getRecLevelParams`,
  `Add.lean:416-417`) — the large eliminator every nonzero-sorted
  structure has (`isLargeEliminator`, `Add.lean:257-259`).
* the single rule's right-hand side is
  `λ p⃗ motive minor f⃗, minor f⃗` (`mkRecRules`, `Add.lean:441-447`).

The per-field universe bound (`Add.lean:225-228`,
nanoda `check_ctor`, `inductive.rs:809`) and the definitional pins of the
recursor's binder domains against the constructor's need inference and
`isDefEq`, so they live in the monadic `checkDirectStruct`
(`Setlec/Kernel/Checker.lean`).

The direct path **does** install real projection *functions* — a
degenerate recursor per field, stored under `projFnName T i`, the same
slot family and same consumer as the modeled path's `checkProjFn`, so
`.proj` nodes annotate through `annotateProjElim` exactly as on a
modeled structure.  The recursor-elimination *template* fallback
cannot serve this class at all: its motive is constant in the
eliminated variable, so a dependent field's projection does not
typecheck through it (DESIGN.md, "Projections compose with the existing
table").

The `k` flag is `false` for this class by construction (`isKTarget`
requires a `Prop` result, `Add.lean:289-296`).  Structure eta and the
unit-like law are *not* claimed either, for a reason that has nothing
to do with the projections: both are frame-relative laws that the
constructed values cannot discharge without a fit-relocation lemma that
does not exist yet (DESIGN.md, "The two frame-relative capabilities").
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
  /-- the recursor's fresh elimination level parameter -/
  elim : Name
  /-- the structure's result sort -/
  resSort : Level
  /-- the single rule's right-hand side (as exported) -/
  rhs : Expr
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
def directShape (T C : Name) (lps : List Name) (elim : Name)
    (nP nF : Nat) (tty cty rty : Expr) : Bool :=
  match tty.stripPis nP, cty.stripPis (nP + nF), rty.stripPis (nP + 3) with
  | some (_, .sort s), some (_, cbody), some (rbs, rbody) =>
    s.isNonZero && cbody == directFam T lps nP nF &&
    rbody == Expr.app (.bvar 2) (.bvar 0) &&
    (match rbs[nP]? with
     | some (_, .forallE _ mmaj (.sort (.param e')) _, _) =>
       e' == elim && mmaj == directFam T lps nP 0
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
    match cvR.levelParams with
    | elim :: relps =>
      if cvR.name == T.str "rec" && relps == lps && !lps.contains elim &&
          cvC.levelParams == lps &&
          reservedBasisNames.contains T == false &&
          reservedBasisNames.contains C == false &&
          reservedBasisNames.contains cvR.name == false &&
          mI == nP + 2 && rP == nP + 2 &&
          rule.ctor == C && rule.nfields == nF &&
          directShape T C lps elim nP nF cvT.type cvC.type cvR.type &&
          (match rule.rhs.stripLams (nP + 2 + nF) with
           | some (_, rbody) => rbody == directRuleBody nF
           | none => false) then
        match cvT.type.stripPis nP with
        | some (_, .sort s) =>
          some ⟨cvT, cvC, nP, nF, cvR, elim, s, rule.rhs⟩
        | _ => none
      else none
    | [] => none
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
          ⟨.default⟩)
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

/-- **No usable artifact**: none of the block's `_model` companions is
stored.  See DESIGN.md, "Direct install of simple structures": the
direct path is the *artifact-free* route, and it defers to the modeled
path whenever the preprocessor's model is available, so that streams
carrying artifacts keep every capability (notably structure eta, whose
environment invariant is spelled in `_model` names) and every verdict
they have today. -/
def directNoModel (env : Env) (p : DirectParts) : Bool :=
  (env.find? (p.cvT.name.str "_model")).isNone &&
  (env.find? (p.cvC.name.str "_model")).isNone &&
  (env.find? (p.cvR.name.str "_model")).isNone &&
  (List.range p.nF).all fun j =>
    (env.find? (projModelName p.cvT.name j)).isNone

/-- Recognise a direct simple-structure block against an environment
(`directPartsCore?`, non-recursiveness, and artifact absence). -/
def directParts? (env : Env) (block : List ConstantInfo) :
    Option DirectParts :=
  match directPartsCore? block with
  | some p =>
    if directNonRec env p && directNoModel env p then some p else none
  | none => none

end Setlec
