module

public import ConLeche.Kernel.Install

@[expose] public section

/-!
# The ι equations, read off a recursor's own type (task #622)

A recursor's rule says how the recursor computes on a constructor: applied to its rule prefix
(parameters, motives, minor premises), the indices and the constructor applied to its parameters
and fields, it is the rule's right-hand side applied to the prefix and the fields.  As a
proposition:

    ∀ (prefix) (fields), @Eq.{u} (motive idx (C.{us} params fields))
      (rec prefix idx (C.{us} params fields)) (rhs prefix fields)

Two readings of that equation meet here.

* **The statement's** (`iotaEqOf`): everything is read off the recursor's own type.  The rule
  `i` of the recursor's rules reads the `i`-th minor premise of the motive its type's body
  applies (`minorsOf`, the prefix binders whose conclusion that motive heads, in order): the
  fields are the minor's first `nfields` binders (the induction hypotheses after them are not
  quantified), the indices are its conclusion's leading arguments, and the constructor —
  the rule's — is used at the levels and parameters of the major premise's type
  (`C.{us} params is` with the `is` the index variables).  No constructor is looked up: what
  `IsModel` (`ConLeche/IsModel.lean`) says of a recursor is said by the recursor alone.
* **The proofs'** (`iotaEqAt`): the fields' domains and the indices come from the constructor's
  stored type, instantiated at the rule's levels and parameters (`RecRule.ctorLevels`,
  `RecRule.iotaParams`, which read the firing mode the install computed).  The model the
  invariant carries satisfies these (`ConLeche.ruleEqs`, `Model.rule_eqs`).

**The checker's rule** (`recReadsOk`, run on every recursor an inductive block installs) makes
them one equation: the minor premise is found and readable, and its parts are the constructor's
— the indices, the levels and the parameters syntactically, the fields' domains syntactically up
to equivalent universe levels (`Expr.lvlEq`) and up to Lean's type annotations (`annEq`).
Lean's kernel builds every local of an inductive declaration through `mk_local_decl`
(`src/kernel/inductive.cpp`), which applies `consume_type_annotations`: `optParam α d`,
`autoParam α s`, `outParam α`, `semiOutParam α` become `α`, repeatedly, at the head of a
binder's domain.  So a stored recursor's minor premise has the constructor's field domains with
those annotations consumed, and its parameters the inductive's.  Lean consumes them by name;
here an annotation is consumed only where the constant is stored as the identity on its type
argument, the way the prelude defines it (`annIdent`: `fun α => α`, resp. `fun α _ => α`), and
only in a rule that fires at the recursor's own parameters whose parameter domains are the
constructor's up to the same consumption (`paramsAnnEq`): the meaning of the consumption — the
annotation is the identity on a type — is read in the constructor's own telescope, which the
recursor's parameters must therefore fit.  A recursor that does not read is rejected: Lean
accepts it when its type is definitionally the generated one, but no stream Lean writes has one
(measured on Init, Std, Lean, Mathlib and the Stacks project).
-/

namespace ConLeche

/-- The sort level of a recursor's motive: the motive application `body`
(under the rule prefix `pre`, the `nIdx` indices and the major) has a
prefix variable as its head, and that binder's domain ends in `Sort u`. -/
def motiveLevel? (pre : List Expr) (nIdx : Nat) (body : Expr) : Option Level :=
  match body.getAppFn with
  | .bvar k =>
    if nIdx + 1 ≤ k ∧ k < nIdx + 1 + pre.length then
      match (pre.getD (pre.length - 1 - (k - (nIdx + 1))) default).piResult with
      | .sort u => some u
      | _ => none
    else none
  | _ => none

/-- The levels a recursor rule's constructor is used at, over the
recursor's own level parameters: the rule's recorded levels where it
records them (a nested or a quotient rule), else the constructor's
own parameters, which are the recursor's. -/
def RecRule.ctorLevels (rl : RecRule) (ctorLps : List Name) : List Level :=
  match rl.fire with
  | .nested lvls _ => lvls
  | .levels lvls => lvls
  | .plain => ctorLps.map .param

/-- The parameters a recursor rule applies its constructor to, in the rule prefix's context
(`rP` binders): a nested rule's recorded pins, else the prefix's first `cnP` variables (as many
as the prefix has: `iotaPartsAt` asks for `cnP` of them). -/
def RecRule.iotaParams (rl : RecRule) (rP cnP : Nat) : List Expr :=
  match rl.fire with
  | .nested _ pins => pins
  | _ => (List.range (min cnP rP)).map fun i => .bvar (rP - 1 - i)

/-- **A recursor's frame**: its rule prefix (the first `rP` binders of its type), the domains of
the `mI - rP` index binders and the major's, the body after them, and the sort level of the
motive the body applies. -/
def iotaFrame (cv : ConstantVal) (mI rP : Nat) :
    Option (List Expr × List Expr × Expr × Level) := do
  let (pre, rest) ← cv.type.stripPis rP
  let (doms, body) ← rest.stripPis (mI - rP + 1)
  let u ← motiveLevel? pre (mI - rP) body
  pure (pre, doms, body, u)

/-- **The parts a rule's ι equation is built from**: the fields' domains (in the context of the
rule prefix and the earlier fields), the indices (in the context of the prefix and the fields),
the constructor's levels and its parameters (in the context of the prefix). -/
structure IotaParts where
  fieldDoms : List Expr
  idx : List Expr
  us : List Level
  params : List Expr

/-- **A rule's ι equation from its parts**, under the recursor's rule prefix `pre` and its
body `body` (the motive at the indices and the major, `u` the motive's sort level):

    ∀ (pre) (fields : fieldDoms), @Eq.{u} (body[idx, major]) (rec pre idx major) (rhs pre fields)

with `major := C.{us} params fields`. -/
def iotaEqMk (cv : ConstantVal) (rP nIdx : Nat) (pre : List Expr) (body : Expr) (u : Level)
    (rl : RecRule) (pt : IotaParts) : Expr :=
  let nF := rl.nfields
  let xs := (List.range rP).map fun i => Expr.bvar (rP + nF - 1 - i)
  let fs := (List.range nF).map fun j => Expr.bvar (nF - 1 - j)
  let major := Expr.mkAppN (.const rl.ctor pt.us) (pt.params.map (·.liftLooseBVars nF 0) ++ fs)
  let lhs := Expr.mkAppN (.const cv.name (cv.levelParams.map .param)) (xs ++ pt.idx ++ [major])
  let rhs := Expr.mkAppN rl.rhs (xs ++ fs)
  let ty := (body.liftLooseBVars nF (nIdx + 1)).instantiateLift (major :: pt.idx.reverse)
  (pre ++ pt.fieldDoms).foldr .forallE (.app (.app (.app (.const eqName [u]) ty) lhs) rhs)

/-! ## The proofs' reading: through the constructor -/

/-- **A rule's parts, read through the constructor `cvj`** (with `cnP` parameters): its type at
the rule's levels, instantiated at the rule's parameters; the fields' domains are its next
`nfields` binders, the indices its conclusion's arguments behind the parameters.  `none` where
the constants do not have this shape. -/
def iotaPartsAt (cvj : ConstantVal) (cnP : Nat) (mI rP : Nat) (rl : RecRule) :
    Option IotaParts := do
  let lvls := rl.ctorLevels cvj.levelParams
  let params := rl.iotaParams rP cnP
  let (_, ctorBody) ← (cvj.type.instantiateLevelParams cvj.levelParams lvls).stripPis cnP
  let (fieldDoms, concl) ← (ctorBody.instantiateLift params.reverse).stripPis rl.nfields
  let indices := concl.getAppArgs.drop cnP
  guard (params.length = cnP ∧ rP ≤ mI ∧ indices.length = mI - rP)
  pure ⟨fieldDoms, indices, lvls, params⟩

/-- **A recursor rule's ι equation, through its constructor** (the proofs' reading): for the
recursor `cv` (major position `mI`, rule prefix `rP`), its rule `rl` and the constructor
constant `cvj` (with `cnP` parameters) the rule names, at the recursor's own level parameters.
`params` are the constructor's parameters in the prefix context: the recursor's leading
arguments, or a nested rule's recorded instantiations; the field binders are the constructor's,
at those parameters; the indices are the arguments of the constructor type's conclusion behind
its parameters. -/
def iotaEqAt (cvj : ConstantVal) (cnP : Nat) (cv : ConstantVal) (mI rP : Nat)
    (rl : RecRule) : Option Expr := do
  let (pre, _, body, u) ← iotaFrame cv mI rP
  let pt ← iotaPartsAt cvj cnP mI rP rl
  pure (iotaEqMk cv rP (mI - rP) pre body u rl pt)

/-! ## The statement's reading: off the recursor's own type -/

/-- A `∀`-telescope's binder count and its body. -/
def Expr.piTele : Expr → Nat × Expr
  | .forallE _ b => ((Expr.piTele b).1 + 1, (Expr.piTele b).2)
  | e => (0, e)

/-- **The minor premises of the motive at prefix position `mot`**: the positions of the prefix
binders whose conclusion (behind all their `∀`s) is headed by that motive, in order. -/
def minorsOf (pre : List Expr) (mot : Nat) : List Nat :=
  (List.range pre.length).filter fun q =>
    match ((pre.getD q default).piTele.2).getAppFn with
    | .bvar m => decide (mot < q) && m == (pre.getD q default).piTele.1 + (q - 1 - mot)
    | _ => false

/-- **A rule's parts, read off the recursor's own type** (the statement's reading): the rule `i`
reads the `i`-th minor premise of the motive the body applies, at prefix position `q`.  Its
first `nfields` binders are the fields (lifted past the later prefix binders); its conclusion's
first `mI - rP` arguments are the indices (behind the induction hypotheses, which they do not
mention, and lifted the same way).  The constructor is used at the levels `us` and the
parameters of the major premise's type `C'.{us} params is` (the `is` the index variables, which
the parameters do not mention). -/
def iotaPartsOf (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Option IotaParts := do
  let nF := rl.nfields
  let nIdx := mI - rP
  let (pre, doms, body, _) ← iotaFrame cv mI rP
  let .bvar k := body.getAppFn | none
  let q ← (minorsOf pre (rP + nIdx - k))[i]?
  let (fd, inner) ← (pre.getD q default).stripPis nF
  let .const _ us := (doms.getD nIdx default).getAppFn | none
  let args := (doms.getD nIdx default).getAppArgs
  pure ⟨fd.mapIdx (fun j d => d.liftLooseBVars (rP - q) j),
    (inner.piTele.2.getAppArgs.take nIdx).map
      (fun a => (a.dropVars inner.piTele.1).liftLooseBVars (rP - q) nF),
    us, (args.take (args.length - nIdx)).map (Expr.dropVars nIdx)⟩

/-- **A recursor's rule `i`'s ι equation, read off the recursor's own type** (see the module
docstring). -/
def iotaEqOf (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Option Expr := do
  let (pre, _, body, u) ← iotaFrame cv mI rP
  let pt ← iotaPartsOf cv mI rP i rl
  pure (iotaEqMk cv rP (mI - rP) pre body u rl pt)

/-! ## The checker's rule: the two readings are one -/

/-- **Equal up to equivalent universe levels**: the same term, each `Sort` and constant at
levels `Level.isEquiv` decides equal. -/
def Expr.lvlEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i t, .fvar j t' => i == j && t == t'
  | .sort u, .sort v => Level.isEquiv u v == some true
  | .const n us, .const m vs => n == m && Level.isEquivList us vs == some true
  | .app f a, .app g b => Expr.lvlEq f g && Expr.lvlEq a b
  | .lam t b, .lam t' b' => Expr.lvlEq t t' && Expr.lvlEq b b'
  | .forallE t b, .forallE t' b' => Expr.lvlEq t t' && Expr.lvlEq b b'
  | .letE t v b, .letE t' v' b' => Expr.lvlEq t t' && Expr.lvlEq v v' && Expr.lvlEq b b'
  | .lit l, .lit l' => l == l'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && Expr.lvlEq e e'
  | _, _ => false

/-- The names of Lean's four type annotations. -/
def optParamName : Name := .str .anonymous "optParam"
def autoParamName : Name := .str .anonymous "autoParam"
def outParamName : Name := .str .anonymous "outParam"
def semiOutParamName : Name := .str .anonymous "semiOutParam"

/-- **A type a stored constant inhabits**: `T` is a constant type `n` at no levels and the
constant `n.missing` is stored at no levels with type `T` (the prelude's `Lean.Syntax.missing`). -/
def annWitness (find? : Name → Option ConstantInfo) : Expr → Bool
  | D@(.const n []) =>
    match find? (n.str "missing") with
    | some c => c.toConstantVal.type == D && c.toConstantVal.levelParams.isEmpty
    | none => false
  | _ => false

/-- `annIdent`'s test of the definition's level parameters and value. -/
def annIdentVal (find? : Name → Option ConstantInfo) : List Name → Nat → Expr → Bool
  | [p], 1, .lam (.sort (.param p')) (.bvar 0) => p == p'
  | [p], 2, .lam (.sort (.param p')) (.lam D (.bvar 1)) =>
    p == p' && (D == .bvar 0 || annWitness find? D)
  | _, _, _ => false

/-- **An annotation stored as the identity on its type argument**: `n` is a definition at one
level parameter `p` whose value is `fun (α : Sort p) => α` (`arity` 1: `outParam`,
`semiOutParam`), resp. `fun (α : Sort p) (_ : D) => α` (`arity` 2) with `D` either `α` itself
(`optParam`) or a type a stored constant inhabits (`autoParam`, at `Lean.Syntax`), as the
prelude defines them.  The second argument's type is asked to be inhabited because the reading
of `fun _ : D => α` over an empty `D` is the proof point, not `α`. -/
def annIdent (find? : Name → Option ConstantInfo) (n : Name) (arity : Nat) : Bool :=
  match find? n with
  | some (.defnInfo cv v _) => annIdentVal find? cv.levelParams arity v
  | _ => false

/-- **`s` is `c` with type annotations consumed at its head** (Lean's
`consume_type_annotations`), up to equivalent levels: `c` itself, or `optParam.{l} α d`,
`autoParam.{l} α t`, `outParam.{l} α`, `semiOutParam.{l} α` where the annotation is the
identity (`annIdent`) and `s` is `α` with annotations consumed. -/
def annEq (find? : Name → Option ConstantInfo) (s : Expr) : Expr → Bool
  | c@(.app (.app (.const n [_]) a) _) =>
    s.lvlEq c || ((n == optParamName || n == autoParamName) && annIdent find? n 2 &&
      annEq find? s a)
  | c@(.app (.const n [_]) a) =>
    s.lvlEq c || ((n == outParamName || n == semiOutParamName) && annIdent find? n 1 &&
      annEq find? s a)
  | c => s.lvlEq c

/-- Two lists, pairwise related by `r`. -/
def listRel {α β : Type} (r : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => r a b && listRel r as bs
  | _, _ => false

/-- **A plain rule's parameters fit its constructor's**: the recursor's first `cnP` binder
domains are the constructor's parameter domains (at the rule's levels) up to consumed
annotations and equivalent levels. -/
def paramsAnnEq (find? : Name → Option ConstantInfo) (cvj : ConstantVal) (cnP : Nat)
    (cv : ConstantVal) (rl : RecRule) : Bool :=
  match cv.type.stripPis cnP,
    (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)).stripPis
      cnP with
  | some (rd, _), some (pd, _) => listRel (annEq find?) rd pd
  | _, _ => false

/-- **The two readings of a rule's parts are one**: the same indices, levels and parameters;
the fields' domains the constructor's up to equivalent levels, or — in a plain rule whose
parameters fit the constructor's (`paramsAnnEq`) — up to consumed annotations as well. -/
def iotaPartsRel (find? : Name → Option ConstantInfo) (cvj : ConstantVal) (cnP : Nat)
    (cv : ConstantVal) (rl : RecRule) (p' p : IotaParts) : Bool :=
  p'.idx == p.idx && p'.us == p.us && p'.params == p.params &&
    (listRel Expr.lvlEq p'.fieldDoms p.fieldDoms ||
      (rl.fire == .plain && paramsAnnEq find? cvj cnP cv rl &&
        listRel (annEq find?) p'.fieldDoms p.fieldDoms))

/-- **One rule reads** (see the module docstring): its parts read off the recursor's type are
the parts read through its constructor, which `find?` stores under the rule's name. -/
def ruleReadsB (find? : Name → Option ConstantInfo) (cv : ConstantVal) (mI rP i : Nat)
    (rl : RecRule) : Bool :=
  match iotaPartsOf cv mI rP i rl, find? rl.ctor with
  | some p', some (.ctorInfo cvj cnP _ _) =>
    match iotaPartsAt cvj cnP mI rP rl with
    | some p => iotaPartsRel find? cvj cnP cv rl p' p
    | none => false
  | _, _ => false

/-- **The checker's rule, at one recursor**: each of its rules reads (`ruleReadsB`), by
position. -/
def recReadsOk (find? : Name → Option ConstantInfo) : ConstantInfo → Except CheckError Unit
  | .recInfo cv mI rP _ rules =>
    (rules.zipIdx).forM fun (rl, i) =>
      unless ruleReadsB find? cv mI rP i rl do
        throw (.invalid s!"the recursor {cv.name}'s minor premise for {rl.ctor} does not \
          state the constructor's fields, indices and parameters as the constructor's type \
          does")
  | _ => pure ()

/-- **The checker's rule, at a block**: every recursor it installs reads, against the
environment after the install. -/
def blockReadsOk (find? : Name → Option ConstantInfo) (p : BlockShape) :
    Except CheckError Unit :=
  (blockRecs p p.recs).forM (recReadsOk find?)

end ConLeche
