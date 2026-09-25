module

public import Fragment.Rules
public import Fragment.Scope

@[expose] public section

/-!
# Declarations: what the checker accepts

The environment grows by **definitions** and by **inductive blocks**.
This file says, relationally, what the checker checks before storing
either — `DefOk` and `IndOk` — and what it stores (`Env.add`,
`IndSpec.install`).  Nothing here is semantic; the environment section
(`Install.lean`) proves that an environment built by these checks has
a model.

**Definitions** (`DefOk`; con-leche's `checkDefnVal`,
`ConLeche/Kernel/Checker.lean:36-52`): the declared type has a sort,
the value's inferred type is definitionally equal to the declared
type, the name is fresh, and both terms are closed, mention only
stored constants and use only the declared level parameters.

**Inductive blocks** (`IndOk`; con-leche's fixpoint route,
`ConLeche/Kernel/Inductives/NativeInstall.lean`, with its recogniser
`NativeParts.lean` and the generators of `StructParts.lean`).  A block
is given by a **specification** (`IndSpec`): a type former with level
parameters, a parameter telescope, an index telescope and a result
sort, and constructors whose fields are *ordinary* (any domain not
mentioning the block), *recursive* (the family at the block's
parameters and some index expressions) or *reflexive* (a function
space into the family — the one shape that makes an inductive type
large).  The types of the former, the constructors and the recursor,
and the recursor's rules, are **generated** from the specification
(`indType`, `ctorType`, `recType`, `ruleRhs`); the checker's checks
are then: the generated former's and constructors' types have sorts
(`Infer`) in the environment as it stands when each is added (the
recursive fields' domains mention the former), every field's sort
respects the universe bound, the elimination level is admissible, and
the generated recursor's type has a sort.  Con-leche recognises the
block's shape from the stream's records and compares the stream's
recursor with the generated one (task #175 S2, #220); the fragment
takes the shape as given and stores the generated recursor — the same
environment either way.

The de Bruijn bookkeeping is the one unavoidable cost of the
generators: an expression of the specification lives under the
parameters and the earlier fields, and reappears in a minor premise
under the motive, the earlier minors, the fields and the earlier
inductive hypotheses, and in a rule under the motive, all the minors
and the fields.  `atCtx` is the one lifting that moves it
(con-leche's `structIdxAt`, `NativeParts.lean:229`).

Contexts are innermost first throughout, as in `Rules.lean`: a
telescope `[Aₙ, …, A₁]` binds `A₁` outermost, and `Aᵢ` may mention the
variables of `A₁ … Aᵢ₋₁` as `bvar 0 … bvar (i-2)`.
-/

namespace Fragment

/-! ## Telescopes over contexts -/

namespace Expr

/-- `∀ Γ, b` over a context (innermost first), every binder annotated
`pw`. -/
def mkPis (pw : PropWhen) : List Expr → Expr → Expr
  | [], b => b
  | A :: Γ, b => mkPis pw Γ (pi A pw b)

/-- `fun Γ => b` over a context, every binder annotated `pw`. -/
def mkLams (pw : PropWhen) : List Expr → Expr → Expr
  | [], b => b
  | A :: Γ, b => mkLams pw Γ (lam A pw b)

@[simp] theorem mkPis_nil (pw : PropWhen) (b : Expr) : mkPis pw [] b = b := rfl
@[simp] theorem mkPis_cons (pw : PropWhen) (A : Expr) (Γ : List Expr) (b : Expr) :
    mkPis pw (A :: Γ) b = mkPis pw Γ (pi A pw b) := rfl
@[simp] theorem mkLams_nil (pw : PropWhen) (b : Expr) : mkLams pw [] b = b := rfl
@[simp] theorem mkLams_cons (pw : PropWhen) (A : Expr) (Γ : List Expr) (b : Expr) :
    mkLams pw (A :: Γ) b = mkLams pw Γ (lam A pw b) := rfl

theorem mkPis_append (pw : PropWhen) (Γ Δ : List Expr) (b : Expr) :
    mkPis pw (Γ ++ Δ) b = mkPis pw Δ (mkPis pw Γ b) := by
  induction Γ generalizing b with
  | nil => rfl
  | cons A Γ ih => simp [ih]

theorem mkLams_append (pw : PropWhen) (Γ Δ : List Expr) (b : Expr) :
    mkLams pw (Γ ++ Δ) b = mkLams pw Δ (mkLams pw Γ b) := by
  induction Γ generalizing b with
  | nil => rfl
  | cons A Γ ih => simp [ih]

/-- The variables of the `n` binders sitting `o` binders up, as a
spine (outermost first): `bvar (o + n - 1), …, bvar o`. -/
def varsAt (o n : Nat) : List Expr := (List.range n).map fun k => bvar (o + n - 1 - k)

/-- Lift each entry of a context by a function of how many entries of
the same context sit below it (the head of an innermost-first context
sits above all the others). -/
def liftCtx (f : Nat → Expr → Expr) : List Expr → List Expr
  | [] => []
  | A :: Γ => f Γ.length A :: liftCtx f Γ

@[simp] theorem liftCtx_nil (f : Nat → Expr → Expr) : liftCtx f [] = [] := rfl
@[simp] theorem liftCtx_cons (f : Nat → Expr → Expr) (A : Expr) (Γ : List Expr) :
    liftCtx f (A :: Γ) = f Γ.length A :: liftCtx f Γ := rfl

theorem length_liftCtx (f : Nat → Expr → Expr) : ∀ Γ : List Expr, (liftCtx f Γ).length = Γ.length
  | [] => rfl
  | _ :: Γ => by simp [length_liftCtx f Γ]

/-- **The lifting into a minor premise or a rule.**  An expression of
the specification stands under the parameters and `k` earlier fields
(and `d` binders of its own, a reflexive field's telescope); in a
minor premise or a rule it stands under the parameters, `o` more
binders (the motive and some minors), all `nF` fields, `l` earlier
inductive hypotheses and its own `d`: the fields and hypotheses in
between shift the earlier fields by `nF - k + l`, the motive and
minors shift the parameters by `o` more. -/
def atCtx (nF k l o d : Nat) (e : Expr) : Expr :=
  (e.liftN (nF - k + l) d).liftN o (nF + l + d)

end Expr

/-! ## The specification of a block -/

/-- A constructor field, as the positivity check classifies it
(con-leche's `RecFieldKind`, `NativeParts.lean:51`).  Its domain is an
expression under the parameters and the earlier fields. -/
inductive Field where
  /-- An ordinary field: any domain that does not mention the block. -/
  | ordinary (A : Expr)
  /-- A recursive field: the family at the block's parameters and the
  index expressions `es` (a spine, outermost first). -/
  | recursive (es : List Expr)
  /-- A reflexive field: `∀ tele, I params es` — a function space into
  the family; `tele` is a context (innermost first) under the
  parameters and the earlier fields, `es` a spine under `tele` too. -/
  | reflexive (tele : List Expr) (es : List Expr)
  deriving DecidableEq

namespace Field

/-- Does the field carry an inductive hypothesis? -/
def isRec : Field → Bool
  | ordinary _ => false
  | recursive _ => true
  | reflexive _ _ => true

end Field

/-- A constructor: its name, its fields (a context, innermost first)
and the index expressions of its result `I params idx` (a spine,
outermost first, under the parameters and all the fields). -/
structure CtorSpec where
  /-- The constructor's name. -/
  name : Name
  /-- The fields, innermost first. -/
  fields : List Field
  /-- The result's index expressions, outermost first. -/
  idx : List Expr
  deriving DecidableEq

/-- **The specification of a single inductive block**
(con-leche's `NativeParts`/`InductiveShape`, `NativeParts.lean:180`,
`SumParts.lean:79`). -/
structure IndSpec where
  /-- The type former's name. -/
  name : Name
  /-- The block's level parameters. -/
  lparams : List Name
  /-- The parameter telescope (a context, innermost first). -/
  params : List Expr
  /-- The index telescope (a context under the parameters). -/
  indices : List Expr
  /-- The result sort `Sort u`. -/
  sort : Level
  /-- The constructors, in order. -/
  ctors : List CtorSpec
  /-- The recursor's name. -/
  recName : Name
  /-- Large elimination: the recursor eliminates into `Sort ℓ` for a
  fresh level parameter `ℓ`; otherwise into `Prop`. -/
  large : Bool
  /-- The fresh elimination level parameter (read only if `large`). -/
  elim : Name
  deriving DecidableEq

namespace IndSpec

open Expr

variable (S : IndSpec)

/-- The number of parameters. -/
def nP : Nat := S.params.length
/-- The number of indices. -/
def nI : Nat := S.indices.length
/-- The number of constructors. -/
def n : Nat := S.ctors.length
/-- The block's level parameters as levels. -/
def lvls : List Level := S.lparams.map .param
/-- The annotation of every binder whose body is a member of the
family or the family itself — a proposition exactly when the result
sort is zero. -/
def pw : PropWhen := Level.zeroness S.sort
/-- The elimination level: the fresh parameter, or `Prop`. -/
def ℓ : Level := if S.large then .param S.elim else .zero
/-- The annotation of the recursor's binders: a proposition exactly
when the elimination level is zero. -/
def q : PropWhen := Level.zeroness S.ℓ
/-- The recursor's level parameters: the elimination parameter in
front of the block's, if large. -/
def recLparams : List Name := if S.large then S.elim :: S.lparams else S.lparams
/-- The recursor's level parameters as levels. -/
def recLvls : List Level := S.recLparams.map .param

/-- The family applied to the parameter variables sitting `o` binders
up and to the index expressions `es`. -/
def famAt (o : Nat) (es : List Expr) : Expr :=
  mkAppN (.const S.name S.lvls) (varsAt o S.nP ++ es)

/-- The family at the parameter variables (`e + nI` up) and the index
variables (`0` up): the type of a major premise. -/
def famVars (e : Nat) : Expr := S.famAt (e + S.nI) (varsAt 0 S.nI)

/-- A field's domain, with `k` earlier fields. -/
def fieldDom (k : Nat) : Field → Expr
  | .ordinary A => A
  | .recursive es => S.famAt k es
  | .reflexive tele es => mkPis S.pw tele (S.famAt (k + tele.length) es)

/-- A constructor's field context: the domains, innermost first (the
head has all the others as earlier fields). -/
def fieldCtx : List Field → List Expr
  | [] => []
  | f :: fs => S.fieldDom fs.length f :: fieldCtx fs

theorem length_fieldCtx : ∀ fs : List Field, (S.fieldCtx fs).length = fs.length
  | [] => rfl
  | _ :: fs => by simp only [fieldCtx, List.length_cons, length_fieldCtx fs]

/-- The field context moved under `o` binders inserted between the
parameters and the fields. -/
def fieldCtxAt (c : CtorSpec) (o : Nat) : List Expr :=
  liftCtx (fun k A => A.liftN o k) (S.fieldCtx c.fields)

/-- The index context moved under `o` binders inserted between the
parameters and the indices. -/
def indicesAt (o : Nat) : List Expr := liftCtx (fun t T => T.liftN o t) S.indices

/-! ### The generated types -/

/-- **The type former's type** `∀ params indices, Sort u`; no binder is
a proposition. -/
def indType : Expr := mkPis .never (S.indices ++ S.params) (.sort S.sort)

/-- **A constructor's type** `∀ params fields, I params idx`; every
binder is a proposition exactly when the family is. -/
def ctorType (c : CtorSpec) : Expr :=
  mkPis S.pw (S.fieldCtx c.fields ++ S.params) (S.famAt c.fields.length c.idx)

/-- The motive's type, under the parameters:
`∀ indices (t : I params indices), Sort ℓ`. -/
def motiveTy : Expr := mkPis .never (S.famVars 0 :: S.indices) (.sort S.ℓ)

/-- The fields with an inductive hypothesis, outermost first, each
with its number of earlier fields. -/
def _root_.Fragment.CtorSpec.recFields (c : CtorSpec) : List (Nat × Field) :=
  ((List.range c.fields.length).filterMap fun k =>
    match c.fields[c.fields.length - 1 - k]? with
    | some f => if f.isRec then some (k, f) else none
    | none => none)

/-- **An inductive hypothesis' type** for the field with `k` earlier
fields, `l` earlier hypotheses, `o` binders between the parameters
and the fields (the motive sits `nF + l + o - 1` binders above):
`motive es f` at a recursive field, `∀ tele, motive es (f tele)` at a
reflexive one. -/
def ihTy (nF k l o : Nat) : Field → Expr
  | .ordinary _ => .sort .zero
  | .recursive es =>
    mkAppN (.bvar (nF + l + o - 1)) (es.map (atCtx nF k l o 0) ++ [.bvar (nF - 1 - k + l)])
  | .reflexive tele es =>
    let m := tele.length
    mkPis S.q (liftCtx (fun t T => atCtx nF k l o t T) tele)
      (mkAppN (.bvar (nF + l + o - 1 + m))
        (es.map (atCtx nF k l o m) ++ [mkAppN (.bvar (nF - 1 - k + l + m)) (varsAt 0 m)]))

/-- The inductive hypotheses of a constructor in minor premise `j`, as
a context (innermost first). -/
def ihCtx (c : CtorSpec) (j : Nat) : List Expr :=
  (c.recFields.mapIdx fun l kf => S.ihTy c.fields.length kf.1 l (j + 1) kf.2).reverse

/-- **A minor premise** for constructor `j`, under the parameters, the
motive and the `j` earlier minors:
`∀ fields ihs, motive idx (C params fields)`. -/
def minorTy (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  let nIh := c.recFields.length
  mkPis S.q (S.ihCtx c j ++ S.fieldCtxAt c (j + 1))
    (mkAppN (.bvar (nIh + nF + j))
      (c.idx.map (atCtx nF nF nIh (j + 1) 0) ++
        [mkAppN (.const c.name S.lvls) (varsAt (nIh + nF + j + 1) S.nP ++ varsAt nIh nF)]))

/-- The minor premises, as a context under the motive (innermost
first). -/
def minorsCtx : List Expr :=
  ((List.range S.n).map fun j => S.minorTy (S.ctors.getD j ⟨"", [], []⟩) j).reverse

/-- **The recursor's type**
`∀ params (motive : motiveTy) minors indices (t : I params indices), motive indices t`
(con-leche's `structRecTyR`, `NativeParts.lean:349`). -/
def recType : Expr :=
  mkPis S.q (S.famVars (S.n + 1) :: S.indicesAt (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params)
    (mkAppN (.bvar (1 + S.nI + S.n)) (varsAt 1 S.nI ++ [.bvar 0]))

/-- **An inductive hypothesis' value** in a rule, for the field with
`k` earlier fields under all `nF` fields, the `n` minors and the
motive: the recursor at the parameters, motive and minors, the
field's index expressions and the field (under the field's own
telescope at a reflexive field). -/
def ihVal (nF k : Nat) : Field → Expr
  | .ordinary _ => .sort .zero
  | .recursive es =>
    mkAppN (.const S.recName S.recLvls)
      (varsAt (nF + S.n + 1) S.nP ++ [.bvar (nF + S.n)] ++ varsAt nF S.n ++
        es.map (atCtx nF k 0 (S.n + 1) 0) ++ [.bvar (nF - 1 - k)])
  | .reflexive tele es =>
    let m := tele.length
    mkLams S.q (liftCtx (fun t T => atCtx nF k 0 (S.n + 1) t T) tele)
      (mkAppN (.const S.recName S.recLvls)
        (varsAt (m + nF + S.n + 1) S.nP ++ [.bvar (m + nF + S.n)] ++ varsAt (m + nF) S.n ++
          es.map (atCtx nF k 0 (S.n + 1) m) ++ [mkAppN (.bvar (m + nF - 1 - k)) (varsAt 0 m)]))

/-- **A rule's right-hand side** for constructor `j`:
`fun params motive minors fields => minor_j fields ihs`
(con-leche's `structRecRhsR`, `NativeParts.lean:368`). -/
def ruleRhs (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  mkLams S.q (S.fieldCtxAt c (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params)
    (mkAppN (.bvar (nF + S.n - 1 - j))
      (varsAt 0 nF ++ c.recFields.map fun kf => S.ihVal nF kf.1 kf.2))

/-- The recursor's rules, one per constructor. -/
def rules : List RecRule :=
  (List.range S.n).map fun j =>
    let c := S.ctors.getD j ⟨"", [], []⟩
    ⟨c.name, c.fields.length, S.ruleRhs c j⟩

/-! ### What is stored -/

/-- The type former's constant. -/
def indInfo : ConstInfo := ⟨S.lparams, S.indType, .induct S.nP S.nI (S.ctors.map (·.name))⟩

/-- A constructor's constant. -/
def ctorInfo (c : CtorSpec) : ConstInfo :=
  ⟨S.lparams, S.ctorType c, .ctor S.name S.nP c.fields.length⟩

/-- The recursor's constant: `nP` parameters, one motive, `n` minors,
`nI` indices, the generated rules. -/
def recInfo : ConstInfo := ⟨S.recLparams, S.recType, .recursor S.nP 1 S.n S.nI S.rules⟩

/-- The environment with the type former added. -/
def envInd (env : Env) : Env := env.add S.name S.indInfo

/-- The environment with the type former and the constructors added,
in order. -/
def envCtors (env : Env) : Env :=
  S.ctors.foldl (fun e c => e.add c.name (S.ctorInfo c)) (S.envInd env)

/-- **The installed block**: former, constructors, recursor. -/
def install (env : Env) : Env := (S.envCtors env).add S.recName S.recInfo

end IndSpec

/-! ## Scope -/

namespace Expr

/-- **A term in scope** of an environment and level parameters, under
`k` binders: closed at `k`, every constant stored, every level
parameter declared. -/
def Scoped (env : Env) (ps : List Name) (k : Nat) (e : Expr) : Prop :=
  e.closedAt k = true ∧ (∀ c ∈ e.consts, (env.find? c).isSome) ∧ e.lparamsIn ps = true

end Expr

/-! ## The checks -/

variable [LevelOracle]

/-- **A definition is accepted** (con-leche's `checkDefnVal`): the
name is fresh, the declared type's type reduces to a sort, the
value's inferred type is definitionally equal to the declared type,
and both terms are in scope (closed, stored constants, declared level
parameters). -/
def DefOk (env : Env) (c : Name) (ci : ConstInfo) : Prop :=
  env.find? c = none ∧
  (∃ s u, Infer env [] ci.type s ∧ Red env [] s (.sort u)) ∧
  (∃ v T, ci.kind = .defn v ∧ Infer env [] v T ∧ DefEq env [] T ci.type ∧
    Expr.Scoped env ci.lparams 0 v) ∧
  Expr.Scoped env ci.lparams 0 ci.type

namespace IndSpec

variable (S : IndSpec)

/-- The scope of a field's pieces: with `k` earlier fields, an
ordinary domain is in scope under the parameters and them; a recursive
field's index expressions too; a reflexive field's telescope entries
under the earlier telescope entries as well, and its index
expressions under the whole telescope.  No piece mentions the block
(it is not stored in `env`): that is **strict positivity** in the
shape the fragment admits (con-leche's `recPositivity`,
`NativeParts.lean:89`). -/
def fieldScoped (env : Env) (k : Nat) : Field → Prop
  | .ordinary A => Expr.Scoped env S.lparams (S.nP + k) A
  | .recursive es => ∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k) e
  | .reflexive tele es =>
    (∀ t T, tele[t]? = some T → Expr.Scoped env S.lparams (S.nP + k + (tele.length - 1 - t)) T) ∧
    (∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k + tele.length) e)

/-- **The specification is in scope** of the environment: every
expression of it is closed at its depth, mentions only stored
constants (so never the block itself) and uses only the block's level
parameters; the elimination parameter is not one of them. -/
def Scoped (env : Env) : Prop :=
  (∀ i A, S.params[i]? = some A → Expr.Scoped env S.lparams (S.nP - 1 - i) A) ∧
  (∀ t T, S.indices[t]? = some T → Expr.Scoped env S.lparams (S.nP + (S.nI - 1 - t)) T) ∧
  S.sort.paramsIn S.lparams = true ∧
  (∀ c ∈ S.ctors,
    (∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f) ∧
    (∀ e ∈ c.idx, Expr.Scoped env S.lparams (S.nP + c.fields.length) e)) ∧
  (S.large = true → S.elim ∉ S.lparams)

/-- The universe bound on a field of sort `v`: the family is a
proposition, or `v ≤ u` (official's "universe level of `type_of(arg)`
is too big" check, `checkStructFieldSortsI`,
`ConLeche/Kernel/Inductives/SumInstall.lean:124`). -/
def FieldBound (v : Level) : Prop :=
  LevelOracle.eq S.sort .zero = true ∨ LevelOracle.le v S.sort = true

/-- "The result sort is never `Prop`": `1 ≤ u` at every valuation
(con-leche's `Level.isNeverZero`). -/
def NeverProp : Prop := LevelOracle.le (.succ .zero) S.sort = true

/-- **The subsingleton criterion** for a field of sort `v` at
position `i` (innermost first) of a constructor with index
expressions `idx`: the field is a proposition, or it is one of the
result's indices (official's `elim_only_at_universe_zero` at one
constructor; con-leche's `checkStructFieldSortsI`).  Required only of a
large eliminator on a block whose sort may be `Prop`. -/
def SubsingletonField (v : Level) (i : Nat) (idx : List Expr) : Prop :=
  S.large = true → ¬ S.NeverProp → (LevelOracle.eq v .zero = true ∨ Expr.bvar i ∈ idx)

/-- **The block is accepted** (con-leche's `checkNative`,
`NativeInstall.lean:617`):

* the block's names are distinct and fresh;
* the specification is in scope (closed, stored constants, declared
  level parameters — positivity included);
* the generated type former's type has a sort in the current
  environment;
* each generated constructor's type has a sort in the environment
  holding the former, and every field's domain has a sort respecting
  the universe bound and, where a large eliminator asks it, the
  subsingleton criterion;
* a large eliminator on a block whose sort may be `Prop` has at most
  one constructor (official's `elim_only_at_universe_zero`);
* the generated recursor's type has a sort in the environment holding
  the former and the constructors.

The recursor's rules are generated and stored, not checked: they
mention the recursor, and con-leche does not infer them either
(`NativeInstall.lean`, "the rules … are scope-checked at the
environment holding its constant and NOT inferred"). -/
def Ok (env : Env) : Prop :=
  (S.name :: S.recName :: S.ctors.map (·.name)).Nodup ∧
  (∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none) ∧
  S.Scoped env ∧
  (∃ T, Infer env [] S.indType T) ∧
  (∀ c ∈ S.ctors,
    (∃ T, Infer (S.envInd env) [] (S.ctorType c) T) ∧
    (∀ i A, (S.fieldCtx c.fields)[i]? = some A →
      ∃ s v, Infer (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) A s ∧
        Red (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) s (.sort v) ∧
        S.FieldBound v ∧ S.SubsingletonField v i c.idx)) ∧
  (S.large = true → ¬ S.NeverProp → S.ctors.length ≤ 1) ∧
  (∃ T, Infer (S.envCtors env) [] S.recType T)

end IndSpec

/-- `IndOk env S`: the block `S` is accepted on top of `env`. -/
abbrev IndOk (env : Env) (S : IndSpec) : Prop := S.Ok env

end Fragment
