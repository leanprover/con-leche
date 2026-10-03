module

public import Fragment.Scope

@[expose] public section

/-!
# The specification of an inductive block

The data a block is given by — the type former's name, level
parameters, parameter and index telescopes and result sort, the
constructors with their fields, the recursor's name and elimination
level — and, for a **nested** block, the one container instantiation
it nests through (its *class*, `NestInfo`).  Everything the checker
checks and stores about a block is generated from this
(`Decl.lean`), and the environment stores the specification alongside
the type former (`ConstKind.induct`, `Env.lean`), so that a later
block nesting through this one can read it back.

Con-leche's counterparts: `BlockShape` (`BlockParts.lean`) for the block,
and the container-instance record of the positivity walk
(`ConLeche/Kernel/Inductives/Positivity.lean`, `nestContainer`) for
the class.
-/

namespace Fragment

/-- A constructor field, as the positivity check classifies it
(con-leche's `RecFieldKind`, `FieldTele.lean:29`).  Its domain is an
expression under the parameters and the earlier fields. -/
inductive Field where
  /-- An ordinary field: any domain that does not mention the block. -/
  | ordinary (A : Expr)
  /-- A reflexive field: `∀ tele, I params es` — a function space into
  the family at the block's parameters and the index expressions `es`;
  `tele` is a context (innermost first) under the parameters and the
  earlier fields, `es` a spine (outermost first) under `tele` too.
  With an empty telescope the field is simply **recursive**: the
  family itself (`reflexive [] es`) — one kind covers both, as the
  generated terms and the model treat them alike.  (Con-leche keeps
  them apart: `RecFieldKind.recursive`/`.reflexive`, `FieldTele.lean`.) -/
  | reflexive (tele : List Expr) (es : List Expr)
  /-- **A container field** (nested blocks): the block's class — a
  previously installed block `K` applied to arguments one of which is
  the nested occurrence `I params idx` (`NestInfo`).  The domain is
  `K.{lsK} args[nested]` lifted over the earlier fields; the field
  carries an inductive hypothesis for the class's motive
  (con-leche's container instance, `Positivity.lean`, `contApp`). -/
  | container
  deriving DecidableEq

namespace Field

/-- Does the field carry an inductive hypothesis?  (A container field
does: the class's motive at the field.) -/
def isRec : Field → Bool
  | ordinary _ => false
  | reflexive _ _ => true
  | container => true

/-- Is the field a container field? -/
def isCont : Field → Bool
  | container => true
  | _ => false

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

/-- **The data of a single inductive block** without its class
(con-leche's `MemberShape`/`InductiveShape`, `BlockParts.lean:62`,
`SumParts.lean:36`). -/
structure IndBase where
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

/-- **The class of a nested block**: the one container instantiation
its container fields are read through — a previously installed block
`K` (its data, as stored with its type former), at levels `lsK` over
the block's level parameters, applied to arguments `args` (outermost
first, under the block's parameters only; the nested position `p`
omitted) with the nested occurrence `I params idx` at position `p` of `K`'s
parameters.  `K` has parameters but no indices, and the nesting is at
depth one: the nested occurrence is `K`'s argument directly.

Con-leche: the container instance `C.{us} Ds` of the positivity walk
(`Positivity.lean`, `contApp`) and the outside class of the recursor
check (`GenRec.lean`, `ClassGen`); the fixture `tests/e2e/src/nested_rec.lean`
has `K = List`, `args = []`, `p = 0`, `idx = []`. -/
structure NestInfo where
  /-- The container's block data (as stored with its type former). -/
  K : IndBase
  /-- The container's levels at the instantiation, over the block's
  level parameters. -/
  lsK : List Level
  /-- The container's other arguments, outermost first, under the
  block's parameters (position `p` left out). -/
  args : List Expr
  /-- The nested position among the container's parameters
  (outermost first). -/
  p : Nat
  /-- The nested occurrence's index expressions, outermost first, under the
  block's parameters. -/
  idx : List Expr
  /-- The auxiliary recursor's name (`T.rec_1`): the recursor for the
  class. -/
  aux : Name
  deriving DecidableEq

/-- **The specification of an inductive block**: its data and, for a
nested block, its class. -/
structure IndSpec extends IndBase where
  /-- The class, when the block nests through a container. -/
  nest : Option NestInfo := none
  deriving DecidableEq

/-- A block's data as a plain (un-nested) specification — how the
container of a nested block is read back from the environment. -/
def IndBase.spec (b : IndBase) : IndSpec := { b with nest := none }

namespace IndSpec

/-- A plain block: no class, no container field. -/
def Plain (S : IndSpec) : Prop :=
  S.nest = none ∧ ∀ c ∈ S.ctors, ∀ f ∈ c.fields, f.isCont = false

end IndSpec

namespace NestInfo

variable (N : NestInfo)

/-- The container's parameter count. -/
def nPK : Nat := N.K.params.length

/-- The container's specification. -/
def KS : IndSpec := N.K.spec

/-- The number of the container's constructors. -/
def nK : Nat := N.K.ctors.length

/-- The nested parameter's variable, seen from under `d` binders below the
container's parameters: the parameter at position `p` (outermost
first) is `bvar (d + nPK - 1 - p)`. -/
def memberVar (d : Nat) : Nat := d + N.nPK - 1 - N.p

/-- Is this field of the container (with `k` earlier fields) the
**parameter field** — the ordinary field whose domain is the nested
parameter itself? -/
def isMember (k : Nat) : Field → Bool
  | .ordinary (.bvar i) => i == N.memberVar k
  | _ => false

/-- **Strict positivity of the container in the nested
position** (con-leche's `nestPos` walking the container's stored
constructors at the instantiation, `Positivity.lean`): the container
has no indices and no container field; the nested parameter's domain
is a sort; no later parameter's domain mentions the nested parameter;
every field of every constructor is the parameter field, a recursive
field (reflexive with an empty telescope, and no index expressions),
or an ordinary field whose domain mentions neither the nested
parameter nor an earlier parameter field — the nested parameter never occurs to
the left of an arrow, under a binder or inside another type, and
nothing after a parameter field reads its value (the class is read at
every approximant, so a parameter field's value must be free to
move). -/
def Positive : Prop :=
  N.K.indices = [] ∧
  N.p < N.nPK ∧
  (∃ ℓ : Level, N.K.params[N.nPK - 1 - N.p]? = some (.sort ℓ)) ∧
  (∀ i A, N.K.params[i]? = some A → i < N.nPK - 1 - N.p →
    A.usesVar (N.nPK - 2 - i - N.p) = false) ∧
  (∀ c ∈ N.K.ctors, c.idx = [] ∧ ∀ i f, c.fields[i]? = some f →
    match f with
    | Field.ordinary A => A = Expr.bvar (N.memberVar (c.fields.length - 1 - i)) ∨
        (A.usesVar (N.memberVar (c.fields.length - 1 - i)) = false ∧
          ∀ i' f', c.fields[i']? = some f' → i < i' →
            N.isMember (c.fields.length - 1 - i') f' = true → A.usesVar (i' - i - 1) = false)
    | Field.reflexive tele es => tele = [] ∧ es = []
    | Field.container => False)

/-- The nested parameter's domain level (`Sort ℓ`), when `Positive`;
`zero` otherwise. -/
def memberLevel : Level :=
  match N.K.params[N.nPK - 1 - N.p]? with
  | some (.sort ℓ) => ℓ
  | _ => .zero

end NestInfo

end Fragment
