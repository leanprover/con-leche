module

public import Fragment.Syntax

@[expose] public section

/-!
# The environment

What the checker has accepted so far: a list of named constants, each
with its level parameters and its type, and with what kind of thing it
is — a definition (with a value, unfolded by the δ step), an inductive
type former, a constructor, or a recursor (with its rules, fired by
the ι step).  There are no axioms, no `theorem`/`opaque` distinction
and no quotients in the fragment.

The env-free part of the proof (`Sound.lean`) treats the environment
**abstractly**: it reads only the syntactic facts below and the
semantic laws of `EnvModel.lean`; that definitions and inductive
blocks establish those laws is the environment section's business.

Mirrors `ConLeche.Env`/`ConstantInfo`/`RecRule`
(`ConLeche/Kernel/Env.lean`), without the install-time data (firing
modes, capability bits, projection tables) the fragment has no use
for.
-/

namespace Fragment

/-- One computation rule of a recursor: the major premise built by
`ctor` with `nfields` fields reduces to `rhs`, a closed term over the
recursor's level parameters, applied to the recursor's parameters,
motives and minor premises and then the constructor's fields. -/
structure RecRule where
  /-- The constructor this rule fires on. -/
  ctor : Name
  /-- The constructor's field count (its arguments after the
  parameters). -/
  nfields : Nat
  /-- The right-hand side, a closed term over the recursor's level
  parameters, `fun params motives minors fields => …`. -/
  rhs : Expr
  deriving DecidableEq

/-- What kind of constant a name is stored as. -/
inductive ConstKind where
  /-- A definition: its value unfolds (δ). -/
  | defn (value : Expr)
  /-- An inductive type former with `numParams` parameters,
  `numIndices` indices and these constructors. -/
  | induct (numParams numIndices : Nat) (ctors : List Name)
  /-- A constructor of the inductive `induct`, with `numParams`
  parameters (the inductive's) and `nfields` fields. -/
  | ctor (induct : Name) (numParams nfields : Nat)
  /-- A recursor with the given telescope shape — `numParams`
  parameters, `numMotives` motives, `numMinors` minor premises,
  `numIndices` indices, then the major premise — and its rules. -/
  | recursor (numParams numMotives numMinors numIndices : Nat) (rules : List RecRule)
  deriving DecidableEq

namespace ConstKind

/-- The value a definition unfolds to. -/
def value? : ConstKind → Option Expr
  | defn v => some v
  | _ => none

end ConstKind

/-- A stored constant: its level parameters, its type (closed, over
those parameters) and its kind. -/
structure ConstInfo where
  /-- The level parameters. -/
  lparams : List Name
  /-- The declared type, a closed term over `lparams`. -/
  type : Expr
  /-- The kind. -/
  kind : ConstKind
  deriving DecidableEq

namespace ConstInfo

/-- The value, for a definition. -/
def value? (ci : ConstInfo) : Option Expr := ci.kind.value?

end ConstInfo

/-- **The environment**: the accepted constants, most recent first.  A
name is stored at most once; `find?` reads the first entry. -/
structure Env where
  /-- The stored constants. -/
  consts : List (Name × ConstInfo)
  deriving DecidableEq

namespace Env

/-- Look a name up. -/
def find? (env : Env) (n : Name) : Option ConstInfo := env.consts.lookup n

/-- The empty environment. -/
def empty : Env := ⟨[]⟩

/-- Store one more constant. -/
def add (env : Env) (n : Name) (ci : ConstInfo) : Env := ⟨(n, ci) :: env.consts⟩

@[simp] theorem find?_empty (n : Name) : find? empty n = none := rfl

theorem find?_add (env : Env) (n m : Name) (ci : ConstInfo) :
    find? (env.add n ci) m = if m = n then some ci else env.find? m := by
  simp only [find?, add, List.lookup]
  split
  · rename_i h
    simp [beq_iff_eq] at h
    simp [h]
  · rename_i h
    simp at h
    simp [h]

end Env

end Fragment
