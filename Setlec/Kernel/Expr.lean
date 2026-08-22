module

/-!
# Kernel expressions

The checker's own term representation, mirroring Lean's kernel expressions.
We deliberately do not reuse `Lean.Expr`: our own inductive has no cached
metadata, which keeps the verification story clean.

Design decisions (see DESIGN.md):
* Free variables (`fvar`) follow nanoda's representation: a de Bruijn *level*
  together with the variable's type (and binder name, for error messages).
  The type is part of the variable's identity, so a local context is implicit
  in every open term.  Input terms coming from declarations are closed and
  use only `bvar` (de Bruijn *indices*).
* No metavariables, no `mdata`: those never reach a kernel.
-/

@[expose] public section

namespace Setlec

/-- Hierarchical names, same shape as `Lean.Name` but without the cached hash,
so that it is a plain inductive datatype convenient for verification. -/
inductive Name where
  | anonymous
  | str (pre : Name) (s : String)
  | num (pre : Name) (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Name

/-- Conversion from `Lean.Name` (dropping macro scopes is the caller's duty). -/
def ofLeanName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ofLeanName p) s
  | .num p n => .num (ofLeanName p) n

protected def toString : Name → String
  | .anonymous => "[anonymous]"
  | .str .anonymous s => s
  | .str p s => p.toString ++ "." ++ s
  | .num .anonymous n => toString n
  | .num p n => p.toString ++ "." ++ toString n

instance : ToString Name := ⟨Name.toString⟩

end Name

/-- Universe levels, mirroring `Lean.Level` without metavariables. -/
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : Name)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Binder annotations. Irrelevant to checking; kept for round-tripping and
error messages. -/
inductive BinderInfo where
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Metadata carried by a binder (`forallE`, `lam`): the display
`BinderInfo`, and the **codomain sort annotation** `cod` — for a
`forallE`, the sort level of the body; for a `lam`, the sort level of the
body's type.  Input expressions carry `none`; the checker computes each
annotation once (by real inference, in the annotation pass) and it is
trusted thereafter.  The set-model's Prop/Type classifier for dependent
products reads this annotation, which makes the interpretation purely
structural (see DESIGN.md, "sort annotations"). -/
structure BinderMeta where
  bi : BinderInfo
  cod : Option Level := none
  deriving DecidableEq, Repr, Hashable

instance : Inhabited BinderMeta := ⟨⟨.default, none⟩⟩

/-- Literals. -/
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Kernel expressions.

`fvar idx name type`: an opened variable, identified by its de Bruijn level
`idx` *and* its type; the binder `name` is display-only.  Closed input terms
contain no `fvar`s. -/
inductive Expr where
  | bvar (i : Nat)
  | fvar (idx : Nat) (name : Name) (type : Expr)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lam (n : Name) (type body : Expr) (m : BinderMeta)
  | forallE (n : Name) (type body : Expr) (m : BinderMeta)
  | letE (n : Name) (type value body : Expr)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- Depth-bounded `Level` hash (towers from universe arithmetic can be
deep; the memo maps only need *some* function of the value). -/
def Level.hashB : Nat → Level → UInt64
  | 0, _ => 511
  | _ + 1, .zero => 1
  | n + 1, .succ u => mixHash 3 (Level.hashB n u)
  | n + 1, .max u v => mixHash 5 (mixHash (Level.hashB n u) (Level.hashB n v))
  | n + 1, .imax u v => mixHash 7 (mixHash (Level.hashB n u) (Level.hashB n v))
  | _ + 1, .param p => mixHash 11 (hash p)

/-- Node-budget-bounded `Expr` hash: visits at most `budget` nodes and
salts the remainder with a sentinel, so memo-map lookups cost `O(1)`
in the term size instead of a full traversal.  Display-only fields
(binder and `fvar` names, binder metadata, `fvar` types) are skipped —
a hash may ignore fields; `BEq`/`DecidableEq` remain full structural
equality, so the memo maps stay correct. -/
def Expr.hashB : Expr → Nat → UInt64 → UInt64 × Nat
  | _, 0, acc => (mixHash acc 511, 0)
  | .bvar i, n + 1, acc => (mixHash acc (mixHash 3 (hash i)), n)
  | .fvar idx _ _, n + 1, acc => (mixHash acc (mixHash 5 (hash idx)), n)
  | .sort u, n + 1, acc => (mixHash acc (mixHash 7 (Level.hashB 4 u)), n)
  | .const c us, n + 1, acc =>
    (mixHash acc (mixHash 11 (mixHash (hash c)
      (us.foldl (fun a u => mixHash a (Level.hashB 4 u)) 13))), n)
  | .app f a, n + 1, acc =>
    let (h₁, n₁) := f.hashB n (mixHash acc 17)
    a.hashB n₁ h₁
  | .lam _ ty b _, n + 1, acc =>
    let (h₁, n₁) := ty.hashB n (mixHash acc 19)
    b.hashB n₁ h₁
  | .forallE _ ty b _, n + 1, acc =>
    let (h₁, n₁) := ty.hashB n (mixHash acc 23)
    b.hashB n₁ h₁
  | .letE _ ty v b, n + 1, acc =>
    let (h₁, n₁) := ty.hashB n (mixHash acc 29)
    let (h₂, n₂) := v.hashB n₁ h₁
    b.hashB n₂ h₂
  | .lit l, n + 1, acc => (mixHash acc (mixHash 31 (hash l)), n)
  | .proj s i e, n + 1, acc =>
    e.hashB n (mixHash acc (mixHash 37 (mixHash (hash s) (hash i))))

instance : Hashable Expr := ⟨fun e => (e.hashB 64 7).1⟩

end Setlec
