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

/-- The zero-ness datum of a binder's codomain sort — the regime
discriminator of the validated-annotation design (task #161).  For
every level `l`, the set `Z(l) := {φ | eval φ l = 0}` of zeroing
valuations is either empty (`never`) or of the form "every parameter
in `ps` is zero" (`ifAllZero ps`; `ps = []` = always zero) — see
`Level.zeronessOf` and the mechanized battery in
`Setlec.Verify.PropWhen`.

`ps` is an unordered, possibly-duplicated parameter *set in list
clothing*: all structural operations (`inter`, `bindZ`,
`Level.substPW`) are shape-preserving — no sorting, no
deduplication — which is what makes level instantiation's identity
and composition laws hold *unconditionally*
(`Level.substPW_self`/`substPW_comp`).  Comparison is by the
containment test `equiv`, which is sound **and complete** for
zero-ness agreement at every valuation (`Verify.PropWhen`); the
checker's validation and defeq sites compare with `equiv`, never
with `==`. -/
inductive PropWhen where
  | never
  | ifAllZero (ps : List Name)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace PropWhen

/-- Does the datum hold at a valuation — is the codomain sort zero
there?  (The model side's dispatch bit; the kernel never evaluates
this, it only compares data by `equiv`.) -/
def holds (φ : Name → Nat) : PropWhen → Bool
  | .never => false
  | .ifAllZero ps => ps.all fun n => φ n == 0

/-- Is the datum `never` — "the codomain sort is nonzero at *every*
valuation", the graph regime everywhere?  This is the **only**
kernel-decidable reading of the annotation that the verification tier
licenses a check-skip on (task #161 bucket 2): the P-tier claims split
their certificate cases on `pwBit φ m.pw = 0`, and `isNever` is
exactly the ∀-`φ` uniform version of the positive branch —
`pwBit φ .never = 1` at every `φ`, and no other datum has that
property (`.ifAllZero ps` holds at the all-zero valuation).  Sound
*and* exact: `PropWhen.holds_eq_false_iff_isNever`
(`Verify/PropWhen.lean`) and `pwBit_ne_zero_of_isNever` /
`isNever_iff_forall_pwBit_ne_zero` (`SetR/Annot/Bit.lean`).

The datum may be read **only** to skip a re-check; it must never
select a reduct, a computed type, or a comparison result (law 1 as
amended at task #161: "annotations never change a reduct or a computed
type; annotation-gated check-skipping is permitted where the skip's
soundness is a P-tier theorem *and* the gate fires only where the
licensing theorems' hypotheses hold — `μ.verified = true`").  Every
executable call site therefore carries the `μ.verified` conjunct; see
`inferBodyIO` (`Kernel/CoreIO.lean`). -/
def isNever : PropWhen → Bool
  | .never => true
  | .ifAllZero _ => false

/-- Does the datum mention any level parameter — is `Level.substPW`
ever non-trivial on it?  Folded into `Expr.hasLevelParam` and the
eager `eparamBs` recurrence (task #87), so the has-param shortcut of
the interned level-instantiation walk stays exact. -/
def hasParams : PropWhen → Bool
  | .never => false
  | .ifAllZero ps => !ps.isEmpty

/-- Are all parameters of the datum among `params`?  Folded into
`Expr.allLevelParamsDefined` (task #161): level instantiation's
composition law (`Level.substPW_comp`) is *false* for data whose
parameters escape the declaration's — exactly as for the levels
themselves. -/
def paramsDefined (params : List Name) : PropWhen → Bool
  | .never => true
  | .ifAllZero ps => ps.all params.contains

/-- Intersection of two zero-ness predicates (the `max` rule: a `max`
is zero iff both sides are): `never` absorbs, sets append. -/
def inter : PropWhen → PropWhen → PropWhen
  | .never, _ => .never
  | _, .never => .never
  | .ifAllZero ps, .ifAllZero qs => .ifAllZero (ps ++ qs)

/-- Substitute each parameter of the datum by a whole datum and
intersect ("all of `ps` zero" becomes "all replacements zero") — the
monadic bind of the zero-ness reading.  Shape-preserving: parameters
mapped to `ifAllZero [n]` reproduce the input list exactly, which is
what the unconditional substitution laws rest on. -/
def bindZ (f : Name → PropWhen) : PropWhen → PropWhen
  | .never => .never
  | .ifAllZero ps => go ps
where
  go : List Name → PropWhen
  | [] => .ifAllZero []
  | n :: rest => (f n).inter (go rest)

/-- Decidable zero-ness agreement at *every* valuation: mutual
containment of the parameter sets (`never` only agrees with `never` —
`ifAllZero` data hold at the all-zero valuation, `never` nowhere).
Sound and complete (`Verify.PropWhen`); this is the comparison every
validation and defeq site uses. -/
def equiv : PropWhen → PropWhen → Bool
  | .never, .never => true
  | .ifAllZero ps, .ifAllZero qs =>
    ps.all qs.contains && qs.all ps.contains
  | _, _ => false

end PropWhen

/-- Metadata carried by a binder (`forallE`, `lam`): the display
`BinderInfo` and the codomain prop-ness annotation `pw` (task #161 —
the validated-annotation design; one datum per binder, written by the
untrusted annotate pass or the input stream and *validated* by the
checker; the reduction rules never read it).  Unannotated input
defaults to `.never` at the parser — a definite, validatable claim. -/
structure BinderMeta where
  bi : BinderInfo
  pw : PropWhen
  deriving DecidableEq, Repr, Hashable

instance : Inhabited BinderMeta := ⟨⟨.default, .never⟩⟩

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
