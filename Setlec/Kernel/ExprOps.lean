import Setlec.Kernel.Expr

/-!
# Expression operations

`instantiate1` opens a binder body: the bound variable `bvar 0` is replaced
by a given expression (in practice an `fvar`, which is closed, so no
de Bruijn shifting of the replacement is needed).

`sizeB` is the termination measure for functions that recurse into
instantiated binder bodies: it counts expression nodes but gives every
`fvar` size 1 regardless of its annotated type.  Instantiating a `bvar`
(size 1) with an `fvar` (size 1) preserves it (`sizeB_instantiate1`), so
`sizeB body < sizeB (forallE n ty body)` keeps holding after opening.
-/

namespace Setlec.Expr

/-- Replace `bvar d` by `v` in `e`, where `d` counts the binders passed on
the way (callers start at the default `d = 0`).  `v` must be closed with
respect to bound variables (an `fvar`, a constant, …); it is not shifted.
Loose `bvar`s above `d` are lowered by one. -/
def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1 f v d) (instantiate1 a v d)
  | .lam n ty body bi => .lam n (instantiate1 ty v d) (instantiate1 body v (d + 1)) bi
  | .forallE n ty body bi => .forallE n (instantiate1 ty v d) (instantiate1 body v (d + 1)) bi
  | .letE n ty val body =>
    .letE n (instantiate1 ty v d) (instantiate1 val v d) (instantiate1 body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1 e v d)

/-- Node count with `fvar` counted as a leaf (its annotated type ignored).
Termination measure for recursion into instantiated binder bodies. -/
def sizeB : Expr → Nat
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lit _ => 1
  | .app f a => sizeB f + sizeB a + 1
  | .lam _ ty body _ | .forallE _ ty body _ => sizeB ty + sizeB body + 1
  | .letE _ ty val body => sizeB ty + sizeB val + sizeB body + 1
  | .proj _ _ e => sizeB e + 1

theorem sizeB_pos (e : Expr) : 0 < sizeB e := by
  cases e <;> simp [sizeB]

/-- Instantiating with a size-1 replacement preserves `sizeB`. -/
theorem sizeB_instantiate1 (v : Expr) (hv : sizeB v = 1) :
    ∀ (e : Expr) (d : Nat), sizeB (instantiate1 e v d) = sizeB e := by
  intro e
  induction e <;> intro d <;> simp [instantiate1, sizeB, *]
  case bvar i =>
    split
    · exact hv
    · split <;> rfl

/-- Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping
`k` under binders — the inverse of `instantiate1` with a fresh variable
(`fvar` type annotations are not descended into; a well-scoped term has no
`fvar d` inside another variable's annotation). -/
def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx n ty => if idx = d then .bvar k else .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstract1 f d k) (abstract1 a d k)
  | .lam n ty body m => .lam n (abstract1 ty d k) (abstract1 body d (k + 1)) m
  | .forallE n ty body m => .forallE n (abstract1 ty d k) (abstract1 body d (k + 1)) m
  | .letE n ty val body =>
    .letE n (abstract1 ty d k) (abstract1 val d k) (abstract1 body d (k + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstract1 e d k)

/-- Full node count, including `fvar` type annotations.  Termination
measure for predicates that recurse into annotations (but never into
instantiated bodies). -/
def sizeF : Expr → Nat
  | .bvar _ | .sort _ | .const .. | .lit _ => 1
  | .fvar _ _ ty => sizeF ty + 1
  | .app f a => sizeF f + sizeF a + 1
  | .lam _ ty body _ | .forallE _ ty body _ => sizeF ty + sizeF body + 1
  | .letE _ ty val body => sizeF ty + sizeF val + sizeF body + 1
  | .proj _ _ e => sizeF e + 1

/-- Are all bound-variable references bound within the expression (below
`k` at the root)?  Input declarations must satisfy `looseBVarsBounded 0`. -/
def looseBVarsBounded (k : Nat) : Expr → Bool
  | .bvar i => i < k
  | .fvar _ _ _ => true
  | .sort _ | .const _ _ | .lit _ => true
  | .app f a => looseBVarsBounded k f && looseBVarsBounded k a
  | .lam _ ty body _ | .forallE _ ty body _ =>
    looseBVarsBounded k ty && looseBVarsBounded (k + 1) body
  | .letE _ ty val body =>
    looseBVarsBounded k ty && looseBVarsBounded k val && looseBVarsBounded (k + 1) body
  | .proj _ _ e => looseBVarsBounded k e

/-- Does the expression contain any free variable (`fvar`)?  Input
declarations must be `fvar`-free; the checker introduces `fvar`s only
internally when opening binders. -/
def hasFvar : Expr → Bool
  | .bvar _ | .sort _ | .const .. | .lit _ => false
  | .fvar .. => true
  | .app f a => hasFvar f || hasFvar a
  | .lam _ ty body _ | .forallE _ ty body _ => hasFvar ty || hasFvar body
  | .letE _ ty val body => hasFvar ty || hasFvar val || hasFvar body
  | .proj _ _ e => hasFvar e

end Setlec.Expr
