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

/-- The head of an application spine. -/
def getAppFn : Expr → Expr
  | .app f _ => getAppFn f
  | e => e

/-- The arguments of an application spine, outermost last. -/
def getAppArgs : Expr → List Expr
  | .app f a => getAppArgs f ++ [a]
  | _ => []

/-- Apply to a list of arguments. -/
def mkAppN (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => mkAppN (.app f a) as

/-- Fully zeta-expand: replace every `let x := v in b` by `b[v/x]`
(value and body expanded first, so the result is let-free and the
recursion structural).  Applied by the frontend when building
declarations; `let` is definitionally its expansion, so checking the
expansion is checking the original (the per-occurrence re-checking
costs performance, not soundness — revisit with performance work). -/
def zetaExpand : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n (zetaExpand ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (zetaExpand f) (zetaExpand a)
  | .lam n ty body m => .lam n (zetaExpand ty) (zetaExpand body) m
  | .forallE n ty body m => .forallE n (zetaExpand ty) (zetaExpand body) m
  | .letE _ _ val body => (zetaExpand body).instantiate1 (zetaExpand val)
  | .lit l => .lit l
  | .proj s i e => .proj s i (zetaExpand e)

/-- Rename constants throughout (including inside `fvar` type
annotations and `proj` type names); levels and binders untouched.  Used
to compare a modeled inductive's members against their `_model`
counterparts. -/
def renameConsts (f : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i n ty => .fvar i n (renameConsts f ty)
  | .sort u => .sort u
  | .const n us => .const (f n) us
  | .app a b => .app (renameConsts f a) (renameConsts f b)
  | .lam n ty body m => .lam n (renameConsts f ty) (renameConsts f body) m
  | .forallE n ty body m =>
    .forallE n (renameConsts f ty) (renameConsts f body) m
  | .letE n ty v body =>
    .letE n (renameConsts f ty) (renameConsts f v) (renameConsts f body)
  | .lit l => .lit l
  | .proj s i e => .proj (f s) i (renameConsts f e)

/-- Bump every loose bound variable `≥ cutoff` by `amount`.  Used to
transport a constructor-telescope field domain (parameters, then prior
fields) into a recursor-rule telescope (parameters, motive, minors,
then prior fields): parameter references must skip the extra motive
and minor binders. -/
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i n ty => .fvar i n ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam n ty body m =>
    .lam n (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body) m
  | c, .forallE n ty body m =>
    .forallE n (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body) m
  | c, .letE n ty v body =>
    .letE n (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)

/-- Strip `k` leading lambdas: the binder list (outermost first) and
the body. -/
def stripLams : Nat → Expr → Option (List (Name × Expr × BinderMeta) × Expr)
  | 0, e => some ([], e)
  | k + 1, .lam n ty b m =>
    (stripLams k b).map fun (bs, e) => ((n, ty, m) :: bs, e)
  | _ + 1, _ => none

/-- Strip `k` leading `∀`s: the binder list (outermost first) and the
body. -/
def stripPis : Nat → Expr → Option (List (Name × Expr × BinderMeta) × Expr)
  | 0, e => some ([], e)
  | k + 1, .forallE n ty b m =>
    (stripPis k b).map fun (bs, e) => ((n, ty, m) :: bs, e)
  | _ + 1, _ => none

/-- The binder infos of the first `k` binders of a `∀`-telescope. -/
def piBinderInfos : Nat → Expr → Option (List BinderInfo)
  | 0, _ => some []
  | k + 1, .forallE _ _ b m => (piBinderInfos k b).map (m.bi :: ·)
  | _ + 1, _ => none

/-- The result sort at the end of a `∀`-telescope. -/
def resultSort : Expr → Option Level
  | .forallE _ _ b _ => resultSort b
  | .sort u => some u
  | _ => none

end Setlec.Expr
