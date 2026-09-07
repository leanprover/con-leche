import Lech.Kernel.Expr
import Lech.Kernel.Level

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

namespace Lech.Expr

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

/-- Bulk instantiation (task #50): substitute the replacement list `vs`
for the bound variables `bvar d, bvar (d + 1), …` in one traversal —
`vs[0]` replaces `bvar d` (the *innermost* binder of a peeled
telescope), `vs[i]` replaces `bvar (d + i)`; loose `bvar`s above the
range are lowered by `vs.length`.

The semantics is by construction the *fold* of `instantiate1`:

  `instantiateList e (v :: vs) d
     = (instantiateList e vs (d + 1)).instantiate1 v d`

(`instantiateList_cons`, unconditional) — so a chain that consumes a
spine `a₁ … aₖ` outermost-first equals one call at the accumulator list
`[aₖ, …, a₁]`.  In the fold, a replacement inserted early is traversed
again by the later `instantiate1` passes; the `bvar` case reproduces
this by recursing into the replacement with the *earlier-listed*
entries (`vs.take i` — the substitutions the fold applies after
inserting `vs[i]`).  On `bvar`-closed replacements (every checker call
site) that recursion is the identity, and the cost is a single
traversal of `e` instead of `vs.length` traversals. -/
def instantiateList (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar j =>
    if j < d then .bvar j
    else if h : j - d < vs.length then
      instantiateList vs[j - d] (vs.take (j - d)) d
    else .bvar (j - vs.length)
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiateList f vs d) (instantiateList a vs d)
  | .lam n ty body bi =>
    .lam n (instantiateList ty vs d) (instantiateList body vs (d + 1)) bi
  | .forallE n ty body bi =>
    .forallE n (instantiateList ty vs d) (instantiateList body vs (d + 1)) bi
  | .letE n ty val body =>
    .letE n (instantiateList ty vs d) (instantiateList val vs d)
      (instantiateList body vs (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiateList e vs d)
termination_by (vs.length, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp [List.length_take]; omega)
    | (apply Prod.Lex.right; simp; omega)

/-- Bump every loose bound variable `≥ cutoff` by `amount`.  Used to
transport a constructor-telescope field domain (parameters, then prior
fields) into a recursor-rule telescope (parameters, motive, minors,
then prior fields): parameter references must skip the extra motive
and minor binders, and by the zeta expansion's substitution to carry
open let-values under binders. -/
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

/-- Lower every loose bound variable `≥ cutoff + amount` by `amount`
(loose variables inside the window `[cutoff, cutoff + amount)` are left
untouched — callers certify their absence by the `liftLooseBVars`
roundtrip).  Used by the nested-rule shape certification to read a
recursor's constructor-parameter instantiations out of the
major-premise domain (an `mI`-binder context) into the rule-prefix
context (`rP` binders): `p = (p.lowerBVars (mI - rP) 0).liftLooseBVars
(mI - rP) 0` holds exactly when `p` mentions no index variable. -/
def lowerBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c + amount then .bvar (i - amount) else .bvar i
  | _, .fvar i n ty => .fvar i n ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (lowerBVars amount c a) (lowerBVars amount c b)
  | c, .lam n ty body m =>
    .lam n (lowerBVars amount c ty) (lowerBVars amount (c + 1) body) m
  | c, .forallE n ty body m =>
    .forallE n (lowerBVars amount c ty) (lowerBVars amount (c + 1) body) m
  | c, .letE n ty v body =>
    .letE n (lowerBVars amount c ty) (lowerBVars amount c v)
      (lowerBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (lowerBVars amount c e)

/-- Replace `bvar d` by `v`, *lifting* `v`'s loose `bvar`s past the
binders crossed on the way — the general capture-avoiding substitution
for an open `v` (unlike `instantiate1`, which requires `v` to be
`bvar`-closed).  Let-values are open terms. -/
def instantiate1Lift (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i =>
    if i = d then Expr.liftLooseBVars d 0 v
    else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1Lift f v d) (instantiate1Lift a v d)
  | .lam n ty body bi =>
    .lam n (instantiate1Lift ty v d) (instantiate1Lift body v (d + 1)) bi
  | .forallE n ty body bi =>
    .forallE n (instantiate1Lift ty v d) (instantiate1Lift body v (d + 1)) bi
  | .letE n ty val body =>
    .letE n (instantiate1Lift ty v d) (instantiate1Lift val v d)
      (instantiate1Lift body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1Lift e v d)

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

/-- Bulk abstraction (task #72): close `k` binders in one traversal —
replace `fvar (d + i) …` leaves (`i < k`) by the bound variable of the
`i`-th binder counted outermost-first, i.e. `bvar (c + (d + k - 1 - idx))`
at the traversal cursor `c` (bumped under binders; `fvar` type
annotations are not descended into, as in `abstract1`).  The semantics
is by construction the *fold* of `abstract1`, innermost binder first:

  `abstractRange e d (k + 1) c
     = abstractRange (e.abstract1 (d + k) c) d k (c + 1)`

(`abstractRange_succ`, `Lech/Verify/Abstract.lean`) — so the nested
per-binder `abstract1` chain of a telescope rebuild equals one
`abstractRange` pass per binder domain and one over the leaf. -/
def abstractRange (e : Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx n ty =>
    if d ≤ idx ∧ idx < d + k then .bvar (c + (d + k - 1 - idx))
    else .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstractRange f d k c) (abstractRange a d k c)
  | .lam n ty body m =>
    .lam n (abstractRange ty d k c) (abstractRange body d k (c + 1)) m
  | .forallE n ty body m =>
    .forallE n (abstractRange ty d k c) (abstractRange body d k (c + 1)) m
  | .letE n ty val body =>
    .letE n (abstractRange ty d k c) (abstractRange val d k c)
      (abstractRange body d k (c + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstractRange e d k c)

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

/-- All reachable `fvar` leaves, including (hereditarily) those inside
their type annotations. -/
def fvarLeaves : Expr → List (Nat × Name × Expr)
  | .fvar idx n ty => (idx, n, ty) :: fvarLeaves ty
  | .app f a => fvarLeaves f ++ fvarLeaves a
  | .lam _ ty b _ | .forallE _ ty b _ => fvarLeaves ty ++ fvarLeaves b
  | .letE _ t v b => fvarLeaves t ++ fvarLeaves v ++ fvarLeaves b
  | .proj _ _ e => fvarLeaves e
  | _ => []
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Scope check: every reachable `fvar` index is below `d`,
hereditarily through annotations (the `Bool` mirror of the
verification-side `WScoped`).

Not on any per-memo-op path (task #43): the memoized knot's cache
operations run unguarded, justified by the proven call discipline
(`Lech/Verify/Disc.lean`).  Remaining executable call sites are the
scope guards on checker-fabricated terms in `Lech/Kernel/Core.lean`
(the stuck-major rescues in `majorToCtor`; the projection
eliminations went with task #175 wiring W5), each O(small
fabricated term) once per fabrication.  TODO(cleanup, task #26):
interning should cache the fvar range per node, making those O(1). -/
def wscopedB : (d : Nat) → Expr → Bool
  | d, .fvar idx _ ty => idx < d && wscopedB idx ty
  | d, .app f a => wscopedB d f && wscopedB d a
  | d, .lam _ ty body _ => wscopedB d ty && wscopedB d body
  | d, .forallE _ ty body _ => wscopedB d ty && wscopedB d body
  | d, .letE _ ty val body =>
    wscopedB d ty && wscopedB d val && wscopedB d body
  | d, .proj _ _ e => wscopedB d e
  | _, .bvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => true
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Are all bound-variable references bound within the expression (below
`k` at the root)?  Input declarations must satisfy `looseBVarsBounded 0`.

TODO(cleanup, task #26): unmemoized expression traversal (exponential
on shared terms); interning should cache the loose-bvar bound per
node, making this O(1). -/
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

/-- Is the expression a λ?  The λ-rule's codomain-sort check (task
#152) fires once per λ *chain* — at the innermost binder, whose body
is not itself a λ — because that is the granularity the interned
binder-telescope loop (task #72) can reproduce. -/
def isLam : Expr → Bool
  | .lam .. => true
  | _ => false

/-- The prop-ness annotation of a λ node's meta, `none` off λs — the
head reading the task-#161 chain rule consumes (an outer λ's codomain
prop-ness is its body-λ's own annotation).  Total, so the walks
commute with it structurally (`lamPw_instantiateList_fvars`,
`lamPw_shiftFrom` in `Lech/Verify`). -/
def lamPw : Expr → Option PropWhen
  | .lam _ _ _ mbI => some mbI.pw
  | _ => none

/-- The ∀ twin of `lamPw`: a ∀ node's prop-ness datum, read off the
node.  Task #161 P5 repair — `annotPwPi` reads it to realise the
telescope collapse (`zeronessOf (imax u v) = zeronessOf v`) as a chain
rule, exactly as `annotPwLam` reads `lamPw`. -/
def forallPw : Expr → Option PropWhen
  | .forallE _ _ _ mbI => some mbI.pw
  | _ => none

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
  -- Task #175 wiring W5: a `.proj` node's struct name is NOT renamed.
  -- The renaming exists for the modeled-block contract (a public
  -- block's types against its `_model` artifacts, `eqUpToNames` and
  -- the fire comparands); a block's own projections can never be
  -- spelled inside its types (their entries do not exist when the
  -- types are annotated), and a `.proj` on any *other* structure names
  -- it the same on both sides — so the rename never had a matching
  -- case here.  Fixing the name keeps the entry-kind readings
  -- (`denote`/`denoteP`, which consult the table at the struct name)
  -- rename-invariant by construction (DESIGN, "W5 opening seam").
  | .proj s i e => .proj s i (renameConsts f e)

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

/-- The body of a syntactic `∀`-telescope (the expression itself when
it is not a `∀`). -/
def piResult : Expr → Expr
  | .forallE _ _ b _ => piResult b
  | e => e

/-- Instantiate a `∀`-telescope with arguments, in order. -/
def instPis : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ body _, a :: as => instPis (body.instantiate1 a) as
  | _, _ :: _ => none

/-- Instantiate the leading `∀`-binders at the given arguments,
returning each binder's (progressively instantiated) domain together
with the fully instantiated residual. -/
def instPisAt : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e)
  | a :: as, .forallE _ dom body _ =>
    (instPisAt as (body.instantiate1 a)).map fun (ds, rest) =>
      (dom :: ds, rest)
  | _ :: _, _ => none

/-- Instantiate the leading `∀`-binders at *open* arguments, returning
the residual.  Unlike `instPisAt` this uses the general
capture-avoiding substitution (`instantiate1Lift`), so an argument may
mention loose `bvar`s of the surrounding context — which is what
building a projection's type out of the constructor telescope needs. -/
def instPisAtLift : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ _ body _ => instPisAtLift as (body.instantiate1Lift a)
  | _ :: _, _ => none

/-- `instPisAt` for `λ`-binders. -/
def instLamsAt : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e)
  | a :: as, .lam _ dom body _ =>
    (instLamsAt as (body.instantiate1 a)).map fun (ds, rest) =>
      (dom :: ds, rest)
  | _ :: _, _ => none

/-! ### Bulk telescope instantiation (task: fields-raw near-cubic)

`instPisAt`/`instLamsAt` fold `instantiate1` over the argument list, so
each argument re-traverses the whole remaining telescope — quadratic in
the telescope, and the per-projection outer loop of the direct
simple-structure install made that cubic.  The `*F` variants below
compute the *same value* (`instPisAtF_eq`/`instLamsAtF_eq`,
`Lech/Verify/FastOps.lean`) in **one** pass: the raw binders are
peeled structurally while the pending substitutions accumulate, and
each domain (and the residual) receives them in a single
`instantiateList` traversal.  When the raw telescope is shorter than
the argument list (a binder only *created* by substitution) the `Go`
walk reports `none` and the wrapper falls back to the sequential
spec — so the equality is unconditional. -/

/-- Core of `instPisAtF`: `acc` holds the pending substitutions,
innermost binder first.  Computes
`instPisAt args (e.instantiateList acc)` whenever `e` raw-strips
`args.length` `∀`-binders (`instPisAtFGo_sound`), `none` otherwise. -/
def instPisAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e.instantiateList acc)
  | a :: as, .forallE _ dom body _ =>
    (instPisAtFGo (a :: acc) as body).map fun (ds, rest) =>
      (dom.instantiateList acc :: ds, rest)
  | _ :: _, _ => none

/-- One-pass `instPisAt` (equal to it: `instPisAtF_eq`). -/
def instPisAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr) :=
  match instPisAtFGo [] args e with
  | some r => some r
  | none => instPisAt args e

/-- Core of `instLamsAtF` (the `λ` counterpart of `instPisAtFGo`). -/
def instLamsAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e.instantiateList acc)
  | a :: as, .lam _ dom body _ =>
    (instLamsAtFGo (a :: acc) as body).map fun (ds, rest) =>
      (dom.instantiateList acc :: ds, rest)
  | _ :: _, _ => none

/-- One-pass `instLamsAt` (equal to it: `instLamsAtF_eq`). -/
def instLamsAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr) :=
  match instLamsAtFGo [] args e with
  | some r => some r
  | none => instLamsAt args e

/-- The type annotation of a free-variable leaf (the expression itself
otherwise; used to read the domains off an opened telescope's
variables). -/
def fvarTypeD : Expr → Expr
  | .fvar _ _ ty => ty
  | e => e

/-- Instantiate a telescope-context expression at an argument spine:
`bvar t` is replaced by the first argument, descending (the per-domain
effect of peeling a `t + 1`-binder telescope at the spine; the
verification's `instSeq`).  Used to evaluate a nested-auxiliary rule's
stored constructor-parameter instantiations at the recursor's actual
arguments. -/
def instSpine : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpine as (t - 1) (e.instantiate1 a t)

/-- A recursor rule is *canonical* when its constructor's parameters
are exactly the recursor's own leading arguments: the major premise's
type applies the eliminated family to the first `cnP` telescope
variables.  Rules for nested auxiliary constructors (whose parameters
are instantiations like `Array Syntax`) are not canonical; they are
stored `.nested` when the certification against the model's `iota_j`
theorem succeeds (see `checkIotaThmN`) and `.inert` otherwise —
`iotaRec` never fires an inert rule, so it carries no fold
obligation. -/
def recRulePlain (recTy : Expr) (mI rP cnP : Nat) : Bool :=
  decide (cnP ≤ rP) && decide (rP ≤ mI) &&
  match recTy.stripPis mI with
  | some (_, .forallE _ dom _ _) =>
    dom.getAppArgs.take cnP ==
      (List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))
  | _ => false

/-- Convert the first `k` `∀`-binders into `λ`-binders over a body.

The copied binder metadata keeps only the display info: a ∀'s `pw`
claims the *codomain*'s prop-ness, which is not the λ's claim (the sort
of the body's *type*), so carrying it over would be a wrong annotation.
The result is emitted at the parse placeholder `.never` and **every
consumer must run the annotate pass over it before storing or using
it** — audited: `CheckerS.checkProjRule` and `CheckerBase`'s projection
rule builder feed `ops.annotate` (DESIGN.md, task #161,
manufacture-site audit row 9; the third consumer, `annotateProjRec`,
went with task #175 wiring W5). -/
def pisToLams : Nat → Expr → Expr → Option Expr
  | 0, _, body => some body
  | k + 1, .forallE n ty rest m, body =>
    (pisToLams k rest body).map fun b => .lam n ty b ⟨m.bi, .never⟩
  | _ + 1, _, _ => none

/-- Replace the body under the first `k` `∀`-binders (binder domains and
names kept, codomain-sort annotations reset — the caller annotates). -/
def replacePiBody : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE n ty rest m, b =>
    (replacePiBody k rest b).map fun r => .forallE n ty r ⟨m.bi, m.pw⟩
  | _ + 1, _, _ => none

/-- The length of the leading `∀`-telescope. -/
def piArity : Expr → Nat
  | .forallE _ _ b _ => piArity b + 1
  | _ => 0

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

/-- Structural equality ignoring display-only names: the binder names
of `lam`/`forallE`/`letE` and an `fvar`'s display name.  Everything
semantic still compares — indices, constants, levels, `BinderMeta`
(binder info *and* the codomain sort annotation), and an `fvar`'s type
annotation (part of the variable's identity).  lean4export interns
expressions irrespective of binder names (the first occurrence's
spelling wins for every shared subterm), so even a correct
preprocessor stream can differ from the input in binder names only;
`checkMemberVal` compares member types with this.

Task #203: since the frontend parses every binder name to
`.anonymous`, this coincides with `==` on every pair `checkMemberVal`
feeds it (both sides are stream terms).  It is kept as the spec the
proofs consume (`ErasedEq.of_eqUpToNames`, `Verify/Subst.lean`, and
its ~20 consumers across `Verify/Extend/*`, `Semantics/*`, `SetP/*`)
rather than replaced by `==`, whose proof-side transport would be the
same theorem restated at `rfl`. -/
def eqUpToNames : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i _ ty, .fvar j _ ty' => i == j && eqUpToNames ty ty'
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app g b => eqUpToNames f g && eqUpToNames a b
  | .lam _ ty b m, .lam _ ty' b' m' =>
    m == m' && eqUpToNames ty ty' && eqUpToNames b b'
  | .forallE _ ty b m, .forallE _ ty' b' m' =>
    m == m' && eqUpToNames ty ty' && eqUpToNames b b'
  | .letE _ ty v b, .letE _ ty' v' b' =>
    eqUpToNames ty ty' && eqUpToNames v v' && eqUpToNames b b'
  | .lit l, .lit l' => l == l'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && eqUpToNames e e'
  | _, _ => false

/-! ## Derived-field spec functions, and their exactness

The four `@[computed_field]`s of `Expr` (`Lech/Kernel/Expr.lean`) are
declared by their recurrences; these are the same recurrences written
as ordinary definitions, together with the equivalences that make a
field read license the traversal cutoff it guards.  Self-contained:
they mention nothing but `Expr`.

They lived in `Lech/Kernel/ArenaWF.lean` (the parallel-array
exactness proofs) and `Lech/Verify/IExpr.lean` until task #172's
interned removal; the cached engine's field facts
(`Lech/Verify/Cached/Erase.lean`) are stated against them. -/

/-- The least `k` with `looseBVarsBounded k` (the spec function of the
eager `bvarBs` entries). -/
def _root_.Lech.Expr.bvarBound : Expr → Nat
  | .bvar i => i + 1
  | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.bvarBound a.bvarBound
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max ty.bvarBound (body.bvarBound - 1)
  | .letE _ ty val body =>
    max (max ty.bvarBound val.bvarBound) (body.bvarBound - 1)
  | .proj _ _ e => e.bvarBound

/-- `bvarBound` is exact for `looseBVarsBounded`. -/
theorem looseBVarsBounded_iff {x : Expr} :
    ∀ {k : Nat}, x.looseBVarsBounded k = true ↔ x.bvarBound ≤ k := by
  induction x <;> intro k <;>
    (try simp [Expr.looseBVarsBounded, Expr.bvarBound, Nat.max_le, *]) <;>
    omega

/-- The least `d` with `fvarsBelow d` (the spec function of the eager
`fvarBs` entries; `fvar` type annotations are not descended, matching
`fvarsBelow` and the abstraction traversals). -/
def _root_.Lech.Expr.fvarRange : Expr → Nat
  | .fvar idx _ _ => idx + 1
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.fvarRange a.fvarRange
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max ty.fvarRange body.fvarRange
  | .letE _ ty val body =>
    max (max ty.fvarRange val.fvarRange) body.fvarRange
  | .proj _ _ e => e.fvarRange

/-- A term is fvar-free iff its range is zero. -/
theorem hasFvar_eq_false_iff {x : Expr} :
    x.hasFvar = false ↔ x.fvarRange = 0 := by
  induction x <;>
    simp_all [Expr.hasFvar, Expr.fvarRange, Nat.max_eq_zero_iff,
      and_assoc]

/-- A term has a reachable fvar leaf iff its range is nonzero. -/
theorem fvarRange_bne_zero {x : Expr} : (x.fvarRange != 0) = x.hasFvar := by
  cases hh : x.hasFvar with
  | false => simp [hasFvar_eq_false_iff.mp hh]
  | true =>
    have hne : x.fvarRange ≠ 0 := by
      intro h0
      rw [hasFvar_eq_false_iff.mpr h0] at hh
      cases hh
    simpa using hne

/-! ## The saturated branch of the packed range fields (task #167)

`Expr.bvarBRaw`/`Expr.fvarBRaw` (`Kernel/Expr.lean`) are the packed
word's 15-bit range fields; they *saturate* at `satRange`.  The
accessors the checker reads — `Expr.bvarB`, `Expr.fvarB` — stay
**exact**: below saturation they are the field, and at saturation they
fall back to a memoized recomputation of the very same recurrence.

Two consequences, and they are the point of the design:

* **no lemma weakens** — `bvarB_eq`/`fvarB_eq`
  (`Verify/Cached/Erase.lean`) are still plain equations with the spec
  functions, so no skip site grows a guard and no invariant is
  threaded anywhere;
* **what saturation costs is time, not truth** — the `O(1)` field read
  becomes an `O(DAG)` walk, and only on a term with `satRange` loose
  bvars (or fvar levels).  The measured maxima on the real streams are
  213 (`init-full`), 488 (`grind-ring-5`) and 4000 (`app-lam`, the
  deepest artificial workload) against `satRange = 32767`.

The walks are **memoized** (an `Std.HashMap` keyed by the node) so
that even the fallback stays linear in the DAG rather than the
unfolded tree — the standing "no unmemoized traversals in executable
paths" rule applies to the saturated branch too. -/

/-- Memoized `bvarBound` (the saturated branch's exact recomputation). -/
def bvarBoundGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .bvar i => (i + 1, memo)
      | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := bvarBoundGo memo f
        let (ra, memo) := bvarBoundGo memo a
        (max rf ra, memo)
      | .lam _ ty body _ | .forallE _ ty body _ =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rb, memo) := bvarBoundGo memo body
        (max rt (rb - 1), memo)
      | .letE _ ty val body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rv, memo) := bvarBoundGo memo val
        let (rb, memo) := bvarBoundGo memo body
        (max (max rt rv) (rb - 1), memo)
      | .proj _ _ sub => bvarBoundGo memo sub
    (r, memo.insert e r)

@[inherit_doc bvarBoundGo]
def bvarBoundMemo (e : Expr) : Nat := (bvarBoundGo {} e).1

/-- Memoized `fvarRange` (the saturated branch's exact
recomputation). -/
def fvarRangeGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .fvar idx _ _ => (idx + 1, memo)
      | .bvar _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := fvarRangeGo memo f
        let (ra, memo) := fvarRangeGo memo a
        (max rf ra, memo)
      | .lam _ ty body _ | .forallE _ ty body _ =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rb, memo) := fvarRangeGo memo body
        (max rt rb, memo)
      | .letE _ ty val body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rv, memo) := fvarRangeGo memo val
        let (rb, memo) := fvarRangeGo memo body
        (max (max rt rv) rb, memo)
      | .proj _ _ sub => fvarRangeGo memo sub
    (r, memo.insert e r)

@[inherit_doc fvarRangeGo]
def fvarRangeMemo (e : Expr) : Nat := (fvarRangeGo {} e).1

/-- **The loose-bvar bound the checker reads**: the packed field, or —
on the saturated branch alone — the exact memoized recomputation.
Equal to `Expr.bvarBound` unconditionally (`bvarB_eq`). -/
@[inline] def bvarB (e : Expr) : Nat :=
  let r := e.bvarBRaw
  if r == satRange then bvarBoundMemo e else r

/-- **The fvar range the checker reads**: the packed field, or — on the
saturated branch alone — the exact memoized recomputation.  Equal to
`Expr.fvarRange` unconditionally (`fvarB_eq`). -/
@[inline] def fvarB (e : Expr) : Nat :=
  let r := e.fvarBRaw
  if r == satRange then fvarRangeMemo e else r


/-! ## Pointer-equality shortcut -/

/-- Structural expression equality with a physical-equality shortcut
(definitionally `a == b`).  Used to validate interned-environment
entries against the stored constant they cache: the entry was created
from the very object stored in the environment, so the pointer test
succeeds without walking either expression. -/
@[inline] def exprPtrBEq (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by subst h; simp)

/-! ## Level-parameter occurrence, and the substitution shortcuts

`Level.hasParam` / `Expr.hasLevelParam` are the spec functions of the
`hasLP` computed field (`Lech/Kernel/Expr.lean`); the lemmas below
are the shortcuts a `false` reading licenses.  Self-contained, and the
cached engine's field facts (`Lech/Verify/Cached/Erase.lean`) are
stated against them.  They lived in `Lech/Kernel/ArenaWF.lean` until
task #172. -/

/-- Whether a level mentions any parameter (the spec function of the
eager `lparamBs` entries; official kernel `level.cpp` `has_param`,
task #87). -/
def _root_.Lech.Level.hasParam : Level → Bool
  | .param _ => true
  | .zero => false
  | .succ u => u.hasParam
  | .max u v | .imax u v => u.hasParam || v.hasParam

/-- Substitution is the identity on param-free levels. -/
theorem _root_.Lech.Level.subst_eq_self {ks : List Name}
    {vs : List Level} {l : Level} (h : l.hasParam = false) :
    l.subst ks vs = l := by
  induction l <;> simp_all [Level.hasParam, Level.subst]

/-- Parameter definedness is trivial on param-free levels. -/
theorem _root_.Lech.Level.allParamsDefined_of_not_hasParam
    {params : List Name} {l : Level} (h : l.hasParam = false) :
    l.allParamsDefined params = true := by
  induction l <;> simp_all [Level.hasParam, Level.allParamsDefined]

/-- Whether an expression mentions any level parameter (the spec
function of the eager `eparamBs` entries; `fvar` type annotations
included, matching `Expr.instantiateLevelParams`; binder prop-ness
data included since task #161 — `instantiateLevelParams` substitutes
into them, so the shortcut must see their parameters). -/
def _root_.Lech.Expr.hasLevelParam : Expr → Bool
  | .bvar _ | .lit _ => false
  | .sort u => u.hasParam
  | .const _ us => us.any Level.hasParam
  | .fvar _ _ ty => ty.hasLevelParam
  | .app f a => f.hasLevelParam || a.hasLevelParam
  | .lam _ ty body m | .forallE _ ty body m =>
    ty.hasLevelParam || body.hasLevelParam || m.pw.hasParams
  | .letE _ ty val body =>
    ty.hasLevelParam || val.hasLevelParam || body.hasLevelParam
  | .proj _ _ e => e.hasLevelParam

/-- `substPW` is the identity on parameter-free data (`never` and
`ifAllZero []`) — the meta half of the has-param shortcut's
soundness. -/
theorem _root_.Lech.Level.substPW_eq_self {ks : List Name}
    {us : List Level} {pw : PropWhen} (h : pw.hasParams = false) :
    Level.substPW ks us pw = pw := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons p ps => simp at h

/-- Parameter-free data are defined under any parameter list. -/
theorem _root_.Lech.PropWhen.paramsDefined_of_not_hasParams
    {params : List Name} {pw : PropWhen} (h : pw.hasParams = false) :
    pw.paramsDefined params = true := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons p ps => simp at h

/-- Level-parameter instantiation is the identity on level-param-free
expressions. -/
theorem _root_.Lech.Expr.instantiateLevelParams_eq_self
    {ks : List Name} {us : List Level} {x : Expr}
    (h : x.hasLevelParam = false) :
    x.instantiateLevelParams ks us = x := by
  induction x with
  | bvar i => rfl
  | lit l => rfl
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, Level.subst_eq_self h]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    have hmap : vs.map (Level.subst ks us) = vs := by
      induction vs with
      | nil => rfl
      | cons v t iht =>
        simp only [List.map_cons]
        rw [Level.subst_eq_self (by simpa using h v (by simp)),
          iht fun w hw => h w (by simp [hw])]
    simp [Expr.instantiateLevelParams, hmap]
  | fvar idx nm ty ih =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ih h]
  | app f a ihf iha =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam nm ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.instantiateLevelParams, iht ht, ihb hb,
      Level.substPW_eq_self hm]
  | forallE nm ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.instantiateLevelParams, iht ht, ihb hb,
      Level.substPW_eq_self hm]
  | letE nm ty val body iht ihv ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj sp j e ihe =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ihe h]

/-- Level-parameter definedness is trivial on level-param-free
expressions. -/
theorem _root_.Lech.Expr.allLevelParamsDefined_of_not_hasLevelParam
    {params : List Name} {x : Expr} (h : x.hasLevelParam = false) :
    x.allLevelParamsDefined params = true := by
  induction x with
  | lam nm ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
      PropWhen.paramsDefined_of_not_hasParams hm]
  | forallE nm ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
      PropWhen.paramsDefined_of_not_hasParams hm]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    exact fun v hv =>
      Level.allParamsDefined_of_not_hasParam (by simpa using h v hv)
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    exact Level.allParamsDefined_of_not_hasParam h
  | _ =>
    simp_all [Expr.hasLevelParam, Expr.allLevelParamsDefined]

end Lech.Expr
