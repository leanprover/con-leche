module

public import ConLeche.Kernel.Inductives.Positivity

@[expose] public section

/-!
# The walk's field normal form, without its positivity decisions

The positivity walk (`nestPos`, `nestFields`) records, at every node it
derives, each constructor's walked field telescope (`NestCtorNf`, K.53′).
That record is a FUNCTION of the constructor's instantiated type alone:
`nestPos`'s normal-form output is decided by the kernel's whnf and the
occurrence test, never by the cache, the frame stack's contents or the
positivity verdicts (`posD_fun`, `ConLeche/Verify/Inductives/PosDerivFun.lean`).

`nestNf`/`nestTeleNf` compute exactly that output and nothing else, so
that a reader other than the walk — the recursor check at a class, once
it no longer reads the walk's record (PRIMREC, DESIGN "PRIMREC / FRAME")
— can recompute the record itself.  The theorem that they agree with
every derivation of the walk is `posD_nfOk`
(`ConLeche/Verify/Inductives/PosNf.lean`).

* `nestNf` at depth `dep`, holes `[nP, hi)`: the whnf `w` of the
  domain; if `w` mentions no hole, the domain itself when it mentions
  none either, else `w` (`nestPos`'s `const` case); a hole-carrying `Π`
  is rebuilt around the normal form of its body opened at `.fvar dep a`
  (the `pi` case); any other hole-carrying reduct is its own normal form
  (the `hole`, `frameHole` and container cases all return the reduct).
* `nestTeleNf`: a constructor's field telescope from field `j`, each
  field's domain through `nestNf` at `base + j`, the rest opened at the
  field's ORIGINAL domain (as `nestFields` opens it); the fields' normal
  forms and the telescope's result.

Neither checks positivity: on an input the walk rejects they compute
something, which no theorem reads.  Fuel bounds the `Π` nesting of one
field; running out throws `.notImplemented`.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A term with every free variable's ANNOTATION erased (the variable
kept): the comparison K.53′ runs up to, which is exactly what the model's
interpretation never reads (`Expr.ErasedEq`). -/
def Expr.eraseFVarTys (e : Expr) : Expr :=
  e.replaceFVars fun i => some (.fvar i (.sort .zero))


/-- One step of `nestNf` at the reduct `w` of `e`, the recursion `rec`
one fuel lower. -/
def nestNfAt (names : List Name) (nP hi : Nat) (rec : Nat → Expr → m Expr) (dep : Nat)
    (e w : Expr) : m Expr :=
  if !w.nestOcc names nP hi then
    pure (if e.nestOcc names nP hi then w else e)
  else
    match w with
    | .forallE a b bm => do
      let nb ← rec (dep + 1) (b.instantiate1 (.fvar dep a))
      pure (.forallE a (nb.abstract1 dep) bm)
    | _ => pure w

/-- **The walk's normal form of a field domain** `e` at depth `dep`, the
holes the free variables `nP ..< hi` (see the module docstring). -/
def nestNf (ops : CheckerOps m) (env : Env) (names : List Name) (nP hi : Nat) :
    Nat → Nat → Expr → m Expr
  | 0, _, _ => throw (.notImplemented "field normal form: fuel")
  | fuel + 1, dep, e => do
    let w ← ops.whnf env dep e
    nestNfAt names nP hi (nestNf ops env names nP hi fuel) dep e w

/-- **The walk's normal form of a field telescope**: `nF` fields of `cur`
from field `j`, field `j` at the variable `base + j` (see the module
docstring). -/
def nestTeleNf (ops : CheckerOps m) (env : Env) (names : List Name) (nP hi fuel base : Nat) :
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Expr)
  | 0, _, cur => pure ([], cur)
  | nF + 1, j, cur =>
    match cur with
    | .forallE a b bm => do
      let nd ← nestNf ops env names nP hi fuel (base + j) a
      let (nds, res) ← nestTeleNf ops env names nP hi fuel base nF (j + 1)
        (b.instantiate1 (.fvar (base + j) a))
      pure ((nd, bm) :: nds, res)
    | _ => throw (.invalid "field normal form: a constructor type does not bind its fields")

/-! ## A class's constructors in the walk's layout (PRIMREC / NESTHOME)

The recursor check at a class of a cyclic layer compares a call's
callee against the called field's normal form as the walk would record
it (K.53).  `nestMemberCtorNf` / `nestFrameCtorNf` recompute that
record from the class alone: a MEMBER class at the block's own
parameters in the walk's member layout (the parameters at the
canonical variables `ctx.params`, member `t` the hole `nP + t`, the
fields above the holes — `nestMemberCtors`), an OUTSIDE class
`I.{us} ds` in the layout of a frame walked at the EMPTY stack (the
container's group abstracted to the frame's holes from `hiAt 0`, the
block's members as holes — `nestFrame`); both run `nestTeleNf` and read
the result back as the walk records it (`nestMemberNfs`,
`nestCtorNf`).  Beside the entry: per field, the normal form's `Π`-leaf
read back where the normal form mentions a hole (the class key a call on
that field must name), and whether every container leaf's parameters
mention no frame hole (`nestLeafShallow`: the walk derives such a
container's frame at the empty stack again).  Nothing here checks
anything: on an input the walk rejects they compute something no
theorem reads. -/

/-- The frame's new walk entries (one per group member, at the key). -/
def grpNews (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    List NestHole :=
  grp.map fun p => { key := ⟨p.1, us, ds⟩, base := hi }

/-- The frame's member substitution (`nestFrame`'s `sub`): the group's
members at the key's levels to their holes. -/
def grpSub (us : List Level) (hi : Nat) (grp : List (Name × Expr)) :
    Name → List Level → Option Expr :=
  fun c us' => if us' == us then
    (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)).lookup c else none

/-- A term below its syntactic `Π` binders. -/
def Expr.piLeaf : Expr → Expr
  | .forallE _ b _ => piLeaf b
  | e => e

/-- A walked field normal form whose `Π`-leaf is a constant-headed
application (a container) mentions no hole of `[lo, hi)` there. -/
def nestLeafShallow (lo hi : Nat) (nd : Expr) : Bool :=
  match nd.piLeaf.getAppFn with
  | .const _ _ => !nd.piLeaf.nestOcc [] lo hi
  | _ => true

/-- **A class constructor's walked normal form, recomputed**: the entry
the walk records, the read-back leaves of the hole-carrying fields, and
the shallowness of the container leaves (see the section header). -/
structure NestClassCtorNf where
  entry : NestCtorNf
  leaves : List (Option Expr)
  shallow : Bool
  deriving Inhabited

/-- The record of a walked telescope `nds` onto `cur` (fields from
`hi`), under the frames `prog`. -/
def nestClassCtorNfOf (ctx : NestCtx) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (nds : List (Expr × BinderMeta)) (cur : Expr) :
    NestClassCtorNf :=
  { entry := nestCtorNf ctx prog hi us ds cv nds cur
    leaves := nds.map fun nd =>
      if nd.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) then
        some (nd.1.piLeaf.replaceFVars (nestHoleConst ctx prog))
      else none
    shallow := nds.all fun nd => nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) nd.1 }

/-- **A member constructor, in the walk's member layout** (the node-`0`
entry, `nestMemberNfs`). -/
def nestMemberCtorNf (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (cv : ConstantVal) (nF : Nat) : m NestClassCtorNf := do
  let crest ← unwrapOr (instPisWith ctx.params (nestAbstract ctx holes cv.type))
    (.invalid "field normal form: a constructor type does not bind the parameters")
  let (nds, cur) ← nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt 0) (whnfWalkFuel crest)
    (ctx.hiAt 0) nF 0 crest
  pure (nestClassCtorNfOf ctx [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params cv nds cur)

/-- **A container's group at a key, as a frame at the EMPTY stack
builds it** (`nestContNew`): the container's instantiated former, then
its recorded group-mates. -/
def nestClassGroup (ctx : NestCtx) (I : Name) (us : List Level) (ds : List Expr) :
    m (List (Name × Expr)) := do
  let (_, cty) ← nestInstType ctx (ctx.hiAt 0) ⟨I, us, ds⟩
  nestGrowGroup ctx (ctx.hiAt 0) us ds (nestFrameMates ctx I) [(I, cty)]

/-- **A container constructor, in the layout of its frame at the EMPTY
stack** (`nestFrame`/`nestCtors`: the group `grp` abstracted to the holes
from `hiAt 0`, the key's parameters `ds` in the walk's representation). -/
def nestFrameCtorNf (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (us : List Level)
    (ds : List Expr) (grp : List (Name × Expr)) (cv : ConstantVal) (nF : Nat) :
    m NestClassCtorNf := do
  let crest ← unwrapOr (instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt 0) grp)))
    (.invalid "field normal form: a container constructor type does not bind the parameters")
  let prog := (grpNews us ds (ctx.hiAt 0) grp).reverse
  let (nds, cur) ← nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) (whnfWalkFuel crest)
    (ctx.hiAt 0 + grp.length) nF 0 crest
  pure (nestClassCtorNfOf ctx prog (ctx.hiAt 0 + grp.length) us ds cv nds cur)

/-- A class key's parameters in the walk's representation: the
recursor's parameter variables re-annotated as the walk's canonical ones
(`ctx.params`), the members abstracted to their holes. -/
def nestKeyDs (ctx : NestCtx) (holes : List Expr) (ds : List Expr) : List Expr :=
  ds.map fun x => nestAbstract ctx holes (x.replaceFVars fun i => ctx.params[i]?)

end ConLeche
