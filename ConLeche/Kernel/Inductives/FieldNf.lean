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

end ConLeche
