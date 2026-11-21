module

public import ConLeche.Kernel.ExprOps

@[expose] public section

/-!
# The ι equations, read off a recursor's own type

A recursor's rule says how the recursor computes on a constructor: applied to its rule prefix
(parameters, motives, minor premises), the indices and the constructor applied to its parameters
and fields, it is the rule's right-hand side applied to the prefix and the fields.  As a
proposition:

    ∀ (prefix) (fields), @Eq.{u} (motive idx (C.{us} params fields))
      (rec prefix idx (C.{us} params fields)) (rhs prefix fields)

This module reads that equation off the recursor's own type (`iotaEqOf`), as `IsModel`
(`ConLeche/IsModel.lean`) states it.  The rule `i` of the recursor's rules reads the `i`-th
minor premise of the motive its type's body applies (`minorsOf`, the prefix binders whose
conclusion that motive heads, in order): the fields are the minor's first `nfields` binders (the
induction hypotheses after them are not quantified), the indices are its conclusion's leading
arguments, and the constructor — the rule's — is used at the levels and parameters of the major
premise's type (`C.{us} params is` with the `is` the index variables).  No constructor is looked
up: what `IsModel` says of a recursor is said by the recursor alone.  The checker's rule that
this reading agrees with the constructor's (`recReadsOk`) is in
`ConLeche/Kernel/Inductives/IotaRead.lean`.
-/

namespace ConLeche

/-- The sort level of a recursor's motive: the motive application `body`
(under the rule prefix `pre`, the `nIdx` indices and the major) has a
prefix variable as its head, and that binder's domain ends in `Sort u`. -/
def motiveLevel? (pre : List Expr) (nIdx : Nat) (body : Expr) : Option Level :=
  match body.getAppFn with
  | .bvar k =>
    if nIdx + 1 ≤ k ∧ k < nIdx + 1 + pre.length then
      match (pre.getD (pre.length - 1 - (k - (nIdx + 1))) default).piResult with
      | .sort u => some u
      | _ => none
    else none
  | _ => none

/-- **A recursor's frame**: its rule prefix (the first `rP` binders of its type), the domains of
the `mI - rP` index binders and the major's, the body after them, and the sort level of the
motive the body applies. -/
def iotaFrame (cv : ConstantVal) (mI rP : Nat) :
    Option (List Expr × List Expr × Expr × Level) := do
  let (pre, rest) ← cv.type.stripPis rP
  let (doms, body) ← rest.stripPis (mI - rP + 1)
  let u ← motiveLevel? pre (mI - rP) body
  pure (pre, doms, body, u)

/-- **The parts a rule's ι equation is built from**: the fields' domains (in the context of the
rule prefix and the earlier fields), the indices (in the context of the prefix and the fields),
the constructor's levels and its parameters (in the context of the prefix). -/
structure IotaParts where
  fieldDoms : List Expr
  idx : List Expr
  us : List Level
  params : List Expr

/-- **A rule's ι equation from its parts**, under the recursor's rule prefix `pre` and its
body `body` (the motive at the indices and the major, `u` the motive's sort level):

    ∀ (pre) (fields : fieldDoms), @Eq.{u} (body[idx, major]) (rec pre idx major) (rhs pre fields)

with `major := C.{us} params fields`. -/
def iotaEqMk (cv : ConstantVal) (rP nIdx : Nat) (pre : List Expr) (body : Expr) (u : Level)
    (rl : RecRule) (pt : IotaParts) : Expr :=
  let nF := rl.nfields
  let xs := (List.range rP).map fun i => Expr.bvar (rP + nF - 1 - i)
  let fs := (List.range nF).map fun j => Expr.bvar (nF - 1 - j)
  let major := Expr.mkAppN (.const rl.ctor pt.us) (pt.params.map (·.liftLooseBVars nF 0) ++ fs)
  let lhs := Expr.mkAppN (.const cv.name (cv.levelParams.map .param)) (xs ++ pt.idx ++ [major])
  let rhs := Expr.mkAppN rl.rhs (xs ++ fs)
  let ty := (body.liftLooseBVars nF (nIdx + 1)).instantiateLift (major :: pt.idx.reverse)
  (pre ++ pt.fieldDoms).foldr .forallE (.app (.app (.app (.const eqName [u]) ty) lhs) rhs)

/-! ## The rule's parts, off the recursor's own type -/

/-- A `∀`-telescope's binder count and its body. -/
def Expr.piTele : Expr → Nat × Expr
  | .forallE _ b => ((Expr.piTele b).1 + 1, (Expr.piTele b).2)
  | e => (0, e)

/-- **The minor premises of the motive at prefix position `mot`**: the positions of the prefix
binders whose conclusion (behind all their `∀`s) is headed by that motive, in order. -/
def minorsOf (pre : List Expr) (mot : Nat) : List Nat :=
  (List.range pre.length).filter fun q =>
    match ((pre.getD q default).piTele.2).getAppFn with
    | .bvar m => decide (mot < q) && m == (pre.getD q default).piTele.1 + (q - 1 - mot)
    | _ => false

/-- **A rule's parts, read off the recursor's own type** (the statement's reading): the rule `i`
reads the `i`-th minor premise of the motive the body applies, at prefix position `q`.  Its
first `nfields` binders are the fields (lifted past the later prefix binders); its conclusion's
first `mI - rP` arguments are the indices (behind the induction hypotheses, which they do not
mention, and lifted the same way).  The constructor is used at the levels `us` and the
parameters of the major premise's type `C'.{us} params is` (the `is` the index variables, which
the parameters do not mention). -/
def iotaPartsOf (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Option IotaParts := do
  let nF := rl.nfields
  let nIdx := mI - rP
  let (pre, doms, body, _) ← iotaFrame cv mI rP
  let .bvar k := body.getAppFn | none
  let q ← (minorsOf pre (rP + nIdx - k))[i]?
  let (fd, inner) ← (pre.getD q default).stripPis nF
  let .const _ us := (doms.getD nIdx default).getAppFn | none
  let args := (doms.getD nIdx default).getAppArgs
  pure ⟨fd.mapIdx (fun j d => d.liftLooseBVars (rP - q) j),
    (inner.piTele.2.getAppArgs.take nIdx).map
      (fun a => (a.dropVars inner.piTele.1).liftLooseBVars (rP - q) nF),
    us, (args.take (args.length - nIdx)).map (Expr.dropVars nIdx)⟩

/-- **A recursor's rule `i`'s ι equation, read off the recursor's own type** (see the module
docstring). -/
def iotaEqOf (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Option Expr := do
  let (pre, _, body, u) ← iotaFrame cv mI rP
  let pt ← iotaPartsOf cv mI rP i rl
  pure (iotaEqMk cv rP (mI - rP) pre body u rl pt)

end ConLeche
