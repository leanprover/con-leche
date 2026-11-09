module

public import ConLeche.Kernel.Expr

@[expose] public section

/-!
# Constructor fields: their kinds and their telescopes

The field-level vocabulary the uniform installer (`BlockShape`,
`BlockRec`, `BlockInstall`) and the model share:

* `RecFieldKind` — a field's kind: `.ordinary` (the domain does not
  mention the block), `.recursive` (`T p⃗ e⃗`), `.reflexive`
  (`Π a⃗ : A⃗, T p⃗ e⃗(a⃗)`), `.negative` (a non-positive or non-valid
  occurrence; the block is rejected) and `.unsupported`;
* a field's own telescope and index expressions off the constructor's
  type (`structFieldTeleOf`, `structFieldIdxOf`), the positions with an
  inductive hypothesis (`recIdxOf`), and those telescopes and indices
  moved to a rule's frame (`structIdxAt`, `structTeleAt`,
  `structTeleVars`, `Expr.mkPisOf`).
-/

namespace ConLeche

/-- The kind of a constructor field of a block (see the module
docstring). -/
inductive RecFieldKind where
  /-- the domain does not mention the block -/
  | ordinary
  /-- the domain is exactly `T p⃗ e⃗`: a finitary recursive field -/
  | recursive
  /-- the domain is `Π a⃗ : A⃗, T p⃗ e⃗(a⃗)` with `A⃗` free of the block: a
  REFLEXIVE (function-space) recursive field (task #202) -/
  | reflexive
  /-- a non-positive (or non-valid) occurrence: the official kernel
  rejects the block -/
  | negative
  /-- an occurrence the official kernel accepts (reflexive, nested,
  under a redex) that this route does not model yet -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- All leading `∀` binders of an expression (outermost first) and
the body — a recursive field's own telescope (`[]` at a finitary
field, the `a⃗ : A⃗` of a reflexive one, task #202). -/
def Expr.piBinders : Expr → List Expr × Expr
  | .forallE ty b =>
    let (bs, e) := piBinders b
    (ty :: bs, e)
  | e => ([], e)

/-- The positions of the recursive fields (finitary or reflexive: the
ones with an inductive hypothesis). -/
def recIdxOf (ks : List RecFieldKind) : List Nat :=
  (List.range ks.length).filter fun i =>
    ks.getD i .ordinary == .recursive || ks.getD i .ordinary == .reflexive

/-- `∀ tele, body` over a binder list (outermost first). -/
def Expr.mkPisOf : List Expr → Expr → Expr
  | [], body => body
  | ty :: bs, body => .forallE ty (mkPisOf bs body)

end ConLeche
