/-!
# Syntax of the declarative type theory (task #74)

`VExpr` is the layer's *own* term datatype — deliberately not
`Setlec.Expr`.  It is what the eventual denotation function from a real
`Env`+`Expr` targets, and it is chosen for proof convenience, not for
fidelity to the checker's representation.

Differences from `Setlec.Expr`, each deliberate:

* **de Bruijn indices only.**  No `fvar`: the local context is an
  explicit `List VExpr` in the judgment (`Setlec/TT/Judgment.lean`),
  so open terms need no type annotation at the leaf.
* **Universe levels are concrete `Nat`s.**  There is no `Level`
  inductive, no level substitution and no level-equality judgment.
  The denotation from a real `Env`+`Expr` unfolds everything, so every
  constant is instantiated at its use site and every level expression
  in the unfolded term evaluates to a ground natural.  `imax` is a
  *computed function* on `Nat` (`Setlec.TT.imax`), so impredicativity
  of `Prop` is just its `v = 0` branch.  Universe polymorphism lives
  entirely in the bridge: a polymorphic declaration is denoted once per
  ground assignment, and "accepted" means the resulting statement holds
  at every assignment.  The layer therefore cannot state a polymorphic
  fact internally — and does not need to, because it has no definable
  constants at all.
* **`letE` is present.**  The checker's input-normalization pass
  currently zeta-expands `let` before storage, but that pass is
  scheduled for removal (task #117), after which stored terms carry
  `letE` and the bridge has to type them.  The typing rule substitutes
  the value (see `Setlec/TT/Judgment.lean`); zeta is an `Eq` rule.
* **No `proj`.**  Projections denote to applications of the basis
  projection constants (`psigmaFst`/`psigmaSnd`) or, for modeled and
  directly-installed structures, to the projection functions of the
  unfolded model — which is exactly what `annotateProjElim` /
  `annotateProjRec` already do inside the checker.
* **No `lit`.**  Literal computation is deferred; see `Setlec/TT/DESIGN.md`.
* **No global environment / no named constants.**  There is no `Env`
  and no delta rule: every constant the checker accepts either has a
  value (definitions, theorems, `opaque`s, the trust family), or has a
  checked model artifact that plays the role of a value (modeled
  inductives, direct structures), or is one of finitely many pinned
  standard axioms.  The first two unfold; the last are the built-in
  constants `propext` / `choice` below.  Consequently the constant
  alphabet `BConst` is *closed and finite*.
* **`eqE`, a primitive equality former.**  All conversion is expressed
  with the object-level equality (`Setlec/TT/Judgment.lean`), so `Eq`
  must be syntax rather than a constant: the conversion rule mentions
  it.  Making it a former (rather than a constant applied to three
  arguments) is what keeps every equational rule *premise-free in the
  type* — the interpretation of `eqE T a b` reads only `a` and `b`.
* **`prf`, the canonical proof.**  Equality proofs are irrelevant
  (`eqE _ _ _` is always a `Prop`), so the layer needs no proof terms
  with structure: every rule that concludes an equation concludes it
  for the single constant `prf`.

## The basis

The basis type formers are the ones the checker pins by hand
(`Setlec/Kernel/Basis/*.lean`): `Nat`, `PUnit`, `PSigma'`, `Empty`,
`Quot`.  `Eq` is absent from the list only because it has been promoted
to a syntactic former.  Everything else the checker stores — every
modeled inductive, every direct structure — unfolds into this alphabet,
which is why the alphabet can be closed.

Two constants of the checker's basis are *derivable* here and therefore
absent: `Eq.rec` (transport is the identity once equality is reflected,
so `fun A a M m b h => m` types by conversion) and `PSigma'.rec`
(`fun A B M f p => f (fst p) (snd p)`, typed by conversion along
structure eta).  Dropping them removes two of the most index-heavy
dependent types from `BConst.type`.
-/

namespace Setlec.TT

/-- Lean's `imax`, as a function on concrete levels: `Prop` is
impredicative, every other codomain takes the `max`. -/
def imax (u v : Nat) : Nat := if v = 0 then 0 else Nat.max u v

@[simp] theorem imax_zero (u : Nat) : imax u 0 = 0 := rfl

theorem imax_of_ne {u v : Nat} (h : v ≠ 0) : imax u v = Nat.max u v := if_neg h

/-- The closed, finite alphabet of built-in constants: the pinned basis
type formers with their constructors, recursors and projections, plus
the two pinned standard axioms that are not equations. -/
inductive BConst where
  /-- `Nat : Type` -/
  | nat
  /-- `Nat.zero : Nat` -/
  | natZero
  /-- `Nat.succ : Nat → Nat` -/
  | natSucc
  /-- `Nat.rec.{u}` -/
  | natRec
  /-- `PUnit.{u} : Sort u` -/
  | punit
  /-- `PUnit.unit.{u} : PUnit.{u}` -/
  | punitUnit
  /-- `PUnit.rec.{u,v}` -/
  | punitRec
  /-- `PSigma'.{u,v} : (A : Sort u) → (A → Sort v) → Sort (max u v)` -/
  | psigma
  /-- `PSigma'.mk.{u,v}` -/
  | psigmaMk
  /-- `PSigma'.fst.{u,v}` -/
  | psigmaFst
  /-- `PSigma'.snd.{u,v}` -/
  | psigmaSnd
  /-- `Empty.{u} : Sort u` (level-polymorphic, so it covers `False` too) -/
  | empty
  /-- `Empty.rec.{u,v}` -/
  | emptyRec
  /-- `Quot.{u}` -/
  | quot
  /-- `Quot.mk.{u}` -/
  | quotMk
  /-- `Quot.lift.{u,v}` -/
  | quotLift
  /-- `Quot.ind.{u}` -/
  | quotInd
  /-- `Quot.sound.{u}` -/
  | quotSound
  /-- `propext`, in primitive form: two implications give equality of
  propositions (no `Iff`, which is a modeled inductive and unfolds). -/
  | propext
  /-- `Classical.choice.{u}`, in primitive form: double-negation
  elimination into `Sort u` (no `Nonempty`, which is a modeled
  inductive and unfolds). -/
  | choice
  deriving Repr, DecidableEq, Inhabited

/-- Terms.  See the module docstring for what is *not* here. -/
inductive VExpr where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- a built-in constant at a concrete level instantiation -/
  | const (c : BConst) (us : List Nat)
  /-- application -/
  | app (f a : VExpr)
  /-- `fun (_ : ty) => body` -/
  | lam (ty body : VExpr)
  /-- `(_ : ty) → body` -/
  | pi (ty body : VExpr)
  /-- `let _ : ty := value; body` -/
  | letE (ty value body : VExpr)
  /-- `@Eq ty lhs rhs`.  `ty` is carried for readability and for the
  denotation to be syntax-directed; it is *semantically inert* (see
  `Setlec/TT/Semantics/Interp.lean`), which is what lets the equational
  rules omit all type-formation premises. -/
  | eqE (ty lhs rhs : VExpr)
  /-- the canonical (irrelevant) proof of a derivable equation -/
  | prf
  deriving Repr, Inhabited

namespace VExpr

/-- Iterated application. -/
def mkAppN (f : VExpr) : List VExpr → VExpr
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : VExpr) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : VExpr) (as : List VExpr) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

end VExpr

/-- How many universe parameters each constant takes.  Level lists that
are too short are read with `0` defaults (`Setlec/TT/Const.lean`), so
this is documentation and a bridge convention, never a side condition
of a rule. -/
def BConst.numLevels : BConst → Nat
  | .nat | .natZero | .natSucc | .propext => 0
  | .natRec | .punit | .punitUnit | .empty
  | .quot | .quotMk | .quotInd | .quotSound | .choice => 1
  | .punitRec | .psigma | .psigmaMk | .psigmaFst | .psigmaSnd
  | .emptyRec | .quotLift => 2

end Setlec.TT
