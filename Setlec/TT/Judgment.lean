import Setlec.TT.Const

/-!
# The typing judgment

**One judgment, one induction.**  There is no separate definitional
equality: conversion is *equality reflection* over the object-level
`eqE`.  Every conversion rule of the checker — β, η, structure η,
unit-like η, K, ι, projections, proof irrelevance, quotient
computation — is a rule concluding `Γ ⊢ prf : eqE T lhs rhs`, and the
single `conv` rule turns such a proof into a type change.  Two
consequences:

* soundness needs no mutual typing/equality induction — membership in
  `⟦eqE T a b⟧` *is* the equation `⟦a⟧ = ⟦b⟧`;
* there is no fixpoint tangle of the "defeq mentions typing, typing
  mentions defeq" kind that a term-level definitional-equality judgment
  forces (cf. lean4lean's `IsDefEq`, where typing is the diagonal).

**Rules carry exactly the premises soundness consumes, and no more.**
The bridge direction is "checker accepts ⇒ derivation exists", so every
extra premise is an extra bridge obligation.  Hence `refl` has no
premise at all, `lam` does not require its domain to be a type, `beta`
does not require the body to be typed, and the type argument of `eqE`
is unconstrained everywhere (it is semantically inert).

**There is no context of opaque constants and no environment.**  Every
constant the checker accepts either has a value, or has a checked model
artifact that plays the role of a value, or is one of the finitely many
pinned standard axioms; the first two unfold at denotation time and the
last are the built-in constants.  Consistency is therefore *absolute*
(`Setlec/TT/Semantics/Consistency.lean`): no side condition about a
satisfiable context.

**The layer is an upper bound on the checker, not a characterization.**
Setlec deliberately never aliases `T := T._model`, so streams cannot see
through a modeled inductive's encoding; a theory that *does* unfold `T`
proves equations the checker rejects.  That is harmless — a stronger
theory is a weaker bridge obligation — but it means no completeness
claim can be read off this file.
-/

namespace Setlec.TT

open VExpr

/-- `∀ (n : Nat), M n → M (n+1)`, the minor-premise type of `Nat.rec`
at motive `M` (a term of the ambient context). -/
def natStepT (M : VExpr) : VExpr :=
  .pi natT (.pi (.app (M.liftN 1) (.bvar 0))
    (.app (M.liftN 2) (natSuccT (.bvar 1))))

/-- `∀ a b, r a b → f a = f b`, the invariance premise of `Quot.lift`
(all of `A`, `r`, `B`, `f` are terms of the ambient context). -/
def quotInvT (A r B f : VExpr) : VExpr :=
  .pi A (.pi (A.liftN 1)
    (.pi (mkAppN (r.liftN 2) [.bvar 1, .bvar 0])
      (.eqE (B.liftN 3) (.app (f.liftN 3) (.bvar 2)) (.app (f.liftN 3) (.bvar 1)))))

/-- The declarative typing relation.  `Γ` lists the types of the
enclosing binders, innermost first. -/
inductive HasType : List VExpr → VExpr → VExpr → Prop where
  -- ## Structural rules

  /-- Variables. -/
  | bvar {Γ i A} : Γ[i]? = some A → HasType Γ (.bvar i) (A.liftN (i + 1))
  /-- The non-cumulative `Sort` hierarchy. -/
  | sort {Γ u} : HasType Γ (.sort u) (.sort (u + 1))
  /-- Built-in constants at a concrete level instantiation. -/
  | const {Γ c us} : HasType Γ (.const c us) (c.type us)
  /-- `Pi` formation, with `imax` — the `v = 0` branch is
  impredicativity of `Prop`. -/
  | pi {Γ A B u v} : HasType Γ A (.sort u) → HasType (A :: Γ) B (.sort v) →
      HasType Γ (.pi A B) (.sort (imax u v))
  /-- Abstraction. -/
  | lam {Γ A b B} : HasType (A :: Γ) b B → HasType Γ (.lam A b) (.pi A B)
  /-- Application.  Note that the premises hand the *argument fact*
  `⟦a⟧ ∈ ⟦A⟧` to soundness for free — the fact the checker has to
  re-establish at every reduction site because the collapsed `app` is
  non-invertible. -/
  | app {Γ f a A B} : HasType Γ f (.pi A B) → HasType Γ a A →
      HasType Γ (.app f a) (B.inst a)
  /-- `let`, typed with the value **substituted**.  Opening the body
  with an opaque variable `x : ty` is provably too weak — real streams
  need the value's definitional content in the body (recorded finding,
  task #79) — and a context carrying definitions would reintroduce the
  context machinery this layer does without.  Since the layer is
  non-algorithmic, eager substitution costs only term size; the
  checker's *lazy* zeta is recovered from the `zeta` equation below
  plus `trans`. -/
  | letE {Γ ty val body B u} : HasType Γ ty (.sort u) → HasType Γ val ty →
      HasType Γ (body.inst val) B → HasType Γ (.letE ty val body) B
  /-- Equations are propositions. -/
  | eqType {Γ T a b} : HasType Γ (.eqE T a b) (.sort 0)
  /-- **Conversion = equality reflection.**  This is the only rule that
  changes a type, and the only consumer of the equational rules. -/
  | conv {Γ t A B T p} : HasType Γ t A → HasType Γ p (.eqE T A B) →
      HasType Γ t B

  -- ## Equivalence and congruence

  | refl {Γ T a} : HasType Γ .prf (.eqE T a a)
  | symm {Γ T T' a b p} : HasType Γ p (.eqE T a b) →
      HasType Γ .prf (.eqE T' b a)
  | trans {Γ T T' T'' a b c p q} : HasType Γ p (.eqE T a b) →
      HasType Γ q (.eqE T' b c) → HasType Γ .prf (.eqE T'' a c)
  | congrApp {Γ T T' T'' f f' a a' p q} : HasType Γ p (.eqE T f f') →
      HasType Γ q (.eqE T' a a') →
      HasType Γ .prf (.eqE T'' (.app f a) (.app f' a'))
  | congrLam {Γ T T' T'' A A' b b' p q} : HasType Γ p (.eqE T A A') →
      HasType (A :: Γ) q (.eqE T' b b') →
      HasType Γ .prf (.eqE T'' (.lam A b) (.lam A' b'))
  | congrPi {Γ T T' T'' A A' B B' p q} : HasType Γ p (.eqE T A A') →
      HasType (A :: Γ) q (.eqE T' B B') →
      HasType Γ .prf (.eqE T'' (.pi A B) (.pi A' B'))
  /-- Congruence for the equality former itself.  Without it the layer
  could not retype an equality proof along an equation between its own
  sides, and `Eq.rec` would *not* be derivable (see
  `Setlec/TT/Examples.lean`, `eqRec_derivable`). -/
  | congrEq {Γ T T' T'' S S' a a' b b' p q} : HasType Γ p (.eqE T a a') →
      HasType Γ q (.eqE T' b b') →
      HasType Γ .prf (.eqE T'' (.eqE S a b) (.eqE S' a' b'))

  -- ## The core computation rules

  /-- β.  Only the argument's typing is needed: under the collapse,
  `app_lamC` is premise-free apart from domain membership. -/
  | beta {Γ T A a b} : HasType Γ a A →
      HasType Γ .prf (.eqE T (.app (.lam A b) a) (b.inst a))
  /-- ζ.  Premise-free: the interpretation of a `let` *is* the
  interpretation of its zeta reduct.  A congruence rule for `letE` is
  not primitive — it is `zeta`, `trans` and `symm zeta` around a proof
  that the two reducts agree, which is the only shape any consumer
  needs (the checker itself zeta-reduces both sides before comparing). -/
  | zeta {Γ T ty val body} :
      HasType Γ .prf (.eqE T (.letE ty val body) (body.inst val))
  /-- η for functions. -/
  | eta {Γ T A B f} : HasType Γ f (.pi A B) →
      HasType Γ .prf (.eqE T (.lam A (.app (f.liftN 1) (.bvar 0))) f)
  /-- Function extensionality — needed to prove an equation at a
  `Pi` type from pointwise equality. -/
  | funext {Γ T T' A B B' f g p} : HasType Γ f (.pi A B) →
      HasType Γ g (.pi A B') →
      HasType (A :: Γ) p
        (.eqE T (.app (f.liftN 1) (.bvar 0)) (.app (g.liftN 1) (.bvar 0))) →
      HasType Γ .prf (.eqE T' f g)
  /-- Proof irrelevance (definitional in Lean; an equation here).
  This is also what makes rule K and the Prop cases of unit-like η
  derivable rather than primitive. -/
  | proofIrrel {Γ P h h'} : HasType Γ P (.sort 0) → HasType Γ h P →
      HasType Γ h' P → HasType Γ .prf (.eqE P h h')

  -- ## Basis computation rules

  /-- ι for `Nat.rec` at `Nat.zero`. -/
  | natRecZero {Γ T u M z s} :
      HasType Γ M (arrow natT (.sort u)) →
      HasType Γ z (.app M natZeroT) →
      HasType Γ s (natStepT M) →
      HasType Γ .prf (.eqE T (natRecT u M z s natZeroT) z)
  /-- ι for `Nat.rec` at `Nat.succ`. -/
  | natRecSucc {Γ T u M z s n} :
      HasType Γ M (arrow natT (.sort u)) →
      HasType Γ z (.app M natZeroT) →
      HasType Γ s (natStepT M) →
      HasType Γ n natT →
      HasType Γ .prf (.eqE T (natRecT u M z s (natSuccT n))
        (.app (.app s n) (natRecT u M z s n)))
  /-- ι for `PUnit.rec`. -/
  | punitRecUnit {Γ T u v M m} :
      HasType Γ M (arrow (punitT u) (.sort v)) →
      HasType Γ m (.app M (punitUnitT u)) →
      HasType Γ .prf (.eqE T (punitRecT u v M m (punitUnitT u)) m)
  /-- Unit-like η for the basis unit. -/
  | punitEta {Γ u x y} :
      HasType Γ x (punitT u) → HasType Γ y (punitT u) →
      HasType Γ .prf (.eqE (punitT u) x y)
  /-- Projection computation, first component. -/
  | psigmaFstMk {Γ T u v A B a b} :
      HasType Γ A (.sort u) → HasType Γ B (arrow A (.sort v)) →
      HasType Γ a A → HasType Γ b (.app B a) →
      HasType Γ .prf (.eqE T (psigmaFstT u v A B (psigmaMkT u v A B a b)) a)
  /-- Projection computation, second component. -/
  | psigmaSndMk {Γ T u v A B a b} :
      HasType Γ A (.sort u) → HasType Γ B (arrow A (.sort v)) →
      HasType Γ a A → HasType Γ b (.app B a) →
      HasType Γ .prf (.eqE T (psigmaSndT u v A B (psigmaMkT u v A B a b)) b)
  /-- **Structure η** for the basis pair.  Every modeled structure's
  η law reduces to this one after the model is unfolded.  (The
  checker's own `PSigma'` is deliberately η-*inert*; the layer is
  stronger here, which is the safe direction.) -/
  | psigmaEta {Γ u v A B p} :
      HasType Γ A (.sort u) → HasType Γ B (arrow A (.sort v)) →
      HasType Γ p (psigmaT u v A B) →
      HasType Γ .prf (.eqE (psigmaT u v A B) p
        (psigmaMkT u v A B (psigmaFstT u v A B p) (psigmaSndT u v A B p)))
  /-- Quotient computation. -/
  | quotLiftMk {Γ T u v A r B f h a} :
      HasType Γ A (.sort u) → HasType Γ r (relT A) →
      HasType Γ B (.sort v) → HasType Γ f (arrow A B) →
      HasType Γ h (quotInvT A r B f) → HasType Γ a A →
      HasType Γ .prf
        (.eqE T (quotLiftT u v A r B f h (quotMkT u A r a)) (.app f a))

@[inherit_doc] notation:50 Γ " ⊢ " e " : " A:51 => HasType Γ e A

end Setlec.TT
