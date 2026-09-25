module

public import Fragment.Env

@[expose] public section

/-!
# The rules: a relational description of the checker

Three mutually inductive relations over the annotated terms, indexed
by the environment and a **context** `Γ` (the types of the bound
variables, innermost first; `bvar i` has type `Γ[i]` lifted over the
`i + 1` binders in between):

* `Red env Γ e e'` — **head reduction**: β at a `never` gate, β
  certified, δ, ι, closed under `appFn` and `trans` (and `refl`).
* `DefEq env Γ a b` — **definitional equality**, the checker's verdict
  `true`: `refl`, `symm`, reduce-the-left-side, sorts by the level
  oracle, constants, congruence for `app`/`lam`/`pi`, η, proof
  irrelevance.  **No `trans`** — see the docstring of `DefEq`.
* `Infer env Γ e T` — **type inference**, one grade: the `pi` and
  `lam` rules CHECK the binder's annotation against the body's sort.

They mirror the six relations of `ConLeche/Rules/Rel.lean` (task
#305) restricted to the fragment: one inference grade instead of two
(no `appSkip`, no `proofFast`), no projections, literals, rescues or
structure η, and the certificate walks (`Certs`, `DefEqList`) folded
into the rules that use them (`Red.iota`).  Each constructor's
docstring names the constructor of `Rel.lean` it corresponds to.

**Premise discipline** (as in `Rel.lean`).  A rule's premises are the
certificates the checker runs at that site — the sub-runs and the
guards that determine the shape of the conclusion.  Well-formedness of
the subjects is NOT a premise anywhere: it is semantic (the invariant
`WellDenoted` of `WellDenoted.lean`) and enters only the soundness
theorems (`Sound.lean`), whose statements assume the conclusion's
terms well-denoted and CONCLUDE it of every term a rule produces.
-/

namespace Fragment

open Expr

variable [LevelOracle]

mutual

/-- **Reduction**: the head steps of the checker's `whnf`, chained. -/
inductive Red (env : Env) : List Expr → Expr → Expr → Prop where
  /-- No step (`Red.refl`, `Rel.lean:101`). -/
  | refl {Γ : List Expr} {e : Expr} : Red env Γ e e
  /-- Chaining (`Red.trans`, `Rel.lean:106`).  A reduction is a
  denotation identity, so chaining costs nothing semantically. -/
  | trans {Γ : List Expr} {e₁ e₂ e₃ : Expr} :
      Red env Γ e₁ e₂ → Red env Γ e₂ e₃ → Red env Γ e₁ e₃
  /-- Head reduction inside an application (`Red.appFn`,
  `Rel.lean:111`): the head is reduced before a redex is looked for. -/
  | appFn {Γ : List Expr} {f f' a : Expr} :
      Red env Γ f f' → Red env Γ (app f a) (app f' a)
  /-- **β at a fired gate** (`Red.betaGate`, `Rel.lean:121`): a λ whose
  annotation is `never` — its body is never a proposition — reduces
  with NO certificate.  The soundness of this step is the *graph
  regime*'s β: an application that is well-denoted applies a graph to
  a member of its domain, and a graph determines its domain
  (`Sound.lean`, `red_sound`'s `betaGate` case). -/
  | betaGate {Γ : List Expr} {A b a : Expr} :
      Red env Γ (app (lam A .never b) a) (b.inst a)
  /-- **β, certified** (`Red.beta`, `Rel.lean:126`): at any annotation,
  the argument's inferred type is definitionally equal to the domain.
  This is the check the real checker runs where the body may be a
  proposition, because then the model cannot recover the domain from
  the function's value (DESIGN.md, "Beta soundness without subject
  reduction"). -/
  | beta {Γ : List Expr} {A b a ta : Expr} {pw : PropWhen} :
      Infer env Γ a ta → DefEq env Γ ta A →
      Red env Γ (app (lam A pw b) a) (b.inst a)
  /-- **δ** (`Red.delta`, `Rel.lean:132`): a definition unfolds to its
  value, at the use's level instantiation.  (With `appFn`, an applied
  definition unfolds at its head.) -/
  | delta {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr} :
      env.find? c = some ci → ci.value? = some v →
      ls.length = ci.lparams.length →
      Red env Γ (const c ls) (v.instL ci.lparams ls)
  /-- **ι** (`Red.iota`, `Rel.lean:184`): a stored recursor applied to
  exactly its telescope — `numParams` parameters, `numMotives` motives,
  `numMinors` minor premises, `numIndices` indices and the major
  premise — whose major reduces to a constructor application with a
  rule, fires the rule: the rule's right-hand side, at the use's
  levels, applied to the parameters, motives and minors, then to the
  constructor's fields (its arguments after the parameters).

  The two **telescope certificates** are `Rel.lean`'s `Certs` walks
  (`:576-587`) folded in: the recursor's argument spine (with the
  reduced major) and the constructor's argument spine are each typed
  against the stored type's `Π`-telescope — every argument's type is
  inferred and found definitionally equal to the binder domain it
  meets (`Expr.piDomains`).  They are what makes the environment's ι
  law (`EnvModel.lean`, `RecRuleLaw`) applicable: they put every
  argument in its domain.  (`Rel.lean`'s ι additionally compares the
  constructor's levels and parameters with the recursor's; those
  follow from the two certificates in the model and are dropped here.) -/
  | iota {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {doms tys doms' tys' : List Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      Red env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0))
        major →
      major = mkAppN (const cj usj) margs →
      rl ∈ rules → rl.ctor = cj →
      env.find? cj = some cij →
      usj.length = cij.lparams.length →
      margs.length = numParams + rl.nfields →
      -- the recursor's telescope certificate, on the spine with the reduced major
      piDomains (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]) = some doms →
      tys.length = doms.length →
      (∀ p ∈ (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]).zip tys,
        Infer env Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEq env Γ p.1 p.2) →
      -- the constructor's telescope certificate
      piDomains (cij.type.instL cij.lparams usj) margs = some doms' →
      tys'.length = doms'.length →
      (∀ p ∈ margs.zip tys', Infer env Γ p.1 p.2) →
      (∀ p ∈ tys'.zip doms', DefEq env Γ p.1 p.2) →
      Red env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us)
          (args.take (numParams + numMotives + numMinors) ++ margs.drop numParams))

/-- **Definitional equality**: the verdict `true` of the checker's
`isDefEq`.

**There is no `trans` rule, deliberately** (`Rel.lean:310-333`, task
#309).  The relation is the checker's verdict on two terms that are
well-formed *together*, a fact no rule states because well-formedness
is semantic (`WellDenoted`) and may not enter this inductive.  Every
rule respects one discipline instead: **the subject of each `DefEq`
premise is a subterm of the conclusion or is produced by a `Red` or
`Infer` premise** (a reduct, an inferred type), so the soundness proof
always has the premise's terms — and their invariant — in hand.  A
`trans` rule is the unique rule that would break it: its middle term
comes from nowhere, so nothing supplies its invariant, and the
induction has nothing to apply the hypothesis to.  In the real checker
the rule is not merely unprovable but unsound (`fvar`s carry
annotations `DefEq.fvar` does not compare while `DefEq.proofFast`
reads; `trans` lets the two meet).  The one sound chaining is "reduce,
then continue": `redL`. -/
inductive DefEq (env : Env) : List Expr → Expr → Expr → Prop where
  /-- The syntactic fast path (`DefEq.refl`, `Rel.lean:338`). -/
  | refl {Γ : List Expr} {a : Expr} : DefEq env Γ a a
  /-- Symmetry (`DefEq.symm`, `Rel.lean:341`).  Not a checker move: the
  constructor from which every right-hand variant of a one-sided rule
  is derived. -/
  | symm {Γ : List Expr} {a b : Expr} : DefEq env Γ a b → DefEq env Γ b a
  /-- **Reduce the left side, then continue** (`DefEq.redL`,
  `Rel.lean:346`): the recursive structure of `isDefEq` — head
  normalisation of either side (with `symm`) and every lazy-δ
  continuation. -/
  | redL {Γ : List Expr} {a a' b : Expr} :
      Red env Γ a a' → DefEq env Γ a' b → DefEq env Γ a b
  /-- Two sorts, by the level oracle (`DefEq.sort`, `Rel.lean:349`). -/
  | sort {Γ : List Expr} {u v : Level} :
      LevelOracle.eq u v = true → DefEq env Γ (sort u) (sort v)
  /-- Two constants of the same name at oracle-equal levels
  (`DefEq.const`, `Rel.lean:360`). -/
  | const {Γ : List Expr} {c : Name} {ls ls' : List Level} :
      Level.eqList ls ls' = true → DefEq env Γ (const c ls) (const c ls')
  /-- `∀`-congruence (`DefEq.forallE`, `Rel.lean:373`): domains, then
  bodies under the RIGHT domain, and the annotations must agree (they
  are compared with `=`, which is semantic: `PropWhen.eq_iff`). -/
  | pi {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} {pw : PropWhen} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) B₁ B₂ →
      DefEq env Γ (pi A₁ pw B₁) (pi A₂ pw B₂)
  /-- λ-congruence (`DefEq.lam`, `Rel.lean:380`), as for `∀`. -/
  | lam {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} {pw : PropWhen} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      DefEq env Γ (lam A₁ pw b₁) (lam A₂ pw b₂)
  /-- Application congruence (`DefEq.app`, `Rel.lean:390`). -/
  | app {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr} :
      DefEq env Γ f₁ f₂ → DefEq env Γ a₁ a₂ →
      DefEq env Γ (app f₁ a₁) (app f₂ a₂)
  /-- **η** (`DefEq.eta`, `Rel.lean:400`): a λ against a term `b`
  whose inferred type reduces to a `∀` with a definitionally equal
  domain and the same annotation, when the λ's body is `b` applied to
  the variable.  Sound because a member of a function space is the
  abstraction of its applications (`SetLib.graph_app_eq`) — and at a
  proposition both sides are the one proof. -/
  | eta {Γ : List Expr} {A₁ b₁ b tb A₂ B : Expr} {pw : PropWhen} :
      Infer env Γ b tb → Red env Γ tb (pi A₂ pw B) →
      DefEq env Γ A₂ A₁ →
      DefEq env (A₁ :: Γ) b₁ (app (b.liftN 1) (bvar 0)) →
      DefEq env Γ (lam A₁ pw b₁) b
  /-- **Proof irrelevance** (`DefEq.proofIrrel`, `Rel.lean:417`): both
  sides' inferred types have sort `Prop`.  **The two types are never
  compared**: the model licenses that, because every proof denotes the
  one point. -/
  | proofIrrel {Γ : List Expr} {a ta tta b tb ttb : Expr} {u v : Level} :
      Infer env Γ a ta → Infer env Γ ta tta → Red env Γ tta (sort u) →
      LevelOracle.eq u .zero = true →
      Infer env Γ b tb → Infer env Γ tb ttb → Red env Γ ttb (sort v) →
      LevelOracle.eq v .zero = true →
      DefEq env Γ a b

/-- **Type inference.** -/
inductive Infer (env : Env) : List Expr → Expr → Expr → Prop where
  /-- A bound variable's type is its context entry, lifted over the
  binders in between (`Infer.fvar`, `Rel.lean:492`; the real checker
  reads the type off the free variable). -/
  | bvar {Γ : List Expr} {i : Nat} {A : Expr} :
      Γ[i]? = some A → Infer env Γ (bvar i) (A.liftN (i + 1))
  /-- `Sort u : Sort (u + 1)` (`Infer.sort`, `Rel.lean:488`). -/
  | sort {Γ : List Expr} {u : Level} :
      Infer env Γ (sort u) (sort (.succ u))
  /-- A stored constant at the right number of levels has its
  declared type, instantiated (`Infer.const`, `Rel.lean:496`). -/
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} :
      env.find? c = some ci → ls.length = ci.lparams.length →
      Infer env Γ (const c ls) (ci.type.instL ci.lparams ls)
  /-- **`∀`-formation** (`Infer.forallE`, `Rel.lean:515`): the domain's
  type reduces to a sort `u`, the body's type (under the domain)
  reduces to a sort `v`, the result is `Sort (imax u v)` — and **the
  annotation is checked**: it must be the zero-ness datum of `v`. -/
  | pi {Γ : List Expr} {A B s t : Expr} {u v : Level} {pw : PropWhen} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) B t → Red env (A :: Γ) t (sort v) →
      Level.zeroness v = pw →
      Infer env Γ (pi A pw B) (sort (.imax u v))
  /-- **λ** (`Infer.lam`, `Rel.lean:530`): the domain's type reduces to
  a sort, the body is inferred under the domain, the body's type has a
  sort `v`, and **the annotation is checked** against `v`.  (The real
  checker validates the datum once per λ-chain; the fragment does it
  at every λ.) -/
  | lam {Γ : List Expr} {A b s bt btt : Expr} {u v : Level} {pw : PropWhen} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) b bt →
      Infer env (A :: Γ) bt btt → Red env (A :: Γ) btt (sort v) →
      Level.zeroness v = pw →
      Infer env Γ (lam A pw b) (pi A pw bt)
  /-- **Application** (`Infer.app`, `Rel.lean:544`): the head's type
  reduces to a `∀`, and the argument's inferred type is definitionally
  equal to its domain.  This is where a syntactic proof would need
  Π-injectivity and the semantic one does not: the `∀` the head's type
  reduces to *is* a function space, and membership in it is what the
  model needs (`Sound.lean`, `infer_sound`'s `app` case). -/
  | app {Γ : List Expr} {f a tf A B ta : Expr} {pw : PropWhen} :
      Infer env Γ f tf → Red env Γ tf (pi A pw B) →
      Infer env Γ a ta → DefEq env Γ ta A →
      Infer env Γ (app f a) (B.inst a)

end

end Fragment
