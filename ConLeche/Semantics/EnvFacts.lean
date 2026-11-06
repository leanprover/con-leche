module

import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.EnvPreds
public import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.Denote.VClosed

@[expose] public section

/-!
# `EnvFacts`: the V-free environment facts (task #148, T3)

The facts about the environment a checker run is read against, and
**all of them are V-free**: none mentions a set, a membership or an
interpretation.  They are collected here rather than taken as loose
hypotheses because there are seven of them and every clause lemma would
otherwise carry all seven.

**This is an interface, not a new invariant.**  Each field below is
a projection of the model's environment invariant or an immediate
consequence of one, supplied by one adapter written once
(`EnvModelM.toEnvFacts`, whose docstring tabulates the sources).

The one semantic-looking field, `ty_denotes`, is deliberately the
**weakest** form that works: the consumers (the `.const` inference
clause and the iota clause's stored telescopes) need a denotation to
name, never a typing.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The environment facts the bridge consumes: a constant valuation,
its closedness, the syntactic well-formedness of the store, level
insensitivity, denotability of stored types, and the two unfolding
equations (which are what make delta steps invisible — design §7.2).

Every field is V-free and mode-independent. -/
structure EnvFacts (env : Env) where
  /-- The type-theory term of each constant (the same `(Name → (Name → Nat) → Term)` the
  denotation uses). -/
  cval : (Name → (Name → Nat) → Term)
  /-- Every constant denotes to a closed term.  Consumed by every
  lifting step. -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), Term.Closed (cval n ψ)
  /-- Stored declarations are syntactically well-formed.  Consumed by
  the frame-condition lemmas of `ConLeche/Verify/*`. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters.
  Consumed by the same-head spine short-circuit. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every stored constant's type denotes.**  It names the `Term`
  the `.const` rule's `denoteClosed` side condition asks for, and
  nothing else. -/
  ty_denotes : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ t, denoteClosed cval env ψ c.toConstantVal.type = some t
  /-- **Every stored recursor rule's right-hand side denotes**,
  at every instantiation of the recursor's level parameters.

  `ty_denotes` covers stored *types*; a rule's `rhs` is not one.
  `EnvWF` gives it `hasFvar = false`, `constsResolve` and
  `looseBVarsBounded 0`, but `constsResolve` records *existence* of the
  referenced constants, not the level-arity matches `denote`'s `.const`
  clause tests — so denotability is a genuinely extra fact, consumed by
  the ι rule's `denoteClosed` side condition. -/
  rec_rhs_denotes : ∀ n cv mI rP isK rules,
    env.find? n = some (.recInfo cv mI rP isK rules) →
    ∀ r ∈ rules,
      ∀ (us : List Level) (ψ : Name → Nat),
        us.length = cv.levelParams.length →
        ∃ R, denoteClosed cval env ψ
          (r.rhs.instantiateLevelParams cv.levelParams us) = some R
  /-- **A stored recursor's parameter count does not exceed its major
  index.**  `EnvWF` concludes `rP ≤ mI` only inside the `.nested`
  branch, while the ι rule's *index* side condition needs it on
  `.plain` fires too (its length disjunct is otherwise open at
  `mI < rP`).  Backed by `rec_rules`' `RecRuleLaw`. -/
  rec_params_le : ∀ n cv mI rP isK rules,
    env.find? n = some (.recInfo cv mI rP isK rules) →
    ∀ r ∈ rules, rP ≤ mI
  /-- Every stored native projection-table entry is a pinned pair entry
  with its block stored (`ProjOkT`).  Syntactic; the projection
  clauses need it to identify the entry's type as a *concrete* closed
  expression, which is what makes their denotation and residual walks
  computations. -/
  proj_ok : ProjOkT env

end ConLeche.Semantics
