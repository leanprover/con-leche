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
  /-- The type-theory term of each constant (the same `TConstVal` the
  denotation uses). -/
  cval : TConstVal
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
  /-- Every definition is denoted by its body — the fact that makes a
  delta step an *identity* of denotations, hence contributes no rule to
  the family (design §7.2, R17). -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ ψ : Name → Nat,
      denoteClosed cval env ψ value = some (cval cv.name ψ)
  /-- **Every stored fireable recursor rule's right-hand side denotes**,
  at every instantiation of the recursor's level parameters.

  `ty_denotes` covers stored *types*; a rule's `rhs` is not one.
  `EnvWF` gives it `hasFvar = false`, `constsResolve` and
  `looseBVarsBounded 0`, but `constsResolve` records *existence* of the
  referenced constants, not the level-arity matches `denote`'s `.const`
  clause tests — so denotability is a genuinely extra fact, consumed by
  the ι rule's `denoteClosed` side condition. -/
  rec_rhs_denotes : ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, RecRule.fire r ≠ .inert →
      ∀ (us : List Level) (ψ : Name → Nat),
        us.length = cv.levelParams.length →
        ∃ R, denoteClosed cval env ψ
          (r.rhs.instantiateLevelParams cv.levelParams us) = some R
  /-- **A stored recursor's parameter count does not exceed its major
  index.**  `EnvWF` concludes `rP ≤ mI` only inside the `.nested`
  branch, while the ι rule's *index* side condition needs it on
  `.plain` fires too (its length disjunct is otherwise open at
  `mI < rP`).  Backed by `rec_rules`' `RecRuleLaw`. -/
  rec_params_le : ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI
  /-- Every stored native projection-table entry is a pinned pair entry
  with its block stored (`ProjOkT`).  Syntactic; the projection
  clauses need it to identify the entry's type as a *concrete* closed
  expression, which is what makes their denotation and residual walks
  computations. -/
  proj_ok : ProjOkT env
  /-- **The install fold's `Nat`-op invariant, narrowed to what the
  literal fast path reads** (task #161 B3): a *stored* one of the
  sixteen accelerated operations is a *guarded* one.

  `reduceNat` tests `natOpStored`, one lookup, instead of re-deriving
  `natOpGuard` at every literal hit.  This field turns that test back
  into the guard the literal rules name, and it is not new evidence:
  the model's `nat_ops`/`div_mod` state exactly this under their
  `defnInfo` hypothesis (they are what `checkDecl` establishes, by
  declining a stream that stores one of these names unguarded). -/
  nat_op_guard : ∀ c, (c ∈ natOpNames ∨ c ∈ natDivModNames) →
    natOpStored env c = true → natOpGuard env c = true

/-! ## Two `find?` readings -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold ConLeche.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold ConLeche.Env.find? at h
  exact List.mem_of_find?_eq_some h

end ConLeche.Semantics
