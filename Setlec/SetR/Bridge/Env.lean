import Setlec.SetR.CtxOkR
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves
import Setlec.SetR.ProjPins

/-!
# `EnvR`: the environment facts the bridge consumes (task #148, T3)

The bridge (`Setlec/SetR/Bridge/*`) turns a successful `--set-model`
checker run into a derivation of the relation family
(`Setlec/SetR/Rel.lean`).  Doing so needs a handful of facts about the
environment it runs against, and **all of them are V-free**: the bridge
never mentions a set, a membership or an interpretation.  They are
collected here rather than taken as loose hypotheses because there are
seven of them and every clause lemma would otherwise carry all seven.

**This is an interface, not a new invariant.**  Each field below is
either literally a field of `Setlec/TTVerify/EnvTT.lean`'s `EnvTT` or an
immediate consequence of one, and each is listed in the campaign
design's §2 among `EnvS`'s *syntactic* fields ("verbatim from `EnvTT`,
all mode-independent").  When T5 builds `EnvS`, it supplies an `EnvR`
by projection — one adapter, written once; nothing in the bridge has to
change, and nothing in the bridge depends on a semantic field.

The one field that is *not* a verbatim `EnvTT` field is `ty_denotes`,
and it is deliberately the **weakest** form that works: `EnvTT.has_type`
and `EnvS.mem_type` both say "the stored type denotes **and** the
constant's valuation inhabits it"; the bridge only ever uses the first
conjunct (the `.const` inference clause and the iota clause's stored
telescopes need a denotation to name, never a typing).  Taking the
weaker fact keeps the bridge free of any semantic content, which is the
whole point of the factoring.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-- The environment facts the bridge consumes: a constant valuation,
its closedness, the syntactic well-formedness of the store, level
insensitivity, denotability of stored types, and the two unfolding
equations (which are what make delta steps invisible — design §7.2).

Every field is V-free and mode-independent. -/
structure EnvR (env : Env) where
  /-- The type-theory term of each constant (the same `TConstVal` the
  denotation and `EnvTT` use). -/
  cval : TConstVal
  /-- Every constant denotes to a closed term.  Consumed by every
  lifting step (`denote_weaken_top`, `denote_lift`) and by M1. -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (cval n ψ)
  /-- Stored declarations are syntactically well-formed.  Consumed by
  the frame-condition lemmas of `Setlec/Verify/*`. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters.
  Consumed by the same-head spine short-circuit. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every stored constant's type denotes.**  The weakest form of
  `EnvTT.has_type` / `EnvS.mem_type` the bridge needs: it names the
  `VExpr` the `.const` rule's `denoteClosed` side condition asks for,
  and nothing else. -/
  ty_denotes : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ t, denoteClosed cval env ψ c.toConstantVal.type = some t
  /-- Every definition is denoted by its body — the fact that makes a
  delta step an *identity* of denotations, hence contributes no rule to
  the family (design §7.2, R17). -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ ψ : Name → Nat,
      denoteClosed cval env ψ value = some (cval cv.name ψ)
  /-- Every stored native projection-table entry is a pinned pair entry
  with its block stored (`ProjOkT`).  Syntactic; the bridge's I9 and R6
  clauses need it to identify the entry's type as a *concrete* closed
  expression (`Setlec/SetR/ProjPins.lean`), which is what makes their
  denotation and residual walks computations.  `EnvS` carries the same
  field. -/
  proj_ok : ProjOkT env
  /-- Every theorem is denoted by its proof value; the `thmInfo` half of
  `defn_eq`. -/
  thm_ok : ∀ cv value,
    ConstantInfo.thmInfo cv value ∈ env.consts → ∀ ψ : Name → Nat,
      denoteClosed cval env ψ value = some (cval cv.name ψ)

/-- `CtxOkR` only reads the leaf set, so it restricts along any subset
of leaves.  (The `Δ.length` conjunct is carried, not re-derived.)
Transpose of `CtxOk.of_subset`. -/
theorem CtxOkR.of_subset {μ : CheckMode} {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} {Δ : List VExpr} {e e' : Expr}
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
    (h : CtxOkR μ cval env φ d Δ e) : CtxOkR μ cval env φ d Δ e' :=
  ⟨h.1, fun l hl => h.2 l (hsub l hl)⟩

end Setlec.SetR
