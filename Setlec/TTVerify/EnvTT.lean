import Setlec.TTVerify.Denote
import Setlec.TT.Semantics.Consistency

/-!
# The environment invariant, transposed from `EnvModel`

`EnvTT env` is `Setlec/Model/Interp.lean`'s `EnvModel env` with the
set-theoretic universe replaced by the declarative type theory:

| `EnvModel` | `EnvTT` |
|---|---|
| `val : ConstVal V` | `cval : TConstVal` |
| `wf : EnvWF env` | *the same* |
| `val_params` | *the same* |
| `mem_type`: `val c φ ∈ˢ ⟦c.type⟧` | `has_type`: `⊢ cval c φ : ⟦c.type⟧` |
| `defn_eq`: `⟦value⟧ = some (val c φ)` | *the same*, at `VExpr` |
| `thm_ok`: the same **plus `AnnotOk`** | just the equation |
| `annot_ok` | **no counterpart** |
| `ind_ok`'s `Empty` clause | `empty_pinned` |

Two of those rows are the point of the whole exercise.

**`mem_type` becomes a typing judgment.**  That is the only change of
substance: "every stored constant's value is a member of its type's
interpretation" becomes "every stored constant's denotation has a
derivation of its type's denotation".  The *induction* is unchanged —
the invariant is re-established declaration by declaration as the
checker installs, and that incremental extension **is** the
stream-ordering fact.  There is no separate ordering concept here, and
none is needed.

**`AnnotOk` disappears.**  The set model's truthfulness predicate
exists to reconstruct, at every binder, the fibre and membership facts
that a typing derivation would have supplied; in the declarative layer
the derivation supplies them, so `annot_ok` has no field and `thm_ok`
loses its second conjunct (`Setlec/TT/DESIGN.md` §6).  This is the
single largest structural saving of the bridge, and it is why the app
rule's premises can be delivered by the induction hypothesis directly
rather than through an `AppSlot`-style existential package.

## What is still to come (task #119 stage 2)

`EnvModel` has six further fields, all of them *semantic laws about
stored declarations* rather than structure.  Each transposes by the
same recipe — **replace an equation between interpretations by a
`Setlec.TT.Deq []` between denotations** — and each is added here as
the corresponding clause of the fuel induction is proved:

* `ind_ok`'s remaining conjuncts (`PairTyFacts`, `PairMkFacts`, the
  `PUnit` collapse, the pinned-valuation clause, and the two purely
  *syntactic* conjuncts `BasisBlocks`/`RecCtorsStored`, which mention
  no `V` and so transpose verbatim);
* `rec_rules : RecRulesOk` — the total λ-equality of every stored
  fireable recursor rule (task #58) becomes a `Deq` between the
  denotations of `ruleLhs` and the stored right-hand side.  Note that
  for a *modeled* inductive this is not new work: the `_model` iota
  theorems are stream declarations the checker itself accepted, so
  `has_type` already hands over a derivation of each, and firing a rule
  is instantiation plus `trans`;
* `proj_ok : ProjOk env` — syntactic, transposes verbatim;
* `caps_ok : CapsOk` — the eta and unit-like laws, likewise from
  checked `_model` theorems;
* `nat_ops : NatOpsOk` and `div_mod : DivModOk` — the certified
  recurrences, whose TT form is exactly the hypothesis shape of
  `Setlec/TT/Nat/*` (`Deq` equations at numerals): the bridge denotes
  the checker's own certificate and hands it to `numeral_add` and
  friends, which are hypothetical over an arbitrary `f : VExpr` and
  therefore need no constant of their own in the layer;
* `reduce_ops : ReduceOpsOk` — the compiler-trust identity, likewise.

They are listed here rather than left implicit because an invariant
that is quietly missing a clause is the classic way for a bridge like
this to look finished while proving nothing.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- A *derivation model* of an environment: a type-theory term for
every constant (a function of the level-parameter assignment), such
that the environment is well-formed, each valuation reads only its own
level parameters, each constant's valuation is derivably of its type's
denotation, and each definition's valuation is its body's denotation.

The transpose of `Setlec.EnvModel`; see the module docstring for the
row-by-row correspondence and for the fields still to come. -/
structure EnvTT (env : Env) where
  /-- The type-theory term of each constant. -/
  cval : TConstVal
  /-- Stored declarations are syntactically well-formed. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every constant has a derivation of its type.**  The transpose of
  `EnvModel.mem_type`, and the whole content of the bridge: its
  incremental re-establishment as declarations install is the
  stream-ordering fact. -/
  has_type : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    ∃ t, denoteClosed cval env φ c.toConstantVal.type = some t ∧
      HasType [] (cval c.name φ) t
  /-- Every definition is denoted by its body. -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- Every theorem is denoted by its proof value.  (`EnvModel.thm_ok`
  carries a second conjunct, `AnnotOk` of the value; there is nothing to
  carry here.) -/
  thm_ok : ∀ cv value,
    ConstantInfo.thmInfo cv value ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- The pinned empty type is valued by the layer's `Empty`, at some
  level.  The transpose of `IndOk`'s last conjunct
  (`∀ ψ x, x ∈ˢ val emptyName ψ → False`), in the stronger
  *pinned-valuation* form that `IndOk`'s fourth conjunct already uses
  for the reserved basis names — from which uninhabitation follows by
  the layer's own consistency theorem, so this invariant needs no
  `SetTheory` instance and the set theory enters only at the corollary. -/
  empty_pinned : ∀ ψ : Name → Nat, ∃ u, cval emptyName ψ = emptyT u

/-- The empty environment has a (trivial) derivation model. -/
def EnvTT.empty : EnvTT Env.empty where
  cval := fun _ _ => emptyT 0
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  has_type := by intro c hc; cases hc
  defn_eq := by intro cv value hint h; cases h
  thm_ok := by intro cv value h; cases h
  empty_pinned := fun _ => ⟨0, rfl⟩

/-! ## What the invariant delivers per declaration

The bridge's per-declaration conclusion — a `def` or `theorem`'s value
has a derivation of its stated type — is `has_type` and `defn_eq`
together, with no further work.  This is the payoff of transposing
`mem_type` rather than inventing a separate statement: the
declaration-level theorem is a two-line consequence of the environment
invariant, exactly as `EnvModel.mem_type` gives the set-model one. -/

/-- A stored definition's body has a derivation of its stated type. -/
theorem EnvTT.hasType_defn {env : Env} (m : EnvTT env) {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧ HasType [] v t := by
  obtain ⟨t, ht, hd⟩ := m.has_type _ hc φ
  exact ⟨_, t, m.defn_eq cv value hint hc φ, ht, hd⟩

/-- A stored theorem's proof value has a derivation of its statement. -/
theorem EnvTT.hasType_thm {env : Env} (m : EnvTT env) {cv : ConstantVal}
    {value : Expr} (hc : ConstantInfo.thmInfo cv value ∈ env.consts)
    (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧ HasType [] v t := by
  obtain ⟨t, ht, hd⟩ := m.has_type _ hc φ
  exact ⟨_, t, m.thm_ok cv value hc φ, ht, hd⟩

end Setlec.TTVerify
