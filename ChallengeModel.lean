import Setlec.Cached.ParsedC
import Setlec.Semantics.Sem

/-!
# Comparator challenge: the model

The checker's acceptance claim in model form (config in
`comparator-model.json`, proof in `SolutionModel.lean`).  Trusted here:
the shipped checker up to its driver `checkDeclsSPCachedD`, the
`SetTheory` interface with its derived set constructions, and `sem`, the
interpretation of a checker term (`Setlec/Semantics/Sem.lean`).
-/

namespace Setlec

open SetTheory

/--
If the checker at `cfgP` (what `setlec --verified`, the default, runs)
accepts `ds` with environment `env'`, then in every model `V` of
`SetTheory` there is a set `cval n φ` for every constant `n` and level
assignment `φ` such that, under `sem`, every stored definition and
theorem denotes its body and every stored constant is a member of its
type.  In particular every theorem's statement is true.
-/
theorem model_exists (V : Type w) [SetTheory V]
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∃ cval : Name → (Name → Nat) → V,
      (∀ (cv : ConstantVal) (value : Expr),
        ((∃ hint, ConstantInfo.defnInfo cv value hint ∈ env'.consts) ∨
          ConstantInfo.thmInfo cv value ∈ env'.consts) →
        ∀ (φ : Name → Nat) (ρ : Nat → V),
          Semantics.sem cval env' φ 0 ρ value = cval cv.name φ) ∧
      (∀ c ∈ env'.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
        cval c.name φ ∈ˢ Semantics.sem cval env' φ 0 ρ c.toConstantVal.type) :=
  sorry
