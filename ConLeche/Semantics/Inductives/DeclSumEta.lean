module

public import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Verify.EnvGuards
import ConLeche.Semantics.Inductives.DeclStructEta

@[expose] public section

/-!
# The direct sum declaration keeps the η-families closed (task #175
sum-types, indexed)

Every store the direct sum install performs is a fresh cons
(`checkConstantVal`'s duplicate guard for the former and the recursor;
the constructors are checked at the former's environment and consed
in order under the distinct-names guard), and the one former it
stores carries the sum's capability record (`sumCaps`, whose
`eta` is `false` — a sum is never structure-like), so
`EtaFamiliesClosed.cons_nonind` applies at every step.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape fueledOps checkSumCtors
   consSumCtors sumRules EtaFamiliesClosed)

/-- A name none of the consed constructors carries looks up below the
conses. -/
theorem consSumCtors_find?_of_not_mem {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      n ∉ ctorsA.map (·.1.name) → (consSumCtors nP ctorsA env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, hn => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [consSumCtors_find?_of_not_mem hn.2, ConLeche.Env.find?_cons, if_neg (fun h => hn.1 h.symm)]

end ConLeche.Semantics
