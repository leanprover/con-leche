import Setlec.Kernel.Basis

/-!
# `V`-free environment predicates (task #123)

Three `Prop`s over a bare `Env` — block completeness for the pinned
basis blocks, "every stored recursor rule's constructor is stored", and
the native projection-table discipline — plus the two level-parameter
names the pinned basis declarations use and the basis-kind test on a
`ConstantInfo`.

These were written inside `Setlec/Model/IndModel.lean` and
`Setlec/Model/BasisVal.lean`, next to the semantic `IndOk`, but none of
them mentions a valuation, a set-theoretic universe or the `SetTheory`
class: they are statements about what the *checker's* environment
stores.  Relocated verbatim so both the set model and the declarative
type-theory bridge can import them (task #123, `Setlec/TTVerify/DESIGN.md`
§14.1).
-/

namespace Setlec

open Name

def uN : Name := anonymous |>.str "u"
def u1N : Name := anonymous |>.str "u_1"
def vN : Name := anonymous |>.str "v"

/-- Is this constant-info one of the basis kinds? -/
def ConstantInfo.isBasis : ConstantInfo → Bool
  | .indInfo _ _ | .ctorInfo _ _ _ | .recInfo _ _ _ _ => true
  | _ => false

/-- Block completeness: whenever a pinned basis *recursor* is stored,
the other members of its block are stored (pinned) too.  This holds
because blocks install as a unit with the recursor last; iota soundness
uses it to resolve the constants a rule right-hand side mentions. -/
def BasisBlocks (env : Env) : Prop :=
  (∀ cv mI rP rules,
    env.find? (eqName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
  (∀ cv mI rP rules,
    env.find? (natName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? natName = some natA ∧ env.find? natZeroName = some natZeroA ∧
    env.find? natSuccName = some natSuccA) ∧
  (∀ cv mI rP rules,
    env.find? (psigmaName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA) ∧
  (∀ cv mI rP rules,
    env.find? (punitName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? punitName = some punitA ∧
    env.find? punitUnitName = some punitUnitA)

/-- Every stored recursor rule's constructor is itself stored: blocks
carry their constructors, and the recursor is installed after them. -/
def RecCtorsStored (env : Env) : Prop :=
  ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, ∃ cvj cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)

theorem RecCtorsStored.empty : RecCtorsStored Env.empty := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

/-- Every stored *native* projection-table entry is one of the two
pinned pair entries, with the pair block's members stored pinned
alongside (native entries install only with the pinned `PSigma'`
block; the proj rules' soundness identifies the pair through this
clause instead of by name).  Template entries carry no obligation
here: the fallback's output is re-checked at every use. -/
def ProjOk (env : Env) : Prop :=
  ∀ n entry, env.find? n = some (.projInfo entry) →
    entry.native = true →
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA

theorem ProjOk.empty : ProjOk Env.empty := by
  intro n entry h
  simp [Env.find?, Env.empty] at h

theorem BasisBlocks.empty : BasisBlocks Env.empty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro cv mI rP rules h; simp [Env.find?, Env.empty] at h)

end Setlec
