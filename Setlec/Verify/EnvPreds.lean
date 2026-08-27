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

Task #148's T1 added the rest of that class: `pinnedInfo` (with its two
`*_cases` inversions) from `Setlec/Model/BasisVal.lean`, and `ProjOkT`
— the strengthening of `ProjOk` that pins the pair block's own
projection names — from `Setlec/TTVerify/EnvTT.lean`.  The bridge's
`uNT`/`vNT`/`u1NT`, `isBasisKind`, `pinnedInfoT` and `RecCtorsStoredT`
restatements are gone; the definitions here are the single home.
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

/-- Every stored *native* projection-table entry is one of the two
pinned pair entries, with the pair block stored alongside.

**Purely syntactic, so it transposes verbatim** — it mentions no
values, no interpretation and no derivations, and the `V` of
`EnvModel`'s `ProjOk` never appears in it.  That is worth noticing
rather than glossing: a clause that survives the transposition
*unchanged* is one that was never about the model in the first place,
and it is the cheapest kind of field to carry.

**Not** the same predicate as `ProjOk` above, which is its first
conjunct: this one additionally pins the pair block's own projection
names to native entries.  Relocated here verbatim (task #148, T1) from
`Setlec/TTVerify/EnvTT.lean`, so that both verification lanes can
import it. -/
def ProjOkT (env : Env) : Prop :=
  (∀ n entry, env.find? n = some (.projInfo entry) →
    entry.native = true →
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA) ∧
  ∀ i entry, env.find? (projFnName psigmaName i) = some (.projInfo entry) →
    entry.native = true

theorem ProjOkT.empty : ProjOkT Env.empty := by
  refine ⟨?_, ?_⟩ <;> (intro n entry h; simp [Env.find?, Env.empty] at h)

theorem BasisBlocks.empty : BasisBlocks Env.empty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro cv mI rP rules h; simp [Env.find?, Env.empty] at h)

/-- The pinned (annotated) declaration of one basis constant. -/
def pinnedInfo (n : Name) : ConstantInfo :=
  if n = eqName then eqA
  else if n = eqReflName then eqReflA
  else if n = eqName.str "rec" then eqRecA
  else if n = natName then natA
  else if n = natZeroName then natZeroA
  else if n = natSuccName then natSuccA
  else if n = natName.str "rec" then natRecA
  else if n = psigmaName then psigmaA
  else if n = psigmaMkName then psigmaMkA
  else if n = psigmaName.str "rec" then psigmaRecA
  else if n = punitName then punitA
  else if n = punitUnitName then punitUnitA
  else if n = punitName.str "rec" then punitRecA
  else if n = emptyName then emptyA
  else if n = emptyName.str "rec" then emptyRecA
  else if n = quotName then quotA
  else if n = quotMkName then quotMkA
  else if n = quotLiftName then quotLiftA
  else if n = quotIndName then quotIndA
  else if n = quotSoundName then quotSoundA
  else .axiomInfo ⟨n, [], .sort .zero⟩

/-- Which names carry constructor-shaped pinned declarations. -/
theorem pinnedInfo_ctorInfo_cases {n : Name} {cv : ConstantVal} {nP nF : Nat}
    (h : pinnedInfo n = .ctorInfo cv nP nF) :
    n = eqReflName ∨ n = natZeroName ∨ n = natSuccName ∨
    n = psigmaMkName ∨ n = punitUnitName ∨ n = quotMkName := by
  delta pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · exact Or.inl h2
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
  · rw [if_pos h3] at h; exact nomatch h
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · exact Or.inr (Or.inl h5)
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · exact Or.inr (Or.inr (Or.inl h6))
  rw [if_neg h6] at h
  by_cases h7 : n = natName.str "rec"
  · rw [if_pos h7] at h; exact nomatch h
  rw [if_neg h7] at h
  by_cases h8 : n = psigmaName
  · rw [if_pos h8] at h; exact nomatch h
  rw [if_neg h8] at h
  by_cases h9 : n = psigmaMkName
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  rw [if_neg h9] at h
  by_cases h10 : n = psigmaName.str "rec"
  · rw [if_pos h10] at h; exact nomatch h
  rw [if_neg h10] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · rw [if_pos h13] at h; exact nomatch h
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · rw [if_pos h15] at h; exact nomatch h
  rw [if_neg h15] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h17))))
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · rw [if_pos h18] at h; exact nomatch h
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · rw [if_pos h19] at h; exact nomatch h
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

/-- Which names carry recursor-shaped pinned declarations. -/
theorem pinnedInfo_recInfo_cases {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfo n = .recInfo cv mI rP rules) :
    n = eqName.str "rec" ∨ n = natName.str "rec" ∨
    n = psigmaName.str "rec" ∨ n = punitName.str "rec" ∨
    n = emptyName.str "rec" ∨ n = quotLiftName ∨ n = quotIndName := by
  delta pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
  · exact Or.inl h3
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · rw [if_pos h5] at h; exact nomatch h
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · rw [if_pos h6] at h; exact nomatch h
  rw [if_neg h6] at h
  by_cases h7 : n = natName.str "rec"
  · exact Or.inr (Or.inl h7)
  rw [if_neg h7] at h
  by_cases h8 : n = psigmaName
  · rw [if_pos h8] at h; exact nomatch h
  rw [if_neg h8] at h
  by_cases h9 : n = psigmaMkName
  · rw [if_pos h9] at h; exact nomatch h
  rw [if_neg h9] at h
  by_cases h10 : n = psigmaName.str "rec"
  · exact Or.inr (Or.inr (Or.inl h10))
  rw [if_neg h10] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · rw [if_pos h12] at h; exact nomatch h
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15))))
  rw [if_neg h15] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · rw [if_pos h17] at h; exact nomatch h
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18)))))
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h19)))))
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

end Setlec
