module

public import Fragment.Install
public import Fragment.NestSem

@[expose] public section

/-!
# The model remembers its blocks

A nested block reads its container's **family** — not just the
container's set in the model, but the fact that this set is the graph
of the least fixed point of the container's constructors, whose
leastness is what makes the class monotone (`NestSem.lean`).  So the
model of an environment carries, besides the three laws of
`EnvModel`, one law per stored plain block (`BlockLaw`): the block is
in scope, its former's and constructors' sets are the family's graph
and the constructors' graphs of the block's own installation, and the
domains met along a fitting instance are bounded at every fitting
parameter list — exactly the facts a later nesting consumes
(`NestFacts`).  A nested block stores no such law: nesting is at depth
one, so it is never a container (the law is conditional on the block
being plain).

The law is stated at the model's own assignment, and survives every
later installation because the block's syntax mentions only constants
stored before it (`EnvModel.transport`'s argument again:
`famSet_congr`, `ctorSet_congr`, `DomsBounded_congr`).

Con-leche: the `lfpBlocks` of `EnvModelM`
(`ConLeche/Model/Annot/EnvModelM.lean`), the datum of every installed
block kept with the model.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) {env : Env}

/-- **The block's law** in a model: for a plain block, its scope, its
constants stored, its former's set the family's graph, its
constructors' sets their graphs, and its domains bounded at fitting
parameters.  Vacuous for a nested block. -/
def BlockLaw (env : Env) (M : Name → List Nat → V) : Prop :=
  S.nest = none →
    S.Scoped env ∧ S.NoCont ∧
    env.find? S.name = some S.indInfo ∧
    (∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → env.find? c.name = some (S.ctorInfo c)) ∧
    (∀ ls, M S.name ls = S.famSet M ls) ∧
    (∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → ∀ ls, M c.name ls = S.ctorSet M ls j c) ∧
    (∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → S.DomsBounded M ls ps)

end IndSpec

/-- **A model of an environment that remembers its blocks**: an
`EnvModel` with the block law of every stored block. -/
structure BlockModel (V : Type u) [IndLib V] (env : Env) extends EnvModel V env where
  /-- Every stored block's law. -/
  blocks : ∀ (K : Name) (ci : ConstInfo) (nP nI : Nat) (cs : List Name) (spec : IndSpec),
    env.find? K = some ci → ci.kind = .induct nP nI cs spec → spec.BlockLaw env M

/-- The empty environment's model remembers nothing. -/
def BlockModel.empty (M : Name → List Nat → V) : BlockModel V Env.empty where
  toEnvModel := EnvModel.empty M
  blocks := fun _ _ _ _ _ _ h => by simp at h

/-! ## Hygiene: a block's semantic objects read the model at its stored constants only -/

namespace IndSpec

variable (S : IndSpec) {env : Env} {M M' : Name → List Nat → V}

/-- The bounding family reads the model at the block's constants only. -/
theorem boundJ_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat) (ps : List V) :
    S.boundJ M ls ps = S.boundJ M' ls ps := by
  sorry

/-- The family reads the model at the block's constants only. -/
theorem Mem_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat) :
    S.Mem M ls = S.Mem M' ls := by
  sorry

theorem Fam_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat) :
    S.Fam M ls = S.Fam M' ls := by
  sorry

theorem famSet_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat) :
    S.famSet M ls = S.famSet M' ls := by
  sorry

theorem ctorSet_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat) (j : Nat)
    (c : CtorSpec) : S.ctorSet M ls j c = S.ctorSet M' ls j c := by
  sorry

theorem DomsBounded_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat)
    (ps : List V) : S.DomsBounded M ls ps ↔ S.DomsBounded M' ls ps := by
  sorry

theorem FitsVals_params_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat)
    (ps : List V) :
    FitsVals M (S.ψ ls) base S.params ps ↔ FitsVals M' (S.ψ ls) base S.params ps := by
  sorry

/-- **The block law survives a change of assignment away from the
stored constants.** -/
theorem BlockLaw_transport (hM : AgreeOn env M M') (h : S.BlockLaw env M) : S.BlockLaw env M' := by
  sorry

/-- **The block law survives growing the environment** under fresh
names. -/
theorem BlockLaw_add (h : S.BlockLaw env M) (c : Name) (ci : ConstInfo) (hfresh : env.find? c = none) :
    S.BlockLaw (env.add c ci) M := by
  sorry

end IndSpec

/-! ## The two installations keep the block laws -/

variable [LevelOracle]

/-- **Installing a definition preserves having a block model.** -/
theorem install_def' {env : Env} {c : Name} {ci : ConstInfo} (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : DefOk env c ci) :
    ∃ m' : BlockModel V (env.add c ci), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  sorry

/-- **Installing a plain inductive block preserves having a block
model**, and the new block satisfies its law. -/
theorem install_ind' {env : Env} {S : IndSpec} (hpl : S.nest = none) (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : S.Ok env) :
    ∃ m' : BlockModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  sorry

end Fragment
