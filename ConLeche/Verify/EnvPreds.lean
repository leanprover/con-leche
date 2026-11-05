module

public import ConLeche.Kernel.Basis
public import ConLeche.Verify.EnvWF

public section

/-!
# `V`-free environment predicates

Three `Prop`s over a bare `Env` — block completeness for the pinned
basis blocks, "every stored recursor rule's constructor is stored", and
the native projection-table discipline (`ProjOkT`) — plus the two
level-parameter names the pinned basis declarations use, the basis-kind
test on a `ConstantInfo` and the pinned declarations themselves
(`pinnedInfo`, with its two `*_cases` inversions).

None of them mentions a valuation, a set-theoretic universe or the
`SetTheory` class: they are statements about what the *checker's*
environment stores, and this module is their single home — the model
tier imports them rather than restating them.
-/

namespace ConLeche

open Name

@[expose] def uN : Name := anonymous |>.str "u"
@[expose] def u1N : Name := anonymous |>.str "u_1"
@[expose] def vN : Name := anonymous |>.str "v"

/-- **A stored recursor's rules against the store**: every rule's
constructor is itself stored (blocks carry their constructors, and the
recursor is installed after them). -/
@[expose] def RecCtorsStored (env : Env) : Prop :=
  ∀ n cv mI rP isK rules,
    env.find? n = some (.recInfo cv mI rP isK rules) →
    ∀ r ∈ rules,
      ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)

theorem RecCtorsStored.empty : RecCtorsStored Env.empty := by
  intro n cv mI rP isK rules h
  simp [Env.find?, Env.empty] at h

/-- **A table entry's syntactic head data** (task #175 wiring
W5): the facts the direct install establishes syntactically for every
entry of the table it stores, and which the readings' consumers need
with no environment record beyond `ProjOkT` — the former, its
recursor and the constructor are unreserved names (the recogniser's
own guards, so a tower entry never sits at a pinned basis family);
the index is in range; the former is stored as an inductive and the
constructor as a constructor at the entry's own arities and level
parameters.  (Task #175 S1: the entry carries a *body*, not a type;
the bodies' scoping is `EnvWF`'s table clause.) -/
@[expose] def TowerHead (env : Env) (entry : ProjEntry) : Prop :=
  reservedBasisNames.contains entry.structName = false ∧
  reservedBasisNames.contains (entry.structName.str "rec") = false ∧
  reservedBasisNames.contains entry.ctor = false ∧
  entry.idx < entry.numFields ∧
  (∃ (cvT : ConstantVal) (caps : IndCaps),
    env.find? entry.structName = some (.indInfo cvT caps) ∧
    cvT.levelParams = entry.levelParams) ∧
  (∃ cvC : ConstantVal,
    env.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
    cvC.levelParams = entry.levelParams ∧
    (cvC.type.stripPis (entry.numParams + entry.numFields)).isSome = true)

/-- The head data survives any extension that keeps the two lookups. -/
theorem TowerHead.mono {env env' : Env} {entry : ProjEntry}
    (hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      env.find? n = some ci → env'.find? n = some ci)
    (h : TowerHead env entry) : TowerHead env' entry := by
  obtain ⟨h2, h3, h4, h5, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, hC, hlC, hstrip⟩⟩ := h
  exact ⟨h2, h3, h4, h5,
    ⟨cvT, caps, hkeep _ _ (fun _ _ _ _ _ hh => ConstantInfo.noConfusion hh) hT, hlT⟩,
    ⟨cvC, hkeep _ _ (fun _ _ _ _ _ hh => ConstantInfo.noConfusion hh) hC, hlC, hstrip⟩⟩

/-- **The projection-table discipline**: every stored table carries,
at each of its fields, the syntactic head data (`TowerHead`).

**Purely syntactic**: it mentions no values, no interpretation and
no derivations.  The
discipline is uniform over every stored table (task #175). -/
@[expose] def ProjOkT (env : Env) : Prop :=
  ∀ T tbl, env.findTable? T = some tbl →
    ∀ i, i < tbl.numFields → TowerHead env (tbl.entry i)

theorem ProjOkT.empty : ProjOkT Env.empty := by
  intro T tbl h; simp [Env.findTable?, Env.find?, Env.empty] at h

/-- The discipline at a lookup: a stored entry's head data. -/
theorem ProjOkT.towerHead {env : Env} (h : ProjOkT env)
    {sn : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) :
    TowerHead env entry := by
  obtain ⟨tbl, hf', hi, rfl⟩ := Env.findProj?_some hf
  exact h _ _ hf' i hi

/-- The pinned (stored) declaration of one basis constant. -/
@[expose] def pinnedInfo (n : Name) : ConstantInfo :=
  if n = eqName then eqA
  else if n = eqReflName then eqReflA
  else if n = eqName.str "rec" then eqRecA
  else if n = natName then natA
  else if n = natZeroName then natZeroA
  else if n = natSuccName then natSuccA
  else if n = natName.str "rec" then natRecA
  else if n = emptyName then emptyA
  else if n = emptyName.str "rec" then emptyRecA
  else if n = falseName then falseA
  else if n = falseName.str "rec" then falseRecA
  else if n = quotName then quotA
  else if n = quotMkName then quotMkA
  else if n = quotLiftName then quotLiftA
  else if n = quotIndName then quotIndA
  else if n = quotSoundName then quotSoundA
  else .axiomInfo ⟨n, [], .sort .zero⟩

end ConLeche
