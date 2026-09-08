module

public import ConLeche.Kernel.BasisA
public import ConLeche.Verify.EnvWF

public section

/-!
# `V`-free environment predicates (task #123)

Three `Prop`s over a bare `Env` — block completeness for the pinned
basis blocks, "every stored recursor rule's constructor is stored", and
the native projection-table discipline — plus the two level-parameter
names the pinned basis declarations use and the basis-kind test on a
`ConstantInfo`.

These were written inside `ConLeche/ModelV1/IndModel.lean` and
`ConLeche/ModelV1/BasisVal.lean`, next to the semantic `IndOk`, but none of
them mentions a valuation, a set-theoretic universe or the `SetTheory`
class: they are statements about what the *checker's* environment
stores.  Relocated verbatim so both the set model and the declarative
type-theory bridge can import them (task #123; the lane and its
record are gone, task #209).

Task #148's T1 added the rest of that class: `pinnedInfo` (with its two
`*_cases` inversions) from `ConLeche/ModelV1/BasisVal.lean`, and `ProjOkT`
— the strengthening of `ProjOk` that pins the pair block's own
projection names — from `ConLeche/TTVerify/EnvTT.lean`.  The bridge's
`uNT`/`vNT`/`u1NT`, `isBasisKind`, `pinnedInfoT` and `RecCtorsStoredT`
restatements are gone; the definitions here are the single home.
-/

namespace ConLeche

open Name

@[expose] def uN : Name := anonymous |>.str "u"
@[expose] def u1N : Name := anonymous |>.str "u_1"
@[expose] def vN : Name := anonymous |>.str "v"

/-- Is this constant-info one of the basis kinds? -/
@[expose] def ConstantInfo.isBasis : ConstantInfo → Bool
  | .indInfo _ _ | .ctorInfo _ _ _ | .recInfo _ _ _ _ => true
  | _ => false

/-- Block completeness: whenever a pinned basis *recursor* is stored,
the other members of its block are stored (pinned) too.  This holds
because blocks install as a unit with the recursor last; iota soundness
uses it to resolve the constants a rule right-hand side mentions. -/
@[expose] def BasisBlocks (env : Env) : Prop :=
  (∀ cv mI rP rules,
    env.find? (eqName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
  (∀ cv mI rP rules,
    env.find? (natName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? natName = some natA ∧ env.find? natZeroName = some natZeroA ∧
    env.find? natSuccName = some natSuccA) ∧
  (∀ cv mI rP rules,
    env.find? (punitName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? punitName = some punitA ∧
    env.find? punitUnitName = some punitUnitA)

/-- Every stored recursor rule's constructor is itself stored: blocks
carry their constructors, and the recursor is installed after them. -/
@[expose] def RecCtorsStored (env : Env) : Prop :=
  ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, ∃ cvj cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)

theorem RecCtorsStored.empty : RecCtorsStored Env.empty := by
  intro n cv mI rP rules h
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
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? n = some ci → env'.find? n = some ci)
    (h : TowerHead env entry) : TowerHead env' entry := by
  obtain ⟨h2, h3, h4, h5, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, hC, hlC, hstrip⟩⟩ := h
  exact ⟨h2, h3, h4, h5,
    ⟨cvT, caps, hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hT, hlT⟩,
    ⟨cvC, hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hC, hlC, hstrip⟩⟩

/-- **The projection-table discipline**: every stored table carries,
at each of its fields, the syntactic head data (`TowerHead`).

**Purely syntactic, so it transposes verbatim** — it mentions no
values, no interpretation and no derivations.  Relocated here (task
#148, T1) from `ConLeche/TTVerify/EnvTT.lean`, so that both verification
lanes can import it.  Until task #175 W6 a first conjunct pinned every
native non-tower entry to one of the two `PSigma'` pair entries; the
pin is retired with the pinned pair, and task #175 tower-flag retired
the table-kind flag itself — the modeled route installs no table, so
the discipline is uniform over every stored one. -/
@[expose] def ProjOkT (env : Env) : Prop :=
  ∀ n tbl, env.find? n = some (.projInfo tbl) →
    ∀ i, i < tbl.numFields → TowerHead env (tbl.entry i)

theorem ProjOkT.empty : ProjOkT Env.empty := by
  intro n tbl h; simp [Env.find?, Env.empty] at h

/-- A constant stored under a name that is not a `num` name is not a
tower table (those live under `projTableName`, a `num` name). -/
theorem isTowerEntry_false_of_find? {env : Env} {n : Name} {c : ConstantInfo}
    (hf : env.find? n = some c) (hn : ∀ p k, n ≠ Name.num p k) :
    c.isTowerEntry = false := by
  cases c with
  | projInfo tbl =>
    exfalso
    have h1 := List.find?_some hf
    have hname : (ConstantInfo.projInfo tbl).name = n := eq_of_beq (by simpa using h1)
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal, projTableName] at hname
    exact hn _ _ hname.symm
  | _ => rfl

/-- The discipline at a lookup: a stored entry's head data. -/
theorem ProjOkT.towerHead {env : Env} (h : ProjOkT env)
    {sn : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) :
    TowerHead env entry := by
  obtain ⟨tbl, hf', hi, rfl⟩ := Env.findProj?_some hf
  exact h _ _ hf' i hi

theorem BasisBlocks.empty : BasisBlocks Env.empty := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intro cv mI rP rules h; simp [Env.find?, Env.empty] at h)

/-- The pinned (annotated) declaration of one basis constant. -/
@[expose] def pinnedInfo (n : Name) : ConstantInfo :=
  if n = eqName then eqA
  else if n = eqReflName then eqReflA
  else if n = eqName.str "rec" then eqRecA
  else if n = natName then natA
  else if n = natZeroName then natZeroA
  else if n = natSuccName then natSuccA
  else if n = natName.str "rec" then natRecA
  else if n = punitName then punitA
  else if n = punitUnitName then punitUnitA
  else if n = punitName.str "rec" then punitRecA
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

/-- Which names carry constructor-shaped pinned declarations. -/
theorem pinnedInfo_ctorInfo_cases {n : Name} {cv : ConstantVal} {nP nF : Nat}
    (h : pinnedInfo n = .ctorInfo cv nP nF) :
    n = eqReflName ∨ n = natZeroName ∨ n = natSuccName ∨
    n = punitUnitName ∨ n = quotMkName := by
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
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · exact Or.inr (Or.inr (Or.inr (Or.inl h12)))
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
  by_cases h15a : n = falseName
  · rw [if_pos h15a] at h; exact nomatch h
  rw [if_neg h15a] at h
  by_cases h15b : n = falseName.str "rec"
  · rw [if_pos h15b] at h; exact nomatch h
  rw [if_neg h15b] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · exact Or.inr (Or.inr (Or.inr (Or.inr h17)))
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

end ConLeche
