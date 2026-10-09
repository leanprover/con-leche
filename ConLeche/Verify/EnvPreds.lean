module

public import ConLeche.Kernel.BasisA
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
recursor is installed after them), and each of the two rescue bits, if
set, is the *lookup's own* verdict — the K bit is `recRuleKOf` and the
η-rescue bit is `recRuleEtaOf` at the recursor's stored name.  The
bits are decided once, at the block's install (`recRuleBits`); this is
what lets `majorToCtor` read them instead of re-deriving the
cross-constant conditions — the capabilities and, at the η bit, the
constructor's level parameters — at every recursor application. -/
@[expose] def RecCtorsStored (env : Env) : Prop :=
  ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules,
      (∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
      (r.k = true → recRuleKOf env.find? r.ctor = true) ∧
      (r.eta = true → recRuleEtaOf env.find? n r.ctor = true)

theorem RecCtorsStored.empty : RecCtorsStored Env.empty := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

/-- **What a set K bit says about the store**: the rule's constructor
is stored with no fields, its result type is headed by a stored
inductive, and that inductive carries the K capability. -/
theorem recRuleKOf_inv {f : Name → Option ConstantInfo} {ctor : Name}
    (h : recRuleKOf f ctor = true) :
    ∃ (cvj : ConstantVal) (cnP : Nat) (T : Name) (us : List Level)
      (cvT : ConstantVal) (caps : IndCaps),
      f ctor = some (.ctorInfo cvj cnP 0) ∧
      (cvj.type.piResult).getAppFn = .const T us ∧
      f T = some (.indInfo cvT caps) ∧ caps.ruleK = true := by
  revert h
  unfold recRuleKOf
  match hfc : f ctor with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) =>
    intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) =>
    dsimp only
    match hpr : (cvj.type.piResult).getAppFn with
    | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
    | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      intro h; exact nomatch h
    | .const T us =>
      dsimp only
      match hfT : f T with
      | none => intro h; exact nomatch h
      | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
      | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _)
      | some (.projInfo _) => intro h; exact nomatch h
      | some (.indInfo cvT caps) =>
        intro h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨cvj, cnP, T, us, cvT, caps, by rw [h.2], hpr, hfT, h.1⟩

/-- The K bit, from the store. -/
theorem recRuleKOf_of {f : Name → Option ConstantInfo} {ctor : Name}
    {cvj : ConstantVal} {cnP : Nat} {T : Name} {us : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (h1 : f ctor = some (.ctorInfo cvj cnP 0))
    (h2 : (cvj.type.piResult).getAppFn = .const T us)
    (h3 : f T = some (.indInfo cvT caps)) (h4 : caps.ruleK = true) :
    recRuleKOf f ctor = true := by
  unfold recRuleKOf
  rw [h1]; dsimp only; rw [h2]; dsimp only; rw [h3]
  simp [h4]

/-- **What a set η-rescue bit says about the store**: the rule's
constructor is stored, its result type is headed by a stored
inductive, that inductive is η-capable through this very constructor,
the constructor carries the inductive's own level parameters, and the
recursor is not a projection function. -/
theorem recRuleEtaOf_inv {f : Name → Option ConstantInfo}
    {recName ctor : Name} (h : recRuleEtaOf f recName ctor = true) :
    ∃ (cvj : ConstantVal) (cnP cnF : Nat) (T : Name) (us : List Level)
      (cvT : ConstantVal) (caps : IndCaps),
      f ctor = some (.ctorInfo cvj cnP cnF) ∧
      (cvj.type.piResult).getAppFn = .const T us ∧
      f T = some (.indInfo cvT caps) ∧ caps.eta = true ∧
      caps.etaCtor = ctor ∧ Name.isProjFnShape recName = false ∧
      cvj.levelParams = cvT.levelParams := by
  revert h
  unfold recRuleEtaOf
  match hfc : f ctor with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) =>
    intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) =>
    dsimp only
    match hpr : (cvj.type.piResult).getAppFn with
    | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
    | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      intro h; exact nomatch h
    | .const T us =>
      dsimp only
      match hfT : f T with
      | none => intro h; exact nomatch h
      | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
      | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _)
      | some (.projInfo _) => intro h; exact nomatch h
      | some (.indInfo cvT caps) =>
        intro h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
          Bool.not_true] at h
        exact ⟨cvj, cnP, cnF, T, us, cvT, caps, rfl, hpr, hfT,
          h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The η-rescue bit, from the store. -/
theorem recRuleEtaOf_of {f : Name → Option ConstantInfo}
    {recName ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {us : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (h1 : f ctor = some (.ctorInfo cvj cnP cnF))
    (h2 : (cvj.type.piResult).getAppFn = .const T us)
    (h3 : f T = some (.indInfo cvT caps)) (h4 : caps.eta = true)
    (h5 : caps.etaCtor = ctor) (h6 : Name.isProjFnShape recName = false)
    (h7 : cvj.levelParams = cvT.levelParams) :
    recRuleEtaOf f recName ctor = true := by
  unfold recRuleEtaOf
  rw [h1]; dsimp only; rw [h2]; dsimp only; rw [h3]
  simp [h4, h5, h6, h7]

/-- The K bit's verdict survives any change of store that keeps the
non-recursor lookups (e.g. a fresh cons): it reads a
constructor and an inductive only. -/
theorem recRuleKOf_mono {f g : Name → Option ConstantInfo} {ctor : Name}
    (hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      f n = some ci → g n = some ci)
    (h : recRuleKOf f ctor = true) : recRuleKOf g ctor = true := by
  obtain ⟨cvj, cnP, T, us, cvT, caps, h1, h2, h3, h4⟩ := recRuleKOf_inv h
  exact recRuleKOf_of
    (hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) h1) h2
    (hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) h3) h4

/-- The η-rescue bit's verdict, likewise. -/
theorem recRuleEtaOf_mono {f g : Name → Option ConstantInfo}
    {recName ctor : Name}
    (hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      f n = some ci → g n = some ci)
    (h : recRuleEtaOf f recName ctor = true) :
    recRuleEtaOf g recName ctor = true := by
  obtain ⟨cvj, cnP, cnF, T, us, cvT, caps, h1, h2, h3, h4, h5, h6, h7⟩ :=
    recRuleEtaOf_inv h
  exact recRuleEtaOf_of
    (hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) h1) h2
    (hkeep _ _ (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) h3) h4 h5 h6 h7

/-- **The rescue bits, read back at a use.**  At a stored recursor
whose (single) rule's constructor and inductive have been looked up,
the invariant turns each set bit into the capability facts the rescue
consumes: the K bit into "no fields, and the inductive is K-capable",
the η bit into "the inductive is η-capable through this very
constructor, which carries the inductive's own level parameters".
These are the cross-constant conditions `majorToCtor` used to
re-derive at every recursor application. -/
theorem recCtors_bits {env : Env} (hctors : RecCtorsStored env)
    {recName : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {us₀ : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hfrec : env.find? recName = some (.recInfo cv mI rP rules))
    (hmem : rl ∈ rules)
    (hfcj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpres : (cvj.type.piResult).getAppFn = .const T us₀)
    (hfT : env.find? T = some (.indInfo cvT caps)) :
    (rl.k = true → caps.ruleK = true ∧ cnF = 0) ∧
    (rl.eta = true → caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
      cvj.levelParams = cvT.levelParams) := by
  obtain ⟨-, hk, he⟩ := hctors recName cv mI rP rules hfrec rl hmem
  constructor
  · intro hb
    obtain ⟨cvj', cnP', T', us', cvT', caps', h1, h2, h3, h4⟩ :=
      recRuleKOf_inv (hk hb)
    rw [hfcj] at h1
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj h1)
    rw [hpres] at h2
    obtain ⟨rfl, -⟩ := Expr.const.inj h2
    rw [hfT] at h3
    obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj h3)
    exact ⟨h4, rfl⟩
  · intro hb
    obtain ⟨cvj', cnP', cnF', T', us', cvT', caps', h1, h2, h3, h4, h5, -, h7⟩ :=
      recRuleEtaOf_inv (he hb)
    rw [hfcj] at h1
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj h1)
    rw [hpres] at h2
    obtain ⟨rfl, -⟩ := Expr.const.inj h2
    rw [hfT] at h3
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj h3)
    exact ⟨h4, h5.symm, h7⟩

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

**Purely syntactic**: it mentions no values, no interpretation and
no derivations.  The
discipline is uniform over every stored table (task #175). -/
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

/-- The pinned (annotated) declaration of one basis constant. -/
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
