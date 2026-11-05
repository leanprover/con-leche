module

public import ConLeche.Kernel.Core
public import ConLeche.Verify.Inductives.NestedRead

public section

/-!
# Environment well-formedness

`EnvWF` collects the syntactic facts the checker establishes for every
accepted constant — closed, level parameters within the declared list,
referenced constants resolving — as an invariant of the environment.  The
delta-unfolding and monotonicity lemmas need it.
-/

namespace ConLeche

/-- Unfold a successful projection-table lookup to the stored table:
the structure's table is stored, the index is in range, and the entry
is the table's view at it (task #175 S1). -/
theorem Env.findProj?_some {env : Env} {T : Name} {i : Nat}
    {entry : ProjEntry} (h : env.findProj? T i = some entry) :
    ∃ tbl : ProjTable, env.findTable? T = some tbl ∧
      i < tbl.numFields ∧ entry = tbl.entry i := by
  unfold Env.findProj? at h
  split at h
  next tbl heq =>
    split at h
    · next hi => exact ⟨tbl, heq, hi, (Option.some.inj h).symm⟩
    · exact nomatch h
  next => exact nomatch h

/-- The lookup at a stored table, in range. -/
theorem Env.findProj?_of_table {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) {i : Nat}
    (hi : i < tbl.numFields) : env.findProj? T i = some (tbl.entry i) := by
  unfold Env.findProj?
  rw [h]
  exact ite_eq_left hi

/-- A stored table is a member of the table component, under its
structure's name, and the structure is stored. -/
theorem Env.findTable?_mem {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) :
    tbl ∈ env.tables ∧ tbl.structName = T ∧ (env.find? T).isSome = true := by
  unfold Env.findTable? at h
  split at h
  · next hT =>
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h, hT⟩
  · exact nomatch h

/-- The table lookup at a stored structure is the table component's. -/
theorem Env.findTable?_of_isSome {env : Env} {T : Name} (hT : (env.find? T).isSome = true) :
    env.findTable? T = env.tables.find? (·.structName == T) := by
  unfold Env.findTable?
  rw [ite_eq_left hT]

/-- A table install leaves the constant lookups alone. -/
@[simp] theorem Env.find?_pushTable (env : Env) (t : ProjTable) :
    Env.find? ⟨env.consts, t :: env.tables⟩ = env.find? := rfl

/-- A table install answers its structure's name (where it is stored),
and leaves every other table lookup alone. -/
theorem Env.findTable?_pushTable (env : Env) (t : ProjTable) (T : Name) :
    Env.findTable? ⟨env.consts, t :: env.tables⟩ T =
      if t.structName = T ∧ (env.find? T).isSome = true then some t
      else env.findTable? T := by
  unfold Env.findTable?
  show (if (env.find? T).isSome = true then (t :: env.tables).find? _ else none) = _
  rw [List.find?_cons]
  by_cases hs : (env.find? T).isSome = true
  · by_cases hT : t.structName = T
    · simp [hT, hs]
    · have hb : (t.structName == T) = false := by simpa using hT
      simp only [hs, hb, hT, false_and, ↓reduceIte]
  · simp [hs]

@[simp] theorem ProjTable.entry_levelParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).levelParams = tbl.levelParams := rfl
@[simp] theorem ProjTable.entry_numParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).numParams = tbl.numParams := rfl
@[simp] theorem ProjTable.entry_body (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).body = tbl.bodies.getD i default := rfl
/-- A `stripPis` at a larger count strips at a smaller one. -/
theorem stripPis_isSome_of_le :
    ∀ {k n : Nat} {e : Expr}, k ≤ n → (e.stripPis n).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro n e _ _; simp [Expr.stripPis]
  | succ k ih =>
    intro n e hle h
    match n, hle with
    | n + 1, hle =>
      match e, h with
      | .forallE d bo, h =>
        simp only [Expr.stripPis, Option.isSome_map] at h ⊢
        exact ih (by omega) h

/-- Syntactic well-formedness of one stored constant w.r.t. `env`. -/
@[expose] def ConstWF (env : Env) (c : ConstantInfo) : Prop :=
  c.toConstantVal.type.hasFvar = false ∧
  c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
  c.toConstantVal.type.constsResolve env = true ∧
  c.toConstantVal.type.looseBVarsBounded 0 = true ∧
  (∀ cv value hint, c = .defnInfo cv value hint →
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true ∧
    value.looseBVarsBounded 0 = true) ∧
  (∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      -- a nested rule's datum reads off the recursor type
      -- (`NestedRead`: the pins are well formed in the rule-prefix
      -- context, and the major's domain applies the class's inductive
      -- at the levels to the pins' liftings past the index binders,
      -- followed by the index variables; what the generated stage
      -- stores, `genStage_nestedRead`)
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        NestedRead (·.constsResolve env) cv.levelParams cv.type mI rP pins.length lvls pins)
  -- (a theorem's stored value carries NO clause: a theorem is opaque
  -- to reduction and stored by its statement — the value is the
  -- record's own, unread by the kernel and by the invariant)

/-- **Syntactic well-formedness of one stored projection table** w.r.t.
`env` (task #175 S1; task #362 for the first clause): its structure is
a stored constant, and its bodies are closed with respect to free
variables, level parameters within the structure's list, resolving,
and scoped at the parameters and the subject; there are exactly
`numFields` of them. -/
@[expose] def TableWF (env : Env) (tbl : ProjTable) : Prop :=
  (env.find? tbl.structName).isSome = true ∧
  tbl.bodies.size = tbl.numFields ∧
  ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
    b.hasFvar = false ∧
    b.allLevelParamsDefined tbl.levelParams = true ∧
    b.constsResolve env = true ∧
    b.looseBVarsBounded (tbl.numParams + 1) = true

/-- `c` is stored as a definition. -/
@[expose] def isDefinitionAt (env : Env) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false

/-- **A stored certified operation's name holds a definition.**  The fast path fires by name; every
other kind of declaration is refused at such a name (`checkConstantVal`, `reservedRecName`). -/
@[expose] def OpDefn (env : Env) : Prop :=
  ∀ c, natOpName c = true → (env.find? c).isSome = true → isDefinitionAt env c = true

/-- A certified operation's name is not a pinned basis name. -/
theorem natOpName_not_reserved {c : Name} (h : natOpName c = true) :
    reservedBasisNames.contains c = false := by
  simp only [natOpName, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact (by decide : ∀ c ∈ natOpNames, reservedBasisNames.contains c = false) c h
  · exact (by decide : ∀ c ∈ natDivModNames, reservedBasisNames.contains c = false) c h

/-- `OpDefn` across a change that keeps which names are stored and every definition. -/
theorem OpDefn.of_same {env₀ env₃ : Env} (h : OpDefn env₀)
    (hs : ∀ n, (env₃.find? n).isSome = true → (env₀.find? n).isSome = true)
    (hd : ∀ n cv v hh, env₀.find? n = some (.defnInfo cv v hh) →
      env₃.find? n = some (.defnInfo cv v hh)) : OpDefn env₃ := by
  intro c hn hc
  have h₀ := h c hn (hs c hc)
  unfold isDefinitionAt at h₀ ⊢
  cases hx : env₀.find? c with
  | none => rw [hx] at h₀; exact nomatch h₀
  | some ci =>
    rw [hx] at h₀
    cases ci with
    | defnInfo cv v hh => rw [hd c cv v hh hx]
    | _ => exact nomatch h₀

/-- Every stored constant and every stored table is syntactically
well-formed. -/
structure EnvWF (env : Env) : Prop where
  consts : ∀ c ∈ env.consts, ConstWF env c
  /-- a constant at a literal's name has the shape a literal's meaning reads -/
  shapes : ∀ c ∈ env.consts, litShapeOk c = true
  tables : ∀ t ∈ env.tables, TableWF env t

/-- The table of a stored structure, off `EnvWF`. -/
theorem EnvWF.table {env : Env} (henv : EnvWF env) {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) : TableWF env tbl :=
  henv.tables tbl (Env.findTable?_mem h).1



/-- **A constant value's shape at a literal's name**, whatever kind of constant carries it. -/
@[expose] def LitShapeAt (cv : ConstantVal) : Prop :=
  ∀ c : ConstantInfo, c.toConstantVal = cv → litShapeOk c = true

/-- Off the reserved names, a constant's shape reads only its name, level parameters and type. -/
theorem litShapeAt_of_check {cv : ConstantVal} (hres : reservedBasisNames.contains cv.name = false)
    (h : litShapeOk (.axiomInfo cv) = true) : LitShapeAt cv := by
  intro c hc
  subst hc
  have hn : (ConstantInfo.axiomInfo c.toConstantVal).name = c.name := rfl
  have hn' : c.toConstantVal.name = c.name := rfl
  rw [hn'] at hres
  have h₁ : c.name ≠ natName := fun e => by rw [e] at hres; exact absurd hres (by decide)
  have h₂ : c.name ≠ natZeroName := fun e => by rw [e] at hres; exact absurd hres (by decide)
  have h₃ : c.name ≠ natSuccName := fun e => by rw [e] at hres; exact absurd hres (by decide)
  unfold litShapeOk at h ⊢
  rw [hn] at h
  simp only [h₁, h₂, h₃, ↓reduceIte] at h ⊢
  cases c <;> exact h

/-- A name off the ten has no shape to keep. -/
theorem litShapeOk_of_not_lit {c : ConstantInfo} (hn : litGuardNames.contains c.name = false) :
    litShapeOk c = true := by
  simp only [litGuardNames, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at hn
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := hn
  unfold litShapeOk
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ↓reduceIte]

/-- A recursor's name is off the ten, so it has no shape to keep. -/
theorem litShapeAt_of_reservedRec {cv : ConstantVal} (h : reservedRecName cv.name = false) :
    LitShapeAt cv := by
  intro c hc
  subst hc
  refine litShapeOk_of_not_lit ?_
  simp only [reservedRecName, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1.2

/-- `find?` on a cons. -/
theorem Env.find?_cons {c : ConstantInfo} {cs : List ConstantInfo} {ts : List ProjTable}
    {n : Name} :
    Env.find? ⟨c :: cs, ts⟩ n = if c.name = n then some c else Env.find? ⟨cs, ts⟩ n := by
  simp only [Env.find?, List.find?]
  split
  · next h => simp_all
  · next h => simp_all

/-- A cons finds its own head. -/
theorem Env.find?_cons_self (c : ConstantInfo) (env : Env) :
    Env.find? ⟨c :: env.consts, env.tables⟩ c.name = some c := by
  rw [Env.find?_cons, ite_eq_left rfl]

/-- A cons of a *fresh* head does not find anything new. -/
theorem Env.find?_cons_of_fresh {c : ConstantInfo} {env : Env}
    {n : Name} {ci : ConstantInfo} (hfresh : env.find? c.name = none)
    (h : env.find? n = some ci) :
    Env.find? ⟨c :: env.consts, env.tables⟩ n = some ci := by
  rw [Env.find?_cons]
  split
  · next heq => rw [heq, h] at hfresh; exact nomatch hfresh
  · exact h

/-- Extending the environment with a fresh constant does not change
successful lookups. -/
theorem Env.find?_cons_of_isSome {c : ConstantInfo} {env : Env} {n : Name}
    (hfresh : env.find? c.name = none) (h : (env.find? n).isSome = true) :
    Env.find? ⟨c :: env.consts, env.tables⟩ n = env.find? n := by
  rw [Env.find?_cons]
  split
  · next heq => rw [← heq] at h; rw [hfresh] at h; simp at h
  · rfl

/-- **A push of a fresh constant leaves the table lookups alone**
(task #362): a stored table's structure is stored (`TableWF`), so no
table waits for the fresh name. -/
theorem EnvWF.findTable?_cons {env : Env} (henv : EnvWF env) {c : ConstantInfo}
    (hfresh : env.find? c.name = none) (T : Name) :
    Env.findTable? ⟨c :: env.consts, env.tables⟩ T = env.findTable? T := by
  unfold Env.findTable?
  rw [Env.find?_cons]
  by_cases hT : c.name = T
  · subst hT
    rw [ite_eq_left rfl, hfresh]
    simp only [Option.isSome_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
    rw [List.find?_eq_none]
    intro t ht hq
    have hn : t.structName = c.name := by simpa using hq
    have := (henv.tables t ht).1
    rw [hn, hfresh] at this
    exact absurd this (by simp)
  · rw [ite_eq_right hT]

theorem EnvWF.findProj?_cons {env : Env} (henv : EnvWF env) {c : ConstantInfo}
    (hfresh : env.find? c.name = none) (T : Name) (i : Nat) :
    Env.findProj? ⟨c :: env.consts, env.tables⟩ T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [henv.findTable?_cons hfresh]

/-- **An extension that keeps the tables keeps the table lookups**
(task #362): a stored name stays stored, and a table waits for no name
the prefix lacks, since every stored table's structure is stored. -/
theorem EnvWF.findTable?_extend {env₀ env : Env} (henv : EnvWF env₀)
    (hF : ∀ n, (env₀.find? n).isSome = true → (env.find? n).isSome = true)
    (hT : env.tables = env₀.tables) (T : Name) :
    env.findTable? T = env₀.findTable? T := by
  unfold Env.findTable?
  by_cases h0 : (env₀.find? T).isSome = true
  · rw [ite_eq_left (hF T h0), ite_eq_left h0, hT]
  · rw [ite_eq_right h0]
    split
    · rw [hT, List.find?_eq_none]
      intro t ht hq
      have hn : t.structName = T := by simpa using hq
      have := (henv.tables t ht).1
      rw [hn] at this
      exact h0 this
    · rfl

theorem EnvWF.findProj?_extend {env₀ env : Env} (henv : EnvWF env₀)
    (hF : ∀ n, (env₀.find? n).isSome = true → (env.find? n).isSome = true)
    (hT : env.tables = env₀.tables) (T : Name) (i : Nat) :
    env.findProj? T i = env₀.findProj? T i := by
  unfold Env.findProj?
  rw [henv.findTable?_extend hF hT]

/-- Resolution depends on the environment only through which names it
finds: every name found in `env` being found in `env'` carries
resolution over. -/
theorem Expr.constsResolve_of_find {env env' : Env}
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ {e : Expr}, e.constsResolve env = true → e.constsResolve env' = true := by
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

/-- Resolution is monotone under environment extension. -/
theorem Expr.constsResolve_mono {c : ConstantInfo} {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨c :: env.consts, env.tables⟩ = true :=
  Expr.constsResolve_of_find fun n h => by
    rw [Env.find?_cons]
    split <;> simp_all

/-- Resolution survives binder opening. -/
theorem Expr.constsResolve_instantiate1 {env : Env} {d : Nat} {ty : Expr}
    (hty : ty.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 (.fvar d ty) k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · simpa [Expr.constsResolve] using hty
    · split <;> simp [Expr.constsResolve]

/-- Level instantiation does not change which constants occur. -/
theorem Expr.constsResolve_instantiateLevelParams {env : Env} (ks : List Name)
    (us : List Level) :
    ∀ {e : Expr}, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- Resolution survives `piResult` (peeling leading `∀`s keeps every
constant the residual mentions — task #342 L10, the `RecRuleExtra`
transport's clause (S)). -/
theorem Expr.constsResolve_piResult {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.piResult.constsResolve env = true
  | .forallE _ b, h => by
      have hb : b.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.2
      exact Expr.constsResolve_piResult (e := b) hb
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .app _ _, h | .lam _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.piResult] using h

/-- Resolution survives `getAppFn` (peeling an application spine's
head keeps every constant it mentions). -/
theorem Expr.constsResolve_getAppFn {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.getAppFn.constsResolve env = true
  | .app f _, h => by
      have hf : f.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.1
      exact Expr.constsResolve_getAppFn (e := f) hf
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .lam _ _, h | .forallE _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.getAppFn] using h

/-- **A resolving expression's `piResult`'s head constant is stored**
(task #342 L10): the constructor's stored type resolves (`ConstWF`),
so the family name heading its result — the one `iotaCtorNeverProp`
looks up — is stored too, hence never the fresh name of a cons. -/
theorem Expr.find?_isSome_of_piResult_getAppFn_const {env : Env} {e : Expr}
    {T : Name} {us : List Level} (hres : e.constsResolve env = true)
    (heq : e.piResult.getAppFn = .const T us) : (env.find? T).isSome = true := by
  have h2 := Expr.constsResolve_getAppFn (Expr.constsResolve_piResult hres)
  rw [heq] at h2
  simpa [Expr.constsResolve] using h2

/-- A constant push keeps a table well formed (its structure stays
found, its bodies keep resolving). -/
theorem TableWF.cons {c : ConstantInfo} {env : Env} {t : ProjTable} (h : TableWF env t) :
    TableWF ⟨c :: env.consts, env.tables⟩ t := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, h1, fun i b hb => ?_⟩
  · rw [Env.find?_cons]; split <;> simp_all
  · obtain ⟨g1, g2, g3, g4⟩ := h2 i b hb
    exact ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩

/-- Extending with a fresh, well-formed constant preserves `EnvWF`. -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env} (hs : litShapeOk c = true)
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts, env.tables⟩ c) :
    EnvWF ⟨c :: env.consts, env.tables⟩ := by
  refine ⟨fun c' hc' => ?_,
    fun c' hc' => (List.mem_cons.mp hc').elim (fun e => e ▸ hs) (henv.shapes c'),
    fun t ht => (henv.tables t ht).cons⟩
  rcases List.mem_cons.mp hc' with rfl | hmem
  · exact hc
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := henv.consts c' hmem
    refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value hint heq =>
      let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_⟩
    intro cv mI rP isK rules heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP isK rules heq r hr
    refine ⟨g1, g2, Expr.constsResolve_mono g3, g4, ?_⟩
    intro lvls pins hfr
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
    exact ⟨n1, n2, fun pin hpin =>
      let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      ⟨p1, p2, Expr.constsResolve_mono p3, p4⟩, n4⟩

/-- Resolution reads the environment only through `find?`. -/
theorem Expr.constsResolve_eq_of_find {env env' : Env} (h : env'.find? = env.find?)
    (e : Expr) : e.constsResolve env' = e.constsResolve env := by
  cases h₁ : e.constsResolve env
  · cases h₂ : e.constsResolve env'
    · rfl
    · have := Expr.constsResolve_of_find (fun n hn => by rw [← h]; exact hn) h₂
      rw [h₁] at this; exact absurd this Bool.false_ne_true
  · exact Expr.constsResolve_of_find (fun n hn => by rw [h]; exact hn) h₁

/-- A constant's well-formedness reads the environment only through
`find?`. -/
theorem ConstWF.of_find {env env' : Env} (h : env'.find? = env.find?) {c : ConstantInfo}
    (hc : ConstWF env c) : ConstWF env' c := by
  unfold ConstWF at hc ⊢
  simp only [Expr.constsResolve_eq_of_find h]
  exact hc

theorem Expr.constsResolve_eq_of_isSome {env env' : Env}
    (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome) (e : Expr) :
    e.constsResolve env' = e.constsResolve env := by
  cases h₂ : e.constsResolve env with
  | true => exact Expr.constsResolve_of_find (fun n hn => by rw [h]; exact hn) h₂
  | false =>
    cases h₁ : e.constsResolve env' with
    | true =>
      have := Expr.constsResolve_of_find (env := env') (env' := env)
        (fun n hn => by rw [← h]; exact hn) h₁
      rw [this] at h₂; exact nomatch h₂
    | false => rfl

/-- A constant's well-formedness reads which names are stored. -/
theorem ConstWF.of_isSome {env env' : Env} (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome)
    {c : ConstantInfo} (hc : ConstWF env c) : ConstWF env' c := by
  unfold ConstWF at hc ⊢
  simp only [Expr.constsResolve_eq_of_isSome h]
  exact hc

theorem TableWF.of_isSome {env env' : Env} (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome)
    {t : ProjTable} (ht : TableWF env t) : TableWF env' t := by
  unfold TableWF at ht ⊢
  simp only [Expr.constsResolve_eq_of_isSome h, h]
  exact ht

/-- A table's well-formedness reads the environment only through
`find?`. -/
theorem TableWF.of_find {env env' : Env} (h : env'.find? = env.find?) {t : ProjTable}
    (ht : TableWF env t) : TableWF env' t := by
  unfold TableWF at ht ⊢
  simp only [Expr.constsResolve_eq_of_find h, h]
  exact ht

/-- **Installing a well-formed table preserves `EnvWF`** (task #362): the
constants read the environment only through `find?`, which a table
install leaves alone. -/
theorem EnvWF.pushTable {env : Env} {t : ProjTable} (henv : EnvWF env)
    (ht : TableWF env t) : EnvWF ⟨env.consts, t :: env.tables⟩ :=
  ⟨fun c hc => (henv.consts c hc).of_find (Env.find?_pushTable env t), henv.shapes, fun t' ht' => by
    rcases List.mem_cons.mp ht' with rfl | hmem
    · exact ht.of_find (Env.find?_pushTable env _)
    · exact (henv.tables t' hmem).of_find (Env.find?_pushTable env t)⟩

/-- The kernel's name-list distinctness check is `List.Nodup`'s. -/
theorem nodup_of_nameNodup : ∀ {ns : List Name}, ConLeche.Name.nodup ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nameNodup h.2⟩
    have := h.1
    simp [hm] at this

/-! ## Two `find?` readings -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold ConLeche.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold ConLeche.Env.find? at h
  exact List.mem_of_find?_eq_some h

end ConLeche
