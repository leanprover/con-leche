module

public import Fragment.Modular
public import Fragment.InstallThm

@[expose] public section

/-!
# Modular checking: one model for every module

A development is a graph of modules (`Module`).  Each module checks
its own declarations against its **context**, an environment made of
constants read from earlier modules, and **resolves** every name it stores
to a **qualified name** (`Key`): an ordinary constant is named by its
home module and its name, a proof by its name and statement.  The
**local checks** (`LocalOk`) read the module and the modules its context draws from
only.  The theorem (`modular`, `ModularInstance.lean`): if every module passes them, one
assignment of sets to the qualified names — the world's model, every
proof the point — gives every module's own environment a model through
its resolution (`modular_model`), so no module proves an empty
proposition (`modular_no_empty_prop_inhabitant`).

The theorem is the generic one (`ModularSemantics.lean`) at the
fragment's semantics (`ModularInstance.lean`).  This file holds what
that instance is made of: a context's model is read from the models of
the modules it reads from through the resolution (`PReads.model`) —
the laws of each context constant are those of the import's constant
it refines, at the qualified names it reads as the import does; the
module's declarations are installed on it (`Checks.blockModel`, the
theorems of `Install.lean`), every proof its point (`defVal_eq_pt`);
and every constant fits its qualified name (`fits`), so a module's own
ordinary constants are new qualified names.  Two constants with one
name that never meet in one context are two qualified names, and
nothing compares them; two proofs of one statement are one qualified
name, and the model gives every proof the point.

**A module may instead be validated by comparison** (`Compared`): its
whole own environment reads from earlier modules — every constant is
an earlier module's constant, or an assumption of its type (a hole).
Its model is then the restriction of the world's (`PReads.model`), and
every statement it stores holds there (`modular_statements_hold`).  A
challenge compared with its solution is such a module.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

/-! ## Proofs denote the point -/

/-- **A declaration of a proposition**: a theorem, or a definition
whose type the checker finds to be a proposition. -/
def Decl.IsProof (E : Env) : Decl → Prop
  | .thm .. => True
  | .defn _ ci => ∃ s u, Infer E [] ci.type s ∧ Red E [] s (.sort u) ∧ LevelOracle.eq u .zero = true
  | .ind _ => False

/-- **A proof's set is the point**, at every list of levels: the value
lies in the type, and the type is a truth value. -/
theorem defVal_eq_pt {env : Env} (m : EnvModel V env) {c : Name} {ci : ConstInfo} {v : Expr}
    (hok : DefOk env c ci) (hk : ci.kind = .defn v)
    (hp : ∃ s u, Infer env [] ci.type s ∧ Red env [] s (.sort u) ∧ LevelOracle.eq u .zero = true)
    (ls : List Nat) : defVal m.M ci v ls = pt := by
  obtain ⟨-, ⟨s₀, u₀, hT, hsu⟩, ⟨v', T, hk', hv, hd, -⟩, -⟩ := hok
  rw [hk] at hk'; cases hk'
  obtain ⟨s, u, hs, hsr, hu⟩ := hp
  let φ := valOf ci.lparams ls
  have hvsem := infer_sound (m := m) (φ := φ) hv base (Sat_nil _ _ _)
  obtain ⟨hTw, hTmem⟩ := Infer.mem_typeU_of (m := m) (φ := φ)
    (infer_sound hT) (red_sound hsu) (Sat_nil _ _ base)
  have heq := defeq_sound (m := m) (φ := φ) hd base (Sat_nil _ _ _)
    hvsem.2.1 hTw hvsem.2.2.1.ne_pt (IsTy_of_mem_typeU hTmem).ne_pt
  obtain ⟨-, hU⟩ := Infer.mem_typeU_of (m := m) (φ := φ)
    (infer_sound hs) (red_sound hsr) (Sat_nil _ _ base)
  rw [eval_eq_of_oracle hu, Level.eval, mem_typeU_zero] at hU
  have hmem := hvsem.2.2.2
  rw [heq] at hmem
  exact eq_pt_of_mem_univ_zero hU hmem

/-! ## Installing a checked list -/

/-- **The proof flags of a list**: a flagged name belongs to a
declaration of a proposition, at the point it is checked. -/
inductive FlagsOk (p : Name → Bool) : Env → List Decl → Prop
  | nil {E : Env} : FlagsOk p E []
  | cons {E : Env} {d : Decl} {ds : List Decl} :
      (∀ n ∈ d.names, p n = true → d.IsProof E) → FlagsOk p (d.apply E) ds → FlagsOk p E (d :: ds)

omit [IndLib V] [LevelOracle] in
theorem isSome_find?_apply {E : Env} {n : Name} (h : (E.find? n).isSome) (d : Decl) :
    ((d.apply E).find? n).isSome := by
  rw [Decl.apply_eq]
  cases hl : d.stores.lookup n with
  | some e => simp [Env.find?, lookup_append_of_some hl]
  | none => simp only [Env.find?, lookup_append_of_none hl]; exact h

/-- **Installing a checked list preserves having a model**: every
stored constant keeps its set, and every flagged constant's set is the
point. -/
theorem Checks.blockModel {E : Env} {ds : List Decl} (hc : Checks E ds) :
    ∀ (p : Name → Bool), FlagsOk p E ds → Env.Scoped E → ∀ m : BlockModel V E,
      ∃ m' : BlockModel V (applyAll ds E),
        (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
        (∀ d ∈ ds, ∀ n ∈ d.names, p n = true → ∀ ls, m'.M n ls = pt) := by
  induction hc with
  | nil => intro p _ _ m; exact ⟨m, fun _ _ _ => rfl, fun _ hd => by cases hd⟩
  | @cons E d ds hd _ ih =>
    intro p hp hs m
    cases hp with
    | cons hflag hrest =>
    -- install `d`, with the value of a proof the point
    obtain ⟨m₁, hag₁, hpt₁⟩ : ∃ m₁ : BlockModel V (d.apply E),
        (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) ∧
        (∀ n ∈ d.names, p n = true → ∀ ls, m₁.M n ls = pt) := by
      cases d with
      | defn c ci =>
        obtain ⟨m₁, hag, hval⟩ := install_def' hs m hd
        refine ⟨m₁, hag, fun n hn hpn ls => ?_⟩
        simp only [Decl.names, List.mem_singleton] at hn
        subst hn
        obtain ⟨v, -, hk, -⟩ := hd.2.2.1
        rw [hval v hk ls]
        exact defVal_eq_pt m.toEnvModel hd hk (hflag _ (by simp [Decl.names]) hpn) ls
      | thm c ci v =>
        obtain ⟨m₁, hag, hval⟩ := install_thm hs m hd
        refine ⟨m₁, hag, fun n hn _ ls => ?_⟩
        simp only [Decl.names, List.mem_singleton] at hn
        subst hn
        rw [hval ls]
        exact defVal_eq_pt m.toEnvModel hd.2.1 rfl hd.2.2 ls
      | ind S =>
        obtain ⟨m₁, hag⟩ := install_ind_any hs m hd
        exact ⟨m₁, hag, fun n hn hpn => absurd (hflag n hn hpn) (by simp [Decl.IsProof])⟩
    have hs₁ : Env.Scoped (d.apply E) := by
      cases d with
      | defn c ci => exact hs.add_def hd
      | thm c ci v => exact hs.add_thm hd
      | ind S => exact hs.install_any hd
    obtain ⟨m', hag', hpt'⟩ := ih p hrest hs₁ m₁
    refine ⟨m', fun n hn ls => (hag' n (isSome_find?_apply hn d) ls).trans (hag₁ n hn ls),
      fun d' hd' n hn hpn ls => ?_⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · have hstored : ((d'.apply E).find? n).isSome := by
        rw [Decl.apply_eq]
        obtain ⟨e, he⟩ := (d'.mem_names_iff n).mp hn
        have := lookup_ne_none_of_mem he
        cases hl : d'.stores.lookup n with
        | none => exact absurd hl this
        | some e' => simp [Env.find?, lookup_append_of_some hl]
      rw [hag' n hstored ls]
      exact hpt₁ n hn hpn ls
    · exact hpt' d' hd' n hn hpn ls

/-! ## Modules, names and their resolution -/

/-- **A qualified name**: an ordinary constant is named by its home
module and its name; a proof by its name and statement (two proofs of
one statement are one constant: the model gives every proof the
point). -/
inductive Key where
  | qual (module : Nat) (n : Name)
  | proof (n : Name) (lparams : List Name) (type : Expr)
  deriving DecidableEq

/-- **A module**: its declarations; its **context**, the environment
they are checked against; for each name of the context, the earlier
module it is read from, its home (`src`); which of its own
constants are proofs (`proofs`); and its **resolution** of names to
qualified names (`res`). -/
structure Module where
  decls : List Decl
  context : Env
  src : Name → Nat
  proofs : Name → Bool
  res : Name → Key

/-- **A module's own environment**: its context with its declarations. -/
def Module.own (m : Module) : Env := applyAll m.decls m.context

/-- The qualified name of an own constant of module `i`. -/
def Module.ownKey (m : Module) (i : Nat) (n : Name) (ci : ConstInfo) : Key :=
  if m.proofs n then .proof n ci.lparams ci.type else .qual i n

/-- **The part of module `b`'s own environment that module `i` reads
as `b` does**, for an environment `E` of `i`: the names `E` stores and
`i` resolves as `b` resolves them. -/
def readsAlike (dev : Nat → Module) (i : Nat) (E : Env) (b : Nat) : Env :=
  ⟨(dev b).own.consts.filter fun p => (E.find? p.1).isSome && (dev i).res p.1 == (dev b).res p.1⟩

/-- **A constant within an environment**: what its laws read — its
type, its value, its rules with their constructors, its block — is in
scope there, and the constructors a recursor's rules name are stored
there as in `E'`. -/
def EntryScoped (C E' : Env) (ci : ConstInfo) : Prop :=
  Expr.Scoped C ci.lparams 0 ci.type ∧
  (∀ v, ci.value? = some v → Expr.Scoped C ci.lparams 0 v) ∧
  (∀ nP nM nMin nI rules, ci.kind = .recursor nP nM nMin nI rules → ∀ rl ∈ rules,
    Expr.Scoped C ci.lparams 0 rl.rhs ∧
    ∃ cij, C.find? rl.ctor = some cij ∧ E'.find? rl.ctor = some cij ∧
      Expr.Scoped C cij.lparams 0 cij.type) ∧
  (∀ nP nI cs S, ci.kind = .induct nP nI cs S → S.nest = none →
    S.Scoped C ∧ (C.find? S.name).isSome ∧
      ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → (C.find? c.name).isSome)

/-- **An environment of module `i` reads from earlier modules**: every
constant it stores is read from an earlier module, its home; it
refines the home's own constant and lies within the part of the home's
own environment `i` reads as the home does; `i` resolves it as the
home does; and a type former stored as such comes with its
constructors.  A type former may be read as an assumption of its type
(it refines the type former), and then brings no constructors. -/
structure ReadsFrom (dev : Nat → Module) (i : Nat) (E : Env) : Prop where
  src_lt : ∀ n, (E.find? n).isSome → (dev i).src n < i
  le : ∀ n ci, E.find? n = some ci →
    ∃ ci', (dev ((dev i).src n)).own.find? n = some ci' ∧ ci.Le ci' ∧
      EntryScoped (readsAlike dev i E ((dev i).src n)) E ci
  res : ∀ n, (E.find? n).isSome → (dev i).res n = (dev ((dev i).src n)).res n
  blocks : ∀ n ci nP nI cs S, E.find? n = some ci → ci.kind = .induct nP nI cs S →
    S.nest = none → E.find? S.name = some S.indInfo ∧
      ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → E.find? c.name = some (S.ctorInfo c)

/-- **The local checks at module `i`.**  They read the module and the
earlier modules its context draws from — their own environments and
resolutions — and nothing else:

* the context reads from earlier modules (`ReadsFrom`);
* the declarations are accepted against the context, and a constant
  flagged a proof is a declaration of a proposition;
* an own name resolves to its own qualified name. -/
structure LocalOk (dev : Nat → Module) (i : Nat) : Prop where
  reads : ReadsFrom dev i (dev i).context
  checks : Checks (dev i).context (dev i).decls
  flags : FlagsOk (dev i).proofs (dev i).context (dev i).decls
  res_own : ∀ d ∈ (dev i).decls, ∀ n ∈ d.names, ∀ ci, (dev i).own.find? n = some ci →
    (dev i).res n = (dev i).ownKey i n ci

/-- **Validation by comparison**: module `i`'s whole own environment,
its declarations included, reads from earlier modules — every constant
is an earlier module's, or an assumption of its type. -/
def Compared (dev : Nat → Module) (i : Nat) : Prop := ReadsFrom dev i (dev i).own

/-- **A validated module**: checked, or compared. -/
def Valid (dev : Nat → Module) (i : Nat) : Prop := LocalOk dev i ∨ Compared dev i

/-! ## Lookups -/

omit [IndLib V] [LevelOracle] in
/-- An environment filtered by names: a kept name is looked up as
before. -/
theorem find?_filter {E : Env} {p : Name → Bool} {n : Name} :
    (⟨E.consts.filter fun q => p q.1⟩ : Env).find? n = if p n then E.find? n else none := by
  obtain ⟨cs⟩ := E
  induction cs with
  | nil => simp [Env.find?]
  | cons q cs ih =>
    obtain ⟨m, cm⟩ := q
    have ih' : List.lookup n (cs.filter fun q => p q.1) = if p n then List.lookup n cs else none := ih
    by_cases hnm : n = m
    · subst hnm
      by_cases hp : p n = true
      · simp [Env.find?, hp, List.lookup]
      · have hpf : p n = false := by simpa using hp
        simp only [Env.find?, List.filter_cons, hpf]
        simpa [hpf] using ih'
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      by_cases hp : p m = true
      · simp only [Env.find?, List.filter_cons, hp, ite_true, List.lookup, hb]
        exact ih'
      · have hpf : p m = false := by simpa using hp
        simp only [Env.find?, List.filter_cons, hpf, List.lookup, hb]
        exact ih'

omit [IndLib V] [LevelOracle] in
theorem find?_readsAlike {dev : Nat → Module} {i b : Nat} {E : Env} {n : Name} {ci : ConstInfo}
    (h : (readsAlike dev i E b).find? n = some ci) :
    (dev b).own.find? n = some ci ∧ (E.find? n).isSome ∧ (dev i).res n = (dev b).res n := by
  unfold readsAlike at h
  rw [find?_filter (p := fun n => (E.find? n).isSome && (dev i).res n == (dev b).res n)] at h
  split at h
  · rename_i hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨h, hp.1, hp.2⟩
  · cases h

/-! ## Resolution -/

/-- **What a qualified name says of a constant** of module `j`
stored under `n`: an ordinary name points to the constant's home
module, no later than `j`, whose own constant it refines; a proof's
name carries its statement. -/
def Key.Fits (dev : Nat → Module) (j : Nat) (n : Name) (ci : ConstInfo) : Key → Prop
  | .qual P n' => n' = n ∧ P ≤ j ∧ ∃ cp, (dev P).own.find? n = some cp ∧ ci.Le cp
  | .proof n' lps T => n' = n ∧ ci.lparams = lps ∧ ci.type = T

/-- **Every constant of a module's own environment fits its qualified
name.** -/
theorem fits (dev : Nat → Module) :
    ∀ i, (∀ j ≤ i, Valid dev j) → ∀ n ci, (dev i).own.find? n = some ci →
      ((dev i).res n).Fits dev i n ci := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hall n ci hf
  -- a constant read from an earlier module fits that module's qualified name
  have hread : ∀ {E : Env}, ReadsFrom dev i E → E.find? n = some ci →
      ((dev i).res n).Fits dev i n ci := by
    intro E hE hl
    obtain ⟨ci', hci', hle, -⟩ := hE.le n ci hl
    have hb := hE.src_lt n (by rw [hl]; rfl)
    have hfit := ih _ hb (fun j hj => hall j (Nat.le_trans hj (Nat.le_of_lt hb))) n ci' hci'
    rw [hE.res n (by rw [hl]; rfl)]
    revert hfit
    cases (dev ((dev i).src n)).res n with
    | qual P n' =>
      rintro ⟨rfl, hP, cp, hcp, hle'⟩
      exact ⟨rfl, Nat.le_trans hP (Nat.le_of_lt hb), cp, hcp, hle.trans hle'⟩
    | proof n' lps T =>
      rintro ⟨rfl, hl', ht'⟩
      exact ⟨rfl, hle.lparams_eq.symm.trans hl', hle.type_eq.symm.trans ht'⟩
  rcases hall i (Nat.le_refl i) with h | hc
  · rcases find?_applyAll hf with ⟨d, hd, hl⟩ | hl
    · have hn : n ∈ d.names := (d.mem_names_iff n).mpr ⟨ci, key_of_lookup hl⟩
      rw [h.res_own d hd n hn ci hf]
      unfold Module.ownKey
      split
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, Nat.le_refl i, ci, hf, .inl rfl⟩
    · exact hread h.reads hl
  · exact hread hc hf

/-! ## The context's model -/

/-- A module's assignment read through its resolution from an
assignment of the qualified names. -/
def resAssign (G : Key → List Nat → V) (m : Module) : Name → List Nat → V :=
  fun n ls => G (m.res n) ls

/-! ## Pieces: an environment with its resolution -/

/-- **A piece**: an environment with its resolution of names to
qualified names — a module's context or own environment as the world
reads it. -/
structure Piece where
  env : Env
  res : Name → Key

/-- The piece with its qualified names renamed. -/
def Piece.rename (ρ : Key → Key) (p : Piece) : Piece := ⟨p.env, ρ ∘ p.res⟩

/-- **The part of piece `q` that piece `p` reads as `q` does**: the
names `p` stores and resolves as `q` resolves them. -/
def readsAlikeP (p q : Piece) : Env :=
  ⟨q.env.consts.filter fun x => (p.env.find? x.1).isSome && p.res x.1 == q.res x.1⟩

omit [IndLib V] [LevelOracle] in
theorem readsAlike_eq (dev : Nat → Module) (i : Nat) (E : Env) (b : Nat) :
    readsAlike dev i E b = readsAlikeP ⟨E, (dev i).res⟩ ⟨(dev b).own, (dev b).res⟩ := rfl

omit [IndLib V] [LevelOracle] in
theorem find?_readsAlikeP {p q : Piece} {n : Name} {ci : ConstInfo}
    (h : (readsAlikeP p q).find? n = some ci) :
    q.env.find? n = some ci ∧ (p.env.find? n).isSome ∧ p.res n = q.res n := by
  unfold readsAlikeP at h
  rw [find?_filter (p := fun n => (p.env.find? n).isSome && p.res n == q.res n)] at h
  split at h
  · rename_i hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨h, hp.1, hp.2⟩
  · cases h

omit [IndLib V] [LevelOracle] in
theorem find?_readsAlikeP_of {p q : Piece} {n : Name} {ci : ConstInfo}
    (h : q.env.find? n = some ci) (hp : (p.env.find? n).isSome) (hr : p.res n = q.res n) :
    (readsAlikeP p q).find? n = some ci := by
  unfold readsAlikeP
  rw [find?_filter (p := fun n => (p.env.find? n).isSome && p.res n == q.res n)]
  simp [hp, hr, h]

/-- **A piece reads from a list of pieces**: every constant it stores
refines the constant of one of them (its source) under the same
qualified name, and lies within the part of the source it reads as the
source does; a type former stored as such comes with its
constructors. -/
structure PReads (p : Piece) (Q : List Piece) : Prop where
  le : ∀ n ci, p.env.find? n = some ci → ∃ q ∈ Q, q.res n = p.res n ∧
    ∃ ci', q.env.find? n = some ci' ∧ ci.Le ci' ∧ EntryScoped (readsAlikeP p q) p.env ci
  blocks : ∀ n ci nP nI cs S, p.env.find? n = some ci → ci.kind = .induct nP nI cs S →
    S.nest = none → p.env.find? S.name = some S.indInfo ∧
      ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → p.env.find? c.name = some (S.ctorInfo c)

omit [IndLib V] [LevelOracle] in
/-- **The local reading is a reading from the earlier modules' own
environments.** -/
theorem ReadsFrom.preads {dev : Nat → Module} {i : Nat} {E : Env} (h : ReadsFrom dev i E)
    {Q : List Piece} (hQ : ∀ b < i, (⟨(dev b).own, (dev b).res⟩ : Piece) ∈ Q) :
    PReads ⟨E, (dev i).res⟩ Q where
  le n ci hf := by
    have hs : (E.find? n).isSome := by rw [hf]; rfl
    obtain ⟨ci', hf', hle, hsc⟩ := h.le n ci hf
    exact ⟨_, hQ _ (h.src_lt n hs), (h.res n hs).symm, ci', hf', hle, hsc⟩
  blocks := h.blocks

omit [LevelOracle] in
/-- **A piece that reads from a list of pieces has a model**, read
through its resolution from models of the pieces that read the
qualified names the same way: the restriction of their models. -/
theorem PReads.model {p : Piece} {Q : List Piece} (h : PReads p Q)
    (G : Key → List Nat → V)
    (hmb : ∀ q ∈ Q, ∃ m : BlockModel V q.env,
      ∀ n, (q.env.find? n).isSome → ∀ ls, m.M n ls = G (q.res n) ls) :
    ∃ m : BlockModel V p.env, m.M = fun n ls => G (p.res n) ls := by
  let M : Name → List Nat → V := fun n ls => G (p.res n) ls
  let mb : ∀ q, q ∈ Q → BlockModel V q.env := fun q hq => Classical.choose (hmb q hq)
  have hmb' : ∀ q (hq : q ∈ Q) n, (q.env.find? n).isSome →
      ∀ ls, (mb q hq).M n ls = G (q.res n) ls :=
    fun q hq => Classical.choose_spec (hmb q hq)
  have hagC : ∀ q (hq : q ∈ Q), AgreeOn (readsAlikeP p q) (mb q hq).M M := by
    intro q hq d hd ls
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨h1, -, h3⟩ := find?_readsAlikeP he
    rw [hmb' q hq d (by rw [h1]; rfl) ls]
    simp only [M, h3]
  have hagn : ∀ q (hq : q ∈ Q) c, q.res c = p.res c → (q.env.find? c).isSome →
      ∀ ls, (mb q hq).M c ls = M c ls := by
    intro q hq c hres hs ls
    rw [hmb' q hq c hs ls]
    simp only [M, hres]
  refine ⟨{ M := M, type_ok := ?_, unfold := ?_, rec_rules := ?_,
            rec_rules_nested := ?_, ind_fib := ?_, rec_rules_slot := ?_, rec_rules_k := ?_,
            blocks := ?_ }, rfl⟩
  · intro c ci hf φ ρ ls hlen
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have hc := consts_agree hsc.1 (hagC q hq) ls
    have := (mb q hq).type_ok c ci' hf' φ ρ ls (by rw [hle.lparams_eq]; exact hlen)
    rw [hle.lparams_eq, hle.type_eq] at this
    rwa [WellDenoted_consts hc, interp_consts hc, hagn q hq c hres hqs] at this
  · intro c ci v hf hv φ ρ ls hlen
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have hne : ci.kind ≠ .assumed := by
      intro hk; simp [ConstInfo.value?, hk, ConstKind.value?] at hv
    have heq := hle.eq_of_ne hne
    subst heq
    have hc := consts_agree (hsc.2.1 v hv) (hagC q hq) ls
    have := (mb q hq).unfold c ci' v hf' hv φ ρ ls hlen
    rwa [WellDenoted_consts hc, interp_consts hc, hagn q hq c hres hqs] at this
  · intro c ci nP nM nMin nI rules hf hkind rl hrl hinst cij hcij
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, cij₀, hC, hE, hcty⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((mb q hq).rec_rules c ci' nP nM nMin nI rules hf' hkind rl hrl hinst cij₀
      (find?_readsAlikeP hC).1).congr (consts_agree hsc.1 (hagC q hq))
      (consts_agree hcty (hagC q hq)) (consts_agree hrhs (hagC q hq)) (hagn q hq c hres hqs)
      (hagC q hq rl.ctor (by rw [hC]; rfl))
  · intro c ci nP nM nMin nI rules hf hkind rl hrl lvs pinst hinst cij I nPc nf hcij hcijk
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, cij₀, hC, hE, hcty⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((mb q hq).rec_rules_nested c ci' nP nM nMin nI rules hf' hkind rl hrl lvs pinst hinst cij₀
      I nPc nf (find?_readsAlikeP hC).1 hcijk).congr (consts_agree hsc.1 (hagC q hq))
      (consts_agree hcty (hagC q hq)) (consts_agree hrhs (hagC q hq)) (hagn q hq c hres hqs)
      (hagC q hq rl.ctor (by rw [hC]; rfl))
  · intro I ci nP nI cs S hf hk
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le I ci hf
    have hqs : (q.env.find? I).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hk]; exact nofun)
    subst heq
    exact ((mb q hq).ind_fib I ci' nP nI cs S hf' hk).congr (consts_agree hsc.1 (hagC q hq))
      (hagn q hq I hres hqs)
  · intro c ci nP nM nMin nI rules hf hkind rl hrl cij hcij
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨-, cij₀, hC, hE, -⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((mb q hq).rec_rules_slot c ci' nP nM nMin nI rules hf' hkind rl hrl cij₀
      (find?_readsAlikeP hC).1).congr (consts_agree hsc.1 (hagC q hq)) (hagn q hq c hres hqs)
      (hagC q hq rl.ctor (by rw [hC]; rfl))
  · intro c ci nP nM nMin nI rules hf hkind rl hrl hk
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hqs : (q.env.find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, -⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    exact ((mb q hq).rec_rules_k c ci' nP nM nMin nI rules hf' hkind rl hrl hk).congr
      (consts_agree hsc.1 (hagC q hq)) (consts_agree hrhs (hagC q hq)) (hagn q hq c hres hqs)
  · intro K ci nP nI cs S hf hk hpl
    obtain ⟨q, hq, hres, ci', hf', hle, hsc⟩ := h.le K ci hf
    have hqs : (q.env.find? K).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hk]; exact nofun)
    subst heq
    obtain ⟨-, hnc, -, -, hfam, hcs, hdoms⟩ := (mb q hq).blocks K ci' nP nI cs S hf' hk hpl
    obtain ⟨hSC, hnameC, hctorsC⟩ := hsc.2.2.2 nP nI cs S hk hpl
    obtain ⟨hfindc, hctorsc⟩ := h.blocks K ci' nP nI cs S hf hk hpl
    have hAg : AgreeOn (readsAlikeP p q) (mb q hq).M M :=
      hagC q hq
    have hKs := S.contScoped_of_plain (env := readsAlikeP p q) hpl
    refine ⟨hSC.mono fun d hd => ?_, hnc, hfindc, hctorsc, fun ls => ?_, fun j c hc ls => ?_,
      fun ls ps hp => ?_⟩
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
      exact (find?_readsAlikeP he).2.1
    · rw [← hagC q hq S.name hnameC ls, hfam ls, S.famSet_congr hSC hKs hAg ls]
    · rw [← hagC q hq c.name (hctorsC j c hc) ls, hcs j c hc ls,
        S.ctorSet_congr hSC hKs hAg ls j (List.mem_of_getElem? hc)]
    · exact (S.DomsBounded_congr hSC hKs hAg ls ps).mp
        (hdoms ls ps ((S.FitsVals_params_congr hSC hAg ls ps).mpr hp))

omit [IndLib V] [LevelOracle] in
/-- **A piece that reads from a list is closed.** -/
theorem PReads.scoped {p : Piece} {Q : List Piece} (h : PReads p Q) : Env.Scoped p.env := by
  have hsub : ∀ q d, ((readsAlikeP p q).find? d).isSome → (p.env.find? d).isSome :=
    fun q d hd => by
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
      exact (find?_readsAlikeP he).2.1
  intro c ci hf
  obtain ⟨q, -, -, -, -, -, hsc⟩ := h.le c ci hf
  refine ⟨hsc.1.mono (hsub _), fun v hv => (hsc.2.1 v hv).mono (hsub _),
    fun nP nM nMin nI rules hk rl hrl => ?_⟩
  · obtain ⟨hrhs, cij, -, hE, -⟩ := hsc.2.2.1 nP nM nMin nI rules hk rl hrl
    exact ⟨hrhs.mono (hsub _), by rw [hE]; rfl⟩

end Fragment
