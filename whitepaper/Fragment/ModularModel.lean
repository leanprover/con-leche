module

public import Fragment.Modular
public import Fragment.InstallThm
public import Fragment.ModularSemantics

@[expose] public section

/-!
# Modular checking: the fragment's modules and their local checks

A development is a graph of modules (`Module`).  Each module checks
its own declarations against its **context**, an environment it
assembles from the **views** its imports present, and says for every
context name the module it reads it from (`src`).  Two modules may hold
copies of one name; what the theory asks is that the copies a module
reads **agree** (`Agrees`): get one set in the models.  There is no
global environment and no renaming: every module uses its own names.

This file holds what the fragment's instance of the modular interface
(`ModularInstance.lean`) is made of:

* **proofs are the point** (`ProofsPt`): in the models the argument
  builds, a definition or an assumption whose type reads as a truth
  value has the point as its set; a definition's set is its value's,
  which lies in its type (`defVal_eq_pt`);
* **the step**: the module's declarations are installed on the
  context's model (`Checks.blockModel`, the theorems of
  `Install.lean`), keeping every set of the context and proofs the point;
* **assembly** (`Assembled C E`): every constant of `C` is, at the
  same name, a constant of a member of the family `E`, or an
  assumption of its type, and lies within the part of that member that
  `C` stores too (`common`);
* **amalgamation** (`Assembled.model`, `Assembled.proofsPt`): models of
  the family that agree on every name of `C` two members store give a
  model of `C` — the laws of each constant are those of the member's
  constant it refines, at names `C` and the member both store;
* **a closed part of a context** (`Assembled.restrict`, `FromViews.restrict`): a context need not be
  everything a module loads; any part closed under what its constants' laws read is assembled from
  the same views, which is why a module may be checked over the reach of its own declarations;
* **proofs among copies** (`ProofIn`): the checker's inference, over a
  part of the context, that a copy's type is a proposition; every model
  that keeps proofs the point gives such a copy the point
  (`ProofIn.eq_dflt`), which is how two proofs of one statement agree;
* **the local checks**, split by who runs them: per home
  (`InterfaceOk`: each view refines the module's own environment), per
  importer (`ImportOk`: the context is assembled from the imports'
  views, and every copy of a context name in a view agrees with the
  one the module reads, `ReadsOk`), and the module's own (`LocalOk`:
  acceptance).

A context entry stays in the module's own environment unchanged
(`Checks.find?_context`): a checked declaration stores only fresh
names.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

/-! ## Proofs denote the point -/

/-- A proof's set, and the value off the family: the point. -/
def dflt : List Nat → V := fun _ => pt

/-- **A type read as a truth value** under `M`, at every list of levels. -/
def PropType (M : Name → List Nat → V) (ci : ConstInfo) : Prop :=
  ∀ ls, interp M (valOf ci.lparams ls) base ci.type ∈ˢ univ 0

/-- **A statement kind**: a definition or an assumption (a theorem's
statement among them), the kinds two copies of one statement may
differ in. -/
def ConstInfo.IsStmt (ci : ConstInfo) : Prop := ci.kind = .assumed ∨ ∃ v, ci.kind = .defn v

/-- **Proofs denote the point**: every constant of a statement kind
whose type reads as a truth value has the point as its set.  The models
the modular argument builds keep it. -/
def ProofsPt (E : Env) (M : Name → List Nat → V) : Prop :=
  ∀ n ci, E.find? n = some ci → ci.IsStmt → PropType M ci → M n = dflt

/-- **A type inferred to be a proposition reads as a truth value** in
every model. -/
theorem PropType.of_infer {E : Env} (m : EnvModel V E) {ci : ConstInfo} {s : Expr} {u : Level}
    (hT : Infer E [] ci.type s) (hr : Red E [] s (.sort u)) (hu : LevelOracle.eq u .zero = true) :
    PropType m.M ci := by
  intro ls
  obtain ⟨-, hU⟩ := Infer.mem_typeU_of (m := m) (φ := valOf ci.lparams ls)
    (infer_sound hT) (red_sound hr) (Sat_nil _ _ base)
  rwa [eval_eq_of_oracle hu, Level.eval, mem_typeU_zero] at hU

omit [LevelOracle] in
/-- Two assignments agreeing on the constants of a type in scope read
it alike. -/
theorem PropType.congr {D : Env} {M M' : Name → List Nat → V} {ci : ConstInfo}
    (hs : Expr.Scoped D ci.lparams 0 ci.type) (h : AgreeOn D M M') :
    PropType M ci ↔ PropType M' ci := by
  have hc : ∀ c ∈ ci.type.consts, ∀ ls, M c ls = M' c ls := fun c hc => h c (hs.2.1 c hc)
  unfold PropType
  constructor
  · intro hp ls; rw [← interp_consts hc]; exact hp ls
  · intro hp ls; rw [interp_consts hc]; exact hp ls

/-- **A definition's set is the point** where its type reads as a truth
value: the value lies in the type. -/
theorem defVal_eq_pt {env : Env} (m : EnvModel V env) {c : Name} {ci : ConstInfo} {v : Expr}
    (hok : DefOk env c ci) (hk : ci.kind = .defn v) (hp : PropType m.M ci)
    (ls : List Nat) : defVal m.M ci v ls = pt := by
  obtain ⟨-, ⟨s₀, u₀, hT, hsu⟩, ⟨v', T, hk', hv, hd, -⟩, -⟩ := hok
  rw [hk] at hk'; cases hk'
  let φ := valOf ci.lparams ls
  have hvsem := infer_sound (m := m) (φ := φ) hv base (Sat_nil _ _ _)
  obtain ⟨hTw, hTmem⟩ := Infer.mem_typeU_of (m := m) (φ := φ)
    (infer_sound hT) (red_sound hsu) (Sat_nil _ _ base)
  have heq := defeq_sound (m := m) (φ := φ) hd base (Sat_nil _ _ _)
    hvsem.2.1 hTw hvsem.2.2.1.ne_pt (IsTy_of_mem_typeU hTmem).ne_pt
  have hmem := hvsem.2.2.2
  rw [heq] at hmem
  exact eq_pt_of_mem_univ_zero (hp ls) hmem

/-! ## Installing a checked list -/

omit [IndLib V] [LevelOracle] in
theorem isSome_find?_apply {E : Env} {n : Name} (h : (E.find? n).isSome) (d : Decl) :
    ((d.apply E).find? n).isSome := by
  rw [Decl.apply_eq]
  cases hl : d.stores.lookup n with
  | some e => simp [Env.find?, lookup_append_of_some hl]
  | none => simp only [Env.find?, lookup_append_of_none hl]; exact h

omit [IndLib V] [LevelOracle] in
theorem isSome_find?_applyAll {E : Env} {n : Name} (h : (E.find? n).isSome) :
    ∀ ds : List Decl, ((applyAll ds E).find? n).isSome
  | [] => h
  | d :: ds => isSome_find?_applyAll (isSome_find?_apply h d) ds

omit [IndLib V] in
/-- **A checked declaration stores only fresh names.** -/
theorem Decl.Ok.fresh {E : Env} {d : Decl} (h : d.Ok E) : ∀ n ∈ d.names, E.find? n = none := by
  cases d with
  | defn c ci =>
    intro n hn
    simp only [Decl.names, List.mem_singleton] at hn
    subst hn; exact h.1
  | thm c ci v =>
    intro n hn
    simp only [Decl.names, List.mem_singleton] at hn
    subst hn; exact h.2.1.1
  | ind S =>
    simp only [Decl.Ok, IndOk] at h
    simp only [Decl.names, IndSpec.names]
    cases hn : S.nest with
    | none => rw [hn] at h; exact h.fresh
    | some N => rw [hn] at h; exact h.fresh

omit [IndLib V] in
/-- **A context entry stays in the own environment**: a checked list
stores only fresh names, so it keeps every entry of the environment it
is checked against. -/
theorem Checks.find?_context {E : Env} {ds : List Decl} (hc : Checks E ds) {n : Name}
    {ci : ConstInfo} (h : E.find? n = some ci) : (applyAll ds E).find? n = some ci := by
  induction hc with
  | nil => exact h
  | @cons E d ds hd _ ih =>
    apply ih
    rw [Decl.apply_eq]
    cases hl : d.stores.lookup n with
    | none => simpa only [Env.find?, lookup_append_of_none hl] using h
    | some e =>
      have hm : n ∈ d.names := (Decl.mem_names_iff d n).mpr ⟨e, key_of_lookup hl⟩
      rw [hd.fresh n hm] at h; cases h

omit [IndLib V] [LevelOracle] in
/-- A block stores no constant of a statement kind. -/
theorem ind_stores_not_stmt {S : IndSpec} {n : Name} {e : ConstInfo}
    (h : (Decl.ind S).stores.lookup n = some e) : ¬ e.IsStmt := by
  have hm := key_of_lookup h
  have hC : (S.envCtors Env.empty).consts =
      (S.ctors.map fun c => (c.name, S.ctorInfo c)).reverse ++ [(S.name, S.indInfo)] :=
    IndSpec.foldl_add_empty S S.ctors [(S.name, S.indInfo)]
  simp only [Decl.stores, Decl.apply, IndSpec.install, IndSpec.installN] at hm
  intro hs
  cases hn : S.nest <;> simp only [hn, Env.add, hC] at hm <;>
    simp only [List.mem_cons, List.mem_append, List.mem_reverse, List.mem_map, Prod.mk.injEq] at hm <;>
    rcases hs with hs | ⟨v, hs⟩ <;>
    grind [IndSpec.indInfo, IndSpec.ctorInfo, IndSpec.recInfo, IndSpec.recInfoN, IndSpec.rec1Info]

/-- **Installing a checked list preserves having a model**: every
stored constant keeps its set, and proofs stay the point. -/
theorem Checks.blockModel {E : Env} {ds : List Decl} (hc : Checks E ds) :
    Env.Scoped E → ∀ m : BlockModel V E, ProofsPt E m.M →
      ∃ m' : BlockModel V (applyAll ds E),
        (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
        ProofsPt (applyAll ds E) m'.M := by
  induction hc with
  | nil => intro _ m hp; exact ⟨m, fun _ _ _ => rfl, hp⟩
  | @cons E d ds hd _ ih =>
    intro hs m hp
    -- an old name keeps its set, and its type its reading
    have hold : ∀ m₁ : BlockModel V (d.apply E),
        (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) →
        ∀ n ci, d.stores.lookup n = none → (d.apply E).find? n = some ci → ci.IsStmt →
          PropType m₁.M ci → m₁.M n = dflt := by
      intro m₁ hag n ci hl hf hk hpt
      have hE : E.find? n = some ci := by
        rw [Decl.apply_eq] at hf
        simpa only [Env.find?, lookup_append_of_none hl] using hf
      rw [show m₁.M n = m.M n from funext (hag n (by rw [hE]; rfl))]
      exact hp n ci hE hk ((PropType.congr (hs n ci hE).1 fun c hc ls => hag c hc ls).1 hpt)
    -- the new name of a definition or a theorem: its set is its value's
    have hnew : ∀ (m₁ : BlockModel V (d.apply E)) (c : Name) (ci : ConstInfo) (v : Expr),
        (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) →
        d.stores = [(c, ci)] → DefOk E c { ci with kind := .defn v } →
        (∀ ls, m₁.M c ls = defVal m.M { ci with kind := .defn v } v ls) → ProofsPt (d.apply E) m₁.M := by
      intro m₁ c ci v hag hst hok hval n ci' hf hk hpt
      cases hl : d.stores.lookup n with
      | none => exact hold m₁ hag n ci' hl hf hk hpt
      | some e =>
        rw [hst] at hl
        simp only [List.lookup] at hl
        split at hl
        · rename_i hnc
          cases hl
          have hnc' : n = c := beq_iff_eq.mp hnc
          subst hnc'
          have he : ci' = ci := by
            rw [Decl.apply_eq, hst] at hf
            simpa [Env.find?, List.lookup] using hf.symm
          subst he
          have hsc := hok.type_scoped
          have hpt' : PropType m.M { ci' with kind := .defn v } :=
            (PropType.congr (ci := { ci' with kind := .defn v }) hsc
              fun c hc ls => hag c hc ls).1 hpt
          funext ls
          rw [hval ls]
          exact defVal_eq_pt m.toEnvModel hok rfl hpt' ls
        · cases hl
    obtain ⟨m₁, hag₁, hp₁⟩ : ∃ m₁ : BlockModel V (d.apply E),
        (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) ∧
        ProofsPt (d.apply E) m₁.M := by
      cases d with
      | defn c ci =>
        obtain ⟨m₁, hag, hval⟩ := install_def' hs m hd
        obtain ⟨v, -, hk, -⟩ := hd.2.2.1
        have hci : { ci with kind := .defn v } = ci := by
          obtain ⟨l, t, k⟩ := ci; simp only at hk; rw [hk]
        refine ⟨m₁, hag, hnew m₁ c ci v hag rfl (hci ▸ hd) fun ls => ?_⟩
        rw [hval v hk ls, hci]
      | thm c ci v =>
        obtain ⟨m₁, hag, hval⟩ := install_thm hs m hd
        exact ⟨m₁, hag, hnew m₁ c ci v hag rfl hd.2.1 hval⟩
      | ind S =>
        obtain ⟨m₁, hag⟩ := install_ind_any hs m hd
        refine ⟨m₁, hag, fun n ci hf hk hpt => ?_⟩
        cases hl : (Decl.ind S).stores.lookup n with
        | none => exact hold m₁ hag n ci hl hf hk hpt
        | some e =>
          have he : ci = e := by
            rw [Decl.apply_eq] at hf
            have := lookup_append_of_some (cs := E.consts) hl
            exact Option.some.inj (hf.symm.trans this)
          subst he
          exact absurd hk (ind_stores_not_stmt hl)
    have hs₁ : Env.Scoped (d.apply E) := by
      cases d with
      | defn c ci => exact hs.add_def hd
      | thm c ci v => exact hs.add_thm hd
      | ind S => exact hs.install_any hd
    obtain ⟨m', hag', hp'⟩ := ih hs₁ m₁ hp₁
    exact ⟨m', fun n hn ls => (hag' n (isSome_find?_apply hn d) ls).trans (hag₁ n hn ls), hp'⟩

/-! ## Assembling an environment from others -/

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

open Classical in
/-- **The part of `E` that `C` stores too**: `E`'s constants at the
names `C` stores. -/
noncomputable def common (C E : Env) : Env :=
  ⟨E.consts.filter fun x => decide ((C.find? x.1).isSome = true)⟩

omit [IndLib V] [LevelOracle] in
open Classical in
theorem find?_common {C E : Env} {n : Name} {ci : ConstInfo}
    (h : (common C E).find? n = some ci) :
    E.find? n = some ci ∧ (C.find? n).isSome := by
  unfold common at h
  rw [find?_filter (p := fun n => decide ((C.find? n).isSome = true))] at h
  split at h
  · rename_i hp
    simp only [decide_eq_true_eq] at hp
    exact ⟨h, hp⟩
  · cases h

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

/-- **`C` is assembled from the family `E`**: every constant of `C` is,
at the same name, the constant of a member or an assumption of its
type, and lies within the part of that member that `C` stores too; a
type former stored as such comes with its constructors.  An assumption
stands for statements only: every member's copy of its name is a
definition or an assumption (`ConstInfo.IsStmt`). -/
structure Assembled (C : Env) {ι : Type} (E : ι → Env) : Prop where
  le : ∀ n ci, C.find? n = some ci → ∃ i,
    ∃ ci', (E i).find? n = some ci' ∧ ci.Le ci' ∧ EntryScoped (common C (E i)) C ci
  blocks : ∀ n ci nP nI cs S, C.find? n = some ci → ci.kind = .induct nP nI cs S →
    S.nest = none → C.find? S.name = some S.indInfo ∧
      ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → C.find? c.name = some (S.ctorInfo c)
  stmt : ∀ n ci, C.find? n = some ci → ci.kind = .assumed → ∀ i ci', (E i).find? n = some ci' →
    ci'.IsStmt

/-- **Refinement**: `Γ` assembled from `E` alone — every constant of
`Γ` is `E`'s or an assumption of its type. -/
def Refines (Γ E : Env) : Prop := Assembled Γ fun _ : Unit => E

open Classical in
/-- **The amalgamated assignment**: at a name some member stores, that
member's set. -/
noncomputable def glueM {ι : Type} {E : ι → Env}
    (m : (i : ι) → BlockModel V (E i)) : Name → List Nat → V :=
  fun n => if h : ∃ i, ((E i).find? n).isSome then (m (Classical.choose h)).M n else dflt

omit [LevelOracle] in
/-- **Amalgamation**: models of the family that agree on every name of
`C` two members store give a model of `C`, with each member's sets. -/
theorem Assembled.model {C : Env} {ι : Type} {E : ι → Env}
    (h : Assembled C E) (m : (i : ι) → BlockModel V (E i))
    (hcomp : ∀ n i i', (C.find? n).isSome →
      ((E i).find? n).isSome → ((E i').find? n).isSome → (m i).M n = (m i').M n) :
    ∃ mC : BlockModel V C, ∀ n i, (C.find? n).isSome → ((E i).find? n).isSome →
      mC.M n = (m i).M n := by
  let M : Name → List Nat → V := glueM m
  have hagn : ∀ q c, ((E q).find? c).isSome → (C.find? c).isSome →
      ∀ ls, (m q).M c ls = M c ls := by
    intro q c hE hC ls
    have hx : ∃ i, ((E i).find? c).isSome := ⟨q, hE⟩
    simp only [M, glueM, dite_eq_left hx]
    rw [hcomp c q _ hC hE (Classical.choose_spec hx)]
  have hagC : ∀ q, AgreeOn (common C (E q)) (m q).M M := by
    intro q d hd ls
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨h1, h2⟩ := find?_common he
    exact hagn q d (by rw [h1]; rfl) h2 ls
  refine ⟨{ M := M, type_ok := ?_, unfold := ?_, rec_rules := ?_,
            rec_rules_nested := ?_, ind_fib := ?_, rec_rules_slot := ?_, rec_rules_k := ?_,
            blocks := ?_ }, fun n q hn hE => funext fun ls => (hagn q n hE hn ls).symm⟩
  · intro c ci hf φ ρ ls hlen
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have hc := consts_agree hsc.1 (hagC q) ls
    have := (m q).type_ok c ci' hf' φ ρ ls (by rw [hle.lparams_eq]; exact hlen)
    rw [hle.lparams_eq, hle.type_eq] at this
    rwa [WellDenoted_consts hc, interp_consts hc, hagn q c hqs hCs] at this
  · intro c ci v hf hv φ ρ ls hlen
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have hne : ci.kind ≠ .assumed := by
      intro hk; simp [ConstInfo.value?, hk, ConstKind.value?] at hv
    have heq := hle.eq_of_ne hne
    subst heq
    have hc := consts_agree (hsc.2.1 v hv) (hagC q) ls
    have := (m q).unfold c ci' v hf' hv φ ρ ls hlen
    rwa [WellDenoted_consts hc, interp_consts hc, hagn q c hqs hCs] at this
  · intro c ci nP nM nMin nI rules hf hkind rl hrl hinst cij hcij
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, cij₀, hC, hE, hcty⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((m q).rec_rules c ci' nP nM nMin nI rules hf' hkind rl hrl hinst cij₀
      (find?_common hC).1).congr (consts_agree hsc.1 (hagC q))
      (consts_agree hcty (hagC q)) (consts_agree hrhs (hagC q)) (hagn q c hqs hCs)
      (hagC q rl.ctor (by rw [hC]; rfl))
  · intro c ci nP nM nMin nI rules hf hkind rl hrl lvs pinst hinst cij I nPc nf hcij hcijk
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, cij₀, hC, hE, hcty⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((m q).rec_rules_nested c ci' nP nM nMin nI rules hf' hkind rl hrl lvs pinst hinst cij₀
      I nPc nf (find?_common hC).1 hcijk).congr (consts_agree hsc.1 (hagC q))
      (consts_agree hcty (hagC q)) (consts_agree hrhs (hagC q)) (hagn q c hqs hCs)
      (hagC q rl.ctor (by rw [hC]; rfl))
  · intro I ci nP nI cs S hf hk
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le I ci hf
    have hCs : (C.find? I).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? I).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hk]; exact nofun)
    subst heq
    exact ((m q).ind_fib I ci' nP nI cs S hf' hk).congr (consts_agree hsc.1 (hagC q))
      (hagn q I hqs hCs)
  · intro c ci nP nM nMin nI rules hf hkind rl hrl cij hcij
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨-, cij₀, hC, hE, -⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    have h0 : cij₀ = cij := Option.some.inj (hE.symm.trans hcij)
    subst h0
    exact ((m q).rec_rules_slot c ci' nP nM nMin nI rules hf' hkind rl hrl cij₀
      (find?_common hC).1).congr (consts_agree hsc.1 (hagC q)) (hagn q c hqs hCs)
      (hagC q rl.ctor (by rw [hC]; rfl))
  · intro c ci nP nM nMin nI rules hf hkind rl hrl hk
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le c ci hf
    have hCs : (C.find? c).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? c).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hkind]; exact nofun)
    subst heq
    obtain ⟨hrhs, -⟩ := hsc.2.2.1 nP nM nMin nI rules hkind rl hrl
    exact ((m q).rec_rules_k c ci' nP nM nMin nI rules hf' hkind rl hrl hk).congr
      (consts_agree hsc.1 (hagC q)) (consts_agree hrhs (hagC q)) (hagn q c hqs hCs)
  · intro K ci nP nI cs S hf hk hpl
    obtain ⟨q, ci', hf', hle, hsc⟩ := h.le K ci hf
    have hCs : (C.find? K).isSome := by rw [hf]; rfl
    have hqs : ((E q).find? K).isSome := by rw [hf']; rfl
    have heq := hle.eq_of_ne (by rw [hk]; exact nofun)
    subst heq
    obtain ⟨-, hnc, -, -, hfam, hcs, hdoms⟩ := (m q).blocks K ci' nP nI cs S hf' hk hpl
    obtain ⟨hSC, hnameC, hctorsC⟩ := hsc.2.2.2 nP nI cs S hk hpl
    obtain ⟨hfindc, hctorsc⟩ := h.blocks K ci' nP nI cs S hf hk hpl
    have hAg : AgreeOn (common C (E q)) (m q).M M :=
      hagC q
    have hKs := S.contScoped_of_plain (env := common C (E q)) hpl
    refine ⟨hSC.mono fun d hd => ?_, hnc, hfindc, hctorsc, fun ls => ?_, fun j c hc ls => ?_,
      fun ls ps hp => ?_⟩
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
      exact (find?_common he).2
    · rw [← hagC q S.name hnameC ls, hfam ls, S.famSet_congr hSC hKs hAg ls]
    · rw [← hagC q c.name (hctorsC j c hc) ls, hcs j c hc ls,
        S.ctorSet_congr hSC hKs hAg ls j (List.mem_of_getElem? hc)]
    · exact (S.DomsBounded_congr hSC hKs hAg ls ps).mp
        (hdoms ls ps ((S.FitsVals_params_congr hSC hAg ls ps).mpr hp))


omit [LevelOracle] in
/-- **The amalgam keeps proofs the point**: a constant of a statement kind
of `C` is one of a member's, of the same type, read alike. -/
theorem Assembled.proofsPt {C : Env} {ι : Type} {E : ι → Env} (h : Assembled C E)
    (m : (i : ι) → BlockModel V (E i)) (hp : ∀ i, ProofsPt (E i) (m i).M) (MC : Name → List Nat → V)
    (hmC : ∀ n i, (C.find? n).isSome → ((E i).find? n).isSome → MC n = (m i).M n) :
    ProofsPt C MC := by
  intro n ci hf hk hpt
  obtain ⟨q, ci', hf', hle, hsc⟩ := h.le n ci hf
  have hk' : ci'.IsStmt := by
    rcases hle with rfl | ⟨ha, -⟩
    · exact hk
    · exact h.stmt n ci hf ha q ci' hf'
  have hag : AgreeOn (common C (E q)) MC (m q).M := by
    intro c hc ls
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨h1, h2⟩ := find?_common he
    rw [hmC c q h2 (by rw [h1]; rfl)]
  have hpt' : PropType (m q).M ci' := by
    have := (PropType.congr hsc.1 hag).1 hpt
    unfold PropType at this ⊢
    rwa [hle.lparams_eq, hle.type_eq]
  rw [hmC n q (by rw [hf]; rfl) (by rw [hf']; rfl)]
  exact hp q n ci' hf' hk' hpt'

/-! ## A closed part of an assembled context

The reach's lemma: a module may be checked over any part of its context that is closed under what
its constants' laws read.  Nothing asks a context to be everything a module loads. -/

omit [IndLib V] [LevelOracle] in
open Classical in
theorem find?_common_eq {C E : Env} {n : Name} :
    (common C E).find? n = if (C.find? n).isSome then E.find? n else none := by
  unfold common
  rw [find?_filter (p := fun n => decide ((C.find? n).isSome = true))]
  by_cases h : (C.find? n).isSome <;> simp [h]

omit [IndLib V] [LevelOracle] in
theorem Expr.Scoped.inter {A B D : Env} {ps : List Name} {k : Nat} {e : Expr}
    (hA : Expr.Scoped A ps k e) (hB : Expr.Scoped B ps k e)
    (h : ∀ d, (A.find? d).isSome → (B.find? d).isSome → (D.find? d).isSome) :
    Expr.Scoped D ps k e :=
  ⟨hA.1, fun d hd => h d (hA.2.1 d hd) (hB.2.1 d hd), hA.2.2⟩

omit [IndLib V] [LevelOracle] in
theorem IndSpec.fieldScoped_inter (S : IndSpec) {A B D : Env} {k : Nat} {f : Field}
    (hA : S.fieldScoped A k f) (hB : S.fieldScoped B k f)
    (h : ∀ d, (A.find? d).isSome → (B.find? d).isSome → (D.find? d).isSome) :
    S.fieldScoped D k f := by
  cases f with
  | ordinary T => exact Expr.Scoped.inter hA hB h
  | reflexive tele es =>
    exact ⟨fun t T hT => (hA.1 t T hT).inter (hB.1 t T hT) h, hA.2.1,
      fun e he => (hA.2.2 e he).inter (hB.2.2 e he) h⟩
  | container => exact hA

omit [IndLib V] [LevelOracle] in
/-- A block without a class in scope of two environments is in scope of any environment storing
what both store. -/
theorem IndSpec.Scoped_inter (S : IndSpec) (hpl : S.nest = none) {A B D : Env}
    (hA : S.Scoped A) (hB : S.Scoped B)
    (h : ∀ d, (A.find? d).isSome → (B.find? d).isSome → (D.find? d).isSome) :
    S.Scoped D := by
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := hA
  obtain ⟨b1, b2, -, b4, -, -, -⟩ := hB
  refine ⟨fun i T hT => (a1 i T hT).inter (b1 i T hT) h,
    fun t T hT => (a2 t T hT).inter (b2 t T hT) h, a3,
    fun c hc => ⟨fun i f hf => S.fieldScoped_inter ((a4 c hc).1 i f hf) ((b4 c hc).1 i f hf) h,
      (a4 c hc).2.1, (a4 c hc).2.2.1,
      fun e he => ((a4 c hc).2.2.2 e he).inter ((b4 c hc).2.2.2 e he) h⟩,
    a5, a6, fun N hN => ?_⟩
  rw [hpl] at hN
  cases hN

omit [IndLib V] [LevelOracle] in
/-- **A closed part of an assembled environment is assembled from the same family**: `C'` stores
some of `C`'s constants, each as `C` does, and what their laws read lies in `C'`
(`EntryScoped C' C'`). -/
theorem Assembled.restrict {C C' : Env} {ι : Type} {E : ι → Env} (h : Assembled C E)
    (hsub : ∀ n ci, C'.find? n = some ci → C.find? n = some ci)
    (hcl : ∀ n ci, C'.find? n = some ci → EntryScoped C' C' ci) :
    Assembled C' E := by
  constructor
  · intro n ci hf
    obtain ⟨i, ci', hE, hle, hsc⟩ := h.le n ci (hsub n ci hf)
    have hD : ∀ d, ((common C (E i)).find? d).isSome → (C'.find? d).isSome →
        ((common C' (E i)).find? d).isSome := by
      intro d h1 h2
      rw [find?_common_eq] at h1 ⊢
      simp only [h2, ↓reduceIte]
      split at h1
      · exact h1
      · exact absurd h1 (by simp)
    obtain ⟨c1, c2, c3, c4⟩ := hcl n ci hf
    refine ⟨i, ci', hE, hle, hsc.1.inter c1 hD, fun v hv => (hsc.2.1 v hv).inter (c2 v hv) hD,
      fun nP nM nMin nI rules hk rl hrl => ?_, fun nP nI cs S hk hpl => ?_⟩
    · obtain ⟨hrhs, cij, hC1, hC2, hty⟩ := hsc.2.2.1 nP nM nMin nI rules hk rl hrl
      obtain ⟨hrhs', cij', hC1', -, hty'⟩ := c3 nP nM nMin nI rules hk rl hrl
      have heq : cij' = cij := Option.some.inj ((hsub _ _ hC1').symm.trans hC2)
      subst heq
      refine ⟨hrhs.inter hrhs' hD, cij', ?_, hC1', hty.inter hty' hD⟩
      rw [find?_common_eq]
      simp only [hC1', Option.isSome_some, ↓reduceIte]
      exact (find?_common hC1).1
    · obtain ⟨hS, hname, hctors⟩ := hsc.2.2.2 nP nI cs S hk hpl
      obtain ⟨hS', hname', hctors'⟩ := c4 nP nI cs S hk hpl
      exact ⟨S.Scoped_inter hpl hS hS' hD, hD _ hname hname',
        fun j c hc => hD _ (hctors j c hc) (hctors' j c hc)⟩
  · intro n ci nP nI cs S hf hk hpl
    obtain ⟨hname, hctors⟩ := h.blocks n ci nP nI cs S (hsub n ci hf) hk hpl
    obtain ⟨-, hname', hctors'⟩ := (hcl n ci hf).2.2.2 nP nI cs S hk hpl
    have hstore : ∀ d x, (C'.find? d).isSome → C.find? d = some x → C'.find? d = some x := by
      intro d x hs hx
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
      rw [hy, ← hx, hsub d y hy]
    exact ⟨hstore _ _ hname' hname, fun j c hc => hstore _ _ (hctors' j c hc) (hctors j c hc)⟩
  · intro n ci hf hk i ci' hf'
    exact h.stmt n ci (hsub n ci hf) hk i ci' hf'

omit [IndLib V] [LevelOracle] in
/-- **An assembled environment is closed.** -/
theorem Assembled.scoped {C : Env} {ι : Type} {E : ι → Env}
    (h : Assembled C E) : Env.Scoped C := by
  have hsub : ∀ q d, ((common C (E q)).find? d).isSome → (C.find? d).isSome :=
    fun q d hd => by
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
      exact (find?_common he).2
  intro c ci hf
  obtain ⟨q, -, -, -, hsc⟩ := h.le c ci hf
  refine ⟨hsc.1.mono (hsub _), fun v hv => (hsc.2.1 v hv).mono (hsub _),
    fun nP nM nMin nI rules hk rl hrl => ?_⟩
  · obtain ⟨hrhs, cij, -, hE, -⟩ := hsc.2.2.1 nP nM nMin nI rules hk rl hrl
    exact ⟨hrhs.mono (hsub _), by rw [hE]; rfl⟩

/-! ## Proofs among copies -/

/-- **`C` proves `E`'s `n` a proof**: `E` stores `n` as a statement kind,
of a type in scope of `C` and of `E` that the checker infers at `C` to
be a proposition. -/
def ProofIn (C E : Env) (n : Name) : Prop :=
  ∃ ci, E.find? n = some ci ∧ ci.IsStmt ∧ Expr.Scoped C ci.lparams 0 ci.type ∧
    Expr.Scoped E ci.lparams 0 ci.type ∧
    ∃ s u, Infer C [] ci.type s ∧ Red C [] s (.sort u) ∧ LevelOracle.eq u .zero = true

/-- **A proof by `C` is the point** in every model of `E` that keeps
proofs the point and agrees with a model of `C` on the constants both
store. -/
theorem ProofIn.eq_dflt {C E : Env} {n : Name} (h : ProofIn C E n) (mC : EnvModel V C)
    (M : Name → List Nat → V) (hp : ProofsPt E M)
    (hag : ∀ c, (C.find? c).isSome → (E.find? c).isSome → mC.M c = M c) : M n = dflt := by
  obtain ⟨ci, hf, hk, hsC, hsE, s, u, hT, hr, hu⟩ := h
  have hc : ∀ c ∈ ci.type.consts, ∀ ls, mC.M c ls = M c ls := fun c hc ls => by
    rw [hag c (hsC.2.1 c hc) (hsE.2.1 c hc)]
  have hpt : PropType M ci := by
    intro ls
    rw [← interp_consts hc]
    exact PropType.of_infer mC hT hr hu ls
  exact hp n ci hf hk hpt

/-- **`E`'s `n` is a proof by `E'`'s**: `E` stores `n` as a statement
kind of the type of `E'`'s `n`, which `E'` proves a proof itself (the
fragment's theorems), the type in scope of `C` and of `E`. -/
def ProofBy (C E E' : Env) (n : Name) : Prop :=
  ∃ ci ci', E.find? n = some ci ∧ ci.IsStmt ∧ E'.find? n = some ci' ∧
    ci'.lparams = ci.lparams ∧ ci'.type = ci.type ∧ Expr.Scoped C ci.lparams 0 ci.type ∧
    Expr.Scoped E ci.lparams 0 ci.type ∧ ProofIn E' E' n

/-- **A proof by `E'`'s is the point** in every model of `E` that keeps
proofs the point and agrees with a model of `C` on the constants both
store, that model agreeing so with one of `E'`. -/
theorem ProofBy.eq_dflt {C E E' : Env} {n : Name} (h : ProofBy C E E' n)
    (MC : Name → List Nat → V) (M : Name → List Nat → V) (m' : EnvModel V E') (hp : ProofsPt E M)
    (hag : ∀ c, (C.find? c).isSome → (E.find? c).isSome → MC c = M c)
    (hag' : ∀ c, (C.find? c).isSome → (E'.find? c).isSome → MC c = m'.M c) : M n = dflt := by
  obtain ⟨ci, ci', hf, hk, hf', hlp, hty, hsC, hsE, ci'', hf'', -, -, hsE', s, u, hT, hr, hu⟩ := h
  rw [hf'] at hf''
  obtain rfl := Option.some.inj hf''
  -- the theorem's type reads as a truth value in `E'`'s model, so in `E`'s
  have hpt' := PropType.of_infer m' hT hr hu
  have hc : ∀ c ∈ ci.type.consts, ∀ ls, m'.M c ls = M c ls := fun c hc ls => by
    have hc' : c ∈ ci'.type.consts := by rw [hty]; exact hc
    rw [← hag' c (hsC.2.1 c hc) (hsE'.2.1 c hc'), hag c (hsC.2.1 c hc) (hsE.2.1 c hc)]
  refine hp n ci hf hk fun ls => ?_
  rw [← interp_consts hc, ← hty, ← hlp]
  exact hpt' ls

/-! ## Modules and their local checks -/

/-- **A module**: its declarations; its **context**, the environment
they are checked against; the modules it imports; the **views** it
presents to its importers; for each context name, the module it is
read from (`src`); and the order among its context names (`rank`) with,
per name, the part of the context below it (`part`). -/
structure Module where
  decls : List Decl
  context : Env
  imports : List Nat
  views : List Env
  src : Name → Nat
  rank : Name → Nat
  part : Name → Env

/-- **A module's own environment**: its context with its declarations. -/
def Module.own (m : Module) : Env := applyAll m.decls m.context

/-- **The sources module `i` reads**: every view of each of its
imports, with the import. -/
def sources (dev : Nat → Module) (i : Nat) : List (Nat × Env) :=
  (dev i).imports.flatMap fun j => (dev j).views.map fun E => (j, E)

omit [LevelOracle] in
theorem mem_sources {dev : Nat → Module} {i : Nat} {x : Nat × Env} :
    x ∈ sources dev i ↔ x.1 ∈ (dev i).imports ∧ x.2 ∈ (dev x.1).views := by
  obtain ⟨j, E⟩ := x
  simp only [sources, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', E', hE', rfl, rfl⟩; exact ⟨hj', hE'⟩
  · rintro ⟨hj, hE⟩; exact ⟨j, hj, E, hE, rfl, rfl⟩

/-- **Source `x`'s copy of `n` is a proof** for module `i`: proved one
over the part below `n`, or a copy of the statement of a source's copy
that its own environment proves a proof. -/
def ProofSide (dev : Nat → Module) (i : Nat) (n : Name) (x : Nat × Env) : Prop :=
  ProofIn ((dev i).part n) x.2 n ∨ ∃ w ∈ sources dev i, ProofBy ((dev i).part n) x.2 w.2 n

/-- **Source `x`'s copy of `n` agrees with the one module `i` reads**:
`x` is the module `n` is read from; or `x`'s module reads `n` from a
source of an earlier module that `i` reads too (one copy, through two
paths); or it and every copy of the module `n` is read from are proofs. -/
def Agrees (dev : Nat → Module) (i : Nat) (n : Name) (x : Nat × Env) : Prop :=
  x.1 = (dev i).src n ∨
    (((dev x.1).context.find? n).isSome = true ∧ ∃ z ∈ sources dev x.1,
      (z.2.find? n).isSome = true ∧
      ∃ w ∈ sources dev i, w.1 = z.1 ∧ (w.2.find? n).isSome = true ∧ w.1 < x.1) ∨
    ProofSide dev i n x ∧
      ∀ y ∈ sources dev i, y.1 = (dev i).src n → (y.2.find? n).isSome = true →
        ProofSide dev i n y

/-- **How module `i` reads a context name `n`**: from a source of the
module it is read from, with an assembled part below it, every source
storing it agreeing. -/
structure ReadsOk (dev : Nat → Module) (i : Nat) (n : Name) : Prop where
  read : ∃ x ∈ sources dev i, x.1 = (dev i).src n ∧ (x.2.find? n).isSome = true
  part : Assembled ((dev i).part n) (fun x : {x // x ∈ sources dev i} => x.1.2)
  below : ∀ c, (((dev i).part n).find? c).isSome = true →
    ((dev i).context.find? c).isSome = true ∧ (dev i).rank c < (dev i).rank n
  agree : ∀ x ∈ sources dev i, (x.2.find? n).isSome = true → Agrees dev i n x

/-- **Assembled from the imports' views, by agreement**: `E` is
assembled from the views, and module `i` reads each of its names from
them, every copy agreeing. -/
def FromViews (dev : Nat → Module) (i : Nat) (E : Env) : Prop :=
  Assembled E (fun x : {x // x ∈ sources dev i} => x.1.2) ∧
    ∀ n, (E.find? n).isSome = true → ReadsOk dev i n

/-- **The check per home**: every view a module presents refines its
own environment.  It reads the module alone, and runs once, however
many modules import it. -/
def InterfaceOk (dev : Nat → Module) (j : Nat) : Prop := ∀ E ∈ (dev j).views, Refines E (dev j).own

/-- **The check per importer**: the module imports earlier modules, and
its context is assembled from their views, by agreement.  It reads the
module, its imports' views and how they read their own names, never an
import's own environment. -/
structure ImportOk (dev : Nat → Module) (i : Nat) : Prop where
  imports : ∀ j ∈ (dev i).imports, j < i
  reads : FromViews dev i (dev i).context

/-- **The local checks at module `i`**: its interface, its imports, and
its declarations accepted against its context. -/
structure LocalOk (dev : Nat → Module) (i : Nat) : Prop where
  iface : InterfaceOk dev i
  importOk : ImportOk dev i
  checks : Checks (dev i).context (dev i).decls

/-! ## Checking over a closed part of the context -/

/-- **The reach's lemma for a module**: a closed part of a context assembled from the imports'
views, each constant as the context has it, is assembled from them too, by agreement. -/
theorem FromViews.restrict {dev : Nat → Module} {i : Nat} {C C' : Env} (h : FromViews dev i C)
    (hsub : ∀ n ci, C'.find? n = some ci → C.find? n = some ci)
    (hcl : ∀ n ci, C'.find? n = some ci → EntryScoped C' C' ci) :
    FromViews dev i C' := by
  refine ⟨h.1.restrict hsub hcl, fun n hn => h.2 n ?_⟩
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  rw [hsub n ci hci]; rfl

end Fragment
