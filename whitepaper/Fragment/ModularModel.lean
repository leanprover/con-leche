module

public import Fragment.Modular
public import Fragment.InstallThm
public import Fragment.ModularSemantics

@[expose] public section

/-!
# Modular checking: the fragment's modules and their local checks

A development is a graph of modules (`Module`).  Each module checks
its own declarations against its **context**, an environment it
assembles from the **views** its imports present, and records for every
name it uses what declared it (`key`, `Key`, `ModularSemantics.lean`):
the module that declared it, or, for a proof, its statement; two
occurrences are **interchangeable** when these agree.  There is no global
environment and no renaming: every module uses its own names.

This file holds what the fragment's instance of the modular interface
(`ModularInstance.lean`) is made of:

* **assembly** (`Assembled C E`): every constant of `C` is, at the
  same name, a constant of a member of the family `E`, or an
  assumption of its type, and lies within the part of that member that
  `C` stores too (`common`);
* **amalgamation** (`Assembled.model`): models of the family that agree
  on every name of `C` two members store give a model of `C` — the
  laws of each constant are those of the member's constant it refines,
  at names `C` and the member both store;
* **the step**: the module's declarations are installed on the
  context's model (`Checks.blockModel`, the theorems of
  `Install.lean`), every proof its point (`defVal_eq_pt`);
* **the local checks**, split by who runs them: per home
  (`InterfaceOk`: each view refines the module's own environment), per
  importer (`ImportOk`: the context is assembled from the imports'
  views, every copy of a context name in a view interchangeable with
  the module's), and the module's own (`LocalOk`: acceptance, proof
  flags, what declared its own constants).

**A module may instead be validated by comparison** (`Compared`): its
whole own environment is assembled from its imports' views — every
constant is an import's constant, or an assumption of its type (a
hole), with one copy of each name.  A challenge compared with its solution is such a module.
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

/-! ## Assembling an environment from others -/

/-- **A constant's statement**: its level parameters and its type, what
what a proof records. -/
abbrev Stmt := List Name × Expr

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
type former stored as such comes with its constructors.  A type former
may be read as an assumption of its type, and then brings no
constructors. -/
structure Assembled (C : Env) {ι : Type} (E : ι → Env) : Prop where
  le : ∀ n ci, C.find? n = some ci → ∃ i,
    ∃ ci', (E i).find? n = some ci' ∧ ci.Le ci' ∧ EntryScoped (common C (E i)) C ci
  blocks : ∀ n ci nP nI cs S, C.find? n = some ci → ci.kind = .induct nP nI cs S →
    S.nest = none → C.find? S.name = some S.indInfo ∧
      ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → C.find? c.name = some (S.ctorInfo c)

/-- **Refinement**: `Γ` assembled from `E` alone — every constant of
`Γ` is `E`'s or an assumption of its type. -/
def Refines (Γ E : Env) : Prop := Assembled Γ fun _ : Unit => E

/-- A proof's set, and the value off the family: the point. -/
def dflt : List Nat → V := fun _ => pt

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

/-! ## Modules and their local checks -/

/-- **A module**: its declarations; its **context**, the environment
they are checked against; the modules it imports; the **views** it
presents to its importers; what declared each name it uses (`key`: the
module that declared it, or a proof's statement); and which of its own
constants it flags as proofs. -/
structure Module where
  decls : List Decl
  context : Env
  imports : List Nat
  views : List Env
  key : Name → Key Stmt
  proofs : Name → Bool

/-- **A module's own environment**: its context with its declarations. -/
def Module.own (m : Module) : Env := applyAll m.decls m.context

/-- What declared an own constant of module `i`: its statement for a
proof, the module itself otherwise. -/
def Module.ownKey (m : Module) (i : Nat) (n : Name) (ci : ConstInfo) : Key Stmt :=
  if m.proofs n then .proof (ci.lparams, ci.type) else .home i

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

/-- **Assembled from the imports' views, with one copy of each name**:
`E` is assembled from the views, and every copy of a name of `E` in a
view is interchangeable with module `i`'s — declared by the same
module, or a proof of the same statement. -/
def FromViews (dev : Nat → Module) (i : Nat) (E : Env) : Prop :=
  Assembled E (fun x : {x // x ∈ sources dev i} => x.1.2) ∧
    ∀ n, (E.find? n).isSome → ∀ x ∈ sources dev i, (x.2.find? n).isSome →
      (dev i).key n = (dev x.1).key n

/-- **The check per home**: every view a module presents refines its
own environment.  It reads the module alone, and runs once, however
many modules import it. -/
def InterfaceOk (dev : Nat → Module) (j : Nat) : Prop := ∀ E ∈ (dev j).views, Refines E (dev j).own

/-- **The check per importer**: the module imports earlier modules, and
its context is assembled from their views, with one copy of each
name.  It reads the module and its
imports' views, never an import's own environment. -/
structure ImportOk (dev : Nat → Module) (i : Nat) : Prop where
  imports : ∀ j ∈ (dev i).imports, j < i
  reads : FromViews dev i (dev i).context

/-- **The local checks at module `i`**: its interface, its imports, its
declarations accepted against its context, a constant flagged a proof
a declaration of a proposition, and every own constant declared by the
module (or recorded by its statement, if a proof). -/
structure LocalOk (dev : Nat → Module) (i : Nat) : Prop where
  iface : InterfaceOk dev i
  importOk : ImportOk dev i
  checks : Checks (dev i).context (dev i).decls
  flags : FlagsOk (dev i).proofs (dev i).context (dev i).decls
  key_own : ∀ d ∈ (dev i).decls, ∀ n ∈ d.names, ∀ ci, (dev i).own.find? n = some ci →
    (dev i).key n = (dev i).ownKey i n ci

/-- **Validation by comparison**: module `i`'s whole own environment,
its declarations included, is assembled from its imports' views —
every constant is an import's, or an assumption of its type — with one
copy of each name. -/
structure Compared (dev : Nat → Module) (i : Nat) : Prop where
  iface : InterfaceOk dev i
  imports : ∀ j ∈ (dev i).imports, j < i
  reads : FromViews dev i (dev i).own

/-- **A validated module**: checked, or compared. -/
def Valid (dev : Nat → Module) (i : Nat) : Prop := LocalOk dev i ∨ Compared dev i

end Fragment
