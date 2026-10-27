module

public import Fragment.BlockModel

@[expose] public section

/-!
# Hiding a value, and installing a theorem

**Hiding** turns some of an environment's definitions into assumptions
of the same level parameters and type (`Env.hide`).  A model of an
environment is a model of it with values hidden, at the same
assignment (`BlockModel.hide`): an assumption's only law is the typing
law, which the definition satisfied, and nothing else changes.

**A theorem** is stored as its statement, an assumption
(`ThmOk`, `Decl.lean`).  Installing it is installing the definition
with its proof as the value (`install_def'`) and hiding that value
(`install_thm`).
-/

namespace Fragment
open SetLib IndLib

universe u

/-! ## Hiding -/

/-- A definition seen without its value: an assumption of the same
type; every other constant as it is. -/
def ConstInfo.hide (ci : ConstInfo) : ConstInfo :=
  match ci.kind with
  | .defn _ => { ci with kind := .assumed }
  | _ => ci

/-- `ci`, hidden when `b` says so. -/
def ConstInfo.hideIf (b : Bool) (ci : ConstInfo) : ConstInfo := if b then ci.hide else ci

/-- **An environment with some values hidden**: the definitions `H`
selects seen as assumptions. -/
def Env.hide (H : Name → Bool) (env : Env) : Env :=
  ⟨env.consts.map fun p => (p.1, p.2.hideIf (H p.1))⟩

namespace ConstInfo

variable {ci : ConstInfo} {b : Bool}

theorem hideIf_cases (b : Bool) (ci : ConstInfo) :
    ci.hideIf b = ci ∨ (ci.hideIf b = { ci with kind := .assumed }) := by
  unfold hideIf hide
  split
  · split
    · exact .inr rfl
    · exact .inl rfl
  · exact .inl rfl

@[simp] theorem hideIf_lparams : (ci.hideIf b).lparams = ci.lparams := by
  rcases hideIf_cases b ci with h | h <;> rw [h]

@[simp] theorem hideIf_type : (ci.hideIf b).type = ci.type := by
  rcases hideIf_cases b ci with h | h <;> rw [h]

/-- A hidden constant that is not an assumption is the constant. -/
theorem hideIf_eq_of_ne (h : (ci.hideIf b).kind ≠ .assumed) : ci.hideIf b = ci := by
  rcases hideIf_cases b ci with h' | h'
  · exact h'
  · rw [h'] at h; exact absurd rfl h

/-- A constant that is not a definition is never hidden. -/
theorem hideIf_of_not_defn (h : ∀ v, ci.kind ≠ .defn v) : ci.hideIf b = ci := by
  unfold hideIf hide
  split
  · split
    · rename_i v hv; exact absurd hv (h v)
    · rfl
  · rfl

end ConstInfo

/-- The lookup in an environment with values hidden. -/
theorem Env.find?_hide (H : Name → Bool) (E : Env) (n : Name) :
    (E.hide H).find? n = (E.find? n).map (·.hideIf (H n)) := by
  obtain ⟨cs⟩ := E
  induction cs with
  | nil => rfl
  | cons p cs ih =>
    obtain ⟨m, cm⟩ := p
    have ih' : List.lookup n (cs.map fun p => (p.1, p.2.hideIf (H p.1))) =
        (List.lookup n cs).map (·.hideIf (H n)) := ih
    show List.lookup n ((m, cm.hideIf (H m)) :: cs.map fun p => (p.1, p.2.hideIf (H p.1))) =
      (List.lookup n ((m, cm) :: cs)).map (·.hideIf (H n))
    by_cases hnm : n = m
    · subst hnm
      have hb : (n == n) = true := beq_self_eq_true n
      simp only [List.lookup, hb, Option.map_some]
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr hnm
      simp only [List.lookup, hb]
      exact ih'

theorem Env.find?_hide_eq_some {H : Name → Bool} {E : Env} {n : Name} {ci' : ConstInfo}
    (h : (E.hide H).find? n = some ci') : ∃ ci, E.find? n = some ci ∧ ci' = ci.hideIf (H n) := by
  rw [Env.find?_hide] at h
  obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ci, hci, rfl⟩

theorem Env.isSome_find?_hide {H : Name → Bool} {E : Env} {n : Name} :
    ((E.hide H).find? n).isSome = (E.find? n).isSome := by
  rw [Env.find?_hide]; cases E.find? n <;> rfl

/-- A constant that is not a definition is found unchanged. -/
theorem Env.find?_hide_of_not_defn {H : Name → Bool} {E : Env} {n : Name} {ci : ConstInfo}
    (h : E.find? n = some ci) (hk : ∀ v, ci.kind ≠ .defn v) : (E.hide H).find? n = some ci := by
  rw [Env.find?_hide, h, Option.map_some, ConstInfo.hideIf_of_not_defn hk]

variable {V : Type u} [IndLib V]

/-! ## The laws survive hiding -/

/-- The ι laws read the rule's constructor through its level
parameters and type alone. -/
theorem RecRuleLaw_hideIf {M : Name → List Nat → V} {c : Name} {ci : ConstInfo} {a b d : Nat}
    {rl : RecRule} {cij : ConstInfo} (x : Bool) :
    RecRuleLaw M c ci a b d rl (cij.hideIf x) ↔ RecRuleLaw M c ci a b d rl cij := by
  rcases ConstInfo.hideIf_cases x cij with h | h
  · rw [h]
  · rw [h]; exact Iff.rfl

theorem RecRuleSlotLaw_hideIf {M : Name → List Nat → V} {c : Name} {ci : ConstInfo} {a : Nat}
    {rl : RecRule} {cij : ConstInfo} (x : Bool) :
    RecRuleSlotLaw M c ci a rl (cij.hideIf x) ↔ RecRuleSlotLaw M c ci a rl cij := by
  rcases ConstInfo.hideIf_cases x cij with h | h
  · rw [h]
  · rw [h]; exact Iff.rfl

theorem not_defn_of_recursor {ci : ConstInfo} {a b c d : Nat} {rs : List RecRule}
    (h : ci.kind = .recursor a b c d rs) : ∀ v, ci.kind ≠ .defn v := by
  intro v hv; rw [hv] at h; cases h

theorem not_defn_of_ctor {ci : ConstInfo} {I : Name} {a b : Nat}
    (h : ci.kind = .ctor I a b) : ∀ v, ci.kind ≠ .defn v := by
  intro v hv; rw [hv] at h; cases h

theorem not_defn_of_induct {ci : ConstInfo} {a b : Nat} {cs : List Name} {S : IndSpec}
    (h : ci.kind = .induct a b cs S) : ∀ v, ci.kind ≠ .defn v := by
  intro v hv; rw [hv] at h; cases h

/-- A found constant whose kind is not an assumption is the stored one. -/
theorem find?_hide_kind {H : Name → Bool} {E : Env} {n : Name} {ci' : ConstInfo}
    (h : (E.hide H).find? n = some ci') (hk : ci'.kind ≠ .assumed) : E.find? n = some ci' := by
  obtain ⟨ci, hci, rfl⟩ := Env.find?_hide_eq_some h
  rw [ConstInfo.hideIf_eq_of_ne hk]; exact hci

theorem kind_ne_of_recursor {ci : ConstInfo} {a b c d : Nat} {rs : List RecRule}
    (h : ci.kind = .recursor a b c d rs) : ci.kind ≠ .assumed := by
  rw [h]; exact nofun

namespace IndSpec

/-- A block's law survives hiding values: its constants are not
definitions, and its scope reads only which names are stored. -/
theorem BlockLaw_hide (S : IndSpec) {E : Env} {M : Name → List Nat → V} (H : Name → Bool)
    (h : S.BlockLaw E M) : S.BlockLaw (E.hide H) M := by
  intro hpl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h hpl
  refine ⟨h1.mono fun n hn => by rwa [Env.isSome_find?_hide], h2,
    Env.find?_hide_of_not_defn h3 (fun v hv => by simp [indInfo] at hv),
    fun j c hc => Env.find?_hide_of_not_defn (h4 j c hc) (fun v hv => by simp [ctorInfo] at hv),
    h5, h6, h7⟩

/-- A block's law transfers along environments with the same lookups. -/
theorem BlockLaw_congr (S : IndSpec) {E₁ E₂ : Env} {M : Name → List Nat → V}
    (hE : ∀ n, E₁.find? n = E₂.find? n) (h : S.BlockLaw E₁ M) : S.BlockLaw E₂ M := by
  intro hpl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h hpl
  exact ⟨h1.mono fun n hn => by rwa [← hE], h2, by rwa [← hE], fun j c hc => by rw [← hE]; exact h4 j c hc,
    h5, h6, h7⟩

end IndSpec

/-- **A model survives hiding values**, at the same assignment. -/
def BlockModel.hide {E : Env} (m : BlockModel V E) (H : Name → Bool) : BlockModel V (E.hide H) where
  M := m.M
  type_ok := fun c ci' hf φ ρ ls hls => by
    obtain ⟨ci, hci, rfl⟩ := Env.find?_hide_eq_some hf
    simp only [ConstInfo.hideIf_lparams, ConstInfo.hideIf_type] at hls ⊢
    exact m.type_ok c ci hci φ ρ ls hls
  unfold := fun c ci' v hf hv φ ρ ls hls => by
    obtain ⟨ci, hci, rfl⟩ := Env.find?_hide_eq_some hf
    have hne : (ci.hideIf (H c)).kind ≠ .assumed := by
      intro hk; simp [ConstInfo.value?, hk, ConstKind.value?] at hv
    rw [ConstInfo.hideIf_eq_of_ne hne] at hv hls ⊢
    exact m.unfold c ci v hci hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hf hkind rl hrl hinst cij' hcij => by
    have hf' := find?_hide_kind hf (kind_ne_of_recursor hkind)
    obtain ⟨cij, hcij', rfl⟩ := Env.find?_hide_eq_some hcij
    exact (RecRuleLaw_hideIf _).mpr (m.rec_rules c ci nP nM nMin nI rules hf' hkind rl hrl hinst cij hcij')
  rec_rules_nested := fun c ci nP nM nMin nI rules hf hkind rl hrl lvs pinst hinst cij I nPc nf hcij
      hcijk => by
    have hf' := find?_hide_kind hf (kind_ne_of_recursor hkind)
    have hcij' := find?_hide_kind hcij (by rw [hcijk]; exact nofun)
    exact m.rec_rules_nested c ci nP nM nMin nI rules hf' hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij' hcijk
  ind_fib := fun I ci nP nI cs S hf hk => by
    have hf' := find?_hide_kind hf (by rw [hk]; exact nofun)
    exact m.ind_fib I ci nP nI cs S hf' hk
  rec_rules_slot := fun c ci nP nM nMin nI rules hf hkind rl hrl cij' hcij => by
    have hf' := find?_hide_kind hf (kind_ne_of_recursor hkind)
    obtain ⟨cij, hcij', rfl⟩ := Env.find?_hide_eq_some hcij
    exact (RecRuleSlotLaw_hideIf _).mpr
      (m.rec_rules_slot c ci nP nM nMin nI rules hf' hkind rl hrl cij hcij')
  rec_rules_k := fun c ci nP nM nMin nI rules hf hkind rl hrl hk => by
    have hf' := find?_hide_kind hf (kind_ne_of_recursor hkind)
    exact m.rec_rules_k c ci nP nM nMin nI rules hf' hkind rl hrl hk
  blocks := fun K ci nP nI cs spec hf hk => by
    have hf' := find?_hide_kind hf (by rw [hk]; exact nofun)
    exact spec.BlockLaw_hide H (m.blocks K ci nP nI cs spec hf' hk)

/-- **A model transfers along environments with the same lookups.** -/
def BlockModel.congr {E₁ E₂ : Env} (m : BlockModel V E₁) (hE : ∀ n, E₁.find? n = E₂.find? n) :
    BlockModel V E₂ where
  M := m.M
  type_ok := fun c ci hf => m.type_ok c ci (by rwa [hE])
  unfold := fun c ci v hf => m.unfold c ci v (by rwa [hE])
  rec_rules := fun c ci nP nM nMin nI rules hf hk rl hrl hinst cij hcij =>
    m.rec_rules c ci nP nM nMin nI rules (by rwa [hE]) hk rl hrl hinst cij (by rwa [hE])
  rec_rules_nested := fun c ci nP nM nMin nI rules hf hk rl hrl lvs pinst hinst cij I nPc nf hcij hcijk =>
    m.rec_rules_nested c ci nP nM nMin nI rules (by rwa [hE]) hk rl hrl lvs pinst hinst cij I nPc nf
      (by rwa [hE]) hcijk
  ind_fib := fun I ci nP nI cs S hf hk => m.ind_fib I ci nP nI cs S (by rwa [hE]) hk
  rec_rules_slot := fun c ci nP nM nMin nI rules hf hk rl hrl cij hcij =>
    m.rec_rules_slot c ci nP nM nMin nI rules (by rwa [hE]) hk rl hrl cij (by rwa [hE])
  rec_rules_k := fun c ci nP nM nMin nI rules hf hk rl hrl hkr =>
    m.rec_rules_k c ci nP nM nMin nI rules (by rwa [hE]) hk rl hrl hkr
  blocks := fun K ci nP nI cs spec hf hk =>
    spec.BlockLaw_congr hE (m.blocks K ci nP nI cs spec (by rwa [hE]) hk)

/-! ## Installing a theorem -/

variable [LevelOracle]

/-- A closed environment stays closed under an accepted theorem. -/
theorem Env.Scoped.add_thm {env : Env} {c : Name} {ci : ConstInfo} {v : Expr} (hs : Env.Scoped env)
    (hok : ThmOk env c ci v) : Env.Scoped (env.add c ci) := by
  obtain ⟨hk, hd, -⟩ := hok
  refine hs.add hd.1 hd.type_scoped (fun v' hv' => ?_) (fun _ _ _ _ _ hk' => ?_)
  · simp [ConstInfo.value?, hk, ConstKind.value?] at hv'
  · rw [hk] at hk'; cases hk'

/-- **Installing a theorem preserves having a model**: install its
proof as a definition, then hide the value.  Every stored constant
keeps its set, and the theorem's is its proof's (`defVal`). -/
theorem install_thm {env : Env} {c : Name} {ci : ConstInfo} {v : Expr}
    (hs : Env.Scoped env) (m : BlockModel V env) (hok : ThmOk env c ci v) :
    ∃ m' : BlockModel V (env.add c ci), (∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
      ∀ ls, m'.M c ls = defVal m.M { ci with kind := .defn v } v ls := by
  obtain ⟨m₁, hagree, hval⟩ := install_def' hs m hok.2.1
  refine ⟨(m₁.hide (· == c)).congr fun n => ?_, hagree, hval v rfl⟩
  rw [Env.find?_hide, Env.find?_add, Env.find?_add]
  by_cases hn : n = c
  · subst hn
    have hci : ci = { ci with kind := .assumed } := by
      obtain ⟨l, t, k⟩ := ci
      have hk : k = .assumed := hok.1
      subst hk; rfl
    simp only [ite_true, Option.map_some, beq_self_eq_true]
    rw [hci]; rfl
  · have hb : (n == c) = false := beq_eq_false_iff_ne.mpr hn
    simp only [hn, ite_false, hb]
    cases env.find? n <;> rfl

end Fragment
