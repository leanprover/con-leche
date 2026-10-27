module

public import Fragment.Modular
public import Fragment.InstallThm

@[expose] public section

/-!
# Modular checking: one model for every module

(The theorem and its local checks; see `Modular.lean` for refinement
and monotonicity.)
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
  | none => rw [Env.find?_append_of_lookup hl]; exact h

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

end Fragment
