module

public import Fragment.NestInstall
public import Fragment.NestIotaRead
public import Fragment.Modular

@[expose] public section

/-!
# The input's clauses in the models the installation builds

The proof's invariant `EnvModel` carries the laws the soundness proof
reads; the statement's `ModelOf` (`IsModel.lean`) is read off the
input.  This file links them.

* `Holds E M`: every constant `E` stores holds in `M` (`ModelOf`).
* `ModelOf.congr`: `ModelOf` is local — two assignments agreeing on
  the constant and on every constant its type, its value and its rules'
  right-hand sides read give it alike.  So an installation, which keeps
  every stored constant's set, keeps `Holds` of what was stored before.
* `EnvModel.modelOf`: a stored constant other than a recursor holds in
  every model of the environment, by the typing law (membership) and
  the unfolding law (a definition).
* `install_ind_holds`: installing an accepted block gives a model in
  which the block's constants hold — the recursors' rules by
  `IndSpec.rule_holds` (plain, `IotaRead.lean`) and
  `IndSpec.rule_holdsN`, `IndSpec.rule_holds1` (nested,
  `NestIotaRead.lean`).
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-- **Every constant `E` stores holds in `M`.** -/
def Holds (E : Env) (M : Name → List Nat → V) : Prop :=
  ∀ n ci, E.find? n = some ci → ModelOf M n ci

theorem Holds.empty (M : Name → List Nat → V) : Holds Env.empty M := fun _ _ h => by simp at h

/-! ## Locality -/

section Locality

variable {M M' : Name → List Nat → V} {φ : Name → Nat}


omit [IndLib V] in
theorem consts_piBodyV : ∀ {ρ : Nat → V} {T : Expr} {vs : List V} {B : Expr} {ρ' : Nat → V},
    piBodyV ρ T vs = some (B, ρ') → ∀ c ∈ B.consts, c ∈ T.consts
  | ρ, T, [], B, ρ', h => by
    rw [piBodyV_nil] at h; cases h; exact fun _ h => h
  | ρ, .pi A B₀, v :: vs, B, ρ', h => fun c hc => by
    simp only [Expr.consts, List.mem_append]
    exact .inr (consts_piBodyV (T := B₀) (ρ := cons v ρ) (vs := vs) h c hc)
  | _, .bvar _, _ :: _, _, _, h => by cases h
  | _, .sort _, _ :: _, _, _, h => by cases h
  | _, .const _ _, _ :: _, _, _, h => by cases h
  | _, .app _ _, _ :: _, _, _, h => by cases h
  | _, .lam _ _, _ :: _, _, _, h => by cases h
  | _, .letE _ _ _, _ :: _, _, _, h => by cases h


theorem consts_conclV : ∀ (ρ : Nat → V) (T : Expr), ∀ c ∈ (conclV ρ T).1.consts, c ∈ T.consts
  | ρ, .pi A B => fun c hc => by
    simp only [Expr.consts, List.mem_append]
    exact .inr (consts_conclV _ B c hc)
  | _, .bvar _ => fun _ h => h
  | _, .sort _ => fun _ h => h
  | _, .const _ _ => fun _ h => h
  | _, .app _ _ => fun _ h => h
  | _, .lam _ _ => fun _ h => h
  | _, .letE _ _ _ => fun _ h => h

theorem consts_args : ∀ (e : Expr), ∀ a ∈ e.args, ∀ c ∈ a.consts, c ∈ e.consts
  | .app f a => fun a' ha c hc => by
    simp only [Expr.args, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.consts, List.mem_append]
    rcases ha with ha | rfl
    · exact .inl (consts_args f a' ha c hc)
    · exact .inr hc
  | .bvar _ => fun _ h => by simp [Expr.args] at h
  | .sort _ => fun _ h => by simp [Expr.args] at h
  | .const _ _ => fun _ h => by simp [Expr.args] at h
  | .lam _ _ => fun _ h => by simp [Expr.args] at h
  | .pi _ _ => fun _ h => by simp [Expr.args] at h
  | .letE _ _ _ => fun _ h => by simp [Expr.args] at h


theorem TeleFitV_consts (h : ∀ c ∈ T.consts, ∀ ls, M c ls = M' c ls) :
    ∀ {ρ : Nat → V} {vs : List V}, TeleFitV M φ ρ T vs ↔ TeleFitV M' φ ρ T vs := by
  induction T with
  | pi A B _ ihB =>
    intro ρ vs
    cases vs with
    | nil => exact ⟨fun _ => TeleFitV_nil _ _ _ _, fun _ => TeleFitV_nil _ _ _ _⟩
    | cons v vs =>
      simp only [Expr.consts, List.mem_append] at h
      rw [TeleFitV_pi_cons, TeleFitV_pi_cons, interp_consts fun c hc => h c (.inl hc),
        ihB fun c hc => h c (.inr hc)]
  | _ =>
    intro ρ vs
    cases vs with
    | nil => exact ⟨fun _ => TeleFitV_nil _ _ _ _, fun _ => TeleFitV_nil _ _ _ _⟩
    | cons v vs => exact Iff.rfl


/-- **`ModelOf` is local**: it reads the assignment at the constant and
at the constants of its type, its value and its rules' right-hand
sides. -/
theorem ModelOf.congr {n : Name} {ci : ConstInfo} (hn : ∀ ls, M n ls = M' n ls)
    (hT : ∀ c ∈ ci.type.consts, ∀ ls, M c ls = M' c ls)
    (hV : ∀ v, ci.value? = some v → ∀ c ∈ v.consts, ∀ ls, M c ls = M' c ls)
    (hR : ∀ nP nM nMin nI rules, ci.kind = .recursor nP nM nMin nI rules → ∀ rl ∈ rules,
      ∀ c ∈ rl.rhs.consts, ∀ ls, M c ls = M' c ls)
    (h : ModelOf M n ci) : ModelOf M' n ci := by
  obtain ⟨ps, T, k⟩ := ci
  intro vals hvals
  obtain ⟨hmem, hk⟩ := h vals hvals
  refine ⟨by rw [← hn, ← interp_consts hT]; exact hmem, ?_⟩
  cases k with
  | defn v =>
    exact (hn vals).symm.trans (hk.trans (interp_consts (hV v rfl)))
  | recursor nP nM nMin nI rules =>
    intro i rl hrl mot q hmot hq xs ys D B C ρq ρc hxs hfit hD hys hfitD hC
    have hrl' : rl ∈ rules := List.mem_of_getElem? hrl
    have hDc : ∀ c ∈ D.consts, ∀ ls, M c ls = M' c ls := fun c hc =>
      hT c (consts_piBodyV hD c (by simp [Expr.consts, hc]))
    have hCc : ∀ a ∈ C.args, ∀ c ∈ a.consts, ∀ ls, M c ls = M' c ls := by
      intro a ha c hc
      cases hp : piBodyV ρq D ys with
      | none => rw [hp] at hC; cases hC
      | some p =>
        rw [hp, Option.map_some, Option.some.injEq] at hC
        have h1 := consts_conclV p.2 p.1 c (by rw [hC]; exact consts_args C a ha c hc)
        exact hDc c (consts_piBodyV (B := p.1) (ρ' := p.2) hp c h1)
    have := hk i rl hrl mot q hmot hq xs ys D B C ρq ρc hxs
      ((TeleFitV_consts hT).mpr hfit) hD hys ((TeleFitV_consts hDc).mpr hfitD) hC
    rw [← hn, ← interp_consts (hR nP nM nMin nI rules rfl rl hrl')]
    rw [List.map_congr_left fun a ha => interp_consts (hCc a ha)] at this
    exact this
  | _ => trivial

/-- **`ModelOf` of a stored constant is local to its environment**:
two assignments agreeing on a closed environment give its constants
alike. -/
theorem ModelOf.congr_env {E : Env} (hs : Env.Scoped E) {n : Name} {ci : ConstInfo}
    (hf : E.find? n = some ci) (hag : AgreeOn E M M') (h : ModelOf M n ci) : ModelOf M' n ci := by
  obtain ⟨hT, hV, hR⟩ := hs n ci hf
  exact h.congr (hag n (by rw [hf]; rfl)) (fun c hc => hag c (hT.2.1 c hc))
    (fun v hv c hc => hag c ((hV v hv).2.1 c hc))
    (fun nP nM nMin nI rules hk rl hrl c hc => hag c ((hR nP nM nMin nI rules hk rl hrl).1.2.1 c hc))

theorem Holds.congr {E : Env} (hs : Env.Scoped E) (hag : AgreeOn E M M') (h : Holds E M) :
    Holds E M' := fun n ci hf => (h n ci hf).congr_env hs hf hag

end Locality

/-! ## Constants other than recursors -/

/-- A natural number list as levels, read back: the valuation of the
values. -/
theorem interp_type_ofNat {M : Name → List Nat → V} (ps : List Name) (vals : List Nat)
    (hl : vals.length = ps.length) (ρ : Nat → V) (e : Expr) :
    interp M (valOf ps vals) ρ (e.instL ps (vals.map Level.ofNat)) = interp M (valOf ps vals) ρ e := by
  rw [interp_instL, Level.substVal_ofNat ps vals hl]

/-- **A stored constant holds by the typing law**: its set is a member
of its type, and a definition's set is its value's (the unfolding
law); a recursor's rules are not read here. -/
theorem EnvModel.modelOf_mem {E : Env} (m : EnvModel V E) {n : Name} {ci : ConstInfo}
    (hf : E.find? n = some ci) (vals : List Nat) (hvals : vals.length = ci.lparams.length) :
    m.M n vals ∈ˢ interp m.M (valOf ci.lparams vals) base ci.type ∧
    ∀ v, ci.kind = .defn v → m.M n vals = interp m.M (valOf ci.lparams vals) base v := by
  have hl : (vals.map Level.ofNat).length = ci.lparams.length := by simpa using hvals
  have h := (m.type_ok n ci hf (valOf ci.lparams vals) base (vals.map Level.ofNat) hl).2.2
  rw [Level.map_eval_ofNat, interp_type_ofNat _ _ hvals] at h
  refine ⟨h, fun v hk => ?_⟩
  have hu := (m.unfold n ci v hf (by simp [ConstInfo.value?, hk, ConstKind.value?])
    (valOf ci.lparams vals) base (vals.map Level.ofNat) hl).2
  rw [Level.map_eval_ofNat, interp_type_ofNat _ _ hvals] at hu
  exact hu.symm

/-- **A stored constant other than a recursor holds** in every model of
the environment. -/
theorem EnvModel.modelOf {E : Env} (m : EnvModel V E) {n : Name} {ci : ConstInfo}
    (hf : E.find? n = some ci)
    (hk : ∀ nP nM nMin nI rules, ci.kind ≠ .recursor nP nM nMin nI rules) : ModelOf m.M n ci := by
  intro vals hvals
  obtain ⟨hmem, hdef⟩ := m.modelOf_mem hf vals hvals
  refine ⟨hmem, ?_⟩
  obtain ⟨ps, T, k⟩ := ci
  cases k with
  | defn v => exact hdef v rfl
  | recursor nP nM nMin nI rules => exact absurd rfl (hk nP nM nMin nI rules)
  | _ => trivial

/-! ## Installing a declaration keeps `Holds` -/

variable [LevelOracle]

omit [LevelOracle] in
/-- **What a checked declaration stores, and what was there.** -/
theorem Holds.apply {E : Env} {d : Decl} (hs : Env.Scoped E)
    {M : Name → List Nat → V} (hE : Holds E M) {M' : Name → List Nat → V} (hag : AgreeOn E M M')
    (hnew : ∀ n ci, d.stores.lookup n = some ci → ModelOf M' n ci) : Holds (d.apply E) M' := by
  intro n ci hf
  rw [Decl.apply_eq] at hf
  cases hl : d.stores.lookup n with
  | some e =>
    have := lookup_append_of_some (cs := E.consts) hl
    rw [show (d.stores ++ E.consts).lookup n = some ci from hf] at this
    cases this
    exact hnew n _ hl
  | none =>
    have hE' : E.find? n = some ci := by simpa only [Env.find?, lookup_append_of_none hl] using hf
    exact ((hE n ci hE').congr_env hs hE' hag)

omit [LevelOracle] in
/-- **The recursors a block stores**: `T.rec` (and a nested block's
`T.rec_1`) with its generated rules. -/
theorem ind_stores_recursor {S : IndSpec} {n : Name} {ci : ConstInfo}
    (h : (n, ci) ∈ (Decl.ind S).stores) {nP nM nMin nI : Nat} {rules : List RecRule}
    (hk : ci.kind = .recursor nP nM nMin nI rules) :
    (S.nest = none → n = S.recName ∧ ci = S.recInfo) ∧
    (∀ N, S.nest = some N → (n = S.recName ∧ ci = S.recInfoN N) ∨ (n = N.aux ∧ ci = S.rec1Info N)) := by
  have hC : (S.envCtors Env.empty).consts =
      (S.ctors.map fun c => (c.name, S.ctorInfo c)).reverse ++ [(S.name, S.indInfo)] :=
    IndSpec.foldl_add_empty S S.ctors [(S.name, S.indInfo)]
  simp only [Decl.stores, Decl.apply, IndSpec.install, IndSpec.installN] at h
  constructor
  · intro hn
    simp only [hn, Env.add, hC, List.mem_cons, List.mem_append, List.mem_reverse, List.mem_map,
      Prod.mk.injEq] at h
    grind [IndSpec.indInfo, IndSpec.ctorInfo]
  · intro N hn
    simp only [hn, Env.add, hC, List.mem_cons, List.mem_append, List.mem_reverse, List.mem_map,
      Prod.mk.injEq] at h
    grind [IndSpec.indInfo, IndSpec.ctorInfo]

/-- **Installing an accepted block**: a model of the installed
environment, keeping every stored constant's set, in which the block's
constants hold. -/
theorem install_ind_holds {env : Env} {S : IndSpec} (hs : Env.Scoped env) (m : BlockModel V env)
    (hok : IndOk env S) :
    ∃ m' : BlockModel V (S.install env), (∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
      ∀ n ci, (Decl.ind S).stores.lookup n = some ci → ModelOf m'.M n ci := by
  have hfind : ∀ (m' : BlockModel V (S.install env)) n ci, (Decl.ind S).stores.lookup n = some ci →
      (S.install env).find? n = some ci := by
    intro m' n ci hl
    rw [show S.install env = (Decl.ind S).apply env from rfl, Decl.apply_eq]
    exact lookup_append_of_some hl
  -- a recursor's clause: membership, and its rules by the given reading
  have hrec : ∀ (m' : BlockModel V (S.install env)) n ci, (S.install env).find? n = some ci →
      (∀ nP nM nMin nI rules, ci.kind = .recursor nP nM nMin nI rules → ∀ vals,
        vals.length = ci.lparams.length → ∀ i rl, rules[i]? = some rl →
          RuleHolds m'.M (valOf ci.lparams vals) (m'.M n vals) ci.type (nP + nM + nMin) i rl) →
      ModelOf m'.M n ci := by
    intro m' n ci hf hR vals hvals
    refine ⟨(m'.modelOf_mem hf vals hvals).1, ?_⟩
    obtain ⟨ps, T, k⟩ := ci
    cases k with
    | recursor nP nM nMin nI rules => exact hR nP nM nMin nI rules rfl vals hvals
    | defn v => exact (m'.modelOf_mem hf vals hvals).2 v rfl
    | _ => trivial
  unfold IndOk at hok
  split at hok
  · rename_i hpl
    obtain ⟨m', hag, hM⟩ := install_ind' hpl hs m hok
    refine ⟨m', hag, fun n ci hl => hrec m' n ci (hfind m' n ci hl) ?_⟩
    intro nP nM nMin nI rules hk vals hvals i rl hrl
    obtain ⟨rfl, rfl⟩ := (ind_stores_recursor (key_of_lookup hl) hk).1 hpl
    simp only [IndSpec.recInfo, ConstKind.recursor.injEq] at hk hvals ⊢
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hk
    rw [hM]
    exact IndSpec.rule_holds hpl hs m.toEnvModel hok vals hvals hrl
  · rename_i N hN
    obtain ⟨m', hag, hM⟩ := install_nest hs m hok
    refine ⟨m', hag, fun n ci hl => hrec m' n ci (hfind m' n ci hl) ?_⟩
    intro nP nM nMin nI rules hk vals hvals i rl hrl
    rcases (ind_stores_recursor (key_of_lookup hl) hk).2 N hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [IndSpec.recInfoN, ConstKind.recursor.injEq] at hk hvals ⊢
      obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hk
      rw [hM, show S.nP + 2 + (S.n + N.nK) = S.nP + 2 + (S.n + N.nK) from rfl]
      exact IndSpec.rule_holdsN hs m hok vals hvals hrl
    · simp only [IndSpec.rec1Info, ConstKind.recursor.injEq] at hk hvals ⊢
      obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hk
      rw [hM]
      exact IndSpec.rule_holds1 hs m hok vals hvals hrl

end Fragment
