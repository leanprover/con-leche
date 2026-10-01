module

public import Fragment.EnvModel

@[expose] public section

/-!
# Telescopes: terms and values

The bridges between the **term-level** certificates the rules carry
(`TeleFit`, `Expr.piResidual`, spines `Expr.mkAppN`) and the
**value-level** forms the environment's ι law is stated in
(`TeleFitV`, `piBodyV`, `appList`, `SpineOk`; `EnvModel.lean`):

* an argument list fits a telescope exactly when its denotations do
  (`teleFitV_of_teleFit`) — the substituted body reads as the body
  under the extended environment (`teleFitV_inst`);
* the residual of a telescope walked along terms is the body walked
  along their values, with the terms substituted in (`instChain`,
  `piResidual_of_piBodyV`), so the residual's index expressions denote
  what the body's do under the values (`interp_instChain`);
* a spine over a well-denoted head with well-denoted arguments is
  well-denoted when its values form a well-formed application chain
  (`WellDenoted_mkAppN_of_spineOk`), and a fit of values to a
  well-denoted telescope the head inhabits gives such a chain
  (`spineOk_of_teleFitV`).

Environments built from value lists (`consList`) and the spine
projections (`Expr.getAppFn`/`getAppArgs`) are the small vocabulary
these need.  Mirrors the `TeleFitV`/`TeleFitPA` transposes and the
index pin of `ConLeche/Model/Annot/Laws.lean`.
-/

namespace Fragment
open SetLib

universe u

/-! ## A list fact -/

/-- Two lists of one length whose zip is pairwise equal under `f` map
alike under `f`. -/
theorem List.map_eq_of_zip {α β : Type _} (f : α → β) :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, f p.1 = f p.2) →
      l₁.map f = l₂.map f
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (a, b) (by simp), map_eq_of_zip f hl fun p hp => h p (by simp [hp])⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-! ## Environments from lists -/

section ConsList

variable {V : Type u}

/-- Push a list of values, innermost first, onto an environment. -/
def consList : List V → (Nat → V) → Nat → V
  | [], ρ => ρ
  | v :: vs, ρ => cons v (consList vs ρ)

@[simp] theorem consList_nil (ρ : Nat → V) : consList [] ρ = ρ := rfl
@[simp] theorem consList_cons (v : V) (vs : List V) (ρ : Nat → V) :
    consList (v :: vs) ρ = cons v (consList vs ρ) := rfl

theorem consList_append (vs ws : List V) (ρ : Nat → V) :
    consList (vs ++ ws) ρ = consList vs (consList ws ρ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem consList_lt {vs : List V} {ρ : Nat → V} {i : Nat} (h : i < vs.length) :
    consList vs ρ i = vs[i] := by
  induction vs generalizing i with
  | nil => simp at h
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa using h)

/-- Environments built by pushing the same values agree below the
pushed values' number. -/
theorem consList_agree_lt {vs : List V} {ρ ρ' : Nat → V} :
    ∀ i, i < vs.length → consList vs ρ i = consList vs ρ' i := by
  intro i hi
  rw [consList_lt hi, consList_lt hi]

theorem consList_ge (vs : List V) (ρ : Nat → V) (i : Nat) :
    consList vs ρ (i + vs.length) = ρ i := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show cons v (consList vs ρ) ((i + vs.length) + 1) = ρ i
    exact ih

/-- Shifting past the pushed values is dropping them. -/
theorem shiftE_consList (vs : List V) (ρ : Nat → V) :
    shiftE vs.length 0 (consList vs ρ) = ρ := by
  funext i
  simp [shiftE, consList_ge]

theorem shiftE_consList' {vs : List V} {k : Nat} (h : vs.length = k) (ρ : Nat → V) :
    shiftE k 0 (consList vs ρ) = ρ := h ▸ shiftE_consList vs ρ

/-- An instantiation below the pushed values is a push onto the
instantiated environment. -/
theorem instE_consList (vs : List V) (x : V) (ρ : Nat → V) :
    instE vs.length x (consList vs ρ) = consList vs (cons x ρ) := by
  induction vs with
  | nil => exact instE_zero x ρ
  | cons v vs ih => simp [← cons_instE, ih]

end ConsList

variable {V : Type u} [SetLib V] (M : Name → List Nat → V) (φ : Name → Nat)

/-! ## Spines -/

/-- The interpretation of a spine, on values. -/
theorem interp_mkAppN_appList (ρ : Nat → V) (f : Expr) (args : List Expr) :
    interp M φ ρ (Expr.mkAppN f args) = appList (interp M φ ρ f) (args.map (interp M φ ρ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp [ih]

namespace Expr

/-- The head of a spine. -/
def getAppFn : Expr → Expr
  | app f _ => getAppFn f
  | e => e

/-- The arguments of a spine, first first. -/
def getAppArgs : Expr → List Expr
  | app f a => getAppArgs f ++ [a]
  | _ => []

theorem getAppFn_mkAppN (f : Expr) (args : List Expr) : getAppFn (mkAppN f args) = getAppFn f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp [ih, getAppFn]

theorem getAppArgs_mkAppN (f : Expr) (args : List Expr) :
    getAppArgs (mkAppN f args) = getAppArgs f ++ args := by
  induction args generalizing f with
  | nil => simp
  | cons a args ih => simp [ih, getAppArgs]

/-- Two constant-headed spines are equal only componentwise. -/
theorem mkAppN_const_inj {c c' : Name} {ls ls' : List Level} {as bs : List Expr}
    (h : mkAppN (const c ls) as = mkAppN (const c' ls') bs) :
    c = c' ∧ ls = ls' ∧ as = bs := by
  have h1 := congrArg getAppFn h
  have h2 := congrArg getAppArgs h
  rw [getAppFn_mkAppN, getAppFn_mkAppN] at h1
  rw [getAppArgs_mkAppN, getAppArgs_mkAppN] at h2
  simp [getAppFn, getAppArgs] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

theorem mkAppN_inst (a : Expr) (k : Nat) (f : Expr) (args : List Expr) :
    (mkAppN f args).inst a k = mkAppN (f.inst a k) (args.map (·.inst a k)) := by
  induction args generalizing f with
  | nil => rfl
  | cons b args ih => simp [ih]

theorem instChain_const (c : Name) (ls : List Level) (as : List Expr) :
    instChain (const c ls) as = const c ls := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem instChain_mkAppN (f : Expr) (args as : List Expr) :
    instChain (mkAppN f args) as = mkAppN (instChain f as) (args.map (instChain · as)) := by
  induction as generalizing f args with
  | nil => simp
  | cons a as ih => simp [mkAppN_inst, ih, List.map_map, Function.comp_def]

end Expr

/-- The substitution chain reads as the body under the arguments'
values, pushed innermost first. -/
theorem interp_instChain (ρ : Nat → V) :
    ∀ (as : List Expr) (e : Expr),
      interp M φ ρ (Expr.instChain e as) = interp M φ (consList (as.map (interp M φ ρ)).reverse ρ) e
  | [], e => rfl
  | a :: as, e => by
    rw [Expr.instChain_cons, interp_instChain ρ as, interp_inst]
    have hlen : (as.map (interp M φ ρ)).reverse.length = as.length := by simp
    rw [← hlen, shiftE_consList, instE_consList]
    simp [consList_append]

/-! ## Value walks -/

omit [SetLib V] in
theorem piBodyV_env : ∀ {ρ ρ' : Nat → V} {T B : Expr} {vs : List V},
    piBodyV ρ T vs = some (B, ρ') → ρ' = consList vs.reverse ρ
  | _, _, _, _, [], h => by simp [piBodyV] at h; exact h.2.symm
  | ρ, ρ', .pi _ _ B₀, B, v :: vs, h => by
    simp only [piBodyV] at h
    rw [piBodyV_env h]
    simp [consList_append]
  | _, _, .bvar _, _, _ :: _, h => by simp [piBodyV] at h
  | _, _, .sort _, _, _ :: _, h => by simp [piBodyV] at h
  | _, _, .const _ _, _, _ :: _, h => by simp [piBodyV] at h
  | _, _, .app _ _, _, _ :: _, h => by simp [piBodyV] at h
  | _, _, .lam _ _ _, _, _ :: _, h => by simp [piBodyV] at h

/-- When the telescope walked under the instantiated environment
leaves a body, the substituted telescope walked under the original
one leaves that body substituted. -/
theorem piBodyV_inst (a : Expr) : ∀ (vs : List V) (e : Expr) (k : Nat) (ρ : Nat → V)
    {B' : Expr} {ρ' : Nat → V},
    piBodyV (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e vs = some (B', ρ') →
    ∃ ρ'', piBodyV ρ (e.inst a k) vs = some (B'.inst a (k + vs.length), ρ'')
  | [], e, k, ρ, B', ρ', h => by
    simp [piBodyV] at h
    exact ⟨ρ, by simp [piBodyV, h.1]⟩
  | v :: vs, .pi A pw B, k, ρ, B', ρ', h => by
    simp only [piBodyV] at h
    have h' : piBodyV (instE (k + 1) (interp M φ (shiftE (k + 1) 0 (cons v ρ)) a) (cons v ρ))
        B vs = some (B', ρ') := by
      rw [shiftE_succ_cons, ← cons_instE]; exact h
    obtain ⟨ρ'', h''⟩ := piBodyV_inst a vs B (k + 1) (cons v ρ) h'
    refine ⟨ρ'', ?_⟩
    simp only [Expr.inst_pi, piBodyV, List.length_cons, h'']
    congr 3
    omega
  | _ :: _, .bvar _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .sort _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .const _ _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .app _ _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .lam _ _ _, _, _, _, _, h => by simp [piBodyV] at h

/-- **The residual is the substitution chain of the body**: walking a
telescope along terms leaves the body the values leave, with the terms
substituted in. -/
theorem piResidual_of_piBodyV (ρ : Nat → V) :
    ∀ {as : List Expr} {T R B : Expr} {ρ' : Nat → V},
      Expr.piResidual T as = some R →
      piBodyV ρ T (as.map (interp M φ ρ)) = some (B, ρ') → R = Expr.instChain B as
  | [], T, R, B, _, h1, h2 => by
    rw [List.map_nil, piBodyV_nil] at h2
    simp only [Expr.piResidual_nil, Option.some.injEq] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h1, h2.1]; rfl
  | a :: as, .pi A pw B₀, R, B, ρ', h1, h2 => by
    rw [Expr.piResidual_pi_cons] at h1
    simp only [List.map_cons, piBodyV] at h2
    -- transport the value walk under `cons ⟦a⟧ ρ` to a walk of the substituted body under `ρ`
    rw [← instE_zero, ← shiftE_zero_zero (ρ := ρ)] at h2
    obtain ⟨ρ'', h''⟩ := piBodyV_inst M φ a _ B₀ 0 ρ h2
    rw [List.length_map, Nat.zero_add] at h''
    rw [piResidual_of_piBodyV ρ h1 h'']
    rfl
  | _ :: _, .bvar _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .sort _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .const _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .app _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .lam _ _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h

/-! ## Fits -/

/-- A fit to a substituted telescope with enough syntactic binders is
a fit under the instantiated environment.  (Without the binders a
substitution could create the telescope — `(x : Type) → x` at a
function type — and the value walk, which never substitutes, would
stop short.) -/
theorem teleFitV_inst (a : Expr) : ∀ (vs : List V) (e : Expr) (k : Nat) (ρ : Nat → V),
    e.hasPis vs.length = true →
    (TeleFitV M φ ρ (e.inst a k) vs ↔
      TeleFitV M φ (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e vs)
  | [], _, _, _, _ => ⟨fun _ => TeleFitV_nil M φ _ _, fun _ => TeleFitV_nil M φ _ _⟩
  | v :: vs, .pi A pw B, k, ρ, h => by
    simp only [Expr.inst_pi, TeleFitV]
    rw [interp_inst, teleFitV_inst a vs B (k + 1) (cons v ρ) (by simpa using h),
      shiftE_succ_cons, cons_instE]
  | _ :: _, .bvar _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .sort _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .const _ _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .app _ _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .lam _ _ _, _, _, h => by simp [Expr.hasPis] at h

/-- **Terms fit when their values do**, on a telescope with the
spine's length of syntactic binders. -/
theorem teleFitV_of_teleFit (ρ : Nat → V) :
    ∀ {as : List Expr} {T : Expr}, T.hasPis as.length = true →
      TeleFit M φ ρ T as → TeleFitV M φ ρ T (as.map (interp M φ ρ))
  | [], _, _, _ => TeleFitV_nil M φ _ _
  | a :: as, .pi A pw B, hp, h => by
    obtain ⟨hmem, hfit⟩ := h
    refine ⟨hmem, ?_⟩
    have hp' : B.hasPis as.length = true := by simpa using hp
    have := teleFitV_of_teleFit ρ (Expr.hasPis_inst a B 0 _ hp') hfit
    rw [teleFitV_inst M φ a _ B 0 ρ (by simpa using hp'), shiftE_zero_zero, instE_zero] at this
    exact this
  | _ :: _, .bvar _, _, h => h.elim
  | _ :: _, .sort _, _, h => h.elim
  | _ :: _, .const _ _, _, h => h.elim
  | _ :: _, .app _ _, _, h => h.elim
  | _ :: _, .lam _ _ _, _, h => h.elim

/-! ## Application chains -/

/-- A spine is well-denoted when its head and arguments are and their
values form a well-formed application chain. -/
theorem WellDenoted_mkAppN_of_spineOk (ρ : Nat → V) :
    ∀ {f : Expr} {args : List Expr}, WellDenoted M φ ρ f → (∀ a ∈ args, WellDenoted M φ ρ a) →
      SpineOk (interp M φ ρ f) (args.map (interp M φ ρ)) → WellDenoted M φ ρ (Expr.mkAppN f args)
  | _, [], hf, _, _ => hf
  | f, a :: args, hf, has, hok => by
    obtain ⟨⟨p, A, B, hslot, hmem, hB⟩, hrest⟩ := hok
    rw [Expr.mkAppN_cons]
    refine WellDenoted_mkAppN_of_spineOk ρ ?_ (fun b hb => has b (List.mem_cons_of_mem a hb)) hrest
    rw [WellDenoted_app]
    exact ⟨hf, has a List.mem_cons_self, p, A, B, hslot, hmem, hB⟩

/-- Values fitting a well-denoted telescope the head inhabits form a
well-formed application chain. -/
theorem spineOk_of_teleFitV :
    ∀ {vs : List V} {T : Expr} {ρ : Nat → V} {f : V}, WellDenoted M φ ρ T →
      f ∈ˢ interp M φ ρ T → TeleFitV M φ ρ T vs → SpineOk f vs
  | [], _, _, _, _, _, _ => by exact trivial
  | v :: vs, .pi A pw B, ρ, f, hT, hf, hfit => by
    obtain ⟨hmem, hfit'⟩ := hfit
    rw [WellDenoted_pi] at hT
    rw [interp_pi] at hf
    refine ⟨⟨pw.holds φ, _, _, hf, hmem, hT.2.2⟩, ?_⟩
    exact spineOk_of_teleFitV (hT.2.1 v hmem) (app_mem_piR hf hmem) hfit'
  | _ :: _, .bvar _, _, _, _, _, h => h.elim
  | _ :: _, .sort _, _, _, _, _, h => h.elim
  | _ :: _, .const _ _, _, _, _, _, h => h.elim
  | _ :: _, .app _ _, _, _, _, _, h => h.elim
  | _ :: _, .lam _ _ _, _, _, _, _, h => h.elim

end Fragment
