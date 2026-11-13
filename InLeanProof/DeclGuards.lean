module

public import InLeanProof.IndBasis
public import InLeanProof.StepPres
public import InLeanProof.LeafGuardI
/- `Expr.hasMVar`/`hasLooseBVars` read the computed fields, whose equations `Lean.Expr` does
not expose. -/
import all Lean.Expr

/-!
# O6: the declaration step's syntactic guards (task #451, lane O6)

InLean's declaration checks (`InLean/CheckerC.lean`: `checkTermWF`,
`checkConstantValC`, the literal names' shapes) against master's pure ones
(`ConLeche/Kernel/CheckerBase.lean`'s `checkConstantVal`, the value checks of
`ConLeche/Kernel/Checker.lean`).

* **Resolution from inference** (`crNF_of_infer`, `constsResolve_of_infer`).
  Master checks a declared term's constants syntactically
  (`Expr.constsResolve`: every constant, every projection's structure, the
  literals' support declarations); InLean's `checkTermWF` checks only the
  constants (`EO.usedConstants`, Lean's `getUsedConstants`).  The rest is what
  check-mode inference reads anyway: a projection's structure is found by its
  table (`findTable?` asks the name stored), a literal by `natLitStored`/
  `strLitStored`, and the full grade visits every subterm.  So master's
  check-mode inference succeeding on a term implies its resolution, and the
  simulation reads master's guard off the inference InLean ran.
* **The cached fields under `checkTermWF`** (`checkTermWF_ok`): on a term in
  range the cached tests are the structural ones (`Expr.fieldsOk`), so an
  accepted term is closed, has no free variable or metavariable, has a closed
  reading (`okC`), and its level parameters are declared
  (`levelParams_complete`: `EO.levelParams` collects every parameter of the
  term, the collecting walk's completeness with its `seen` skip and its
  `hasLevelParam` cut).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Resolution from master's inference -/

/-- `Expr.constsResolve` with every free variable resolving: what check-mode
inference establishes of the term it walks (a free variable's type was walked
where its binder was opened). -/
@[expose] def crNF (env : ConLeche.Env) : ConLeche.Expr → Bool
  | .bvar _ | .sort _ | .fvar _ _ => true
  | .lit (.natVal _) => ConLeche.natLitStored env
  | .lit (.strVal _) => ConLeche.strLitStored env
  | .const n _ => (env.find? n).isSome
  | .app f a => crNF env f && crNF env a
  | .lam t b | .forallE t b => crNF env t && crNF env b
  | .letE t v b => crNF env t && crNF env v && crNF env b
  | .proj s _ e => (env.find? s).isSome && crNF env e

/-- Without free variables, `crNF` is master's resolution. -/
theorem constsResolve_of_crNF {env : ConLeche.Env} :
    ∀ {e : ConLeche.Expr}, e.hasFvar = false → crNF env e = true → e.constsResolve env = true := by
  intro e
  induction e with
  | bvar | sort => intro _ _; rfl
  | fvar => intro h _; simp [ConLeche.Expr.hasFvar] at h
  | const => intro _ h; exact h
  | lit l =>
    cases l <;> intro _ h <;>
      simpa [crNF, ConLeche.Expr.constsResolve, ConLeche.natLitStored, ConLeche.strLitStored,
        Bool.and_assoc] using h
  | app f a ihf iha =>
    intro hf h
    simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [crNF, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.constsResolve, ihf hf.1 h.1, iha hf.2 h.2, Bool.and_self]
  | lam t b iht ihb | forallE t b iht ihb =>
    intro hf h
    simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [crNF, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.constsResolve, iht hf.1 h.1, ihb hf.2 h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro hf h
    simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [crNF, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.constsResolve, iht hf.1.1 h.1.1, ihv hf.1.2 h.1.2, ihb hf.2 h.2,
      Bool.and_self]
  | proj s i x ih =>
    intro hf h
    simp only [ConLeche.Expr.hasFvar] at hf
    simp only [crNF, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.constsResolve, h.1, ih hf h.2, Bool.and_self]

/-- Instantiation replaces bound variables only: what it resolves, the term
resolved. -/
theorem crNF_of_instantiate1 {env : ConLeche.Env} {v : ConLeche.Expr} :
    ∀ {e : ConLeche.Expr} (k : Nat), crNF env (e.instantiate1 v k) = true → crNF env e = true := by
  intro e
  induction e with
  | bvar => intro _ _; rfl
  | fvar | sort | const | lit => intro _ h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, crNF, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b iht ihb | forallE t b iht ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, crNF, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t x b iht ihx ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, crNF, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihx k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i x ih =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, crNF, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih k h.2⟩

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; exact nomatch h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem findProj_find {env : ConLeche.Env} {T : ConLeche.Name} {i : Nat} {pe : ConLeche.ProjEntry}
    (h : env.findProj? T i = some pe) : (env.find? T).isSome = true := by
  unfold ConLeche.Env.findProj? ConLeche.Env.findTable? at h
  by_cases hT : (env.find? T).isSome = true
  · exact hT
  · simp [hT] at h

/-- **Check-mode inference walks every constant**: master's full-grade
inference succeeding on `e` resolves it (free variables aside). -/
theorem crNF_of_infer {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env} :
    ∀ (F d : Nat) (e t : ConLeche.Expr),
      ConLeche.inferTypeCore mode eager env F d e = .ok t → crNF env e = true := by
  intro F
  induction F with
  | zero => intro d e t h; exact nomatch h
  | succ F ih =>
    intro d e t h
    have hI : ∀ d e t, (ConLeche.coreKnot mode eager env id F).infer d e = Except.ok t →
        crNF env e = true := ih
    change ConLeche.inferBody (ConLeche.coreKnot mode eager env id F) env d e = Except.ok t at h
    unfold ConLeche.inferBody at h
    cases e with
    | bvar => rfl
    | sort => rfl
    | fvar => rfl
    | const n us =>
      simp only [crNF]
      cases hf : env.find? n with
      | none => simp only [hf] at h; exact nomatch h
      | some => rfl
    | lit l =>
      cases l with
      | natVal =>
        simp only [crNF]
        cases hn : ConLeche.natLitStored env
        · simp only [hn] at h; exact nomatch h
        · rfl
      | strVal =>
        simp only [crNF]
        cases hn : ConLeche.strLitStored env
        · simp only [hn] at h; exact nomatch h
        · rfl
    | app f a =>
      obtain ⟨tf, h1, h⟩ := except_bind_ok h
      obtain ⟨w, -, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨ta, h3, -⟩ := except_bind_ok h
        simp only [crNF, hI _ _ _ h1, hI _ _ _ h3, Bool.and_self]
      · exact nomatch h
    | lam ty body =>
      obtain ⟨tty, h1, h⟩ := except_bind_ok h
      obtain ⟨w, -, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨bt, h3, -⟩ := except_bind_ok h
        simp only [crNF, hI _ _ _ h1, crNF_of_instantiate1 0 (hI _ _ _ h3), Bool.and_self]
      · exact nomatch h
    | forallE ty body =>
      obtain ⟨tty, h1, h⟩ := except_bind_ok h
      obtain ⟨w, -, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨bt, h3, -⟩ := except_bind_ok h
        simp only [crNF, hI _ _ _ h1, crNF_of_instantiate1 0 (hI _ _ _ h3), Bool.and_self]
      · exact nomatch h
    | letE ty v b =>
      obtain ⟨tty, h1, h⟩ := except_bind_ok h
      obtain ⟨_, -, h⟩ := except_bind_ok h
      obtain ⟨tv, h2, h⟩ := except_bind_ok h
      obtain ⟨ok, -, h⟩ := except_bind_ok h
      split at h
      · dsimp only at h
        simp only [crNF, hI _ _ _ h1, hI _ _ _ h2, crNF_of_instantiate1 0 (hI _ _ _ h), Bool.and_self]
      · obtain ⟨_, h3, -⟩ := except_bind_ok h
        exact nomatch h3
    | proj sn i pe =>
      obtain ⟨tp, h1, h⟩ := except_bind_ok h
      obtain ⟨te, -, h⟩ := except_bind_ok h
      split at h
      · split at h
        · rename_i T us _ entry hfp
          split at h
          · rename_i hc
            obtain ⟨rfl, -⟩ := hc
            simp only [crNF, findProj_find hfp, hI _ _ _ h1, Bool.and_self]
          · exact nomatch h
        · exact nomatch h
      · exact nomatch h

/-- **Master's resolution guard from its inference**, at a term without free
variables. -/
theorem constsResolve_of_infer {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {F d : Nat} {e t : ConLeche.Expr} (hf : e.hasFvar = false)
    (h : ConLeche.inferTypeCore mode eager env F d e = .ok t) : e.constsResolve env = true :=
  constsResolve_of_crNF hf (crNF_of_infer F d e t h)

/-! ## The cached flags of a term in range -/

theorem hasMVar_eq {e : Expr} (h : Expr.RangeOk e) : e.hasMVar = (emvarS e || elmvarS e) := by
  have F := Expr.fieldsOk e h
  show (e.data.hasExprMVar || e.data.hasLevelMVar) = _
  rw [F.emvar, F.lmvar]

theorem hasLooseBVars_eq {e : Expr} (h : Expr.RangeOk e) :
    e.hasLooseBVars = decide (0 < rangeS e) := by
  show decide (e.looseBVarRange > 0) = _
  rw [Expr.looseBVarRange_eq h]

theorem okL_of_lmvarS : ∀ {u : Level}, lmvarS u = false → okL u = true := by
  intro u; induction u <;> simp_all [lmvarS, okL]

/-- **A term in range without free variables and metavariables has a closed
reading.** -/
theorem okC_of_flags : ∀ {e : Expr}, Expr.RangeOk e → fvarS e = false → emvarS e = false →
    elmvarS e = false → okC e = true := by
  intro e
  induction e with
  | bvar i => intro hr _ _ _; simp only [okC, okE, decide_eq_true_eq]; exact hr
  | fvar => intro _ h; simp [fvarS] at h
  | mvar => intro _ _ h; simp [emvarS] at h
  | lit => intro _ _ _ _; rfl
  | sort u =>
    intro hr _ _ hl
    simp only [okC, okE, okLv, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨okL_of_lmvarS hl, hr⟩
  | const n us =>
    intro hr _ _ hl
    simp only [okC, okE, List.all_eq_true]
    intro u hu
    simp only [elmvarS, List.any_eq_false] at hl
    simp only [okLv, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨okL_of_lmvarS (by simpa using hl u hu), hr u hu⟩
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro hr h1 h2 h3
    simp only [fvarS, emvarS, elmvarS, Bool.or_eq_false_iff] at h1 h2 h3
    have := ihf hr.1 h1.1 h2.1 h3.1; have := iha hr.2 h1.2 h2.2 h3.2
    simp_all [okC, okE]
  | letE _ t v b _ iht ihv ihb =>
    intro hr h1 h2 h3
    simp only [fvarS, emvarS, elmvarS, Bool.or_eq_false_iff] at h1 h2 h3
    have := iht hr.1 h1.1.1 h2.1.1 h3.1.1; have := ihv hr.2.1 h1.1.2 h2.1.2 h3.1.2
    have := ihb hr.2.2 h1.2 h2.2 h3.2
    simp_all [okC, okE]
  | mdata _ x ih | proj _ _ x ih =>
    intro hr h1 h2 h3
    exact ih hr h1 h2 h3

/-! ## The collecting walk's completeness, generic

`EO.collect stop pick` (`InLean/ExprOps.lean`) pushes `pick` of every node it
reaches that `stop` does not cut, and skips a compound node already `seen`.
`OccS` is what it reaches; `collectG_go_spec` says every value at such a node
is collected (the `seen` skip loses nothing: a seen node's values were
collected when it was first walked, `CPreG`).  `LeafGuardI.lean` proves the
free-variable instance with its soundness; this one is generic in the collected
type and states completeness only. -/

section CollectG
attribute [local instance 3000] instBEqExprExact
attribute [local instance] instBEqExprExact_lawful

variable {α : Type} (stop : Expr → Bool) (pick : Expr → Option α)

/-- `a` is picked at a node of `e` the walk reaches. -/
@[expose] def OccS (a : α) : Expr → Prop
  | .app f x => stop (.app f x) = false ∧ (OccS a f ∨ OccS a x)
  | .lam n t b bi => stop (.lam n t b bi) = false ∧ (OccS a t ∨ OccS a b)
  | .forallE n t b bi => stop (.forallE n t b bi) = false ∧ (OccS a t ∨ OccS a b)
  | .letE n t v b nd => stop (.letE n t v b nd) = false ∧ (OccS a t ∨ OccS a v ∨ OccS a b)
  | .mdata m x => stop (.mdata m x) = false ∧ OccS a x
  | .proj s i x => stop (.proj s i x) = false ∧ OccS a x
  | .bvar i => stop (.bvar i) = false ∧ pick (.bvar i) = some a
  | .fvar i => stop (.fvar i) = false ∧ pick (.fvar i) = some a
  | .mvar i => stop (.mvar i) = false ∧ pick (.mvar i) = some a
  | .sort u => stop (.sort u) = false ∧ pick (.sort u) = some a
  | .const n us => stop (.const n us) = false ∧ pick (.const n us) = some a
  | .lit l => stop (.lit l) = false ∧ pick (.lit l) = some a

/-- Every node of `seen` up to size `sz` has its values in `acc`. -/
@[expose] def CPreG (seen : Std.HashSet Expr) (acc : Array α) (sz : Nat) : Prop :=
  ∀ x, seen.contains x = true → sizeOf x ≤ sz → ∀ a, OccS stop pick a x → a ∈ acc

/-- One call of the walk, for the values `P` of what it walks, at size bound
`sz`: it keeps `acc` and `seen`, adds to `seen` only nodes up to `sz`, and
under `CPreG` keeps it and collects `P`. -/
@[expose] def GoSpecG (P : α → Prop) (sz : Nat) (seen : Std.HashSet Expr) (acc : Array α)
    (r : Std.HashSet Expr × Array α) : Prop :=
  (∀ a, a ∈ acc → a ∈ r.2) ∧
  (∀ x, seen.contains x = true → r.1.contains x = true) ∧
  (∀ x, r.1.contains x = true → seen.contains x = true ∨ sizeOf x ≤ sz) ∧
  (CPreG stop pick seen acc sz → CPreG stop pick r.1 r.2 sz ∧ ∀ a, P a → a ∈ r.2)

variable {stop pick}

theorem GoSpecG.seq {P Q : α → Prop} {sz₁ sz₂ : Nat} {seen : Std.HashSet Expr}
    {acc : Array α} {r₁ r₂ : Std.HashSet Expr × Array α}
    (h₁ : GoSpecG stop pick P sz₁ seen acc r₁) (h₂ : GoSpecG stop pick Q sz₂ r₁.1 r₁.2 r₂) :
    GoSpecG stop pick (fun a => P a ∨ Q a) (max sz₁ sz₂) seen acc r₂ := by
  obtain ⟨m₁, c₁, n₁, k₁⟩ := h₁
  obtain ⟨m₂, c₂, n₂, k₂⟩ := h₂
  refine ⟨fun a ha => m₂ a (m₁ a ha), fun x hx => c₂ x (c₁ x hx), fun x hx => ?_, fun hpre => ?_⟩
  · rcases n₂ x hx with h | h
    · rcases n₁ x h with h' | h'
      · exact .inl h'
      · exact .inr (by omega)
    · exact .inr (by omega)
  · have hpre₁ : CPreG stop pick seen acc sz₁ := fun x hx hs a ha => hpre x hx (by omega) a ha
    obtain ⟨post₁, comp₁⟩ := k₁ hpre₁
    have hpre₂ : CPreG stop pick r₁.1 r₁.2 sz₂ := by
      intro x hx hs a ha
      by_cases hle : sizeOf x ≤ sz₁
      · exact post₁ x hx hle a ha
      · rcases n₁ x hx with h | h
        · exact m₁ a (hpre x h (by omega) a ha)
        · exact absurd h hle
    obtain ⟨post₂, comp₂⟩ := k₂ hpre₂
    refine ⟨fun x hx hs a ha => ?_, fun a ha => ?_⟩
    · by_cases hle₂ : sizeOf x ≤ sz₂
      · exact post₂ x hx hle₂ a ha
      · rcases n₂ x hx with h | h
        · by_cases hle₁ : sizeOf x ≤ sz₁
          · exact m₂ a (post₁ x h hle₁ a ha)
          · rcases n₁ x h with h' | h'
            · exact m₂ a (m₁ a (hpre x h' hs a ha))
            · exact absurd h' hle₁
        · exact absurd h hle₂
    · rcases ha with ha | ha
      · exact m₂ a (comp₁ a ha)
      · exact comp₂ a ha

theorem GoSpecG.wrap {P : α → Prop} {sz : Nat} {e : Expr} {seen : Std.HashSet Expr}
    {acc : Array α} {r : Std.HashSet Expr × Array α}
    (hsz : sz < sizeOf e) (hP : ∀ a, OccS stop pick a e → P a)
    (h : GoSpecG stop pick P sz (seen.insert e) acc r) :
    GoSpecG stop pick (fun a => OccS stop pick a e) (sizeOf e) seen acc r := by
  obtain ⟨m, c, n, k⟩ := h
  refine ⟨m, fun x hx => c x ?_, fun x hx => ?_, fun hpre => ?_⟩
  · rw [Std.HashSet.contains_insert, hx, Bool.or_true]
  · rcases n x hx with h | h
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; exact .inr (Nat.le_refl _)
      · exact .inl h
    · exact .inr (by omega)
  · have hpre' : CPreG stop pick (seen.insert e) acc sz := by
      intro x hx hs a ha
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx | hx
      · subst hx; omega
      · exact hpre x hx (by omega) a ha
    obtain ⟨post, comp⟩ := k hpre'
    have compE : ∀ a, OccS stop pick a e → a ∈ r.2 := fun a ha => comp a (hP a ha)
    refine ⟨fun x hx hs a ha => ?_, compE⟩
    by_cases hle : sizeOf x ≤ sz
    · exact post x hx hle a ha
    · rcases n x hx with h | h
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · subst h; exact compE a ha
        · exact m a (hpre x h hs a ha)
      · exact absurd h hle

theorem GoSpecG.seen {e : Expr} {seen : Std.HashSet Expr} {acc : Array α}
    (h : seen.contains e = true) :
    GoSpecG stop pick (fun a => OccS stop pick a e) (sizeOf e) seen acc (seen, acc) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => .inl h,
    fun hpre => ⟨hpre, fun a ha => hpre e h (Nat.le_refl _) a ha⟩⟩

/-- A stopped node: nothing is collected. -/
theorem GoSpecG.stopped {e : Expr} {seen : Std.HashSet Expr} {acc : Array α}
    (hs : stop e = true) (hno : ∀ a, ¬ OccS stop pick a e) :
    GoSpecG stop pick (fun a => OccS stop pick a e) (sizeOf e) seen acc
      (EO.collect.go stop pick e seen acc) := by
  unfold EO.collect.go
  simp only [hs, ↓reduceIte]
  exact ⟨fun _ h => h, fun _ h => h, fun _ h => .inl h,
    fun hpre => ⟨hpre, fun a ha => absurd ha (hno a)⟩⟩

/-- A leaf: its pick is pushed (the walk does not descend). -/
theorem GoSpecG.leaf {e : Expr} {seen : Std.HashSet Expr} {acc : Array α}
    (hs : stop e = false) (hc : EO.isCompound e = false)
    (hocc : ∀ a, OccS stop pick a e → pick e = some a) :
    GoSpecG stop pick (fun a => OccS stop pick a e) (sizeOf e) seen acc
      (EO.collect.go stop pick e seen acc) := by
  unfold EO.collect.go
  simp only [hs, Bool.false_eq_true, ↓reduceIte, hc, Bool.not_false]
  have hmono : ∀ a, a ∈ acc → a ∈ (match pick e with | some a => acc.push a | none => acc) := by
    intro a h; split
    · exact Array.mem_push_of_mem _ h
    · exact h
  refine ⟨hmono, fun _ h => h, fun _ h => .inl h,
    fun hpre => ⟨fun x hx hsz a ha => hmono a (hpre x hx hsz a ha), fun a ha => ?_⟩⟩
  rw [hocc a ha]; exact Array.mem_push_self

variable (hcomp : ∀ x, EO.isCompound x = true → pick x = none)
include hcomp

theorem collectG_go_spec : ∀ (e : Expr) (seen : Std.HashSet Expr) (acc : Array α),
    GoSpecG stop pick (fun a => OccS stop pick a e) (sizeOf e) seen acc
      (EO.collect.go stop pick e seen acc) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro seen acc
    by_cases hs : stop (.app f a) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.app f a) = false := by simpa using hs
    have hp := hcomp (.app f a) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.app f a)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs'] using h) ((ihf _ acc).seq (iha _ _))
      simp only [Expr.app.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | lam n t b bi iht ihb =>
    intro seen acc
    by_cases hs : stop (.lam n t b bi) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.lam n t b bi) = false := by simpa using hs
    have hp := hcomp (.lam n t b bi) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.lam n t b bi)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs'] using h) ((iht _ acc).seq (ihb _ _))
      simp only [Expr.lam.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | forallE n t b bi iht ihb =>
    intro seen acc
    by_cases hs : stop (.forallE n t b bi) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.forallE n t b bi) = false := by simpa using hs
    have hp := hcomp (.forallE n t b bi) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.forallE n t b bi)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs'] using h) ((iht _ acc).seq (ihb _ _))
      simp only [Expr.forallE.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | letE n t v b nd iht ihv ihb =>
    intro seen acc
    by_cases hs : stop (.letE n t v b nd) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.letE n t v b nd) = false := by simpa using hs
    have hp := hcomp (.letE n t v b nd) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.letE n t v b nd)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs', or_assoc] using h)
        (((iht _ acc).seq (ihv _ _)).seq (ihb _ _))
      simp only [Expr.letE.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | mdata m x ih =>
    intro seen acc
    by_cases hs : stop (.mdata m x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.mdata m x) = false := by simpa using hs
    have hp := hcomp (.mdata m x) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.mdata m x)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs'] using h) (ih _ acc)
      simp only [Expr.mdata.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | proj sn i x ih =>
    intro seen acc
    by_cases hs : stop (.proj sn i x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    have hs' : stop (.proj sn i x) = false := by simpa using hs
    have hp := hcomp (.proj sn i x) rfl
    unfold EO.collect.go
    simp only [hs', Bool.false_eq_true, ↓reduceIte, hp, EO.isCompound, Bool.not_true]
    cases hc : seen.contains (.proj sn i x)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine GoSpecG.wrap ?_ (fun _ h => by simpa [OccS, hs'] using h) (ih _ acc)
      simp only [Expr.proj.sizeOf_spec]; omega
    · simp only [↓reduceIte]; exact GoSpecG.seen hc
  | bvar x =>
    intro seen acc
    by_cases hs : stop (.bvar x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)
  | fvar x =>
    intro seen acc
    by_cases hs : stop (.fvar x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)
  | mvar x =>
    intro seen acc
    by_cases hs : stop (.mvar x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)
  | sort x =>
    intro seen acc
    by_cases hs : stop (.sort x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)
  | const x us =>
    intro seen acc
    by_cases hs : stop (.const x us) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)
  | lit x =>
    intro seen acc
    by_cases hs : stop (.lit x) = true
    · exact GoSpecG.stopped hs (fun _ h => by simp [OccS, hs] at h)
    · exact GoSpecG.leaf (by simpa using hs) rfl (fun a h => h.2)

/-- **Completeness of `EO.collect`**: every value picked at a node the walk
reaches is collected. -/
theorem collect_complete (e : Expr) {a : α} (h : OccS stop pick a e) :
    a ∈ EO.collect stop pick e := by
  unfold EO.collect
  have := (collectG_go_spec (stop := stop) hcomp e
    (Std.HashSet.emptyWithCapacity (e.approxDepth.toNat + 8)) #[]).2.2.2
    (fun x hx => by simp at hx)
  exact this.2 a h

end CollectG

/-! ## `EO.levelParams`: every level parameter of a term is collected -/

/-- `p` is a parameter of `u`. -/
@[expose] def LpIn (p : Name) : Level → Prop
  | .param n => n = p
  | .succ u => LpIn p u
  | .max u v | .imax u v => LpIn p u ∨ LpIn p v
  | .zero | .mvar _ => False

theorem lvl_spec (p : Name) : ∀ (u : Level) (acc : Array Name),
    (∀ n, n ∈ acc → n ∈ EO.levelParams.lvl u acc) ∧ (LpIn p u → p ∈ EO.levelParams.lvl u acc) := by
  intro u
  induction u with
  | zero => intro acc; exact ⟨fun _ h => by simpa [EO.levelParams.lvl] using h, fun h => h.elim⟩
  | mvar => intro acc; exact ⟨fun _ h => by simpa [EO.levelParams.lvl] using h, fun h => h.elim⟩
  | param n =>
    intro acc
    simp only [EO.levelParams.lvl, LpIn]
    split
    · rename_i hc
      exact ⟨fun _ h => h, fun h => by subst h; exact Array.contains_iff_mem.1 hc⟩
    · exact ⟨fun _ h => Array.mem_push_of_mem _ h, fun h => by subst h; exact Array.mem_push_self⟩
  | succ u ih => intro acc; exact ih acc
  | max u v ihu ihv | imax u v ihu ihv =>
    intro acc
    refine ⟨fun n h => (ihv _).1 n ((ihu acc).1 n h), fun h => ?_⟩
    rcases h with h | h
    · exact (ihv _).1 p ((ihu acc).2 h)
    · exact (ihv _).2 h

theorem lvlList_spec (p : Name) : ∀ (us : List Level) (acc : Array Name),
    (∀ n, n ∈ acc → n ∈ us.foldl (fun acc u => EO.levelParams.lvl u acc) acc) ∧
    (∀ u ∈ us, LpIn p u → p ∈ us.foldl (fun acc u => EO.levelParams.lvl u acc) acc) := by
  intro us
  induction us with
  | nil => intro acc; exact ⟨fun _ h => h, fun _ h => by cases h⟩
  | cons u us ih =>
    intro acc
    simp only [List.foldl_cons]
    refine ⟨fun n h => (ih _).1 n ((lvl_spec p u acc).1 n h), fun v hv hp => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact (ih _).1 p ((lvl_spec p v acc).2 hp)
    · exact (ih _).2 v hv hp

theorem lvlAll_spec (p : Name) : ∀ (all : List (List Level)) (acc : Array Name),
    (∀ n, n ∈ acc → n ∈ all.foldl (fun acc us => us.foldl (fun acc u => EO.levelParams.lvl u acc) acc) acc) ∧
    (∀ us ∈ all, ∀ u ∈ us, LpIn p u →
      p ∈ all.foldl (fun acc us => us.foldl (fun acc u => EO.levelParams.lvl u acc) acc) acc) := by
  intro all
  induction all with
  | nil => intro acc; exact ⟨fun _ h => h, fun _ h => by cases h⟩
  | cons us all ih =>
    intro acc
    simp only [List.foldl_cons]
    refine ⟨fun n h => (ih _).1 n ((lvlList_spec p us acc).1 n h), fun vs hv u hu hp => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact (ih _).1 p ((lvlList_spec p vs acc).2 u hu hp)
    · exact (ih _).2 vs hv u hu hp

/-- The level lists `EO.levelParams` picks. -/
@[expose] def lpPick : Expr → Option (List Level)
  | .sort u => some [u]
  | .const _ us => some us
  | _ => none

theorem lpPick_compound : ∀ x, EO.isCompound x = true → lpPick x = none := by
  intro x hx; cases x <;> first | rfl | simp [EO.isCompound] at hx

theorem levelParams_eq (e : Expr) :
    EO.levelParams e = (EO.collect (fun x => !x.hasLevelParam) lpPick e).foldl
      (fun acc us => us.foldl (fun acc u => EO.levelParams.lvl u acc) acc) #[] := by
  unfold EO.levelParams
  congr 2

theorem levelParams_complete {e : Expr} {us : List Level} {u : Level} {p : Name}
    (h : OccS (fun x => !x.hasLevelParam) lpPick us e) (hu : u ∈ us) (hp : LpIn p u) :
    p ∈ EO.levelParams e := by
  rw [levelParams_eq, ← Array.foldl_toList]
  exact (lvlAll_spec p _ #[]).2 us
    (Array.mem_toList_iff.2 (collect_complete lpPick_compound e h)) u hu hp

theorem allParamsDefined_trL (lps : List Name) :
    ∀ {u : Level}, (∀ p, LpIn p u → p ∈ lps) →
      ConLeche.Level.allParamsDefined (lps.map toName) (trL u) = true := by
  intro u
  induction u with
  | zero | mvar => intro _; rfl
  | param n =>
    intro h
    simp only [trL, ConLeche.Level.allParamsDefined, contains_map_toName, List.contains_iff_mem]
    exact h n rfl
  | succ u ih => intro h; exact ih h
  | max u v ihu ihv | imax u v ihu ihv =>
    intro h
    simp only [trL, ConLeche.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨ihu fun p hp => h p (.inl hp), ihv fun p hp => h p (.inr hp)⟩

theorem allParamsDefined_of_lparamS (ps : List ConLeche.Name) :
    ∀ {u : Level}, lparamS u = false → ConLeche.Level.allParamsDefined ps (trL u) = true := by
  intro u
  induction u <;> simp_all [lparamS, trL, ConLeche.Level.allParamsDefined]

theorem allLevelParamsDefined_of_elparamS (ps : List ConLeche.Name) :
    ∀ {e : Expr}, elparamS e = false → (trC e).allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar | fvar | mvar | lit => intro _; rfl
  | sort u =>
    intro h
    exact allParamsDefined_of_lparamS ps h
  | const n us =>
    intro h
    simp only [elparamS, List.any_eq_false, Bool.not_eq_true] at h
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, List.all_map, List.all_eq_true,
      Function.comp_apply]
    exact fun u hu => allParamsDefined_of_lparamS ps (h u hu)
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro h
    simp only [elparamS, Bool.or_eq_false_iff] at h
    have h1 := ihf h.1; have h2 := iha h.2
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h
    simp only [elparamS, Bool.or_eq_false_iff] at h
    have h1 := iht h.1.1; have h2 := ihv h.1.2; have h3 := ihb h.2
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 h3 ⊢
    exact ⟨⟨h1, h2⟩, h3⟩
  | mdata _ x ih => intro h; exact ih h
  | proj _ _ x ih => intro h; exact ih h

/-- **Declared level parameters**: every parameter `EO.levelParams` would
collect is declared, so master's test holds of the translation. -/
theorem allLevelParamsDefined_of_occ (lps : List Name) :
    ∀ {e : Expr}, Expr.RangeOk e →
      (∀ us u p, OccS (fun x => !x.hasLevelParam) lpPick us e → u ∈ us → LpIn p u → p ∈ lps) →
      (trC e).allLevelParamsDefined (lps.map toName) = true := by
  intro e
  induction e with
  | bvar | fvar | mvar | lit => intro _ _; rfl
  | sort u =>
    intro hr H
    cases hs : (Expr.sort u).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · exact allParamsDefined_trL lps fun p hp =>
        H [u] u p ⟨by simp [hs], rfl⟩ (List.mem_singleton_self u) hp
  | const n us =>
    intro hr H
    cases hs : (Expr.const n us).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, List.all_map, List.all_eq_true,
        Function.comp_apply]
      exact fun u hu => allParamsDefined_trL lps fun p hp => H us u p ⟨by simp [hs], rfl⟩ hu hp
  | app f a ihf iha =>
    intro hr H
    cases hs : (Expr.app f a).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.app f a) = false := by simp [hs]
      have h1 := ihf hr.1 fun us u p h => H us u p ⟨hs', .inl h⟩
      have h2 := iha hr.2 fun us u p h => H us u p ⟨hs', .inr h⟩
      simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1, h2⟩
  | lam n t b bi iht ihb =>
    intro hr H
    cases hs : (Expr.lam n t b bi).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.lam n t b bi) = false := by simp [hs]
      have h1 := iht hr.1 fun us u p h => H us u p ⟨hs', .inl h⟩
      have h2 := ihb hr.2 fun us u p h => H us u p ⟨hs', .inr h⟩
      simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1, h2⟩
  | forallE n t b bi iht ihb =>
    intro hr H
    cases hs : (Expr.forallE n t b bi).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.forallE n t b bi) = false := by simp [hs]
      have h1 := iht hr.1 fun us u p h => H us u p ⟨hs', .inl h⟩
      have h2 := ihb hr.2 fun us u p h => H us u p ⟨hs', .inr h⟩
      simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1, h2⟩
  | letE n t v b nd iht ihv ihb =>
    intro hr H
    cases hs : (Expr.letE n t v b nd).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.letE n t v b nd) = false := by simp [hs]
      have h1 := iht hr.1 fun us u p h => H us u p ⟨hs', .inl h⟩
      have h2 := ihv hr.2.1 fun us u p h => H us u p ⟨hs', .inr (.inl h)⟩
      have h3 := ihb hr.2.2 fun us u p h => H us u p ⟨hs', .inr (.inr h)⟩
      simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at h1 h2 h3 ⊢
      exact ⟨⟨h1, h2⟩, h3⟩
  | mdata m x ih =>
    intro hr H
    cases hs : (Expr.mdata m x).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.mdata m x) = false := by simp [hs]
      exact ih hr fun us u p h => H us u p ⟨hs', h⟩
  | proj s i x ih =>
    intro hr H
    cases hs : (Expr.proj s i x).hasLevelParam
    · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hs)
    · have hs' : (fun x => !x.hasLevelParam) (Expr.proj s i x) = false := by simp [hs]
      exact ih hr fun us u p h => H us u p ⟨hs', h⟩

/-- **InLean's level-parameter guard is master's**, on a term in range. -/
theorem allLevelParamsDefined_of_guard {lps : List Name} {e : Expr} (hr : Expr.RangeOk e)
    (h : e.hasLevelParam = true → (EO.levelParams e).all lps.contains = true) :
    (trC e).allLevelParamsDefined (lps.map toName) = true := by
  cases hl : e.hasLevelParam
  · exact allLevelParamsDefined_of_elparamS _ (by rw [← Expr.hasLevelParam_eq hr]; exact hl)
  · have h' := h hl
    refine allLevelParamsDefined_of_occ lps hr fun us u p ho hu hp => ?_
    have := Array.all_eq_true_iff_forall_mem.1 h' p (levelParams_complete ho hu hp)
    simpa using this

/-! ## `checkTermWF` -/

theorem throw_bindI_ok {α β : Type} {e : InLean.CheckError} {f : α → InLean.CheckCM β}
    {s₀ : InLean.CState} {v : β} {s' : InLean.CState}
    (h : ((throw e : InLean.CheckCM α) >>= f) s₀ = .ok (v, s')) : False := by
  obtain ⟨_, _, h1, _⟩ := bindI_ok h
  exact throwI_ok h1

/-- **What an accepted `checkTermWF` read**: the cached flags, the level
parameters; no state change. -/
theorem checkTermWF_run {fe : InLean.FEnv} {pre : String} {n : Name} {lps : List Name} {e : Expr}
    {s s' : InLean.CState} {u : Unit} (h : InLean.checkTermWF fe pre n lps e s = .ok (u, s')) :
    s' = s ∧ e.hasLooseBVars = false ∧ e.hasFVar = false ∧ e.hasMVar = false ∧
      (e.hasLevelParam = true → (EO.levelParams e).all lps.contains = true) := by
  unfold InLean.checkTermWF at h
  dsimp only at h
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i h1
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i h2
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i h3
  have hfin : ∀ {s₁ : InLean.CState},
      (if InLean.constsResolve fe e = true then pure ()
        else throw (InLean.unresolvedConstsErrorL fe (strLitStoredF fe) s!"{pre}{n}" e) : InLean.CheckCM Unit)
        s₁ = .ok (u, s') → s' = s₁ := by
    intro s₁ hh
    split at hh
    · exact (pureI_ok hh).2.symm
    · exact (throwI_ok hh).elim
  split at h
  · rename_i h4
    split at h
    · rename_i h5
      exact ⟨hfin h, by simpa using h1, by simpa using h2, by simpa using h3, fun _ => h5⟩
    · exact (throw_bindI_ok h).elim
  · rename_i h4
    exact ⟨hfin h, by simpa using h1, by simpa using h2, by simpa using h3,
      fun hh => absurd hh h4⟩

theorem lbb_trC_of_range {e : Expr} (hr : Expr.RangeOk e) (hok : okC e = true)
    (h : e.hasLooseBVars = false) : (trC e).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.looseBVarsBounded_iff,
    bvarBound_toExpr (fv := fun _ => none) (fun _ _ h => nomatch h) e (trC e) (toExprC_of_okC hok)]
  rw [hasLooseBVars_eq hr] at h
  simpa using h

/-- **An accepted term in range**, read as master's guards read its
translation (resolution aside: `constsResolve_of_infer`). -/
theorem checkTermWF_ok {fe : InLean.FEnv} {pre : String} {n : Name} {lps : List Name} {e : Expr}
    {s s' : InLean.CState} {u : Unit} (hr : Expr.RangeOk e)
    (h : InLean.checkTermWF fe pre n lps e s = .ok (u, s')) :
    s' = s ∧ okC e = true ∧ (trC e).looseBVarsBounded 0 = true ∧ (trC e).hasFvar = false ∧
      (trC e).allLevelParamsDefined (lps.map toName) = true := by
  obtain ⟨hs, h1, h2, h3, h4⟩ := checkTermWF_run h
  have hf : fvarS e = false := by rw [← Expr.hasFVar_eq hr]; exact h2
  rw [hasMVar_eq hr, Bool.or_eq_false_iff] at h3
  have hok := okC_of_flags hr hf h3.1 h3.2
  exact ⟨hs, hok, lbb_trC_of_range hr hok h1, trC_hasFvar e, allLevelParamsDefined_of_guard hr h4⟩

/-! ## The literal names' shapes -/

theorem trC_of_clEq {a b : Expr} (ha : okC a = true) (hb : okC b = true)
    (h : Expr.clEq a b = true) : trC a = trC b := by
  have := toExpr_of_clEq (fun _ => none) h
  rw [show toExpr (fun _ => none) a = some (trC a) from toExprC_of_okC ha,
    show toExpr (fun _ => none) b = some (trC b) from toExprC_of_okC hb] at this
  exact Option.some.inj this

theorem cl_litNames :
    toName InLean.natName = ConLeche.natName ∧ toName InLean.natZeroName = ConLeche.natZeroName ∧
    toName InLean.natSuccName = ConLeche.natSuccName ∧
    toName InLean.stringName = ConLeche.stringName ∧
    toName InLean.stringOfListName = ConLeche.stringOfListName ∧
    toName InLean.listName = ConLeche.listName ∧ toName InLean.listNilName = ConLeche.listNilName ∧
    toName InLean.listConsName = ConLeche.listConsName ∧ toName InLean.charName = ConLeche.charName ∧
    toName InLean.charOfNatName = ConLeche.charOfNatName :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem okC_shape_param (p : Name) : okLv (.succ (.param p)) = true := by
  simp [okLv, okL, depthS, maxLevelDepth]

/-- **InLean's literal-name shapes are master's**, on a type with a closed
reading. -/
theorem litShapeOk_tr {n : Name} {lps : List Name} {ty : Expr}
    (hok : okC ty = true)
    (h : InLean.litShapeOk n lps ty = true) :
    ConLeche.litShapeOk (.axiomInfo ⟨toName n, lps.map toName, trC ty⟩) = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := cl_litNames
  have tr : ∀ {X : Name}, n ≠ X → toName n ≠ toName X := fun hx e => hx (toName_inj e)
  have hn : (ConLeche.ConstantInfo.axiomInfo ⟨toName n, lps.map toName, trC ty⟩).name = toName n :=
    rfl
  unfold InLean.litShapeOk at h
  unfold ConLeche.litShapeOk
  rw [hn]
  by_cases hN : n = InLean.natName
  · subst hN
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [c1, trC_of_clEq hok (by decide) ht]
    simp [ConLeche.natIndOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL]
  have tN : toName n ≠ ConLeche.natName := c1 ▸ tr hN
  simp only [tN, ↓reduceIte]
  simp only [beq_iff_eq, hN, ↓reduceIte] at h
  by_cases hZ : n = InLean.natZeroName
  · subst hZ
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [c2, trC_of_clEq hok (by decide) ht]
    simp +decide [ConLeche.natZeroOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE,
      InLean.natTy, c1]
  have tZ : toName n ≠ ConLeche.natZeroName := c2 ▸ tr hZ
  simp only [tZ, ↓reduceIte]
  simp only [hZ, ↓reduceIte] at h
  by_cases hS : n = InLean.natSuccName
  · subst hS
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [c3, trC_of_clEq hok (by decide) ht]
    simp +decide [ConLeche.natSuccOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE,
      InLean.natTy, c1]
  have tS : toName n ≠ ConLeche.natSuccName := c3 ▸ tr hS
  simp only [tS, ↓reduceIte]
  simp only [hS, ↓reduceIte] at h
  by_cases h4 : n = InLean.stringName
  · rw [h4, c4]
    rw [h4] at h
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [trC_of_clEq hok (by decide) ht]
    simp [ConLeche.stringTyOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL]
  simp only [h4, ↓reduceIte] at h
  simp only [show toName n ≠ ConLeche.stringName from c4 ▸ tr h4, ↓reduceIte]
  have t4 := c4 ▸ tr h4
  by_cases h9 : n = InLean.charName
  · rw [h9] at h
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [h9, c9, trC_of_clEq hok (by decide) ht]
    simp +decide [ConLeche.charTyOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL]
  simp only [h9, ↓reduceIte] at h
  have t9 := c9 ▸ tr h9
  by_cases h10 : n = InLean.charOfNatName
  · rw [h10] at h
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [h10, c10, trC_of_clEq hok (by decide) ht]
    simp +decide [ConLeche.charOfNatTyOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE,
      InLean.natTy, InLean.charTy, c1, c9]
  simp only [h10, ↓reduceIte] at h
  have t10 := c10 ▸ tr h10
  by_cases h5 : n = InLean.stringOfListName
  · rw [h5] at h
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff, InLean.tyIs] at h
    obtain ⟨hl, ht⟩ := h
    rw [h5, c5, trC_of_clEq hok (by decide) ht]
    simp +decide [ConLeche.stringOfListTyOk, hl, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL,
      InLean.charTy, c4, c6, c9]
  simp only [h5, ↓reduceIte] at h
  have t5 := c5 ▸ tr h5
  by_cases h6 : n = InLean.listName
  · rw [h6] at h
    simp only [↓reduceIte, Bool.and_eq_true, InLean.tyIs, beq_iff_eq] at h
    obtain ⟨hl, ht⟩ := h
    match lps, hl, ht with
    | [p], _, ht =>
      rw [h6, c6, trC_of_clEq hok (by simp [okC, okE, okC_shape_param]) ht]
      simp +decide [ConLeche.listTyOk, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL]
  simp only [h6, ↓reduceIte] at h
  have t6 := c6 ▸ tr h6
  by_cases h7 : n = InLean.listNilName
  · rw [h7] at h
    simp only [↓reduceIte, Bool.and_eq_true, InLean.tyIs, beq_iff_eq] at h
    obtain ⟨hl, ht⟩ := h
    match lps, hl, ht with
    | [p], _, ht =>
      rw [h7, c7, trC_of_clEq hok (by simp [okC, okE, okLv, okL, maxRange, depthS, maxLevelDepth]) ht]
      simp +decide [ConLeche.listNilTyOk, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL, c6]
  simp only [h7, ↓reduceIte] at h
  have t7 := c7 ▸ tr h7
  by_cases h8 : n = InLean.listConsName
  · rw [h8] at h
    simp only [↓reduceIte, Bool.and_eq_true, InLean.tyIs, beq_iff_eq] at h
    obtain ⟨hl, ht⟩ := h
    match lps, hl, ht with
    | [p], _, ht =>
      rw [h8, c8, trC_of_clEq hok (by simp [okC, okE, okLv, okL, maxRange, depthS, maxLevelDepth]) ht]
      simp +decide [ConLeche.listConsTyOk, ConLeche.ConstantInfo.toConstantVal, trC, trE, trL, c6]
  have t8 := c8 ▸ tr h8
  simp [t5, t6, t7, t8, t9, t10]

/-- `natOpName` at the translation. -/
theorem natOpName_tr (n : Name) : ConLeche.natOpName (toName n) = InLean.natOpName n := by
  have h1 : ConLeche.natOpNames = InLean.natOpNames.map toName := rfl
  have h2 : ConLeche.natDivModNames = InLean.natDivModNames.map toName := rfl
  simp only [ConLeche.natOpName, InLean.natOpName, h1, h2, contains_map_toName]

end InLeanProof
