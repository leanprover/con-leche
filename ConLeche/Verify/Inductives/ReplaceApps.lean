module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift
public import ConLeche.Verify.Subst
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLemmas

public section

/-!
# The whole-application replacement, syntactically

`Expr.replaceApps f b n` (`Kernel/Inductives/Positivity.lean`) replaces
every subterm that is a constant applied to exactly the placeholder
variables `fvar b, …, fvar (b + n - 1)` — a WHOLE application `c.{us} q⃗`
that `f` maps — by its image, pre-order.  Everything it leaves is the
input's structure, so every structural fact about the input and the
images is a fact about the result: scoping (`WScoped.replaceApps`,
`looseBVarsBounded_replaceApps`), leaves (`fvarLeaves_replaceApps`),
closedness (`hasFvar_replaceApps`), and erasure (`replaceApps_erasedEq`:
the hits read only free-variable indices and constant names and levels).
-/

namespace ConLeche.Expr

/-! ## The hits -/

theorem appHole?_some {f : Name → List Level → Option Expr} {b n : Nat} {e h : Expr}
    (hh : e.appHole? f b n = some h) : ∃ c us, f c us = some h := by
  unfold appHole? at hh
  cases hp : e.phApp? b n with
  | none => rw [hp] at hh; exact nomatch hh
  | some p => rw [hp] at hh; exact ⟨p.1, p.2, hh⟩

theorem phApp?_lam {b n : Nat} {t body : Expr} {m : BinderMeta} :
    (Expr.lam t body m).phApp? b n = none := by cases n <;> rfl

/-- The one-node unfolding at an application. -/
theorem replaceApps_app (f : Name → List Level → Option Expr) (b n : Nat) (a x : Expr) :
    (Expr.app a x).replaceApps f b n =
      match (Expr.app a x).appHole? f b n with
      | some h => h
      | none => .app (a.replaceApps f b n) (x.replaceApps f b n) := by
  rw [replaceApps]
  cases (Expr.app a x).appHole? f b n <;> rfl

theorem replaceApps_const (f : Name → List Level → Option Expr) (b n : Nat) (c : Name)
    (us : List Level) :
    (Expr.const c us).replaceApps f b n =
      match (Expr.const c us).appHole? f b n with
      | some h => h
      | none => .const c us := by
  rw [replaceApps]
  cases (Expr.const c us).appHole? f b n <;> rfl

/-! ## Structural facts -/

/-- **A property built bottom-up survives the replacement** when every
image has it. -/
theorem replaceApps_rec {P : Expr → Prop} {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us h, f c us = some h → P h)
    (happ : ∀ a x, P a → P x → P (.app a x))
    (hlam : ∀ t body m, P t → P body → P (.lam t body m))
    (hpi : ∀ t body m, P t → P body → P (.forallE t body m))
    (hlet : ∀ t v body, P t → P v → P body → P (.letE t v body))
    (hproj : ∀ s i x, P x → P (.proj s i x))
    (hbvar : ∀ i, P (.bvar i)) (hfvar : ∀ i ty, P (.fvar i ty)) (hsort : ∀ u, P (.sort u))
    (hconst : ∀ c us, P (.const c us)) (hlit : ∀ l, P (.lit l)) :
    ∀ e : Expr, P (e.replaceApps f b n) := by
  intro e
  induction e with
  | bvar i => exact hbvar i
  | fvar i ty _ => exact hfvar i ty
  | sort u => exact hsort u
  | lit l => exact hlit l
  | const c us =>
    rw [replaceApps_const]
    split
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact hf _ _ _ hc
    · exact hconst c us
  | app a x iha ihx =>
    rw [replaceApps_app]
    split
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact hf _ _ _ hc
    · exact happ _ _ iha ihx
  | lam t body m iht ihb => exact hlam _ _ _ iht ihb
  | forallE t body m iht ihb => exact hpi _ _ _ iht ihb
  | letE t v body iht ihv ihb => exact hlet _ _ _ iht ihv ihb
  | proj s i x ih => exact hproj _ _ _ ih

/-- **A relation between the input and the result**, proved node by node:
`R e (replaceApps e)` whenever `R` holds at every hit and is a congruence
for the nodes the replacement keeps. -/
theorem replaceApps_rel {R : Expr → Expr → Prop} {f : Name → List Level → Option Expr}
    {b n : Nat}
    (hhit : ∀ e h, e.appHole? f b n = some h → R e h)
    (happ : ∀ a x a' x', R a a' → R x x' → R (.app a x) (.app a' x'))
    (hlam : ∀ t body m t' body', R t t' → R body body' → R (.lam t body m) (.lam t' body' m))
    (hpi : ∀ t body m t' body', R t t' → R body body' →
      R (.forallE t body m) (.forallE t' body' m))
    (hlet : ∀ t v body t' v' body', R t t' → R v v' → R body body' →
      R (.letE t v body) (.letE t' v' body'))
    (hproj : ∀ s i x x', R x x' → R (.proj s i x) (.proj s i x'))
    (hbvar : ∀ i, R (.bvar i) (.bvar i)) (hfvar : ∀ i ty, R (.fvar i ty) (.fvar i ty))
    (hsort : ∀ u, R (.sort u) (.sort u)) (hconst : ∀ c us, R (.const c us) (.const c us))
    (hlit : ∀ l, R (.lit l) (.lit l)) :
    ∀ e : Expr, R e (e.replaceApps f b n) := by
  intro e
  induction e with
  | bvar i => exact hbvar i
  | fvar i ty _ => exact hfvar i ty
  | sort u => exact hsort u
  | lit l => exact hlit l
  | const c us =>
    rw [replaceApps_const]
    split
    · rename_i h hh; exact hhit _ _ hh
    · exact hconst c us
  | app a x iha ihx =>
    rw [replaceApps_app]
    split
    · rename_i h hh; exact hhit _ _ hh
    · exact happ _ _ _ _ iha ihx
  | lam t body m iht ihb => exact hlam _ _ _ _ _ iht ihb
  | forallE t body m iht ihb => exact hpi _ _ _ _ _ iht ihb
  | letE t v body iht ihv ihb => exact hlet _ _ _ _ _ _ iht ihv ihb
  | proj s i x ih => exact hproj _ _ _ _ ih

/-- The loose-bvar bound survives when the images are closed. -/
theorem looseBVarsBounded_replaceApps {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us h, f c us = some h → h.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceApps f b n).looseBVarsBounded k = true := by
  intro e
  induction e with
  | const c us =>
    intro k _
    rw [replaceApps_const]
    split
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ _ hc)
    · rfl
  | app a x iha ihx =>
    intro k h
    rw [replaceApps_app]
    split
    · rename_i h' hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ _ hc)
    · simp only [looseBVarsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨iha k h.1, ihx k h.2⟩
  | lam t body m iht ihb =>
    intro k h
    simp only [replaceApps, looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t body m iht ihb =>
    intro k h
    simp only [replaceApps, looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v body iht ihv ihb =>
    intro k h
    simp only [replaceApps, looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i x ih =>
    intro k h
    simp only [replaceApps, looseBVarsBounded] at h ⊢
    exact ih k h
  | bvar i => intro k h; exact h
  | fvar i ty _ => intro k h; exact h
  | sort u => intro k h; exact h
  | lit l => intro k h; exact h

/-- Scoping survives when the images are scoped. -/
theorem WScoped_replaceApps {f : Name → List Level → Option Expr} {b n d : Nat}
    (hf : ∀ c us h, f c us = some h → WScoped d h) :
    ∀ e : Expr, WScoped d e → WScoped d (e.replaceApps f b n) := by
  intro e
  induction e with
  | const c us =>
    intro _
    rw [replaceApps_const]
    split
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact hf _ _ _ hc
    · simp [WScoped]
  | app a x iha ihx =>
    intro h
    rw [replaceApps_app]
    split
    · rename_i h' hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact hf _ _ _ hc
    · simp only [WScoped] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam t body m iht ihb =>
    intro h; simp only [replaceApps, WScoped] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE t body m iht ihb =>
    intro h; simp only [replaceApps, WScoped] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb =>
    intro h; simp only [replaceApps, WScoped] at h ⊢; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih => intro h; simp only [replaceApps, WScoped] at h ⊢; exact ih h
  | bvar i => intro h; exact h
  | fvar i ty _ => intro h; exact h
  | sort u => intro h; exact h
  | lit l => intro h; exact h

/-- The leaves of the result are the input's or an image's. -/
theorem fvarLeaves_replaceApps {f : Name → List Level → Option Expr} {b n : Nat} :
    ∀ (e : Expr), ∀ l ∈ (e.replaceApps f b n).fvarLeaves,
      l ∈ e.fvarLeaves ∨ ∃ c us h, f c us = some h ∧ l ∈ h.fvarLeaves := by
  intro e
  induction e with
  | const c us =>
    intro l hl
    rw [replaceApps_const] at hl
    split at hl
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact .inr ⟨_, _, _, hc, hl⟩
    · exact .inl hl
  | app a x iha ihx =>
    intro l hl
    rw [replaceApps_app] at hl
    split at hl
    · rename_i h hh
      obtain ⟨c', us', hc⟩ := appHole?_some hh
      exact .inr ⟨_, _, _, hc, hl⟩
    · simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact (iha l hl).imp_left .inl
      · exact (ihx l hl).imp_left .inr
  | lam t body m iht ihb =>
    intro l hl
    simp only [replaceApps, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact (iht l hl).imp_left .inl
    · exact (ihb l hl).imp_left .inr
  | forallE t body m iht ihb =>
    intro l hl
    simp only [replaceApps, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact (iht l hl).imp_left .inl
    · exact (ihb l hl).imp_left .inr
  | letE t v body iht ihv ihb =>
    intro l hl
    simp only [replaceApps, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · exact (iht l hl).imp_left (.inl ∘ .inl)
    · exact (ihv l hl).imp_left (.inl ∘ .inr)
    · exact (ihb l hl).imp_left .inr
  | proj s i x ih =>
    intro l hl
    simp only [replaceApps, fvarLeaves] at hl ⊢
    exact ih l hl
  | bvar i => intro l hl; exact .inl hl
  | fvar i ty _ => intro l hl; exact .inl hl
  | sort u => intro l hl; exact .inl hl
  | lit v => intro l hl; exact .inl hl

/-! ## Erasure -/

theorem phApp?_erasedEq {b : Nat} :
    ∀ (n : Nat) (e e' : Expr), ErasedEq e e' → e.phApp? b n = e'.phApp? b n
  | 0, e, e', h => by
    cases e <;> cases e' <;> simp only [ErasedEq] at h <;>
      first | exact h.elim | (obtain ⟨rfl, rfl⟩ := h; rfl) | rfl | simp [phApp?]
  | n + 1, e, e', h => by
    cases e <;> cases e' <;> simp only [ErasedEq] at h <;> first | rfl | exact h.elim | skip
    rename_i f a f' a'
    obtain ⟨hf, ha⟩ := h
    cases a <;> cases a' <;> simp only [ErasedEq] at ha <;> first | rfl | exact ha.elim | skip
    subst ha
    simp only [phApp?]
    split
    · exact phApp?_erasedEq n f f' hf
    · rfl

/-- **The replacement respects erasure**: its hits read only free-variable
indices and constant names and levels, so erasure-equal inputs have
erasure-equal results, at maps whose images are erasure-equal. -/
theorem replaceApps_erasedEq {f f' : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us, Option.Rel ErasedEq (f c us) (f' c us)) :
    ∀ (e e' : Expr), ErasedEq e e' → ErasedEq (e.replaceApps f b n) (e'.replaceApps f' b n) := by
  have hhit : ∀ e e', ErasedEq e e' →
      Option.Rel ErasedEq (e.appHole? f b n) (e'.appHole? f' b n) := by
    intro e e' h
    unfold appHole?
    rw [phApp?_erasedEq n e e' h]
    cases e'.phApp? b n with
    | none => exact .none
    | some p => exact hf p.1 p.2
  intro e
  induction e with
  | const c us =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    obtain ⟨rfl, rfl⟩ := h
    rw [replaceApps_const, replaceApps_const]
    have := hhit _ _ (ErasedEq.rfl (.const c us))
    revert this
    rcases (Expr.const c us).appHole? f b n with _ | h1 <;>
      rcases (Expr.const c us).appHole? f' b n with _ | h2 <;> intro hr <;> cases hr
    · exact ErasedEq.rfl _
    · assumption
  | app a x iha ihx =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    rename_i a' x'
    have hh := hhit (.app a x) (.app a' x') h
    rw [replaceApps_app, replaceApps_app]
    revert hh
    rcases (Expr.app a x).appHole? f b n with _ | h1 <;>
      rcases (Expr.app a' x').appHole? f' b n with _ | h2 <;> intro hr <;> cases hr
    · exact ⟨iha a' h.1, ihx x' h.2⟩
    · assumption
  | lam t body m iht ihb =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    obtain ⟨rfl, h1, h2⟩ := h
    exact ⟨rfl, iht _ h1, ihb _ h2⟩
  | forallE t body m iht ihb =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    obtain ⟨rfl, h1, h2⟩ := h
    exact ⟨rfl, iht _ h1, ihb _ h2⟩
  | letE t v body iht ihv ihb =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    exact ⟨iht _ h.1, ihv _ h.2.1, ihb _ h.2.2⟩
  | proj s i x ih =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    obtain ⟨rfl, rfl, h1⟩ := h
    exact ⟨rfl, rfl, ih _ h1⟩
  | bvar i =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    subst h; exact ErasedEq.rfl _
  | fvar i ty _ =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    exact h
  | sort u =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    subst h; exact ErasedEq.rfl _
  | lit l =>
    intro e' h
    cases e' <;> simp only [ErasedEq] at h <;> first | exact h.elim | skip
    subst h; exact ErasedEq.rfl _

/-! ## Spines -/

/-- A placeholder spine has exactly its placeholders as arguments. -/
theorem phApp?_argsLen {b : Nat} :
    ∀ (n : Nat) {e : Expr} {p : Name × List Level}, e.phApp? b n = some p →
      e.getAppArgs.length = n
  | 0, e, p, h => by
    obtain ⟨c, v⟩ := p
    cases e <;> simp_all [phApp?, getAppArgs]
  | n + 1, e, p, h => by
    match e, h with
    | .app f (.fvar j ty), h =>
      simp only [phApp?] at h
      split at h
      · simp only [getAppArgs, List.length_append, List.length_singleton]
        rw [phApp?_argsLen n h]
      · exact nomatch h

/-- **A whole application, over-applied, is replaced at its head**: the
member applied to exactly the placeholders and then to `rest` becomes
its hole applied to `rest` replaced. -/
theorem replaceApps_mkAppN_hit {f : Name → List Level → Option Expr} {b n : Nat} {c : Name}
    {v : List Level} {h : Expr} {phs : List Expr} (hf : f c v = some h)
    (hph : (Expr.mkAppN (.const c v) phs).phApp? b n = some (c, v)) :
    ∀ rest : List Expr, (Expr.mkAppN (.const c v) (phs ++ rest)).replaceApps f b n
      = Expr.mkAppN h (rest.map (·.replaceApps f b n)) := by
  have hlen := phApp?_argsLen n hph
  rw [getAppArgs_mkAppN] at hlen
  simp only [getAppArgs, List.nil_append] at hlen
  intro rest
  induction hk : rest.length generalizing rest with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero hk
    rw [List.append_nil, List.map_nil]
    show _ = h
    rcases List.eq_nil_or_concat phs with rfl | ⟨xs, y, rfl⟩
    · rw [show Expr.mkAppN (.const c v) [] = .const c v from rfl, replaceApps_const]
      simp only [show Expr.mkAppN (.const c v) [] = .const c v from rfl] at hph
      simp [appHole?, hph, hf]
    · rw [List.concat_eq_append] at hph ⊢
      rw [mkAppN_append_one] at hph ⊢
      rw [replaceApps_app]
      simp [appHole?, hph, hf]
  | succ m ih =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨pre, x, rfl⟩
    · simp at hk
    · rw [List.concat_eq_append] at hk ⊢
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hk
      rw [← List.append_assoc, mkAppN_append_one, replaceApps_app, List.map_append,
        List.map_singleton, mkAppN_append_one, ← ih pre hk]
      have hnone : (Expr.app (Expr.mkAppN (.const c v) (phs ++ pre)) x).appHole? f b n = none := by
        unfold appHole?
        cases hp : (Expr.app (Expr.mkAppN (.const c v) (phs ++ pre)) x).phApp? b n with
        | none => rfl
        | some q =>
          have := phApp?_argsLen n hp
          rw [← mkAppN_append_one, getAppArgs_mkAppN] at this
          simp [getAppArgs] at this
          omega
      rw [hnone]

/-- The placeholder spine test is blind to instantiating a bound variable
by a free one that is no placeholder. -/
theorem phApp?_instantiate1_fvar {b N : Nat} {i : Nat} {ty : Expr} (hi : ¬ (b ≤ i ∧ i < b + N)) :
    ∀ (n : Nat), n ≤ N → ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar i ty) k).phApp? b n = e.phApp? b n
  | 0, _, e, k => by
    cases e with
    | bvar j =>
      simp only [instantiate1]
      split
      · simp [phApp?]
      · split <;> simp [phApp?]
    | _ => simp [instantiate1, phApp?]
  | n + 1, hn, e, k => by
    cases e with
    | app f x =>
      cases x with
      | fvar j t =>
        simp only [instantiate1, phApp?]
        split
        · exact phApp?_instantiate1_fvar hi n (by omega) f k
        · rfl
      | bvar j =>
        simp only [instantiate1]
        split
        · simp only [phApp?]
          rw [if_neg (by omega)]
        · split <;> simp [phApp?]
      | _ => simp [instantiate1, phApp?]
    | bvar j =>
      simp only [instantiate1]
      split
      · simp [phApp?]
      · split <;> simp [phApp?]
    | _ => simp [instantiate1, phApp?]

/-- **The replacement commutes with opening a binder at a free variable
that is no placeholder**, when the images are closed under binders. -/
theorem replaceApps_instantiate1_fvar {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us h, f c us = some h → h.looseBVarsBounded 0 = true) {i : Nat} {ty : Expr}
    (hi : ¬ (b ≤ i ∧ i < b + n)) :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar i ty) k).replaceApps f b n
      = (e.replaceApps f b n).instantiate1 (.fvar i ty) k := by
  have hhit : ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar i ty) k).appHole? f b n
      = e.appHole? f b n := fun e k => by
    unfold appHole?; rw [phApp?_instantiate1_fvar hi n (Nat.le_refl _)]
  have himg : ∀ (e h : Expr) (k : Nat), e.appHole? f b n = some h →
      h.instantiate1 (.fvar i ty) k = h := fun e h k hh => by
    obtain ⟨c, us, hc⟩ := appHole?_some hh
    exact instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le _) (hf _ _ _ hc))
  intro e
  induction e with
  | bvar j =>
    intro k
    by_cases hjk : j = k
    · subst hjk; simp [instantiate1, replaceApps]
    · simp only [instantiate1, hjk, if_false, replaceApps]
      split <;> simp [instantiate1, replaceApps, hjk, *]
  | fvar j t _ => intro k; rfl
  | sort u => intro k; rfl
  | lit l => intro k; rfl
  | const c us =>
    intro k
    rw [show (Expr.const c us).instantiate1 (.fvar i ty) k = .const c us from rfl, replaceApps_const]
    split
    · rename_i h hh; exact (himg _ _ k hh).symm
    · rfl
  | app a x iha ihx =>
    intro k
    rw [show (Expr.app a x).instantiate1 (.fvar i ty) k
      = .app (a.instantiate1 (.fvar i ty) k) (x.instantiate1 (.fvar i ty) k) from rfl,
      replaceApps_app, replaceApps_app, show Expr.app (a.instantiate1 (.fvar i ty) k)
        (x.instantiate1 (.fvar i ty) k) = (Expr.app a x).instantiate1 (.fvar i ty) k from rfl,
      hhit]
    split
    · rename_i h hh; exact (himg _ _ k hh).symm
    · simp only [instantiate1, iha, ihx]
  | lam t body m iht ihb => intro k; simp only [instantiate1, replaceApps, iht, ihb]
  | forallE t body m iht ihb => intro k; simp only [instantiate1, replaceApps, iht, ihb]
  | letE t v body iht ihv ihb => intro k; simp only [instantiate1, replaceApps, iht, ihv, ihb]
  | proj s j x ih => intro k; simp only [instantiate1, replaceApps, ih]

/-! ## Leaves and scoping -/

/-- A leaf's own annotation's leaves are leaves. -/
theorem fvarLeaves_leaf_closed : ∀ (e : Expr) {i : Nat} {ty : Expr}, (i, ty) ∈ e.fvarLeaves →
    ∀ l ∈ (Expr.fvar i ty).fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | fvar j t ih =>
    intro i ty hl l hl'
    simp only [fvarLeaves, List.mem_cons] at hl hl' ⊢
    rcases hl with h | hl
    · cases h
      exact hl'
    · rcases hl' with rfl | hl'
      · exact .inr hl
      · exact .inr (ih hl l (by simp [fvarLeaves, hl']))
  | app f a ihf iha =>
    intro i ty hl l hl'
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    exact hl.imp (fun h => ihf h l hl') (fun h => iha h l hl')
  | lam t b m iht ihb =>
    intro i ty hl l hl'
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    exact hl.imp (fun h => iht h l hl') (fun h => ihb h l hl')
  | forallE t b m iht ihb =>
    intro i ty hl l hl'
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    exact hl.imp (fun h => iht h l hl') (fun h => ihb h l hl')
  | letE t v b iht ihv ihb =>
    intro i ty hl l hl'
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (h | h) | h
    · exact .inl (.inl (iht h l hl'))
    · exact .inl (.inr (ihv h l hl'))
    · exact .inr (ihb h l hl')
  | proj s k x ih =>
    intro i ty hl l hl'
    simp only [fvarLeaves] at hl ⊢
    exact ih hl l hl'
  | bvar => intro i ty hl; simp [fvarLeaves] at hl
  | sort => intro i ty hl; simp [fvarLeaves] at hl
  | const => intro i ty hl; simp [fvarLeaves] at hl
  | lit => intro i ty hl; simp [fvarLeaves] at hl

/-- **Scoping from the leaves**: a term whose every leaf is below `d` and
scoped below itself is scoped at `d` (the converse of `WScoped_leaves`). -/
theorem WScoped_of_leaves : ∀ (e : Expr) {d : Nat},
    (∀ l ∈ e.fvarLeaves, l.1 < d ∧ WScoped l.1 l.2) → WScoped d e := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro d h
    have := h (i, ty) (by simp [fvarLeaves])
    simp only [WScoped]
    exact ⟨this.1, this.2⟩
  | app f a ihf iha =>
    intro d h
    simp only [fvarLeaves, List.mem_append] at h
    simp only [WScoped]
    exact ⟨ihf fun l hl => h l (.inl hl), iha fun l hl => h l (.inr hl)⟩
  | lam t b m iht ihb =>
    intro d h
    simp only [fvarLeaves, List.mem_append] at h
    simp only [WScoped]
    exact ⟨iht fun l hl => h l (.inl hl), ihb fun l hl => h l (.inr hl)⟩
  | forallE t b m iht ihb =>
    intro d h
    simp only [fvarLeaves, List.mem_append] at h
    simp only [WScoped]
    exact ⟨iht fun l hl => h l (.inl hl), ihb fun l hl => h l (.inr hl)⟩
  | letE t v b iht ihv ihb =>
    intro d h
    simp only [fvarLeaves, List.mem_append] at h
    simp only [WScoped]
    exact ⟨iht fun l hl => h l (.inl (.inl hl)), ihv fun l hl => h l (.inl (.inr hl)),
      ihb fun l hl => h l (.inr hl)⟩
  | proj s k x ih =>
    intro d h
    simp only [fvarLeaves] at h
    simp only [WScoped]
    exact ih h
  | bvar => intro _ _; simp [WScoped]
  | sort => intro _ _; simp [WScoped]
  | const => intro _ _; simp [WScoped]
  | lit => intro _ _; simp [WScoped]

/-- The leaves of a variable replacement: a kept variable's (it and its
annotation's), or a replacement's. -/
theorem fvarLeaves_replaceFVars {g : Nat → Option Expr} :
    ∀ (e : Expr), ∀ l ∈ (e.replaceFVars g).fvarLeaves,
      (∃ i ty, (i, ty) ∈ e.fvarLeaves ∧ g i = none ∧ l ∈ (Expr.fvar i ty).fvarLeaves) ∨
        ∃ i a, g i = some a ∧ l ∈ a.fvarLeaves := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro l hl
    simp only [replaceFVars] at hl
    cases hg : g i with
    | none =>
      rw [hg, Option.getD_none] at hl
      exact .inl ⟨i, ty, by simp [fvarLeaves], hg, hl⟩
    | some a =>
      rw [hg, Option.getD_some] at hl
      exact .inr ⟨i, a, hg, hl⟩
  | app f a ihf iha =>
    intro l hl
    simp only [replaceFVars, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact (ihf l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
    · exact (iha l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
  | lam t b m iht ihb =>
    intro l hl
    simp only [replaceFVars, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact (iht l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
    · exact (ihb l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
  | forallE t b m iht ihb =>
    intro l hl
    simp only [replaceFVars, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact (iht l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
    · exact (ihb l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
  | letE t v b iht ihv ihb =>
    intro l hl
    simp only [replaceFVars, fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact (iht l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
    · exact (ihv l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
    · exact (ihb l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
  | proj s k x ih =>
    intro l hl
    simp only [replaceFVars, fvarLeaves] at hl
    exact (ih l hl).imp_left fun ⟨i, ty, h1, h2, h3⟩ => ⟨i, ty, by simp [fvarLeaves, h1], h2, h3⟩
  | bvar => intro l hl; simp [replaceFVars, fvarLeaves] at hl
  | sort => intro l hl; simp [replaceFVars, fvarLeaves] at hl
  | const => intro l hl; simp [replaceFVars, fvarLeaves] at hl
  | lit => intro l hl; simp [replaceFVars, fvarLeaves] at hl

end ConLeche.Expr

namespace ConLeche

open Expr

/-- The leaves of a Π-telescope instantiated at arguments come from the
telescope or the arguments. -/
theorem fvarLeaves_instPisWith :
    ∀ {as : List Expr} {e r : Expr}, instPisWith as e = some r →
      ∀ l ∈ r.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves
  | [], e, r, h, l, hl => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h; exact Or.inl hl
  | a :: as, e, r, h, l, hl => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      rcases fvarLeaves_instPisWith h' l hl with hl' | ⟨x, hx, hl'⟩
      · rcases fvarLeaves_instantiate1 b 0 hl' with hb | ha
        · left; simp only [fvarLeaves, List.mem_append]; exact Or.inr hb
        · exact Or.inr ⟨a, List.mem_cons_self, ha⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hl'⟩

/-- Instantiating a telescope at well-scoped arguments keeps a term well
scoped. -/
theorem wscoped_instPisWith {d : Nat} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, WScoped d a) → WScoped d e →
      ConLeche.instPisWith as e = some r → WScoped d r
  | [], e, r, _, he, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; exact he
  | a :: as, e, r, ha, he, h => by
    match e, he, h with
    | .forallE t b m, he, h =>
      have h' : ConLeche.instPisWith as (b.instantiate1 a) = some r := h
      simp only [WScoped] at he
      exact wscoped_instPisWith (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (WScoped.instantiate1_gen (ha a List.mem_cons_self) 0 he.2) h'


/-- The canonical parameter variables' leaves: themselves, annotated `Sort 0`. -/
theorem fvarLeaves_nestPhs {n : Nat} :
    ∀ x ∈ nestPhs n, ∀ l ∈ x.fvarLeaves, ∃ i, i < n ∧ l = (i, .sort .zero) := by
  intro x hx l hl
  simp only [nestPhs, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [fvarLeaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  exact ⟨i, hi, hl⟩

theorem nestPhs_length (n : Nat) : (nestPhs n).length = n := by simp [nestPhs]

/-- The canonical substitution's images are the canonical holes. -/
theorem nestCanonSub_some {names : List Name} {us : List Level} {n : Nat} {c : Name}
    {v : List Level} {h : Expr} (hs : nestCanonSub names us n c v = some h) :
    ∃ m, m < names.length ∧ names[m]? = some c ∧ v = us ∧ h = .fvar (n + m) (.sort .zero) := by
  unfold nestCanonSub at hs
  split at hs
  · rename_i hv
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hlt, hget, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hm
    exact ⟨m, hlt, by simpa [List.getElem?_eq_getElem hlt] using hget, by simpa using hv, rfl⟩
  · exact nomatch hs

/-- **The leaves of a canonical crest** of a closed constructor type: the
canonical parameter variables and holes, annotated `Sort 0`. -/
theorem fvarLeaves_nestCanonCrest {names : List Name} {us : List Level} {n : Nat}
    {cty A : Expr} (hcl : cty.hasFvar = false) (h : nestCanonCrest names us n cty = some A) :
    ∀ l ∈ A.fvarLeaves, ∃ i, i < n + names.length ∧ l = (i, .sort .zero) := by
  unfold nestCanonCrest at h
  obtain ⟨e0, he, rfl⟩ := Option.map_eq_some_iff.mp h
  intro l hl
  rcases fvarLeaves_replaceApps e0 l hl with h1 | ⟨c, us', h', hc, h2⟩
  · rcases fvarLeaves_instPisWith he l h1 with hl | ⟨x, hx, hl⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hcl] at hl; exact nomatch hl
    · obtain ⟨i, hi, rfl⟩ := fvarLeaves_nestPhs x hx l hl
      exact ⟨i, by omega, rfl⟩
  · obtain ⟨m, hm, -, -, rfl⟩ := nestCanonSub_some hc
    simp only [fvarLeaves, List.mem_cons, List.not_mem_nil, or_false] at h2
    exact ⟨n + m, by omega, h2⟩

/-- **The leaves of a crest at a key** (`nestCrest`) of a closed
constructor type: a parameter's or a hole's (every canonical variable is
replaced, at one hole per member). -/
theorem fvarLeaves_nestCrest {names : List Name} {us : List Level} {ds holes : List Expr}
    {cty crest : Expr} (hcl : cty.hasFvar = false) (hlen : names.length ≤ holes.length)
    (h : nestCrest names us ds holes cty = some crest) :
    ∀ l ∈ crest.fvarLeaves, ∃ a ∈ ds ++ holes, l ∈ a.fvarLeaves := by
  unfold nestCrest at h
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
  intro l hl
  rcases fvarLeaves_replaceFVars _ l hl with ⟨i, ty, hi, hg, -⟩ | ⟨i, a, hg, hl'⟩
  · obtain ⟨j, hj, hij⟩ := fvarLeaves_nestCanonCrest hcl hA _ hi
    simp only [Prod.mk.injEq] at hij
    obtain ⟨rfl, rfl⟩ := hij
    unfold nestKeyMap at hg
    split at hg
    · rename_i hlt; simp [List.getElem?_eq_getElem hlt] at hg
    · simp at hg; omega
  · unfold nestKeyMap at hg
    split at hg
    · exact ⟨a, List.mem_append_left _ (List.mem_of_getElem? hg), hl'⟩
    · exact ⟨a, List.mem_append_right _ (List.mem_of_getElem? hg), hl'⟩

/-- **A crest is scoped** where the parameters and the holes are. -/
theorem WScoped_nestCrest {names : List Name} {us : List Level} {ds holes : List Expr} {d : Nat}
    {cty crest : Expr} (hcl : cty.hasFvar = false) (hlen : names.length ≤ holes.length)
    (hds : ∀ x ∈ ds ++ holes, WScoped d x)
    (h : nestCrest names us ds holes cty = some crest) : WScoped d crest := by
  refine WScoped_of_leaves _ fun l hl => ?_
  obtain ⟨a, ha, hl'⟩ := fvarLeaves_nestCrest hcl hlen h l hl
  exact WScoped_leaves a (hds a ha) l hl'

end ConLeche
