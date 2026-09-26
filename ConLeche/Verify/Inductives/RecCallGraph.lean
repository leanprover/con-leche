module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Abstract
import ConLeche.Verify.BridgeWfImp

public section

set_option linter.unusedSimpArgs false

/-!
# The family's call graph bounds its calls (PRIMREC)

The recursor check decides, before it checks anything else, whether the
family's CALL GRAPH is acyclic (`targetLegacyAux`, `RecCheck.lean`): the
graph `targetCallGraph` has an edge `c → c'` when a rule of recursor `c`,
as the stream gives it, names recursor `c'`.  The proof orders the
classes along the calls the check actually recognised (`TargetRank.lean`),
so it needs every recognised call to be an edge of that graph:

* a recognised call names its callee (`targetCall?_names`), and the
  abstraction collects only recognised calls (`targetAbstract_callees`);
* the names survive, backwards, every step between the stream's rule and
  the abstracted body — opening by free variables
  (`namesConst_instantiateList`), stripping the λ-prefix
  (`namesConst_stripLams`) and annotation (`annotateCore_namesConst`,
  whose `let` clause substitutes the value, the only step that moves a
  subterm);
* so at a rule's run every `ih` variable's callee is an edge
  (`TargetRuleRun.callee_names`), and at an acyclic graph the rank
  `graphRank` descends along it (`graphAcyclic_descends`).

"Names" is `Expr.namesConst`: a constant occurrence outside every free
variable's annotation — the positions the abstraction walks.  It implies
the kernel's `Expr.mentionsConst` (`namesConst_mentionsConst`).
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- **`n` occurs as a constant in `e`**, outside every free variable's
annotation and every projection's structure name. -/
@[expose] def Expr.namesConst (n : Name) : Expr → Bool
  | .const m _ => m == n
  | .app f a => f.namesConst n || a.namesConst n
  | .lam t b _ | .forallE t b _ => t.namesConst n || b.namesConst n
  | .letE t v b => t.namesConst n || v.namesConst n || b.namesConst n
  | .proj _ _ e => e.namesConst n
  | _ => false

/-- The kernel's occurrence test sees every such occurrence. -/
theorem namesConst_mentionsConst {n : Name} :
    ∀ e : Expr, e.namesConst n = true → e.mentionsConst n = true := by
  intro e
  induction e <;> simp_all [Expr.namesConst, Expr.mentionsConst] <;> grind

/-- Instantiating one bound variable adds at most the value's names. -/
theorem namesConst_instantiate1 {n : Name} {v : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 v k).namesConst n = true →
      e.namesConst n = true ∨ v.namesConst n = true := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [Expr.instantiate1] at h
    split at h
    · exact Or.inr h
    · split at h <;> simp [Expr.namesConst] at h
  | fvar => intro k h; simp [Expr.instantiate1, Expr.namesConst] at h
  | sort => intro k h; simp [Expr.instantiate1, Expr.namesConst] at h
  | lit => intro k h; simp [Expr.instantiate1, Expr.namesConst] at h
  | const m us => intro k h; exact Or.inl (by simpa [Expr.instantiate1] using h)
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact (ihf k h).imp_left Or.inl
    · exact (iha k h).imp_left Or.inr
  | lam t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact (iht k h).imp_left Or.inl
    · exact (ihb (k + 1) h).imp_left Or.inr
  | forallE t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact (iht k h).imp_left Or.inl
    · exact (ihb (k + 1) h).imp_left Or.inr
  | letE t v' b iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact (iht k h).imp_left (fun h => Or.inl (Or.inl h))
    · exact (ihv k h).imp_left (fun h => Or.inl (Or.inr h))
    · exact (ihb (k + 1) h).imp_left Or.inr
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.namesConst] at h ⊢
    exact ih k h

/-- Abstracting a free variable changes no name. -/
theorem namesConst_abstract1 {n : Name} {d : Nat} :
    ∀ (e : Expr) (k : Nat), (e.abstract1 d k).namesConst n = true → e.namesConst n = true := by
  intro e
  induction e with
  | fvar i ty =>
    intro k h
    simp only [Expr.abstract1] at h
    split at h <;> simp [Expr.namesConst] at h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.abstract1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (ihf k) (iha k)
  | lam t b m iht ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (iht k) (ihb (k + 1))
  | forallE t b m iht ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (iht k) (ihb (k + 1))
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (fun h => h.imp (iht k) (ihv k)) (ihb (k + 1))
  | proj s i e ih =>
    intro k h
    simp only [Expr.abstract1, Expr.namesConst] at h ⊢
    exact ih k h
  | _ => intro k h; simpa [Expr.abstract1] using h

/-- **Annotation adds no name**: every name of the annotated term is one
of the input's (its `let` clause substitutes the value into the body). -/
theorem annotateCore_namesConst {env : Env} {n : Name} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore mode env fuel d e = .ok e' → e'.namesConst n = true →
      e.namesConst n = true
  | 0, _, _, _, h, _ => by
    simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, hn => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hn
  | fuel + 1, .fvar idx ty, d, e', h, hn => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hn
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, hn => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hn
  | fuel + 1, .const m us, d, e', h, hn => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hn
  | fuel + 1, .lit l, d, e', h, hn => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal _, h =>
      dsimp only [annotateBody] at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hn
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | .strVal _, h =>
      dsimp only [annotateBody] at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hn
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .app f a, d, e', h, hn => by
    obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv h
    simp only [Expr.namesConst, Bool.or_eq_true] at hn ⊢
    exact hn.imp (annotateCore_namesConst fuel f hf) (annotateCore_namesConst fuel a ha)
  | fuel + 1, .proj sn i e, d, e', h, hn => by
    obtain ⟨e₂, _, _, he, _, _, _, _, _, _, _, _, he'⟩ := annotateCore_proj_inv h
    subst he'
    simp only [Expr.namesConst] at hn ⊢
    exact annotateCore_namesConst fuel e he hn
  | fuel + 1, .forallE ty body m, d, e', h, hn => by
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
    simp only [Expr.namesConst, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (annotateCore_namesConst fuel ty hty hn)
    · rcases namesConst_instantiate1 body 0
          (annotateCore_namesConst fuel _ hbody (namesConst_abstract1 body' 0 hn)) with h1 | h1
      · exact Or.inr h1
      · simp [Expr.namesConst] at h1
  | fuel + 1, .lam ty body m, d, e', h, hn => by
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
    simp only [Expr.namesConst, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (annotateCore_namesConst fuel ty hty hn)
    · rcases namesConst_instantiate1 body 0
          (annotateCore_namesConst fuel _ hbody (namesConst_abstract1 body' 0 hn)) with h1 | h1
      · exact Or.inr h1
      · simp [Expr.namesConst] at h1
  | fuel + 1, .letE ty v b, d, e', h, hn => by
    obtain ⟨ty', v', -, -, hb, -⟩ := annotateCore_letE_inv h
    simp only [Expr.namesConst, Bool.or_eq_true]
    rcases namesConst_instantiate1 b 0 (annotateCore_namesConst fuel _ hb hn) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl (Or.inr h1)

/-- Opening by free variables adds no name. -/
theorem namesConst_instantiateList {n : Name} {vs : List Expr}
    (hvs : ∀ x ∈ vs, ∃ (i : Nat) (ty : Expr), x = .fvar i ty) :
    ∀ (e : Expr) (k : Nat), (e.instantiateList vs k).namesConst n = true →
      e.namesConst n = true := by
  intro e
  induction e with
  | bvar j =>
    intro k h
    rw [Expr.instantiateList] at h
    split at h
    · simp [Expr.namesConst] at h
    · split at h
      · next hin =>
        obtain ⟨i, ty, hx⟩ := hvs _ (List.getElem_mem hin)
        rw [hx, Expr.instantiateList] at h
        simp [Expr.namesConst] at h
      · simp [Expr.namesConst] at h
  | fvar => intro k h; rw [Expr.instantiateList] at h; simp [Expr.namesConst] at h
  | sort => intro k h; rw [Expr.instantiateList] at h; simp [Expr.namesConst] at h
  | lit => intro k h; rw [Expr.instantiateList] at h; simp [Expr.namesConst] at h
  | const => intro k h; rw [Expr.instantiateList] at h; exact h
  | app f a ihf iha =>
    intro k h
    rw [Expr.instantiateList] at h
    simp only [Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (ihf k) (iha k)
  | lam t b m iht ihb =>
    intro k h
    rw [Expr.instantiateList] at h
    simp only [Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (iht k) (ihb (k + 1))
  | forallE t b m iht ihb =>
    intro k h
    rw [Expr.instantiateList] at h
    simp only [Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (iht k) (ihb (k + 1))
  | letE t v b iht ihv ihb =>
    intro k h
    rw [Expr.instantiateList] at h
    simp only [Expr.namesConst, Bool.or_eq_true] at h ⊢
    exact h.imp (fun h => h.imp (iht k) (ihv k)) (ihb (k + 1))
  | proj s i e ih =>
    intro k h
    rw [Expr.instantiateList] at h
    simp only [Expr.namesConst] at h ⊢
    exact ih k h

/-- Stripping a λ-prefix keeps the body's names. -/
theorem namesConst_stripLams {n : Name} :
    ∀ (k : Nat) (e : Expr) {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripLams k = some (bs, body) → body.namesConst n = true → e.namesConst n = true
  | 0, e, bs, body, h, hn => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hn
  | k + 1, .lam ty b m, bs, body, h, hn => by
    simp only [Expr.stripLams] at h
    cases hb : b.stripLams k with
    | none => rw [hb] at h; exact nomatch h
    | some r =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Expr.namesConst, Bool.or_eq_true]
      exact Or.inr (namesConst_stripLams k b hb hn)
  | k + 1, .bvar _, _, _, h, _ => nomatch h
  | k + 1, .fvar _ _, _, _, h, _ => nomatch h
  | k + 1, .sort _, _, _, h, _ => nomatch h
  | k + 1, .const _ _, _, _, h, _ => nomatch h
  | k + 1, .app _ _, _, _, h, _ => nomatch h
  | k + 1, .forallE _ _ _, _, _, h, _ => nomatch h
  | k + 1, .letE _ _ _, _, _, h, _ => nomatch h
  | k + 1, .lit _, _, _, h, _ => nomatch h
  | k + 1, .proj _ _ _, _, _, h, _ => nomatch h

/-- An application names its head. -/
theorem namesConst_of_getAppFn {n : Name} {us : List Level} :
    ∀ e : Expr, e.getAppFn = .const n us → e.namesConst n = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.getAppFn] at h
    simp [Expr.namesConst, ihf h]
  | const m vs =>
    intro h
    simp only [Expr.getAppFn, Expr.const.injEq] at h
    simp [Expr.namesConst, h.1]
  | _ => intro h; simp [Expr.getAppFn] at h

/-- `nameIdxOf?` finds a position holding the name. -/
theorem nameIdxOf?_spec {names : List Name} {n : Name} {c : Nat}
    (h : nameIdxOf? names n = some c) : c < names.length ∧ names.getD c .anonymous = n := by
  unfold nameIdxOf? at h
  have hmem : c ∈ List.range names.length := List.mem_of_find?_eq_some h
  refine ⟨List.mem_range.mp hmem, ?_⟩
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  exact this

/-- A recognised call's head is its callee's name. -/
theorem targetCall?_head {fr : TargetFrame} {d : Nat} {e : Expr} {i c m : Nat}
    {idx : List Expr} (h : targetCall? fr d e = some (i, c, m, idx)) :
    ∃ r us, e.getAppFn = .const r us ∧ nameIdxOf? fr.recNames r = some c := by
  unfold targetCall? at h
  split at h
  · next r us hfn =>
    split at h
    · exact nomatch h
    · next c' hc' =>
      refine ⟨r, us, hfn, ?_⟩
      rw [hc']
      dsimp only at h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      split at h
      · exact nomatch h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2.1]
  · exact nomatch h

/-- **A recognised call names its callee.** -/
theorem targetCall?_names {fr : TargetFrame} {d : Nat} {e : Expr} {i c m : Nat}
    {idx : List Expr} (h : targetCall? fr d e = some (i, c, m, idx)) :
    c < fr.recNames.length ∧ e.namesConst (fr.recNames.getD c .anonymous) = true := by
  obtain ⟨r, us, hfn, hc⟩ := targetCall?_head h
  obtain ⟨hlt, hn⟩ := nameIdxOf?_spec hc
  exact ⟨hlt, hn ▸ namesConst_of_getAppFn e hfn⟩

/-- **The abstraction collects only recognised calls**: each `ih`
variable it adds names its callee in the walked term. -/
theorem targetAbstract_callees {fr : TargetFrame} {base : Nat} :
    ∀ (e : Expr) {d : Nat} {acc : Array TargetIh} {e' : Expr} {acc' : Array TargetIh},
      targetAbstract fr base d e acc = some (e', acc') →
      ∀ ih ∈ acc'.toList, ih ∈ acc.toList ∨
        (ih.callee < fr.recNames.length ∧
          e.namesConst (fr.recNames.getD ih.callee .anonymous) = true) := by
  intro e
  induction e with
  | bvar j => intro d acc e' acc' h; simp only [targetAbstract, Option.some.injEq,
      Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact fun ih hih => Or.inl hih
  | sort u => intro d acc e' acc' h; simp only [targetAbstract, Option.some.injEq,
      Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact fun ih hih => Or.inl hih
  | lit l => intro d acc e' acc' h; simp only [targetAbstract, Option.some.injEq,
      Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact fun ih hih => Or.inl hih
  | fvar i ty => intro d acc e' acc' h; simp only [targetAbstract, Option.some.injEq,
      Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact fun ih hih => Or.inl hih
  | const n us =>
    intro d acc e' acc' h
    simp only [targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun ih hih => Or.inl hih
  | lam ty b bi iht ihb =>
    intro d acc e' acc' h
    simp only [targetAbstract, Option.bind_eq_bind] at h
    obtain ⟨⟨ty', acc1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b', acc2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases ihb h2 ih hih with h' | ⟨hl, hn⟩
    · rcases iht h1 ih h' with h'' | ⟨hl, hn⟩
      · exact Or.inl h''
      · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
    · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
  | forallE ty b bi iht ihb =>
    intro d acc e' acc' h
    simp only [targetAbstract, Option.bind_eq_bind] at h
    obtain ⟨⟨ty', acc1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b', acc2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases ihb h2 ih hih with h' | ⟨hl, hn⟩
    · rcases iht h1 ih h' with h'' | ⟨hl, hn⟩
      · exact Or.inl h''
      · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
    · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
  | letE ty v b iht ihv ihb =>
    intro d acc e' acc' h
    simp only [targetAbstract, Option.bind_eq_bind] at h
    obtain ⟨⟨ty', acc1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨v', acc2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b', acc3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases ihb h3 ih hih with h' | ⟨hl, hn⟩
    · rcases ihv h2 ih h' with h'' | ⟨hl, hn⟩
      · rcases iht h1 ih h'' with h''' | ⟨hl, hn⟩
        · exact Or.inl h'''
        · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
      · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
    · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
  | proj s i e ihe =>
    intro d acc e' acc' h
    simp only [targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind] at h
      obtain ⟨⟨e1, acc1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro ih hih
      rcases ihe h1 ih hih with h' | ⟨hl, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
  | app f a ihf iha =>
    intro d acc e' acc' h
    simp only [targetAbstract] at h
    split at h
    · next i c m idx hcall =>
      obtain ⟨hlt, hn⟩ := targetCall?_names hcall
      simp only [Option.bind_eq_bind] at h
      obtain ⟨ty, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact fun ih hih => Or.inl hih
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro ih hih
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hih
        rcases hih with hih | rfl
        · exact Or.inl hih
        · exact Or.inr ⟨hlt, hn⟩
    · simp only [Option.bind_eq_bind] at h
      obtain ⟨⟨f', acc1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨a', acc2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro ih hih
      rcases iha h2 ih hih with h' | ⟨hl, hn⟩
      · rcases ihf h1 ih h' with h'' | ⟨hl, hn⟩
        · exact Or.inl h''
        · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩
      · exact Or.inr ⟨hl, by simp only [Expr.namesConst, Bool.or_eq_true, hn, Bool.true_or, Bool.or_true, true_or, or_true]⟩

/-- **At a rule's run, every `ih` variable's callee is named by the
stream's rule** (the abstraction, back through the opening, the
λ-prefix and the annotation). -/
theorem TargetRuleRun.callee_names {F : Nat} {feR feT : FEnv} {p : BlockShape}
    {formerTys : List Expr} {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (Q : TargetRuleRun mode F feR feT p formerTys fam cvR rP recTy M c rhs out) :
    ∀ ih ∈ Q.ihs.toList, ih.callee < fam.recNames.length ∧
      rhs.mentionsConst (fam.recNames.getD ih.callee .anonymous) = true := by
  intro ih hih
  rcases targetAbstract_callees _ Q.habs ih hih with h | ⟨hl, hn⟩
  · exact nomatch h
  refine ⟨hl, namesConst_mentionsConst _ (annotateCore_namesConst F _ Q.hann ?_)⟩
  refine namesConst_stripLams _ _ Q.hstrip (namesConst_instantiateList ?_ _ 0 hn)
  intro x hx
  rw [List.mem_reverse, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ Q.hpref j x hj
    exact ⟨_, ty, rfl⟩
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ Q.hfld j x hj
    exact ⟨_, ty, rfl⟩

/-! ## The graph -/

/-- An edge of the family's call graph. -/
theorem mem_targetCallGraph {names : List Name} {rhss : List (List Expr)} {c c' : Nat}
    {rs : List Expr} (hrs : rhss[c]? = some rs) {r : Expr} (hr : r ∈ rs)
    (hc' : c' < names.length) (hn : r.mentionsConst (names.getD c' .anonymous) = true) :
    c' ∈ (targetCallGraph names rhss).getD c [] := by
  rw [targetCallGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hrs, Option.map_some,
    Option.getD_some]
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hc', List.any_eq_true.mpr ⟨r, hr, hn⟩⟩

/-- **An acyclic graph's rank descends along every edge.** -/
theorem graphAcyclic_descends {g : List (List Nat)} (h : graphAcyclic g = true) {c c' : Nat}
    (hc : c < g.length) (hc' : c' ∈ g.getD c []) :
    (graphRank g).getD c' 0 < (graphRank g).getD c 0 := by
  unfold graphAcyclic graphDescends at h
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  exact of_decide_eq_true (List.all_eq_true.mp this c' hc')

end ConLeche

namespace ConLeche

/-! ## The rank never climbs along an edge

`graphRank` is the size of every node's reach, iterated to a fixed point
(`reachFix`).  At the fixed point a node's reach holds its successors'
(`reachStep`), so an edge never climbs the rank (`graphRank_mono`) — the
fact a cyclic layer's `LayerStep` reads (`layerStep_of_der`'s `hdown`).
If the fuel ran out the rank is all zero, which is monotone too. -/

/-- The fixed point `reachFix` returns is one. -/
theorem reachFix_fix {g : List (List Nat)} :
    ∀ {fuel : Nat} {R₀ R : List (List Bool)}, reachFix g fuel R₀ = some R → reachStep g R = R
  | 0, _, _, h => nomatch h
  | fuel + 1, R₀, R, h => by
    unfold reachFix at h
    split at h
    · next heq =>
      obtain rfl := Option.some.inj h
      exact eq_of_beq heq
    · exact reachFix_fix h

/-- Counting `true`s is monotone along pointwise implication. -/
theorem count_true_le_of_imp :
    ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = true → l₂[i] = true) →
      l₁.count true ≤ l₂.count true
  | [], [], _, _ => Nat.le_refl _
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a :: as, b :: bs, hl, himp => by
    have hrest : as.count true ≤ bs.count true :=
      count_true_le_of_imp (by simpa using hl) fun i h₁ h₂ hi =>
        himp (i + 1) (by simp; omega) (by simp; omega) hi
    have h0 := himp 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    cases a <;> cases b <;> simp [List.count_cons] at h0 ⊢ <;> omega

/-- A row of a fixed point, at a node. -/
theorem reachStep_row {g : List (List Nat)} {R : List (List Bool)} (hR : reachStep g R = R)
    {c : Nat} (hc : c < g.length) :
    R.getD c [] = (List.range g.length).map fun x =>
      (R.getD c []).getD x false || (g.getD c []).any fun c' => (R.getD c' []).getD x false := by
  conv => lhs; rw [← hR]
  unfold reachStep
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc, Option.map_some,
    Option.getD_some]

/-- **An edge never climbs the rank.** -/
theorem graphRank_mono {g : List (List Nat)} {c c' : Nat} (hc : c < g.length)
    (hc' : c' < g.length) (he : c' ∈ g.getD c []) :
    (graphRank g).getD c' 0 ≤ (graphRank g).getD c 0 := by
  unfold graphRank
  split
  · next R hRf =>
    have hR := reachFix_fix hRf
    have hlen : R.length = g.length := by
      have := congrArg List.length hR
      simpa [reachStep] using this.symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega),
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some]
    have hrc := reachStep_row hR hc
    have hrc' := reachStep_row hR hc'
    have e1 : R[c] = R.getD c [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have e2 : R[c'] = R.getD c' [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [e1, e2]
    refine count_true_le_of_imp (by rw [hrc, hrc']; simp) fun i h₁ h₂ hi => ?_
    have hi' : i < g.length := by rw [hrc'] at h₁; simpa using h₁
    -- the node's own entry at `i` is its successors' disjunction
    have hx : (R.getD c' []).getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]; exact hi
    have hgoal : (R.getD c []).getD i false = true := by
      rw [hrc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi',
        Option.map_some, Option.getD_some, Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨c', he, hx⟩)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at hgoal
    exact hgoal
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc',
      Option.map_some, Option.getD_some]
    exact Nat.zero_le _

end ConLeche
