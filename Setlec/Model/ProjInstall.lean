import Setlec.Model.IndInstall

/-!
# Fold facts for an installed projection function

`proj_rule_eq` derives the single rule's `RecRulesOk` **total
λ-equality** obligation for a projection function (a degenerate
recursor installed against the structure model's `proj_i` definition)
from the checked `T._model.proj_i.iota` theorem.  The pipeline mirrors
`modeled_rule_eq`, radically simplified: the statement's telescope is
the constructor's telescope (renamed), and the rule right-hand side is
`pisToLams` of the constructor's telescope, so the canonical frame,
the rule λ-tower and the statement telescope walk in lockstep over
*syntactically shared* raw binder domains.  `proj_tower_rec` descends
the three telescopes together, carrying the partially eliminated
theorem inhabitant; at the bottom the theorem's `Eq` collapses the
interpreted projection redex onto the projected field's value.
-/

namespace Setlec

open SetTheory

/-! ## Syntactic helpers -/

namespace Expr

theorem ErasedEq.symm : ∀ {e₁ e₂ : Expr}, ErasedEq e₁ e₂ → ErasedEq e₂ e₁
  | .bvar _, .bvar _, h => Eq.symm h
  | .fvar _ _ _, .fvar _ _ _, h => Eq.symm h
  | .sort _, .sort _, h => Eq.symm h
  | .const _ _, .const _ _, h => ⟨Eq.symm h.1, Eq.symm h.2⟩
  | .app _ _, .app _ _, h => ⟨ErasedEq.symm h.1, ErasedEq.symm h.2⟩
  | .lam _ _ _ _, .lam _ _ _ _, h =>
    ⟨Eq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .forallE _ _ _ _, .forallE _ _ _ _, h =>
    ⟨Eq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .letE _ _ _ _, .letE _ _ _ _, h =>
    ⟨ErasedEq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .lit _, .lit _, h => Eq.symm h
  | .proj _ _ _, .proj _ _ _, h =>
    ⟨Eq.symm h.1, Eq.symm h.2.1, ErasedEq.symm h.2.2⟩

/-- Split a `∀`-telescope decomposition at a prefix length: the
residual of the prefix strips the remaining binders. -/
theorem stripPis_add :
    ∀ (a b : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis (a + b) = some (bs, body) →
      ∃ mid, e.stripPis a = some (bs.take a, mid) ∧
        mid.stripPis b = some (bs.drop a, body) := by
  intro a
  induction a with
  | zero =>
    intro b e bs body h
    exact ⟨e, by simp [stripPis], by simpa using h⟩
  | succ a ih =>
    intro b e bs body h
    rw [show a + 1 + b = (a + b) + 1 from by omega] at h
    match e, h with
    | .forallE n d bo m, h =>
      simp only [stripPis] at h ⊢
      cases hs : bo.stripPis (a + b) with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨mid, h1, h2⟩ := ih b (by rw [hs])
        refine ⟨mid, ?_, ?_⟩
        · rw [h1, ← hb]
          rfl
        · rw [← hb]
          simpa using h2

/-- An instantiation sequence preserves a `∀`-telescope's arity. -/
theorem stripPis_instSeq_isSome :
    ∀ (args : List Expr) (t : Nat) {e : Expr} (k : Nat),
      (e.stripPis k).isSome = true →
      ((instSeq args t e).stripPis k).isSome = true
  | [], _, _, _, h => h
  | _a :: as, t, _e, k, h =>
    stripPis_instSeq_isSome as (t - 1) k
      (stripPis_instantiate1_isSome k t h)

/-- Instantiation distributes over a λ-tower's decomposition,
transforming only the binder domains. -/
theorem stripLams_instantiate1_full {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr} (j : Nat),
      e.stripLams k = some (bs, body) →
      ∃ bs', (e.instantiate1 v j).stripLams k =
          some (bs', body.instantiate1 v (j + k)) ∧
        ∀ (i : Nat) (b : Name × Expr × BinderMeta), bs[i]? = some b →
          bs'[i]? = some (b.1, b.2.1.instantiate1 v (j + i), b.2.2) := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [stripLams], fun i b hb => by simp at hb⟩
  | succ k ih =>
    intro e bs body j h
    match e, h with
    | .lam n d bo m, h =>
      simp only [stripLams] at h
      cases hs : bo.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨bs', h1, h2⟩ := ih (j + 1) (by rw [hs])
        refine ⟨(n, d.instantiate1 v j, m) :: bs', ?_, ?_⟩
        · simp only [instantiate1, stripLams, h1,
            show j + 1 + k = j + (k + 1) from by omega, Option.map_some]
        · intro i b hbi
          rw [← hb] at hbi
          cases i with
          | zero =>
            obtain rfl : (n, d, m) = b := by simpa using hbi
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hbi ⊢
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h2 i b hbi

/-- Instantiation distributes over a `∀`-tower's decomposition,
transforming only the binder domains. -/
theorem stripPis_instantiate1_full {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.instantiate1 v j).stripPis k =
          some (bs', body.instantiate1 v (j + k)) ∧
        ∀ (i : Nat) (b : Name × Expr × BinderMeta), bs[i]? = some b →
          bs'[i]? = some (b.1, b.2.1.instantiate1 v (j + i), b.2.2) := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [stripPis], fun i b hb => by simp at hb⟩
  | succ k ih =>
    intro e bs body j h
    match e, h with
    | .forallE n d bo m, h =>
      simp only [stripPis] at h
      cases hs : bo.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨bs', h1, h2⟩ := ih (j + 1) (by rw [hs])
        refine ⟨(n, d.instantiate1 v j, m) :: bs', ?_, ?_⟩
        · simp only [instantiate1, stripPis, h1,
            show j + 1 + k = j + (k + 1) from by omega, Option.map_some]
        · intro i b hbi
          rw [← hb] at hbi
          cases i with
          | zero =>
            obtain rfl : (n, d, m) = b := by simpa using hbi
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hbi ⊢
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h2 i b hbi

/-- The head binder of a partial λ-instantiation walk, characterized
by the raw tower's binder list, together with the one-step extension
of the walk. -/
theorem instLamsAt_head :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr}
      {mrem : Nat} {bs : List (Name × Expr × BinderMeta)} {body : Expr}
      {b : Name × Expr × BinderMeta},
      Expr.instLamsAt args e = some (ds, rest) →
      e.stripLams (args.length + (mrem + 1)) = some (bs, body) →
      bs[args.length]? = some b →
      ∃ bodyR,
        rest = .lam b.1 (instSeq args (args.length - 1) b.2.1) bodyR b.2.2 ∧
        ∀ a, Expr.instLamsAt (args ++ [a]) e =
          some (ds ++ [instSeq args (args.length - 1) b.2.1],
            bodyR.instantiate1 a) := by
  intro args
  induction args with
  | nil =>
    intro e ds rest mrem bs body b h hstrip hb
    simp only [instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show [].length + (mrem + 1) = mrem + 1 from by simp] at hstrip
    match e, hstrip with
    | .lam n d bo m, hstrip =>
      simp only [stripLams] at hstrip
      cases hs : bo.stripLams mrem with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some p =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        obtain rfl : (n, d, m) = b := by simpa using hb
        exact ⟨bo, rfl, fun a => by simp [instLamsAt, instSeq]⟩
  | cons a as ih =>
    intro e ds rest mrem bs body b h hstrip hb
    match e, h with
    | .lam n d bo m, h =>
      simp only [instLamsAt] at h
      cases h0 : Expr.instLamsAt as (bo.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : d :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        rw [show (a :: as).length + (mrem + 1) =
          (as.length + (mrem + 1)) + 1 from by simp; omega] at hstrip
        simp only [stripLams] at hstrip
        cases hs : bo.stripLams (as.length + (mrem + 1)) with
        | none => rw [hs] at hstrip; exact nomatch hstrip
        | some q =>
          rw [hs] at hstrip
          simp only [Option.map_some, Option.some.injEq] at hstrip
          obtain ⟨hbs, -⟩ : (n, d, m) :: q.1 = bs ∧ q.2 = body := by
            cases hstrip; exact ⟨rfl, rfl⟩
          rw [← hbs] at hb
          simp only [List.length_cons, List.getElem?_cons_succ] at hb
          obtain ⟨bs', hstrip', hpos⟩ :=
            stripLams_instantiate1_full (v := a)
              (as.length + (mrem + 1)) 0 hs
          obtain ⟨bodyR, hhead, hext⟩ := ih (b := (b.1,
              b.2.1.instantiate1 a as.length, b.2.2)) h0 hstrip'
            (by rw [hpos as.length b hb]; simp)
          refine ⟨bodyR, ?_, ?_⟩
          · rw [← hrest, hhead]
            rfl
          · intro a'
            have h2 := hext a'
            simp only [List.cons_append, instLamsAt, h2, Option.map_some]
            rw [← hds]
            rfl

/-- The head binder of a partial `∀`-instantiation walk, characterized
by the raw telescope's binder list, together with the one-step
extension of the walk. -/
theorem instPisAt_head :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr}
      {mrem : Nat} {bs : List (Name × Expr × BinderMeta)} {body : Expr}
      {b : Name × Expr × BinderMeta},
      Expr.instPisAt args e = some (ds, rest) →
      e.stripPis (args.length + (mrem + 1)) = some (bs, body) →
      bs[args.length]? = some b →
      ∃ bodyR,
        rest = .forallE b.1 (instSeq args (args.length - 1) b.2.1) bodyR
          b.2.2 ∧
        ∀ a, Expr.instPisAt (args ++ [a]) e =
          some (ds ++ [instSeq args (args.length - 1) b.2.1],
            bodyR.instantiate1 a) := by
  intro args
  induction args with
  | nil =>
    intro e ds rest mrem bs body b h hstrip hb
    simp only [instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show [].length + (mrem + 1) = mrem + 1 from by simp] at hstrip
    match e, hstrip with
    | .forallE n d bo m, hstrip =>
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis mrem with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some p =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        obtain rfl : (n, d, m) = b := by simpa using hb
        exact ⟨bo, rfl, fun a => by simp [instPisAt, instSeq]⟩
  | cons a as ih =>
    intro e ds rest mrem bs body b h hstrip hb
    match e, h with
    | .forallE n d bo m, h =>
      simp only [instPisAt] at h
      cases h0 : Expr.instPisAt as (bo.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : d :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        rw [show (a :: as).length + (mrem + 1) =
          (as.length + (mrem + 1)) + 1 from by simp; omega] at hstrip
        simp only [stripPis] at hstrip
        cases hs : bo.stripPis (as.length + (mrem + 1)) with
        | none => rw [hs] at hstrip; exact nomatch hstrip
        | some q =>
          rw [hs] at hstrip
          simp only [Option.map_some, Option.some.injEq] at hstrip
          obtain ⟨hbs, -⟩ : (n, d, m) :: q.1 = bs ∧ q.2 = body := by
            cases hstrip; exact ⟨rfl, rfl⟩
          rw [← hbs] at hb
          simp only [List.length_cons, List.getElem?_cons_succ] at hb
          obtain ⟨bs', hstrip', hpos⟩ :=
            stripPis_instantiate1_full (v := a)
              (as.length + (mrem + 1)) 0 hs
          obtain ⟨bodyR, hhead, hext⟩ := ih (b := (b.1,
              b.2.1.instantiate1 a as.length, b.2.2)) h0 hstrip'
            (by rw [hpos as.length b hb]; simp)
          refine ⟨bodyR, ?_, ?_⟩
          · rw [← hrest, hhead]
            rfl
          · intro a'
            have h2 := hext a'
            simp only [List.cons_append, instPisAt, h2, Option.map_some]
            rw [← hds]
            rfl

end Expr

/-- A `∀`-telescope that strips syntactically admits the fresh-variable
opening at any base index. -/
theorem openPisAtFvars_isSome_of_stripPis :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat),
      (e.stripPis n).isSome = true →
      (openPisAtFvars n e i₀).isSome = true
  | 0, _, _, _ => by simp [openPisAtFvars]
  | n + 1, e, i₀, h => by
    match e, h with
    | .forallE nm dom body m, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      have h' := Expr.stripPis_instantiate1_isSome
        (v := .fvar i₀ nm dom) n 0 h
      have hrec := openPisAtFvars_isSome_of_stripPis n (i₀ + 1) h'
      simp only [openPisAtFvars]
      cases h0 : openPisAtFvars n (body.instantiate1 (.fvar i₀ nm dom))
          (i₀ + 1) with
      | none => rw [h0] at hrec; exact nomatch hrec
      | some p => rfl
