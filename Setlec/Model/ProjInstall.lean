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

/-! ## Semantic helpers -/

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open Expr

omit [SetTheory V] in
/-- A consecutively indexed free-variable spine carries its valuation
values, positionally. -/
theorem fvarSpine_exists {D : Nat} {ρ : Nat → V} :
    ∀ (spine : List Expr) (off : Nat),
      (∀ j a, spine[j]? = some a → ∃ nm ty, a = Expr.fvar (off + j) nm ty) →
      off + spine.length ≤ D →
      ∃ vs, FvarSpine D ρ spine vs ∧ vs.length = spine.length ∧
        ∀ j, j < spine.length → vs[j]? = some (ρ (off + j)) := by
  intro spine
  induction spine with
  | nil =>
    intro off _ _
    exact ⟨[], trivial, rfl, fun j hj => by simp at hj⟩
  | cons a as ih =>
    intro off hsh hD
    obtain ⟨nm, ty, ha⟩ := hsh 0 a (by simp)
    rw [Nat.add_zero] at ha
    obtain ⟨vs, hfs, hlen, hpos⟩ := ih (off + 1)
      (fun j x hj => by
        obtain ⟨nm', ty', hx⟩ := hsh (j + 1) x (by simpa using hj)
        exact ⟨nm', ty', by
          rw [show off + 1 + j = off + (j + 1) from by omega]
          exact hx⟩)
      (by simp only [List.length_cons] at hD; omega)
    refine ⟨ρ off :: vs, ⟨⟨off, nm, ty, ha, ?_, rfl⟩, hfs⟩, ?_, ?_⟩
    · simp only [List.length_cons] at hD
      omega
    · simp [hlen]
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.length_cons] at hj
        have := hpos j (by omega)
        simpa [show off + (j + 1) = off + 1 + j from by omega] using this

/-- A consecutively indexed free-variable spine interprets pointwise to
its valuation values. -/
theorem interpSpine_fvars_exists {d : Nat} {ρ : Nat → V} :
    ∀ (spine : List Expr) (off : Nat),
      (∀ j a, spine[j]? = some a → ∃ nm ty, a = Expr.fvar (off + j) nm ty) →
      ∃ vs, InterpSpine cval env φ d ρ spine vs ∧ vs.length = spine.length ∧
        ∀ j, j < spine.length → vs[j]? = some (ρ (off + j)) := by
  intro spine
  induction spine with
  | nil =>
    intro off _
    exact ⟨[], trivial, rfl, fun j hj => by simp at hj⟩
  | cons a as ih =>
    intro off hsh
    obtain ⟨nm, ty, ha⟩ := hsh 0 a (by simp)
    rw [Nat.add_zero] at ha
    obtain ⟨vs, hsp, hlen, hpos⟩ := ih (off + 1)
      (fun j x hj => by
        obtain ⟨nm', ty', hx⟩ := hsh (j + 1) x (by simpa using hj)
        exact ⟨nm', ty', by
          rw [show off + 1 + j = off + (j + 1) from by omega]
          exact hx⟩)
    refine ⟨ρ off :: vs, ⟨?_, hsp⟩, by simp [hlen], ?_⟩
    · rw [ha]
      simp only [interpExpr]
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.length_cons] at hj
        have := hpos j (by omega)
        simpa [show off + (j + 1) = off + 1 + j from by omega] using this

/-- Pointwise spine interpretation is functional in the values. -/
theorem InterpSpine.functional {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs vs' : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ xs vs' → vs = vs' := by
  intro xs
  induction xs with
  | nil =>
    intro vs vs' h h'
    match vs, h with
    | [], _ =>
      match vs', h' with
      | [], _ => rfl
  | cons x xs ih =>
    intro vs vs' h h'
    match vs, h with
    | v :: vs, ⟨hv, hrest⟩ =>
      match vs', h' with
      | v' :: vs', ⟨hv', hrest'⟩ =>
        rw [hv] at hv'
        obtain rfl := Option.some.inj hv'
        rw [ih hrest hrest']

/-! ## The lockstep tower descent -/

set_option maxHeartbeats 3200000 in
/-- Build the projection rule's `TowerOk` spec by descending the
canonical frame, the rule λ-tower and the checked iota statement's
telescope together (their raw binder domains are syntactically shared,
modulo the model renaming on the statement's side), carrying the
partially eliminated theorem inhabitant.  At the bottom the theorem's
`Eq` collapses the interpreted projection redex onto the projected
field's value. -/
theorem proj_tower_rec
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name} {ψ : Name → Nat}
    (hro : RenameOk val' env₁ f)
    {P ctor : Name} {cvA cvj cvt : ConstantVal} {nP nF i : Nat}
    (hi : i < nF)
    {ciP : ConstantInfo}
    (hfP : env₁.find? P = some ciP)
    (hlpsP : ciP.toConstantVal.levelParams = cvA.levelParams)
    (hfj : env₁.find? ctor = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env₁.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = cvA.levelParams)
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    {spineC : List Expr}
    (hN : spineC.length = nP + nF)
    (hspineShape : ∀ j a, spineC[j]? = some a →
      ∃ nm ty, a = Expr.fvar j nm ty)
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hframeTy : ∀ (k : Nat) (a : Expr) (b : Name × Expr × BinderMeta),
      spineC[k]? = some a → cbinders[k]? = some b →
      Expr.fvarTypeD a = instSeq (spineC.take k) (k - 1) b.2.1)
    {sbinders : List (Name × Expr × BinderMeta)} {sbody : Expr}
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    {rhsA : Expr} {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : rhsA.stripLams (nP + nF) = some (rbs, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    (hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbs[k]? = some b → cbinders[k]? = some b' → b.2.1 = b'.2.1)
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    {tySlot : Expr} {ℓA : Level}
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    {bL : Expr}
    (hbLeq : bL = Expr.mkAppN (.const P (cvA.levelParams.map .param))
      (spineC.take nP ++
       [Expr.mkAppN (.const ctor (cvj.levelParams.map .param)) spineC])) :
    ∀ (fvmsK : List (Expr × BinderMeta)) (k : Nat) (ρ : Nat → V)
      (ownSpine : List Expr) (eRk stmtMid : Expr) (thAcc : V),
      k + fvmsK.length = nP + nF →
      fvmsK = (spineC.drop k).zip ((rbs.map (·.2.2)).drop k) →
      ownSpine.length = k →
      (∀ j a, ownSpine[j]? = some a → ∃ nm ty, a = Expr.fvar j nm ty) →
      (∃ rds, Expr.instLamsAt ownSpine rhsA = some (rds, eRk)) →
      (∃ sds, Expr.instPisAt (spineC.take k) cvt.type =
        some (sds, stmtMid)) →
      (∃ Qk, interpExpr V val' env₁ ψ k ρ stmtMid = some Qk ∧
        thAcc ∈ˢ Qk) →
      AnnotOk V val' env₁ ψ k ρ stmtMid →
      TowerOk val' env₁ ψ k ρ fvmsK bL eRk := by
  intro fvmsK
  induction fvmsK with
  | nil =>
    intro k ρ ownSpine eRk stmtMid thAcc hk hfvmsK hOwnLen hOwnShape hR hS
      hSQ hSA
    obtain rfl : k = nP + nF := by simpa using hk
    have htake : spineC.take (nP + nF) = spineC := by
      rw [← hN]
      exact List.take_length
    obtain ⟨sds, hSi⟩ := hS
    rw [htake] at hSi
    obtain ⟨rds, hRi⟩ := hR
    have hSmid : stmtMid = instSeq spineC (spineC.length - 1) sbody :=
      (instPisAt_stripPis spineC hSi (by rw [hN]; exact hS_strip)).1
    rw [hN] at hSmid
    have hRmid : eRk = instSeq ownSpine (ownSpine.length - 1) rbody :=
      (instLamsAt_stripLams ownSpine hRi
        (by rw [hOwnLen]; exact hstripR)).1
    rw [hOwnLen] at hRmid
    -- the projected field resolves to its frame value
    have hOwnB : ∀ a ∈ ownSpine, a.looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, ty, rfl⟩ := hOwnShape j a hj
      rfl
    have hbv := Expr.instSeq_bvar ownSpine (nP + nF - 1) (nF - 1 - i)
      hOwnB (by omega) (by rw [hOwnLen]; omega)
    rw [show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega] at hbv
    obtain ⟨nmr, tyr, hfld⟩ := hOwnShape (nP + i) _ hbv
    have heRi : interpExpr V val' env₁ ψ (nP + nF) ρ eRk =
        some (ρ (nP + i)) := by
      rw [hRmid, hrbody, hfld]
      simp only [interpExpr]
    -- resolve the statement residual's components
    have hbounded : ∀ a ∈ spineC, a.looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, ty, rfl⟩ := hspineShape j a hj
      rfl
    have hresolve : ∀ (j : Nat), j < nP + nF →
        spineC[j]? = some (Expr.instSeq spineC (nP + nF - 1)
          (.bvar (nP + nF - 1 - j))) := by
      intro j hj
      have h1 := Expr.instSeq_bvar spineC (nP + nF - 1)
        (nP + nF - 1 - j) hbounded (by omega) (by rw [hN]; omega)
      rwa [show nP + nF - 1 - (nP + nF - 1 - j) = j from by omega] at h1
    have hres_p : (((List.range nP).map fun j =>
          Expr.bvar (nP + nF - 1 - j))).map
          (Expr.instSeq spineC (nP + nF - 1) ·) = spineC.take nP := by
      refine List.ext_getElem? ?_
      intro j
      rcases Nat.lt_or_ge j nP with hj | hj
      · rw [List.getElem?_take_of_lt hj, List.getElem?_map,
          List.getElem?_map, List.getElem?_range hj,
          hresolve j (by omega)]
        rfl
      · rw [List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_none (by simp; omega),
          List.getElem?_take_eq_none hj]
        rfl
    have hres_x : (((List.range nF).map fun j =>
          Expr.bvar (nF - 1 - j))).map
          (Expr.instSeq spineC (nP + nF - 1) ·) = spineC.drop nP := by
      refine List.ext_getElem? ?_
      intro j
      rcases Nat.lt_or_ge j nF with hj | hj
      · rw [List.getElem?_drop, List.getElem?_map, List.getElem?_map,
          List.getElem?_range hj,
          show spineC[nP + j]? = some (Expr.instSeq spineC (nP + nF - 1)
            (.bvar (nP + nF - 1 - (nP + j)))) from
            hresolve (nP + j) (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        congr 2
        omega
      · rw [List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by
            rw [List.length_drop, hN]
            omega)]
        rfl
    have hctorRes : Expr.instSeq spineC (nP + nF - 1)
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (((List.range nP).map fun j =>
              Expr.bvar (nP + nF - 1 - j)) ++
           ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)))) =
        Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (spineC.take nP ++ spineC.drop nP) := by
      rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
      congr 1
      rw [List.map_append]
      congr 1
      all_goals first
        | exact hres_p
        | exact hres_x
    have hlhsRes : Expr.instSeq spineC (nP + nF - 1)
        (Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
          (((List.range nP).map fun j =>
              Expr.bvar (nP + nF - 1 - j)) ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             (((List.range nP).map fun j =>
                 Expr.bvar (nP + nF - 1 - j)) ++
              ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)))])) =
        Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
          (spineC.take nP ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             (spineC.take nP ++ spineC.drop nP)]) := by
      rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
      congr 1
      rw [List.map_append]
      congr 1
      all_goals first
        | exact hres_p
        | (simp only [List.map_cons, List.map_nil]; rw [hctorRes])
    have hresidual : Expr.instSeq spineC (nP + nF - 1) sbody =
        Expr.mkAppN (.const eqName [ℓA])
          [Expr.instSeq spineC (nP + nF - 1) tySlot,
           Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
            (spineC.take nP ++
             [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
               (spineC.take nP ++ spineC.drop nP)]),
           Expr.instSeq spineC (nP + nF - 1) (.bvar (nF - 1 - i))] := by
      rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
      simp only [List.map_cons, List.map_nil]
      rw [hlhsRes]
    obtain ⟨QN, hQi, hthMem⟩ := hSQ
    rw [hSmid, hresidual] at hQi hSA
    -- the spine's values
    obtain ⟨vals, hvalsSp, hvalsLen, hvalsPos⟩ :=
      interpSpine_fvars_exists (cval := val') (env := env₁) (φ := ψ)
        (d := nP + nF) (ρ := ρ) spineC 0
        (fun j a hj => by
          obtain ⟨nm, ty, ha⟩ := hspineShape j a hj
          exact ⟨nm, ty, by rw [Nat.zero_add]; exact ha⟩)
    -- component values
    obtain ⟨cimC, hfCm, hlpCm⟩ := hro.1 ctor _ hfj
    have hcCi : interpExpr V val' env₁ ψ (nP + nF) ρ
        (.const (f ctor) (cvj.levelParams.map .param)) =
        some (val' ctor ψ) := by
      simp only [interpExpr, hfCm]
      rw [if_pos (by rw [hlpCm]; simp [ConstantInfo.toConstantVal])]
      rw [show cimC.toConstantVal.levelParams = cvj.levelParams from by
        rw [hlpCm]; rfl]
      rw [show Level.substFn ψ cvj.levelParams
          (cvj.levelParams.map .param) = ψ from
        funext fun p => Level.substFn_map_param]
      rw [hro.2.2 ctor]
    have hctorVal : interpExpr V val' env₁ ψ (nP + nF) ρ
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (spineC.take nP ++ spineC.drop nP)) =
        some (SpineFold V (val' ctor ψ) vals) := by
      rw [interp_mkAppN _ _ hcCi
        (InterpSpine.append (InterpSpine.take nP hvalsSp)
          (InterpSpine.drop nP hvalsSp))]
      rw [List.take_append_drop]
    have hcPi : interpExpr V val' env₁ ψ (nP + nF) ρ
        (.const (f P) (cvA.levelParams.map .param)) =
        some (val' P ψ) := by
      simp only [interpExpr, hfPm]
      rw [if_pos (by rw [hPmlps]; simp)]
      rw [show cimP.toConstantVal.levelParams = cvA.levelParams from
        hPmlps]
      rw [show Level.substFn ψ cvA.levelParams
          (cvA.levelParams.map .param) = ψ from
        funext fun p => Level.substFn_map_param]
      rw [hro.2.2 P]
    have hlhsVal : interpExpr V val' env₁ ψ (nP + nF) ρ
        (Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
          (spineC.take nP ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             (spineC.take nP ++ spineC.drop nP)])) =
        some (SpineFold V (val' P ψ)
          (vals.take nP ++ [SpineFold V (val' ctor ψ) vals])) := by
      rw [interp_mkAppN _ _ hcPi
        (InterpSpine.append (InterpSpine.take nP hvalsSp)
          (show InterpSpine val' env₁ ψ (nP + nF) ρ
            [_] [SpineFold V (val' ctor ψ) vals] from ⟨hctorVal, trivial⟩))]
    -- destructure the equation's chain
    obtain ⟨-, hcomps, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
      annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hSA
    obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
      match vsE, hspE with
      | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
      | [], h => exact nomatch h
      | [_], h => exact nomatch h.2
      | [_, _], h => exact nomatch h.2.2
      | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
    obtain ⟨hiα, hil, hir, -⟩ := hspE
    have hvl : vl = SpineFold V (val' P ψ)
        (vals.take nP ++ [SpineFold V (val' ctor ψ) vals]) := by
      rw [hlhsVal] at hil
      exact (Option.some.inj hil).symm
    have hvr : vr = ρ (nP + i) := by
      have h1 := Expr.instSeq_bvar spineC (nP + nF - 1) (nF - 1 - i)
        hbounded (by omega) (by rw [hN]; omega)
      rw [show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega] at h1
      obtain ⟨nm2, ty2, hsh2⟩ := hspineShape (nP + i) _ h1
      rw [hsh2] at hir
      simp only [interpExpr] at hir
      exact (Option.some.inj hir).symm
    have hveq : veq = eqVal V (Level.substFn ψ [uN] [ℓA]) := by
      simp only [interpExpr, heqfind] at hveqi
      rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
      rw [← Option.some.inj hveqi, heqval]
      congr 2
    obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
    obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
    obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
    rw [hveq] at hpi₁ hpi₂ hpi₃
    have hαu : vα ∈ˢ univ (Level.substFn ψ [uN] [ℓA] uN) := by
      have h1 := hpi₁
      simp only [eqVal] at h1
      refine lam_dom_of_ne h1 ?_ vα hmem₁
      simp [Nat.max_eq_zero_iff]
    have hvlmem : vl ∈ˢ vα := by
      have h2 := hpi₂
      rw [eqVal_app hαu] at h2
      refine lam_dom_of_ne h2 ?_ vl hmem₂
      simp [Nat.max_eq_zero_iff]
    have hvrmem : vr ∈ˢ vα := by
      have h3 := hpi₃
      rw [eqVal_app₂ hαu hvlmem] at h3
      refine lam_dom_of_ne h3 ?_ vr hmem₃
      simp
    have hQeqv : QN = eqv vl vr := by
      rw [hfoldQ] at hQi
      rw [← Option.some.inj hQi, hveq]
      show SpineFold V _ [vα, vl, vr] = _
      rw [show SpineFold V (eqVal V (Level.substFn ψ [uN] [ℓA]))
          [vα, vl, vr] =
        SetTheory.app (SetTheory.app (SetTheory.app
          (eqVal V (Level.substFn ψ [uN] [ℓA])) vα) vl) vr from rfl]
      exact eqVal_app₃ hαu hvlmem hvrmem
    have hveq_final : vl = vr := by
      rw [hQeqv] at hthMem
      exact mem_eqv hthMem
    -- interpret and certify the canonical body
    have hPi2 : interpExpr V val' env₁ ψ (nP + nF) ρ
        (.const P (cvA.levelParams.map .param)) =
        some (val' P ψ) := by
      simp only [interpExpr, hfP]
      rw [if_pos (by rw [hlpsP]; simp)]
      rw [show ciP.toConstantVal.levelParams = cvA.levelParams from hlpsP]
      rw [show Level.substFn ψ cvA.levelParams
          (cvA.levelParams.map .param) = ψ from
        funext fun p => Level.substFn_map_param]
    have hCi2 : interpExpr V val' env₁ ψ (nP + nF) ρ
        (.const ctor (cvj.levelParams.map .param)) =
        some (val' ctor ψ) := by
      simp only [interpExpr, hfj]
      rw [if_pos (by simp [ConstantInfo.toConstantVal])]
      rw [show (ConstantInfo.ctorInfo cvj nP nF).toConstantVal.levelParams
          = cvj.levelParams from rfl]
      rw [show Level.substFn ψ cvj.levelParams
          (cvj.levelParams.map .param) = ψ from
        funext fun p => Level.substFn_map_param]
    -- chain slots, transferred from the statement's inversions
    have hlhsA := hcomps _ (show
        Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
          (spineC.take nP ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             (spineC.take nP ++ spineC.drop nP)]) ∈
        [Expr.instSeq spineC (nP + nF - 1) tySlot, _, _] by simp)
    have hLne : spineC.take nP ++
        [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (spineC.take nP ++ spineC.drop nP)] ≠ [] := by
      simp
    obtain ⟨-, hcompsL, vfP, vsL, hifP, hispL, hchainL, -⟩ :=
      annotOk_spine_inv _ (.const (f P) (cvA.levelParams.map .param))
        hLne hlhsA
    have hvfP : vfP = val' P ψ := by
      rw [hcPi] at hifP
      exact (Option.some.inj hifP).symm
    have hvsL : vsL = vals.take nP ++ [SpineFold V (val' ctor ψ) vals] :=
      InterpSpine.functional hispL
        (InterpSpine.append (InterpSpine.take nP hvalsSp)
          ⟨hctorVal, trivial⟩)
    have hctorA := hcompsL _ (show
        Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (spineC.take nP ++ spineC.drop nP) ∈
        spineC.take nP ++
          [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
            (spineC.take nP ++ spineC.drop nP)] by simp)
    have hCne : spineC.take nP ++ spineC.drop nP ≠ [] := by
      rw [List.take_append_drop]
      intro hcon
      rw [hcon] at hN
      simp at hN
      omega
    obtain ⟨-, -, vfC, vsC, hifC, hispC, hchainC, -⟩ :=
      annotOk_spine_inv _
        (.const (f ctor) (cvj.levelParams.map .param)) hCne hctorA
    have hvfC : vfC = val' ctor ψ := by
      rw [hcCi] at hifC
      exact (Option.some.inj hifC).symm
    have hvsC : vsC = vals := by
      refine InterpSpine.functional hispC ?_
      have := InterpSpine.append (InterpSpine.take nP hvalsSp)
        (InterpSpine.drop nP hvalsSp)
      rwa [List.take_append_drop nP vals] at this
    -- assemble the body's truthfulness and value
    have hfvA : ∀ x ∈ spineC, AnnotOk V val' env₁ ψ (nP + nF) ρ x := by
      intro x hx
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      obtain ⟨nm, ty, rfl⟩ := hspineShape j x hj
      simp only [AnnotOk]
    have hchainC' : ChainSlots V (val' ctor ψ) vals := by
      rw [← hvfC, ← hvsC]
      exact hchainC
    obtain ⟨hActor, hictor⟩ := annotOk_spine spineC
      (.const ctor (cvj.levelParams.map .param))
      (by simp only [AnnotOk]) hCi2 hfvA hvalsSp hchainC'
    have hchainL' : ChainSlots V (val' P ψ)
        (vals.take nP ++ [SpineFold V (val' ctor ψ) vals]) := by
      rw [← hvfP, ← hvsL]
      exact hchainL
    obtain ⟨hAbL, hibL⟩ := annotOk_spine
      (spineC.take nP ++
        [Expr.mkAppN (.const ctor (cvj.levelParams.map .param)) spineC])
      (.const P (cvA.levelParams.map .param))
      (by simp only [AnnotOk]) hPi2
      (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hfvA x (List.mem_of_mem_take hx)
        · obtain rfl : x = Expr.mkAppN
              (.const ctor (cvj.levelParams.map .param)) spineC := by
            simpa using hx
          exact hActor)
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        (show InterpSpine val' env₁ ψ (nP + nF) ρ [_]
          [SpineFold V (val' ctor ψ) vals] from ⟨hictor, trivial⟩))
      hchainL'
    rw [hbLeq]
    refine TowerOk.nil (w := ρ (nP + i)) ?_ heRi hAbL
    rw [hibL]
    congr 1
    rw [← hvl, hveq_final, hvr]
  | cons pk rest ih =>
    intro k ρ ownSpine eRk stmtMid thAcc hk hfvmsK hOwnLen hOwnShape hR hS
      hSQ hSA
    have hkN : k < nP + nF := by
      simp only [List.length_cons] at hk
      omega
    -- peel the frame entry
    cases hsd : spineC.drop k with
    | nil =>
      rw [hsd] at hfvmsK
      simp at hfvmsK
    | cons a arest =>
    cases hmd : (rbs.map (·.2.2)).drop k with
    | nil =>
      rw [hsd, hmd] at hfvmsK
      simp at hfvmsK
    | cons mk mrest =>
      rw [hsd, hmd] at hfvmsK
      simp only [List.zip_cons_cons, List.cons.injEq] at hfvmsK
      obtain ⟨rfl, rfl⟩ := hfvmsK
      have hak : spineC[k]? = some a := by
        have h0 : (spineC.drop k)[0]? = some a := by rw [hsd]; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      have harest : spineC.drop (k + 1) = arest := by
        have h0 : (spineC.drop k).tail = arest := by rw [hsd]; rfl
        rwa [List.tail_drop] at h0
      have hmk : (rbs.map (·.2.2))[k]? = some mk := by
        have h0 : ((rbs.map (·.2.2)).drop k)[0]? = some mk := by
          rw [hmd]; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      have hmrest : (rbs.map (·.2.2)).drop (k + 1) = mrest := by
        have h0 : ((rbs.map (·.2.2)).drop k).tail = mrest := by
          rw [hmd]; rfl
        rwa [List.tail_drop] at h0
      -- the binder rows at position `k`
      have hcbLen : cbinders.length = nP + nF :=
        Expr.stripPis_length _ hC_strip
      have hsbLen : sbinders.length = nP + nF :=
        Expr.stripPis_length _ hS_strip
      have hrbLen : rbs.length = nP + nF :=
        Expr.stripLams_length _ hstripR
      obtain ⟨cb, hcb⟩ : ∃ cb, cbinders[k]? = some cb :=
        ⟨cbinders[k]'(by omega), List.getElem?_eq_getElem _⟩
      obtain ⟨sb, hsb⟩ : ∃ sb, sbinders[k]? = some sb :=
        ⟨sbinders[k]'(by omega), List.getElem?_eq_getElem _⟩
      obtain ⟨rb, hrb⟩ : ∃ rb, rbs[k]? = some rb :=
        ⟨rbs[k]'(by omega), List.getElem?_eq_getElem _⟩
      obtain rfl : mk = rb.2.2 := by
        simp only [List.getElem?_map, hrb, Option.map_some,
          Option.some.injEq] at hmk
        exact hmk.symm
      -- the frame variable's shape and annotation
      obtain ⟨nmC, tyC0, haC⟩ := hspineShape k a hak
      have htyC : tyC0 = instSeq (spineC.take k) (k - 1) cb.2.1 := by
        have h1 := hframeTy k a cb hak hcb
        rw [haC] at h1
        simpa [Expr.fvarTypeD] using h1
      subst haC
      subst htyC
      -- statement telescope: peel one binder
      have htklen : (spineC.take k).length = k := by
        rw [List.length_take, hN]
        omega
      obtain ⟨sds, hSi⟩ := hS
      obtain ⟨sbodyMid, hSmidEq, hSext⟩ :=
        Expr.instPisAt_head (mrem := nP + nF - k - 1) (spineC.take k) hSi
          (by rw [htklen,
                show k + (nP + nF - k - 1 + 1) = nP + nF from by omega]
              exact hS_strip)
          (by rw [htklen]; exact hsb)
      rw [htklen] at hSmidEq hSext
      subst hSmidEq
      -- the statement's interpretation peels to the shared domain
      obtain ⟨QK, hQk, hthm⟩ := hSQ
      simp only [AnnotOk] at hSA
      obtain ⟨hAsdom, ⟨scod, hscod⟩, hScond⟩ := hSA
      rw [interpExpr, hscod] at hQk
      cases hAs : interpExpr V val' env₁ ψ k ρ
          (instSeq (spineC.take k) (k - 1) sb.2.1) with
      | none =>
        rw [hAs] at hQk
        exact nomatch hQk
      | some As =>
      rw [hAs] at hQk
      dsimp only at hQk
      obtain rfl := Option.some.inj hQk
      -- the shared-domain interp equalities
      have hfvTake : ∀ x ∈ spineC.take k, ∃ i' nm' ty',
          x = Expr.fvar i' nm' ty' := by
        intro x hx
        obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.mem_of_mem_take hx)
        obtain ⟨nm', ty', hx'⟩ := hspineShape j x hj
        exact ⟨j, nm', ty', hx'⟩
      have hsdomEq : sb.2.1 = (cb.2.1).renameConsts f :=
        hsdoms k sb cb hsb hcb
      have hAs' : interpExpr V val' env₁ ψ k ρ
          (instSeq (spineC.take k) (k - 1) cb.2.1) = some As := by
        rw [← interp_instSeq_ren hro hfvTake (X := cb.2.1) (t := k - 1),
          ← hsdomEq]
        exact hAs
      -- the rule tower: peel one binder
      obtain ⟨rds, hRi⟩ := hR
      obtain ⟨rbodyR, hRmidEq, hRext⟩ :=
        Expr.instLamsAt_head (mrem := nP + nF - k - 1) ownSpine hRi
          (by rw [hOwnLen,
                show k + (nP + nF - k - 1 + 1) = nP + nF from by omega]
              exact hstripR)
          (by rw [hOwnLen]; exact hrb)
      rw [hOwnLen] at hRmidEq hRext
      subst hRmidEq
      -- both instantiated domains interpret alike
      have hOwnFvs : ∀ j x, ownSpine[j]? = some x →
          ∃ nm' ty', x = Expr.fvar (0 + j) nm' ty' := by
        intro j x hj
        obtain ⟨nm', ty', hx⟩ := hOwnShape j x hj
        exact ⟨nm', ty', by rw [Nat.zero_add]; exact hx⟩
      have hTakeFvs : ∀ j x, (spineC.take k)[j]? = some x →
          ∃ nm' ty', x = Expr.fvar (0 + j) nm' ty' := by
        intro j x hj
        rcases Nat.lt_or_ge j k with hjk | hjk
        · rw [List.getElem?_take_of_lt hjk] at hj
          obtain ⟨nm', ty', hx⟩ := hspineShape j x hj
          exact ⟨nm', ty', by rw [Nat.zero_add]; exact hx⟩
        · rw [List.getElem?_take_eq_none hjk] at hj
          exact nomatch hj
      obtain ⟨vsO, hfsO, hlenO, hposO⟩ :=
        fvarSpine_exists (D := k) (ρ := ρ) ownSpine 0 hOwnFvs
          (by omega)
      obtain ⟨vsT, hfsT, hlenT, hposT⟩ :=
        fvarSpine_exists (D := k) (ρ := ρ) (spineC.take k) 0 hTakeFvs
          (by rw [htklen]; omega)
      obtain rfl : vsO = vsT := by
        refine List.ext_getElem? ?_
        intro j
        rcases Nat.lt_or_ge j k with hjk | hjk
        · rw [hposO j (by omega), hposT j (by rw [htklen]; omega)]
        · rw [List.getElem?_eq_none (by rw [hlenO, hOwnLen]; omega),
            List.getElem?_eq_none (by rw [hlenT, htklen]; omega)]
      have hcbcl : cb.2.1.hasFvar = false :=
        stripPis_doms_hasFvar _ hC_strip hCcl cb (List.mem_of_getElem? hcb)
      have hcbb : cb.2.1.looseBVarsBounded k = true := by
        have h1 := stripPis_doms_bounded _ 0 hC_strip hCb k cb hcb
        simpa using h1
      have htyR2 : interpExpr V val' env₁ ψ k ρ
          (instSeq ownSpine (k - 1) rb.2.1) = some As := by
        rw [hdoms k rb cb hrb hcb]
        have h1 := interp_instSeq_fvarFrames (e := cb.2.1)
          (cval := val') (env := env₁) (φ := ψ)
          hcbcl (by rw [hOwnLen]; exact hcbb) hfsO hfsT
        rw [hOwnLen, htklen] at h1
        rw [h1]
        exact hAs'
      -- the frame annotation's truthfulness
      have hAty : AnnotOk V val' env₁ ψ k ρ
          (instSeq (spineC.take k) (k - 1) cb.2.1) := by
        have hee : Expr.ErasedEq
            (instSeq (spineC.take k) (k - 1) sb.2.1)
            ((instSeq (spineC.take k) (k - 1) cb.2.1).renameConsts f) := by
          rw [hsdomEq]
          refine Expr.ErasedEq.symm (instSeq_renameConsts _ _ ?_)
          intro x hx
          obtain ⟨i', nm', ty', hx'⟩ := hfvTake x hx
          rw [hx']
          simp [Expr.renameConsts, Expr.ErasedEq]
        exact AnnotOk_renameConsts hro _ k ρ
          (AnnotOk.erasedEq _ hee k ρ hAsdom)
      refine TowerOk.cons hAs' htyR2 hAty ?_
      intro x hx
      -- the statement inhabitant descends through the binder
      obtain ⟨hSbodyA, hSwfact⟩ := hScond x As hAs hx
      have hfib : ∀ y, y ∈ˢ As →
          ((interpExpr V val' env₁ ψ (k + 1) (updV V ρ k y)
            (sbodyMid.instantiate1 (.fvar k sb.1
              (instSeq (spineC.take k) (k - 1) sb.2.1)))).getD
            SetTheory.empty) ∈ˢ univ (scod.eval ψ) := by
        intro y hy
        obtain ⟨-, hwf⟩ := hScond y As hAs hy
        obtain ⟨w, hwi, hwu⟩ := hwf scod hscod
        rw [hwi]
        exact hwu
      have happ := app_mem hthm hx hfib
      obtain ⟨w, hwi, hwu⟩ := hSwfact scod hscod
      rw [hwi] at happ
      simp only [Option.getD_some] at happ
      have hEE : Expr.ErasedEq
          (sbodyMid.instantiate1 (.fvar k sb.1
            (instSeq (spineC.take k) (k - 1) sb.2.1)))
          (sbodyMid.instantiate1 (.fvar k nmC
            (instSeq (spineC.take k) (k - 1) cb.2.1))) :=
        Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl _)
          (by simp [Expr.ErasedEq])
      have hwi' : interpExpr V val' env₁ ψ (k + 1) (updV V ρ k x)
          (sbodyMid.instantiate1 (.fvar k nmC
            (instSeq (spineC.take k) (k - 1) cb.2.1))) = some w := by
        rw [← interp_erasedEq hEE (k + 1) (updV V ρ k x)]
        exact hwi
      have hSA' : AnnotOk V val' env₁ ψ (k + 1) (updV V ρ k x)
          (sbodyMid.instantiate1 (.fvar k nmC
            (instSeq (spineC.take k) (k - 1) cb.2.1))) :=
        AnnotOk.erasedEq _ hEE (k + 1) (updV V ρ k x) hSbodyA
      have htake1 : spineC.take (k + 1) = spineC.take k ++
          [Expr.fvar k nmC (instSeq (spineC.take k) (k - 1) cb.2.1)] := by
        rw [List.take_add_one, hak]
        rfl
      refine ih (k + 1) (updV V ρ k x)
        (ownSpine ++ [Expr.fvar k rb.1 (instSeq ownSpine (k - 1) rb.2.1)])
        _ _ (SetTheory.app thAcc x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hSA'
      · simp only [List.length_cons] at hk
        omega
      · rw [harest, hmrest]
      · simp [hOwnLen]
      · intro j x' hj
        rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
        · rw [List.getElem?_append_left (by rw [hOwnLen]; exact hjk)]
            at hj
          exact hOwnShape j x' hj
        · have hj' : j = ownSpine.length := by omega
          rw [hj', List.getElem?_concat_length] at hj
          obtain rfl := Option.some.inj hj
          exact ⟨rb.1, _, by rw [hjk]⟩
        · rw [List.getElem?_eq_none (by simp [hOwnLen]; omega)] at hj
          exact nomatch hj
      · exact ⟨_, hRext _⟩
      · rw [htake1]
        exact ⟨_, hSext _⟩
      · exact ⟨w, hwi', happ⟩

set_option maxHeartbeats 3200000 in
/-- The projection rule's bottom fact (`Hbot` of `TowerOk.of_stages`):
over any full frame-fitting value list, the canonical body (the
projection applied to the parameters and the applied constructor)
interprets, at the *extended* environment carrying the projection
recursor, equal to the rule tower's instantiated body — the field's
own frame value — and its annotations are truthful.  The checked
`proj_i.iota` theorem eliminates at the master frame over the *base*
environment (where the kernel ran the definitional parameter pins),
and the residual facts transport across the fresh extension. -/
theorem proj_bottom
    {env : Env} (m₀ : EnvModel V env) (F : Nat) {ψ : Name → Nat}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {f : Name → Name}
    (hro₀ : RenameOk m₀.val env f)
    (hro₁ : RenameOk m₀.val (⟨c₀ :: env.consts⟩ : Env) f)
    {P ctor : Name} {cvA cvj cvt : ConstantVal} {nP nF i : Nat}
    (hi : i < nF)
    (hfP₁ : (⟨c₀ :: env.consts⟩ : Env).find? P = some c₀)
    (hlpsP : c₀.toConstantVal.levelParams = cvA.levelParams)
    (hfj : env.find? ctor = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = cvA.levelParams)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts, over the base environment
    {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V m₀.val env ψ'' cvt.type = some Pv ∧
      m₀.val thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSres : cvt.type.constsResolve env = true)
    -- the statement's shape
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    {sbinders : List (Name × Expr × BinderMeta)} {sbody : Expr}
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    {tySlot : Expr} {ℓA : Level}
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    -- the rule right-hand side
    {rhsA : Expr} {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : rhsA.stripLams (nP + nF) = some (rbs, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    -- the kernel pins over the base environment
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvs : List Expr} {crest2X : Expr}
    {ldoms : List Expr} {lrestL : Expr}
    (hopenP : openPisAtFvars nP cvA.type 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt fvsP cvj.type = some (cdomsP, crestP))
    (hdeParsP : DefEqListOk F env (nP + nF)
      (fvsP.map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars nF crestP nP = some (xFvs, crest2X))
    (hlinstP : Expr.instLamsAt (fvsP ++ xFvs) rhsA =
      some (ldoms, lrestL))
    -- well-formedness over the base environment
    (htyw : cvA.type.hasFvar = false)
    (htyb : cvA.type.looseBVarsBounded 0 = true)
    (hTres : cvA.type.constsResolve env = true)
    (hAty : AnnotOk V m₀.val env ψ 0 (rho0 V) cvA.type)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCres : cvj.type.constsResolve env = true)
    (hACty : AnnotOk V m₀.val env ψ 0 (rho0 V) cvj.type)
    (hICty : ∃ T, interpClosed V m₀.val env ψ cvj.type = some T) :
    ∀ (xs : List V), xs.length = nP + nF →
      FramePref m₀.val env ψ (fvsP ++ xFvs) xs →
      (∃ w, interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
          (fun l => xs.getD l SetTheory.empty)
          (Expr.mkAppN (.const P (cvA.levelParams.map .param))
            ((fvsP ++ xFvs).take nP ++
              [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
                (fvsP ++ xFvs)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrestL →
          interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
            (fun l => xs.getD l SetTheory.empty) e = some w) ∧
      AnnotOk V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
        (fun l => xs.getD l SetTheory.empty)
        (Expr.mkAppN (.const P (cvA.levelParams.map .param))
          ((fvsP ++ xFvs).take nP ++
            [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
              (fvsP ++ xFvs)])) := by
  intro xs hxs hpref
  -- ===== B0: the master frame's public walks (base environment) =====
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec nP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf nP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec nF nP hopenX
  have hspineLen : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hfvsPLen, hxLen]
  have hspP : FvarSpine (nP + nF)
      (fun l => xs.getD l SetTheory.empty) fvsP (xs.take nP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < nP := by
      rcases Nat.lt_or_ge j nP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (nP + nF) a := fun a ha => by
    have h := (hfvsPWf a ha).1
    exact h.mono (by omega)
  have hmemP : ∀ (l : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[l]? = some a →
      (xs.take nP)[l]? = some v →
      ∃ B, interpExpr V m₀.val env ψ (nP + nF)
        (fun l' => xs.getD l' SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro l a v ha hv
    have hlr : l < nP := by
      rcases Nat.lt_or_ge l nP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hlr] at hv
    have hlfv : l < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[l]? = some fvi :=
      ⟨fvsP[l]'hlfv, List.getElem?_eq_getElem hlfv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvs)[l]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref l v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape l fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped l (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := nP + nF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (nP + nF) cvA.type := WScoped.of_not_hasFvar htyw
  have hΘP := (self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw)
    (AnnotOk.closed_invariant htyw _ _ hAty) hmemP).2
  have hLsP : ∀ a ∈ fvsP, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a ha).2.2
  -- the constructor walk at the parameters, through the pins
  have hWc : WScoped (nP + nF) cvj.type := WScoped.of_not_hasFvar hCw
  have hAc : AnnotOk V m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvj.type :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvj.type = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m₀ F hcinstP hdeParsP hspP hwsP
    hLsP hΘP hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcrEx⟩ := peel_walk hcinstP hspP hwsP hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  have hFcr : FvarsOk V m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hΘP a ha l hla
  have hLcr : Expr.LeavesBounded crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hLsP a ha l hla
  -- the field walk
  have hwsCrP : ∀ a ∈ fvsP, WScoped nP a := by
    intro a ha
    have h := (hfvsPWf a ha).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcrRp⟩ := instPisAt_wscoped (D := nP) fvsP
    hcinstP (WScoped.of_not_hasFvar hCw) hwsCrP
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf nF nP hopenX hWcrRp
    hbcr hLcr
  have hspX : FvarSpine (nP + nF)
      (fun l => xs.getD l SetTheory.empty) xFvs (xs.drop nP) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_drop]; omega) (by omega) ?_
    intro j v hjv
    rw [List.getElem?_drop] at hjv
    show xs.getD (nP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsX : ∀ a ∈ xFvs, WScoped (nP + nF) a := fun a ha =>
    (hxWf a ha).1
  have hLsX : ∀ a ∈ xFvs, Expr.LeavesBounded a := fun a ha =>
    (hxWf a ha).2.2
  have hmemX : ∀ (l : Nat) (a : Expr) (v : V),
      (xFvs.map Expr.fvarTypeD)[l]? = some a →
      (xs.drop nP)[l]? = some v →
      ∃ B, interpExpr V m₀.val env ψ (nP + nF)
        (fun l' => xs.getD l' SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro l a v ha hv
    have hlt : l < nF := by
      rcases Nat.lt_or_ge l nF with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hlx : l < xFvs.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvs[l]? = some fvi :=
      ⟨xFvs[l]'hlx, List.getElem?_eq_getElem hlx⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvs)[nP + l]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show nP + l - nP = l from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (nP + l) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape l fvi hfvi
    have hWi : WScoped (nP + l) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := nP + nF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWcrD' : WScoped (nP + nF) crestP := hWcrRp.mono (by omega)
  obtain ⟨hfitXP, hΘX⟩ := self_walk hxInst hspX hwsX hWcrD' hbcr hLcr
    hFcr hAcr hmemX
  have hfitCfullP : TeleFitI V m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvj.type
      (fvsP ++ xFvs) (xs.take nP ++ xs.drop nP) crest2X :=
    TeleFitI.append hfitC hfitXP
  -- ===== B1: the statement walk at the same spine =====
  have hspPX : FvarSpine (nP + nF)
      (fun l => xs.getD l SetTheory.empty) (fvsP ++ xFvs) xs := by
    have h := FvarSpine.append hspP hspX
    rwa [List.take_append_drop] at h
  have hwsPX : ∀ a ∈ fvsP ++ xFvs, WScoped (nP + nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hwsP a ha
    · exact hwsX a ha
  have hcombined : Expr.instPisAt (fvsP ++ xFvs) cvj.type =
      some (cdomsP ++ xFvs.map Expr.fvarTypeD, crest2X) :=
    instPisAt_append_of fvsP hcinstP hxInst
  have hiaPX : InstArgs m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) (fvsP ++ xFvs)
      (xs.take nP ++ xs.drop nP) :=
    InstArgs.of_fvarSpine (by
        rw [List.take_append_drop]
        exact hspPX)
      (fun a ha => by
        rcases List.mem_append.mp ha with ha' | ha'
        · exact ⟨hwsP a ha', (hfvsPWf a ha').2.1⟩
        · exact ⟨hwsX a ha', (hxWf a ha').2.1⟩)
  have hpackComb := fit_mem_frames (φ := ψ) hCw hCb hC_strip hcombined
    hspineLen hiaPX hfitCfullP
  -- the statement telescope's own walk, memberships along `hsdoms`
  obtain ⟨⟨sds, stmtRes⟩, hSinst⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvsP ++ xFvs)
        (by rw [hspineLen, hS_strip]; rfl))
  have hfvPXShapes : ∀ x ∈ fvsP ++ xFvs, ∃ i' n' t',
      x = Expr.fvar i' n' t' := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx'
      obtain ⟨nm, hsh⟩ := hfvsPShape j x hj
      exact ⟨0 + j, nm, _, hsh⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx'
      obtain ⟨nm, hsh⟩ := hxShape j x hj
      exact ⟨nP + j, nm, _, hsh⟩
  have hmemS : ∀ (l : Nat) (a : Expr) (v : V), sds[l]? = some a →
      xs[l]? = some v →
      ∃ B, interpExpr V m₀.val env ψ (nP + nF)
        (fun l' => xs.getD l' SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro l a v ha hv
    have hlN : l < nP + nF := by
      rcases Nat.lt_or_ge l (nP + nF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hSinst, hspineLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨sb, hsb⟩ : ∃ sb, sbinders[l]? = some sb := by
      have := Expr.stripPis_length (nP + nF) hS_strip
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨cb, hcb⟩ : ∃ cb, cbinders[l]? = some cb := by
      have := Expr.stripPis_length (nP + nF) hC_strip
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsS⟩ := instPisAt_stripPis (fvsP ++ xFvs) hSinst
      (by rw [hspineLen]; exact hS_strip)
    have ha1 := hdsS l sb hsb
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨-, hdsC⟩ := instPisAt_stripPis (fvsP ++ xFvs) hcombined
      (by rw [hspineLen]; exact hC_strip)
    obtain ⟨B, hBi, hvB⟩ := hpackComb l _ v (hdsC l cb hcb)
      (by rw [List.take_append_drop]; exact hv)
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvsP ++ xFvs).take l, ∃ i' n' t',
        x = Expr.fvar i' n' t' := fun x hx =>
      hfvPXShapes x (List.mem_of_mem_take hx)
    rw [hsdoms l sb cb hsb hcb, interp_instSeq_ren hro₀ hshapes]
    exact hBi
  -- eliminate the theorem's inhabitant at the master frame
  obtain ⟨hfitS, hQEx⟩ := peel_walk hSinst hspPX hwsPX
    (WScoped.of_not_hasFvar hSw)
    (AnnotOk.closed_invariant hSw _ _ (hthm_annot ψ))
    (by
      obtain ⟨Pv, hPv, -⟩ := hthm_mem ψ
      refine ⟨Pv, ?_⟩
      rw [interp_closed_invariant hSw _ _]
      exact hPv)
    hmemS
  obtain ⟨Pv, hPvc, hPvMem⟩ := hthm_mem ψ
  have hPvI : interpExpr V m₀.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvt.type = some Pv := by
    rw [interp_closed_invariant hSw _ _]
    exact hPvc
  obtain ⟨Q0, hQ0, hQMem0, hSAres⟩ := TeleFitI.elim hfitS
    (AnnotOk.closed_invariant hSw _ _ (hthm_annot ψ)) hPvI hPvMem
  -- transport the residual's facts across the fresh extension
  have hfvsPres : ∀ a ∈ fvsP, a.constsResolve env = true :=
    (openPisAtFvars_resolve nP 0 hopenP hTres).1
  have hcrestPres : crestP.constsResolve env = true :=
    instPisAt_resolve fvsP hcinstP hCres hfvsPres
  have hxFvsRes : ∀ a ∈ xFvs, a.constsResolve env = true :=
    (openPisAtFvars_resolve nF nP hopenX hcrestPres).1
  have hspineRes : ∀ a ∈ fvsP ++ xFvs, a.constsResolve env = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsPres a ha
    · exact hxFvsRes a ha
  have hResRes : stmtRes.constsResolve env = true :=
    instPisAt_resolve (fvsP ++ xFvs) hSinst hSres hspineRes
  have hSQ1 : ∃ QN, interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ
      (nP + nF) (fun l => xs.getD l SetTheory.empty) stmtRes =
        some QN ∧
      SpineFold V (m₀.val thmName ψ) xs ∈ˢ QN := by
    refine ⟨Q0, ?_, hQMem0⟩
    rw [interp_mono (cval := m₀.val) hfresh stmtRes _ _ hResRes]
    exact hQ0
  have hSA1 : AnnotOk V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) stmtRes :=
    AnnotOk.mono hfresh stmtRes _ _ hResRes hSAres
  -- the extended environment's lookups
  have hfj₁ : (⟨c₀ :: env.consts⟩ : Env).find? ctor =
      some (.ctorInfo cvj nP nF) := by
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfj]; rfl)]
    exact hfj
  have hfPm₁ : (⟨c₀ :: env.consts⟩ : Env).find? (f P) = some cimP := by
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfPm]; rfl)]
    exact hfPm
  have heqfind₁ : (⟨c₀ :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons_of_isSome hfresh (by rw [heqfind]; rfl)]
    exact heqfind
  -- shapes at absolute indices
  have hspineLenA := hspineLen
  have hspineShapeA : ∀ (j : Nat) (a : Expr),
      (fvsP ++ xFvs)[j]? = some a → ∃ nm ty, a = Expr.fvar j nm ty := by
    intro j a hj
    rcases Nat.lt_or_ge j nP with hjn | hjn
    · rw [List.getElem?_append_left (by omega)] at hj
      obtain ⟨nm, ha⟩ := hfvsPShape j a hj
      rw [Nat.zero_add] at ha
      exact ⟨nm, Expr.fvarTypeD a, ha⟩
    · rw [List.getElem?_append_right (by omega), hfvsPLen] at hj
      obtain ⟨nm, ha⟩ := hxShape (j - nP) a hj
      refine ⟨nm, Expr.fvarTypeD a, ?_⟩
      rw [show j = nP + (j - nP) from by omega]
      exact ha
  -- the residuals' instantiated forms
  have hSmid : stmtRes = instSeq (fvsP ++ xFvs) (nP + nF - 1) sbody := by
    have h1 := (instPisAt_stripPis (fvsP ++ xFvs) hSinst
      (by rw [hspineLenA]; exact hS_strip)).1
    rw [hspineLenA] at h1
    exact h1
  have hRmid : lrestL = instSeq (fvsP ++ xFvs) (nP + nF - 1) rbody := by
    have h1 := (instLamsAt_stripLams (fvsP ++ xFvs) hlinstP
      (by rw [hspineLenA]; exact hstripR)).1
    rw [hspineLenA] at h1
    exact h1
  have hOwnB : ∀ a ∈ fvsP ++ xFvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hspineShapeA j a hj
    rfl
  have hbv := Expr.instSeq_bvar (fvsP ++ xFvs) (nP + nF - 1)
    (nF - 1 - i) hOwnB (by omega) (by rw [hspineLenA]; omega)
  rw [show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega] at hbv
  obtain ⟨nmr, tyr, hfld⟩ := hspineShapeA (nP + i) _ hbv
  have heRi : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ
      (nP + nF) (fun l => xs.getD l SetTheory.empty) lrestL =
      some (xs.getD (nP + i) SetTheory.empty) := by
    rw [hRmid, hrbody, hfld]
    simp only [interpExpr]
  have hbounded : ∀ a ∈ (fvsP ++ xFvs), a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hspineShapeA j a hj
    rfl
  have hresolve : ∀ (j : Nat), j < nP + nF →
      (fvsP ++ xFvs)[j]? = some (Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1)
        (.bvar (nP + nF - 1 - j))) := by
    intro j hj
    have h1 := Expr.instSeq_bvar (fvsP ++ xFvs) (nP + nF - 1)
      (nP + nF - 1 - j) hbounded (by omega) (by rw [hspineLenA]; omega)
    rwa [show nP + nF - 1 - (nP + nF - 1 - j) = j from by omega] at h1
  have hres_p : (((List.range nP).map fun j =>
        Expr.bvar (nP + nF - 1 - j))).map
        (Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) ·) = (fvsP ++ xFvs).take nP := by
    refine List.ext_getElem? ?_
    intro j
    rcases Nat.lt_or_ge j nP with hj | hj
    · rw [List.getElem?_take_of_lt hj, List.getElem?_map,
        List.getElem?_map, List.getElem?_range hj,
        hresolve j (by omega)]
      rfl
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_take_eq_none hj]
      rfl
  have hres_x : (((List.range nF).map fun j =>
        Expr.bvar (nF - 1 - j))).map
        (Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) ·) = (fvsP ++ xFvs).drop nP := by
    refine List.ext_getElem? ?_
    intro j
    rcases Nat.lt_or_ge j nF with hj | hj
    · rw [List.getElem?_drop, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hj,
        show (fvsP ++ xFvs)[nP + j]? = some (Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1)
          (.bvar (nP + nF - 1 - (nP + j)))) from
          hresolve (nP + j) (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      congr 2
      omega
    · rw [List.getElem?_map, List.getElem?_map,
        List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by
          rw [List.length_drop, hspineLenA]
          omega)]
      rfl
  have hctorRes : Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (((List.range nP).map fun j =>
            Expr.bvar (nP + nF - 1 - j)) ++
         ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)))) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p
      | exact hres_x
  have hlhsRes : Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1)
      (Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        (((List.range nP).map fun j =>
            Expr.bvar (nP + nF - 1 - j)) ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           (((List.range nP).map fun j =>
               Expr.bvar (nP + nF - 1 - j)) ++
            ((List.range nF).map fun j => Expr.bvar (nF - 1 - j)))])) =
      Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)]) := by
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    rw [List.map_append]
    congr 1
    all_goals first
      | exact hres_p
      | (simp only [List.map_cons, List.map_nil]; rw [hctorRes])
  have hresidual : Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) sbody =
      Expr.mkAppN (.const eqName [ℓA])
        [Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) tySlot,
         Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
          ((fvsP ++ xFvs).take nP ++
           [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
             ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)]),
         Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) (.bvar (nF - 1 - i))] := by
    rw [hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
    simp only [List.map_cons, List.map_nil]
    rw [hlhsRes]
  obtain ⟨QN, hQi, hthMem⟩ := hSQ1
  rw [hSmid, hresidual] at hQi hSA1
  -- the spine's values
  obtain ⟨vals, hvalsSp, hvalsLen, hvalsPos⟩ :=
    interpSpine_fvars_exists (cval := m₀.val) (env := (⟨c₀ :: env.consts⟩ : Env)) (φ := ψ)
      (d := nP + nF) (ρ := fun l => xs.getD l SetTheory.empty) (fvsP ++ xFvs) 0
      (fun j a hj => by
        obtain ⟨nm, ty, ha⟩ := hspineShapeA j a hj
        exact ⟨nm, ty, by rw [Nat.zero_add]; exact ha⟩)
  -- component values
  obtain ⟨cimC, hfCm, hlpCm⟩ := hro₁.1 ctor _ hfj₁
  have hcCi : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const (f ctor) (cvj.levelParams.map .param)) =
      some (m₀.val ctor ψ) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hlpCm]; simp [ConstantInfo.toConstantVal])]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from by
      rw [hlpCm]; rfl]
    rw [show Level.substFn ψ cvj.levelParams
        (cvj.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
    rw [hro₁.2.2 ctor]
  have hctorVal : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)) =
      some (SpineFold V (m₀.val ctor ψ) vals) := by
    rw [interp_mkAppN _ _ hcCi
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        (InterpSpine.drop nP hvalsSp))]
    rw [List.take_append_drop]
  have hcPi : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const (f P) (cvA.levelParams.map .param)) =
      some (m₀.val P ψ) := by
    simp only [interpExpr, hfPm₁]
    rw [if_pos (by rw [hPmlps]; simp)]
    rw [show cimP.toConstantVal.levelParams = cvA.levelParams from
      hPmlps]
    rw [show Level.substFn ψ cvA.levelParams
        (cvA.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
    rw [hro₁.2.2 P]
  have hlhsVal : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)])) =
      some (SpineFold V (m₀.val P ψ)
        (vals.take nP ++ [SpineFold V (m₀.val ctor ψ) vals])) := by
    rw [interp_mkAppN _ _ hcPi
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        (show InterpSpine m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
          [_] [SpineFold V (m₀.val ctor ψ) vals] from ⟨hctorVal, trivial⟩))]
  -- destructure the equation's chain
  obtain ⟨-, hcomps, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hSA1
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hvl : vl = SpineFold V (m₀.val P ψ)
      (vals.take nP ++ [SpineFold V (m₀.val ctor ψ) vals]) := by
    rw [hlhsVal] at hil
    exact (Option.some.inj hil).symm
  have hvr : vr = xs.getD (nP + i) SetTheory.empty := by
    have h1 := Expr.instSeq_bvar (fvsP ++ xFvs) (nP + nF - 1) (nF - 1 - i)
      hbounded (by omega) (by rw [hspineLenA]; omega)
    rw [show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega] at h1
    obtain ⟨nm2, ty2, hsh2⟩ := hspineShapeA (nP + i) _ h1
    rw [hsh2] at hir
    simp only [interpExpr] at hir
    exact (Option.some.inj hir).symm
  have hveq : veq = eqVal V (Level.substFn ψ [uN] [ℓA]) := by
    simp only [interpExpr, heqfind₁] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn ψ [uN] [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : QN = eqv vl vr := by
    rw [hfoldQ] at hQi
    rw [← Option.some.inj hQi, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn ψ [uN] [ℓA]))
        [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [ℓA])) vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hveq_final : vl = vr := by
    rw [hQeqv] at hthMem
    exact mem_eqv hthMem
  -- interpret and certify the canonical body
  have hPi2 : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const P (cvA.levelParams.map .param)) =
      some (m₀.val P ψ) := by
    simp only [interpExpr, hfP₁]
    rw [if_pos (by rw [hlpsP]; simp)]
    rw [show c₀.toConstantVal.levelParams = cvA.levelParams from hlpsP]
    rw [show Level.substFn ψ cvA.levelParams
        (cvA.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
  have hCi2 : interpExpr V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const ctor (cvj.levelParams.map .param)) =
      some (m₀.val ctor ψ) := by
    simp only [interpExpr, hfj₁]
    rw [if_pos (by simp [ConstantInfo.toConstantVal])]
    rw [show (ConstantInfo.ctorInfo cvj nP nF).toConstantVal.levelParams
        = cvj.levelParams from rfl]
    rw [show Level.substFn ψ cvj.levelParams
        (cvj.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
  -- chain slots, transferred from the statement's inversions
  have hlhsA := hcomps _ (show
      Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)]) ∈
      [Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) tySlot, _, _] by simp)
  have hLne : (fvsP ++ xFvs).take nP ++
      [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)] ≠ [] := by
    simp
  obtain ⟨-, hcompsL, vfP, vsL, hifP, hispL, hchainL, -⟩ :=
    annotOk_spine_inv _ (.const (f P) (cvA.levelParams.map .param))
      hLne hlhsA
  have hvfP : vfP = m₀.val P ψ := by
    rw [hcPi] at hifP
    exact (Option.some.inj hifP).symm
  have hvsL : vsL = vals.take nP ++ [SpineFold V (m₀.val ctor ψ) vals] :=
    InterpSpine.functional hispL
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        ⟨hctorVal, trivial⟩)
  have hctorA := hcompsL _ (show
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP) ∈
      (fvsP ++ xFvs).take nP ++
        [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)] by simp)
  have hCne : (fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP ≠ [] := by
    rw [List.take_append_drop]
    intro hcon
    rw [hcon] at hspineLenA
    simp at hspineLenA
    omega
  obtain ⟨-, -, vfC, vsC, hifC, hispC, hchainC, -⟩ :=
    annotOk_spine_inv _
      (.const (f ctor) (cvj.levelParams.map .param)) hCne hctorA
  have hvfC : vfC = m₀.val ctor ψ := by
    rw [hcCi] at hifC
    exact (Option.some.inj hifC).symm
  have hvsC : vsC = vals := by
    refine InterpSpine.functional hispC ?_
    have := InterpSpine.append (InterpSpine.take nP hvalsSp)
      (InterpSpine.drop nP hvalsSp)
    rwa [List.take_append_drop nP vals] at this
  -- assemble the body's truthfulness and value
  have hfvA : ∀ x ∈ (fvsP ++ xFvs), AnnotOk V m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty) x := by
    intro x hx
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hspineShapeA j x hj
    simp only [AnnotOk]
  have hchainC' : ChainSlots V (m₀.val ctor ψ) vals := by
    rw [← hvfC, ← hvsC]
    exact hchainC
  obtain ⟨hActor, hictor⟩ := annotOk_spine (fvsP ++ xFvs)
    (.const ctor (cvj.levelParams.map .param))
    (by simp only [AnnotOk]) hCi2 hfvA hvalsSp hchainC'
  have hchainL' : ChainSlots V (m₀.val P ψ)
      (vals.take nP ++ [SpineFold V (m₀.val ctor ψ) vals]) := by
    rw [← hvfP, ← hvsL]
    exact hchainL
  obtain ⟨hAbL, hibL⟩ := annotOk_spine
    ((fvsP ++ xFvs).take nP ++
      [Expr.mkAppN (.const ctor (cvj.levelParams.map .param)) (fvsP ++ xFvs)])
    (.const P (cvA.levelParams.map .param))
    (by simp only [AnnotOk]) hPi2
    (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hfvA x (List.mem_of_mem_take hx)
      · obtain rfl : x = Expr.mkAppN
            (.const ctor (cvj.levelParams.map .param)) (fvsP ++ xFvs) := by
          simpa using hx
        exact hActor)
    (InterpSpine.append (InterpSpine.take nP hvalsSp)
      (show InterpSpine m₀.val (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty) [_]
        [SpineFold V (m₀.val ctor ψ) vals] from ⟨hictor, trivial⟩))
    hchainL'
  refine ⟨⟨SpineFold V (m₀.val P ψ)
      (vals.take nP ++ [SpineFold V (m₀.val ctor ψ) vals]), ?_, ?_⟩,
    hAbL⟩
  · rw [hibL]
  · intro e hee
    rw [interp_erasedEq hee _ _, heRi]
    refine congrArg some ?_
    have h1 : xs.getD (nP + i) SetTheory.empty = vr := hvr.symm
    rw [h1, ← hveq_final, hvl]

/-! ## The projection rule's total λ-equality -/

set_option maxHeartbeats 1600000 in
/-- The single projection rule's `RecRulesOk` obligation tail: the
canonical left-hand side λ-tower exists, is well-formed and resolves,
and its interpretation **equals** the stored rule right-hand side's at
every level assignment — from the checked `proj_i.iota` theorem. -/
theorem proj_rule_eq
    {env₁ : Env} {val' : ConstVal V} {f : Name → Name}
    (hro : RenameOk val' env₁ f)
    {P : Name} {nP nF i : Nat} (hi : i < nF)
    {rule : RecRule} {cvA cvj : ConstantVal}
    {ciP : ConstantInfo}
    (hfP : env₁.find? P = some ciP)
    (hlpsP : ciP.toConstantVal.levelParams = cvA.levelParams)
    (hfj : env₁.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env₁.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = cvA.levelParams)
    (heqfind : env₁.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    {thmName : Name} {cvt : ConstantVal}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val' env₁ ψ'' cvt.type = some Pv ∧
      val' thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) cvt.type)
    (hfirep : RecRule.fire rule = .plain)
    (hcp : RecRule.ctorParams rule = nP)
    (hnf : RecRule.nfields rule = nF)
    {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) = some (rbs, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    {abinders : List (Name × Expr × BinderMeta)} {arest : Expr}
    (hA_strip : cvA.type.stripPis nP = some (abinders, arest))
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    {sbinders : List (Name × Expr × BinderMeta)} {sbody : Expr}
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hpredoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      abinders[k]? = some b → cbinders[k]? = some b' → b.2.1 = b'.2.1)
    (hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbs[k]? = some b → cbinders[k]? = some b' → b.2.1 = b'.2.1)
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    {tySlot : Expr} {ℓA : Level}
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f (RecRule.ctor rule))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    {dN : Name} {dus : List Level} {dargs : List Expr}
    (hcbody : cbody = Expr.mkAppN (.const dN dus) dargs)
    (hdargs : dargs.length = nP)
    (hTcl : cvA.type.hasFvar = false)
    (hTb : cvA.type.looseBVarsBounded 0 = true)
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hTres : cvA.type.constsResolve env₁ = true)
    (hCres : cvj.type.constsResolve env₁ = true)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V val' env₁ ψ'' 0 (rho0 V) (RecRule.rhs rule)) :
    ∃ fvms bL, ruleLhsParts P cvA nP rule cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = nP + RecRule.nfields rule ∧
      (closeLamsAt fvms bL).constsResolve env₁ = true ∧
      ∀ ψ'' : Name → Nat,
        AnnotOk V val' env₁ ψ'' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V val' env₁ ψ'' (closeLamsAt fvms bL) =
            some Rv ∧
          interpClosed V val' env₁ ψ'' (RecRule.rhs rule) = some Rv := by
  -- feasibility of the canonical decomposition
  have hAopen0 : (openPisAtFvars nP cvA.type 0).isSome = true :=
    openPisAtFvars_isSome_of_stripPis nP 0 (by rw [hA_strip]; rfl)
  obtain ⟨⟨fvsP0, rest00⟩, hAopen⟩ := Option.isSome_iff_exists.mp hAopen0
  obtain ⟨-, hfvsLen0, -⟩ := openPisAtFvars_spec nP 0 hAopen
  have htakeP0 : fvsP0.take (RecRule.ctorParams rule) = fvsP0 := by
    rw [hcp, ← hfvsLen0]
    exact List.take_length
  obtain ⟨cmid, hCpre, hCmidStrip⟩ := Expr.stripPis_add nP nF hC_strip
  have hcinst00 : (Expr.instPisAt fvsP0 cvj.type).isSome = true :=
    instPisAt_isSome_of_stripPis fvsP0 (by rw [hfvsLen0, hCpre]; rfl)
  obtain ⟨⟨cdomsP0, crestP0⟩, hcinst0⟩ :=
    Option.isSome_iff_exists.mp hcinst00
  have hcrest0 : crestP0 = instSeq fvsP0 (fvsP0.length - 1) cmid :=
    (instPisAt_stripPis fvsP0 hcinst0 (by rw [hfvsLen0]; exact hCpre)).1
  have hXopen00 : (openPisAtFvars nF crestP0 nP).isSome = true := by
    refine openPisAtFvars_isSome_of_stripPis nF nP ?_
    rw [hcrest0]
    exact Expr.stripPis_instSeq_isSome fvsP0 _ nF (by rw [hCmidStrip]; rfl)
  obtain ⟨⟨xFvs0, crest20⟩, hXopen0⟩ :=
    Option.isSome_iff_exists.mp hXopen00
  have hpartsSome : (ruleLhsParts P cvA nP rule cvj).isSome = true := by
    simp only [ruleLhsParts, hAopen, hfirep, ruleLhsAux, htakeP0, hcinst0,
      hnf, hXopen0, hstripR]
    rfl
  obtain ⟨⟨fvms, bL⟩, hparts⟩ := Option.isSome_iff_exists.mp hpartsSome
  -- the decomposition's components
  obtain ⟨fvsP, rest0v, usC', cargs', cdomsP, crestP, xFvs, crest2,
    rbs', rb', heqO, hcinst', hXopen', hstripR', hfireCase', hfvmsEq,
    hbLEq⟩ := ruleLhsParts_inv hparts
  obtain ⟨hfvsInstA, hfvsLen, hfvsShape⟩ := openPisAtFvars_spec nP 0 heqO
  obtain ⟨husC, hcargs⟩ : usC' = cvj.levelParams.map Level.param ∧
      cargs' = fvsP.take (RecRule.ctorParams rule) := by
    rcases hfireCase' with ⟨-, h1, h2⟩ | ⟨lvls, pins, hcon, -, -⟩
    · exact ⟨h1, h2⟩
    · rw [hfirep] at hcon
      exact nomatch hcon
  have htakeP : fvsP.take (RecRule.ctorParams rule) = fvsP := by
    rw [hcp, ← hfvsLen]
    exact List.take_length
  rw [hfirep] at hcinst'
  dsimp only at hcinst'
  rw [hcargs, htakeP] at hcinst'
  rw [hnf] at hXopen' hstripR'
  obtain ⟨hxInstC, hxLen, hxShape⟩ := openPisAtFvars_spec nF nP hXopen'
  rw [hstripR] at hstripR'
  have hpr4 := Option.some.inj hstripR'
  have hrbsE : rbs' = rbs := (congrArg Prod.fst hpr4).symm
  rw [hrbsE] at hfvmsEq
  rw [husC, hcargs, htakeP] at hbLEq
  -- the combined constructor walk: the index tuple is empty
  have hcombined : Expr.instPisAt (fvsP ++ xFvs) cvj.type =
      some (cdomsP ++ xFvs.map Expr.fvarTypeD, crest2) :=
    instPisAt_append_of fvsP hcinst' hxInstC
  have hspineLen : (fvsP ++ xFvs).length = nP + nF := by
    simp [hfvsLen, hxLen]
  have hcrest2 : crest2 = instSeq (fvsP ++ xFvs) (nP + nF - 1) cbody := by
    have h1 := (instPisAt_stripPis (fvsP ++ xFvs) hcombined
      (by rw [hspineLen]; exact hC_strip)).1
    rw [hspineLen] at h1
    exact h1
  have hidxNil : crest2.getAppArgs.drop (RecRule.ctorParams rule) = [] := by
    rw [hcrest2, hcbody, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (by rfl), Expr.getAppArgs_mkAppN]
    rw [show (Expr.const dN dus).getAppArgs = [] from rfl,
      List.nil_append]
    refine List.drop_eq_nil_of_le ?_
    rw [hcp]
    simp [hdargs]
  have htakeSp : (fvsP ++ xFvs).take nP = fvsP := by
    rw [List.take_append_of_le_length (by omega)]
    rw [← hfvsLen, List.take_length]
  have hbLeq2 : bL = Expr.mkAppN (.const P (cvA.levelParams.map .param))
      ((fvsP ++ xFvs).take nP ++
       [Expr.mkAppN (.const (RecRule.ctor rule)
          (cvj.levelParams.map Level.param)) (fvsP ++ xFvs)]) := by
    rw [hbLEq, hidxNil, htakeSp, List.append_nil]
  -- the frame's shapes and annotations
  have hspineShape : ∀ (j : Nat) (a : Expr), (fvsP ++ xFvs)[j]? = some a →
      ∃ nm ty, a = Expr.fvar j nm ty := by
    intro j a hj
    rcases Nat.lt_or_ge j nP with hjn | hjn
    · rw [List.getElem?_append_left (by rw [hfvsLen]; exact hjn)] at hj
      obtain ⟨nm, ha⟩ := hfvsShape j a hj
      rw [Nat.zero_add] at ha
      exact ⟨nm, a.fvarTypeD, ha⟩
    · rw [List.getElem?_append_right (by rw [hfvsLen]; exact hjn)] at hj
      obtain ⟨nm, ha⟩ := hxShape (j - fvsP.length) a hj
      refine ⟨nm, a.fvarTypeD, ?_⟩
      rw [show j = nP + (j - fvsP.length) from by rw [hfvsLen]; omega]
      exact ha
  have hcombPos := (instPisAt_stripPis (fvsP ++ xFvs) hcombined
    (by rw [hspineLen]; exact hC_strip)).2
  have hAPos := (instPisAt_stripPis fvsP hfvsInstA
    (by rw [hfvsLen]; exact hA_strip)).2
  have hcdomsLen : cdomsP.length = nP := by
    rw [instPisAt_length fvsP hcinst', hfvsLen]
  have hframeTy : ∀ (k : Nat) (a : Expr) (b : Name × Expr × BinderMeta),
      (fvsP ++ xFvs)[k]? = some a → cbinders[k]? = some b →
      Expr.fvarTypeD a = instSeq ((fvsP ++ xFvs).take k) (k - 1) b.2.1 := by
    intro k a b hk hb
    have hcw := hcombPos k b hb
    rcases Nat.lt_or_ge k nP with hkn | hkn
    · rw [List.getElem?_append_left (by rw [hfvsLen]; exact hkn)] at hk
      obtain ⟨ab, hab⟩ : ∃ ab, abinders[k]? = some ab := by
        have hal : abinders.length = nP := Expr.stripPis_length _ hA_strip
        exact ⟨abinders[k]'(by omega), List.getElem?_eq_getElem _⟩
      have hA1 := hAPos k ab hab
      rw [List.getElem?_map, hk] at hA1
      simp only [Option.map_some, Option.some.injEq] at hA1
      rw [List.take_append_of_le_length (by rw [hfvsLen]; omega),
        ← hpredoms k ab b hab hb]
      exact hA1
    · rw [List.getElem?_append_right (by rw [hfvsLen]; exact hkn)] at hk
      rw [List.getElem?_append_right (by rw [hcdomsLen]; exact hkn),
        hcdomsLen] at hcw
      rw [hfvsLen] at hk
      rw [List.getElem?_map, hk] at hcw
      simp only [Option.map_some, Option.some.injEq] at hcw
      exact hcw
  -- well-formedness, length, resolution
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts hTcl hTb hCcl hCb
    (fun lvls pins hcon => by rw [hfirep] at hcon; exact nomatch hcon)
  have hres := ruleLhsParts_resolve hparts (by rw [hfP]; rfl)
    (by rw [hfj]; rfl) hTres hCres
    (fun lvls pins hcon => by rw [hfirep] at hcon; exact nomatch hcon)
  refine ⟨fvms, bL, hparts, hwf, hlen, hres, ?_⟩
  intro ψ''
  obtain ⟨Pv, hPv, hPmem⟩ := hthm_mem ψ''
  have htow : TowerOk val' env₁ ψ'' 0 (rho0 V) fvms bL
      (RecRule.rhs rule) := by
    rw [hfvmsEq]
    refine proj_tower_rec (ctor := RecRule.ctor rule) hro hi hfP hlpsP
      hfj hfPm hPmlps heqfind heqval hspineLen hspineShape hC_strip hCcl
      hCb hframeTy hS_strip hstripR hrbody hdoms hsdoms hsbody hbLeq2
      ((fvsP ++ xFvs).zip (rbs.map (·.2.2))) 0 (rho0 V) [] _ _
      (val' thmName ψ'') ?_ (by simp) rfl (fun j a hj => by simp at hj)
      ⟨[], rfl⟩ ⟨[], rfl⟩ ⟨Pv, hPv, hPmem⟩ (hthm_annot ψ'')
    have hrl : rbs.length = nP + nF := Expr.stripLams_length _ hstripR
    simp [List.length_zip, hspineLen, hrl]
  obtain ⟨⟨Rv, hL, hR2⟩, hAL⟩ := TowerOk.out htow hwf (hArhs ψ'')
  exact ⟨hAL, Rv, hL, hR2⟩
