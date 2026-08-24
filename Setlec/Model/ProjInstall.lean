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
    {env : Env} (m : EnvModel V env) (F : Nat) {ψ : Name → Nat}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {val' : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ'' : Name → Nat,
      val' n ψ'' = m.val n ψ'')
    {f f₀ : Name → Name}
    (hff₀ : ∀ n, (env.find? n).isSome = true → f n = f₀ n)
    (hro₀ : RenameOk m.val env f₀)
    (hro₁ : RenameOk val' (⟨c₀ :: env.consts⟩ : Env) f)
    {P ctor : Name} {cvA cvj cvt : ConstantVal} {nP nF i : Nat}
    (hi : i < nF)
    (hfP₁ : (⟨c₀ :: env.consts⟩ : Env).find? P = some c₀)
    (hlpsP : c₀.toConstantVal.levelParams = cvA.levelParams)
    (hfj : env.find? ctor = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = cvA.levelParams)
    (heqfind : env.find? eqName = some eqA)
    (heqval₁ : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts, over the base environment
    {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V m.val env ψ'' cvt.type = some Pv ∧
      m.val thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvt.type)
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
    (hAty : AnnotOk V m.val env ψ 0 (rho0 V) cvA.type)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCres : cvj.type.constsResolve env = true)
    (hACty : AnnotOk V m.val env ψ 0 (rho0 V) cvj.type)
    (hICty : ∃ T, interpClosed V m.val env ψ cvj.type = some T) :
    ∀ (xs : List V), xs.length = nP + nF →
      FramePref m.val env ψ (fvsP ++ xFvs) xs →
      (∃ w, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
          (fun l => xs.getD l SetTheory.empty)
          (Expr.mkAppN (.const P (cvA.levelParams.map .param))
            ((fvsP ++ xFvs).take nP ++
              [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
                (fvsP ++ xFvs)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrestL →
          interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
            (fun l => xs.getD l SetTheory.empty) e = some w) ∧
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
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
      ∃ B, interpExpr V m.val env ψ (nP + nF)
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
    have hcan := interp_getD_canon (cval := m.val) (env := env)
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
  have hAc : AnnotOk V m.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvj.type :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m.val env ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) cvj.type = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m F hcinstP hdeParsP hspP hwsP
    hLsP hΘP hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcrEx⟩ := peel_walk hcinstP hspP hwsP hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  have hFcr : FvarsOk V m.val env ψ (nP + nF)
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
      ∃ B, interpExpr V m.val env ψ (nP + nF)
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
    have hcan := interp_getD_canon (cval := m.val) (env := env)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := nP + nF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWcrD' : WScoped (nP + nF) crestP := hWcrRp.mono (by omega)
  obtain ⟨hfitXP, hΘX⟩ := self_walk hxInst hspX hwsX hWcrD' hbcr hLcr
    hFcr hAcr hmemX
  have hfitCfullP : TeleFitI V m.val env ψ (nP + nF)
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
  have hiaPX : InstArgs m.val env ψ (nP + nF)
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
      ∃ B, interpExpr V m.val env ψ (nP + nF)
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
    have hcbres : (cb.2.1).constsResolve env = true :=
      (Expr.constsResolve_stripPis (nP + nF) hC_strip hCres).1
        cb (List.mem_of_getElem? hcb)
    rw [hsdoms l sb cb hsb hcb,
      Expr.renameConsts_congr_resolve hff₀ _ hcbres,
      interp_instSeq_ren hro₀ hshapes]
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
  have hPvI : interpExpr V m.val env ψ (nP + nF)
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
  have hSQ1 : ∃ QN, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ
      (nP + nF) (fun l => xs.getD l SetTheory.empty) stmtRes =
        some QN ∧
      SpineFold V (m.val thmName ψ) xs ∈ˢ QN := by
    refine ⟨Q0, ?_, hQMem0⟩
    rw [interp_mono (cval := val') hfresh stmtRes _ _ hResRes,
      interp_cval_ext hagree stmtRes _ _]
    exact hQ0
  have hSA1 : AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
      (fun l => xs.getD l SetTheory.empty) stmtRes :=
    AnnotOk.mono hfresh stmtRes _ _ hResRes
      (AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm)
        stmtRes _ _ hSAres)
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
  have heRi : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ
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
    interpSpine_fvars_exists (cval := val') (env := (⟨c₀ :: env.consts⟩ : Env)) (φ := ψ)
      (d := nP + nF) (ρ := fun l => xs.getD l SetTheory.empty) (fvsP ++ xFvs) 0
      (fun j a hj => by
        obtain ⟨nm, ty, ha⟩ := hspineShapeA j a hj
        exact ⟨nm, ty, by rw [Nat.zero_add]; exact ha⟩)
  -- component values
  obtain ⟨cimC, hfCm, hlpCm⟩ := hro₁.1 ctor _ hfj₁
  have hcCi : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const (f ctor) (cvj.levelParams.map .param)) =
      some (val' ctor ψ) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hlpCm]; simp [ConstantInfo.toConstantVal])]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from by
      rw [hlpCm]; rfl]
    rw [show Level.substFn ψ cvj.levelParams
        (cvj.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
    rw [hro₁.2.2 ctor]
  have hctorVal : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)) =
      some (SpineFold V (val' ctor ψ) vals) := by
    rw [interp_mkAppN _ _ hcCi
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        (InterpSpine.drop nP hvalsSp))]
    rw [List.take_append_drop]
  have hcPi : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const (f P) (cvA.levelParams.map .param)) =
      some (val' P ψ) := by
    simp only [interpExpr, hfPm₁]
    rw [if_pos (by rw [hPmlps]; simp)]
    rw [show cimP.toConstantVal.levelParams = cvA.levelParams from
      hPmlps]
    rw [show Level.substFn ψ cvA.levelParams
        (cvA.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
    rw [hro₁.2.2 P]
  have hlhsVal : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (Expr.mkAppN (.const (f P) (cvA.levelParams.map .param))
        ((fvsP ++ xFvs).take nP ++
         [Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
           ((fvsP ++ xFvs).take nP ++ (fvsP ++ xFvs).drop nP)])) =
      some (SpineFold V (val' P ψ)
        (vals.take nP ++ [SpineFold V (val' ctor ψ) vals])) := by
    rw [interp_mkAppN _ _ hcPi
      (InterpSpine.append (InterpSpine.take nP hvalsSp)
        (show InterpSpine val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
          [_] [SpineFold V (val' ctor ψ) vals] from ⟨hctorVal, trivial⟩))]
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
  have hvl : vl = SpineFold V (val' P ψ)
      (vals.take nP ++ [SpineFold V (val' ctor ψ) vals]) := by
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
    rw [← Option.some.inj hveqi, heqval₁]
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
  have hPi2 : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const P (cvA.levelParams.map .param)) =
      some (val' P ψ) := by
    simp only [interpExpr, hfP₁]
    rw [if_pos (by rw [hlpsP]; simp)]
    rw [show c₀.toConstantVal.levelParams = cvA.levelParams from hlpsP]
    rw [show Level.substFn ψ cvA.levelParams
        (cvA.levelParams.map .param) = ψ from
      funext fun p => Level.substFn_map_param]
  have hCi2 : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty)
      (.const ctor (cvj.levelParams.map .param)) =
      some (val' ctor ψ) := by
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
  have hvfP : vfP = val' P ψ := by
    rw [hcPi] at hifP
    exact (Option.some.inj hifP).symm
  have hvsL : vsL = vals.take nP ++ [SpineFold V (val' ctor ψ) vals] :=
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
  have hvfC : vfC = val' ctor ψ := by
    rw [hcCi] at hifC
    exact (Option.some.inj hifC).symm
  have hvsC : vsC = vals := by
    refine InterpSpine.functional hispC ?_
    have := InterpSpine.append (InterpSpine.take nP hvalsSp)
      (InterpSpine.drop nP hvalsSp)
    rwa [List.take_append_drop nP vals] at this
  -- assemble the body's truthfulness and value
  have hfvA : ∀ x ∈ (fvsP ++ xFvs), AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty) x := by
    intro x hx
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hspineShapeA j x hj
    simp only [AnnotOk]
  have hchainC' : ChainSlots V (val' ctor ψ) vals := by
    rw [← hvfC, ← hvsC]
    exact hchainC
  obtain ⟨hActor, hictor⟩ := annotOk_spine (fvsP ++ xFvs)
    (.const ctor (cvj.levelParams.map .param))
    (by simp only [AnnotOk]) hCi2 hfvA hvalsSp hchainC'
  have hchainL' : ChainSlots V (val' P ψ)
      (vals.take nP ++ [SpineFold V (val' ctor ψ) vals]) := by
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
      (show InterpSpine val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF) (fun l => xs.getD l SetTheory.empty) [_]
        [SpineFold V (val' ctor ψ) vals] from ⟨hictor, trivial⟩))
    hchainL'
  refine ⟨⟨SpineFold V (val' P ψ)
      (vals.take nP ++ [SpineFold V (val' ctor ψ) vals]), ?_, ?_⟩,
    hAbL⟩
  · rw [hibL]
  · intro e hee
    rw [interp_erasedEq hee _ _, heRi]
    refine congrArg some ?_
    have h1 : xs.getD (nP + i) SetTheory.empty = vr := hvr.symm
    rw [h1, ← hveq_final, hvl]

/-! ## The projection rule's total λ-equality -/

set_option maxHeartbeats 1600000 in
/-- The single projection rule's `RecRulesOk` obligation tail,
**parametric in the bottom fact**: the canonical left-hand side λ-tower
exists, is well-formed and resolves, and its interpretation equals the
stored rule right-hand side's at every level assignment.  Everything
but the bottom is provenance-free — the flat stage facts come from the
kernel's definitional parameter pins (`modeled_stage`), the gluing from
`TowerOk.of_stages`/`TowerOk.out` — so the modeled path (`proj_bottom`,
off the checked `proj_i.iota` theorem) and the direct path (off the
constructed values' fold equations) share it. -/
theorem rule_eq_of_bottom_ext
    {env : Env} (m : EnvModel V env) (F : Nat)
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {val' : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ'' : Name → Nat,
      val' n ψ'' = m.val n ψ'')
    {P : Name} {rP cnP nF : Nat}
    (hplainLe : cnP ≤ rP)
    {rule : RecRule} {cvA cvj : ConstantVal}
    (hfP₁ : (⟨c₀ :: env.consts⟩ : Env).find? P = some c₀)
    (hfj : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj cnP nF))
    (hfirep : RecRule.fire rule = .plain)
    (hcp : RecRule.ctorParams rule = cnP)
    (hnf : RecRule.nfields rule = nF)
    {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (rP + nF) = some (rbs, rbody))
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hC_strip : cvj.type.stripPis (cnP + nF) = some (cbinders, cbody))
    {dN : Name} {dus : List Level} {dargs : List Expr}
    (hcbody : cbody = Expr.mkAppN (.const dN dus) dargs)
    (hdargs : dargs.length = cnP)
    -- the kernel pins over the base environment
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvs : List Expr} {crest2X : Expr}
    {ldoms : List Expr} {lrestL : Expr}
    (hopenP : openPisAtFvars rP cvA.type 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hctorPkg : ∀ (ψ : Name → Nat) (xs : List V),
      xs.length ≤ rP + nF → rP ≤ xs.length →
      FramePref m.val env ψ (fvsP ++ xFvs) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m.val env ψ (rP + nF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m.val env ψ (rP + nF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m.val env ψ (rP + nF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P)
    (hopenX : openPisAtFvars nF crestP rP = some (xFvs, crest2X))
    (hlinstP : Expr.instLamsAt (fvsP ++ xFvs) (RecRule.rhs rule) =
      some (ldoms, lrestL))
    (hdeLamP : DefEqListOk F env (rP + nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms)
    -- well-formedness over the base environment
    (hTcl : cvA.type.hasFvar = false)
    (hTb : cvA.type.looseBVarsBounded 0 = true)
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hTres : cvA.type.constsResolve env = true)
    (hCres : cvj.type.constsResolve env = true)
    (hRres : (RecRule.rhs rule).constsResolve env = true)
    (hrhsw : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvA.type)
    (hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m.val env ψ'' cvA.type = some T)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) (RecRule.rhs rule))
    (hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V m.val env ψ'' (RecRule.rhs rule) = some L)
    (Hbot : ∀ (ψ : Name → Nat) (xs : List V), xs.length = rP + nF →
      FramePref m.val env ψ (fvsP ++ xFvs) xs →
      (∃ w, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (rP + nF)
          (fun l => xs.getD l SetTheory.empty)
          (Expr.mkAppN (.const P (cvA.levelParams.map .param))
            (fvsP ++
              [Expr.mkAppN (.const (RecRule.ctor rule)
                  (cvj.levelParams.map .param))
                (fvsP.take cnP ++ xFvs)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrestL →
          interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (rP + nF)
            (fun l => xs.getD l SetTheory.empty) e = some w) ∧
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ (rP + nF)
        (fun l => xs.getD l SetTheory.empty)
        (Expr.mkAppN (.const P (cvA.levelParams.map .param))
          (fvsP ++
            [Expr.mkAppN (.const (RecRule.ctor rule)
                (cvj.levelParams.map .param))
              (fvsP.take cnP ++ xFvs)]))) :
    ∃ fvms bL, ruleLhsParts P cvA rP rule cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = rP + RecRule.nfields rule ∧
      (closeLamsAt fvms bL).constsResolve
        (⟨c₀ :: env.consts⟩ : Env) = true ∧
      ∀ ψ'' : Name → Nat,
        AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ'' 0 (rho0 V)
          (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (RecRule.rhs rule) = some Rv := by
  -- spine data and shapes
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec nF rP hopenX
  have hspineLen : (fvsP ++ xFvs).length = rP + nF := by
    rw [List.length_append, hfvsPLen, hxLen]
  -- the canonical decomposition computes
  have hparts : ruleLhsParts P cvA rP rule cvj =
      some ((fvsP ++ xFvs).zip (rbs.map (·.2.2)),
        Expr.mkAppN (.const P (cvA.levelParams.map .param))
          (fvsP ++ crest2X.getAppArgs.drop (RecRule.ctorParams rule) ++
            [Expr.mkAppN (.const (RecRule.ctor rule)
                (cvj.levelParams.map Level.param))
              (fvsP.take (RecRule.ctorParams rule) ++ xFvs)])) := by
    simp only [ruleLhsParts, hopenP, hfirep, ruleLhsAux, hcp,
      hcinstP, hnf, hopenX,
      show (RecRule.rhs rule).stripLams (rP + nF) = some (rbs, rbody)
        from hstripR]
  refine ⟨_, _, hparts, ?_⟩
  have hpinsVac : ∀ lvls pins, RecRule.fire rule = .nested lvls pins →
      ∀ p ∈ pins, p.hasFvar = false ∧
        p.looseBVarsBounded rP = true := by
    intro lvls pins hcon
    rw [hfirep] at hcon
    exact nomatch hcon
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts hTcl hTb hCcl hCb
    hpinsVac
  refine ⟨hwf, hlen, ?_, ?_⟩
  · refine ruleLhsParts_resolve hparts ?_ ?_
      (Expr.constsResolve_mono hTres) (Expr.constsResolve_mono hCres)
      (fun lvls pins hcon => by
        rw [hfirep] at hcon
        exact nomatch hcon)
    · rw [hfP₁]
      rfl
    · rw [Env.find?_cons_of_isSome hfresh (by rw [hfj]; rfl), hfj]
      rfl
  -- the semantic clause, per level assignment
  intro ψ
  -- Hty: the flat stage facts at the base environment, transported
  have hstage := modeled_stage (rP := rP) (cnF := nF) m F hopenP hTcl
    hTb (hAty ψ) (hIty ψ) hopenX (hctorPkg ψ) hlinstP hdeLamP hrhsw hrhsb
    (hArhs ψ) (hIrhs ψ)
  -- resolution of the frame annotations and tower domains
  have hfvsPres : ∀ a ∈ fvsP, a.constsResolve env = true :=
    (openPisAtFvars_resolve rP 0 hopenP hTres).1
  have hcrestPres : crestP.constsResolve env = true :=
    instPisAt_resolve (fvsP.take cnP) hcinstP hCres
      (fun a ha => hfvsPres a (List.mem_of_mem_take ha))
  have hxFvsRes : ∀ a ∈ xFvs, a.constsResolve env = true :=
    (openPisAtFvars_resolve nF rP hopenX hcrestPres).1
  have hspineRes : ∀ a ∈ fvsP ++ xFvs, a.constsResolve env = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsPres a ha
    · exact hxFvsRes a ha
  have hldomsRes : ∀ (k : Nat) (ld : Expr), ldoms[k]? = some ld →
      ld.constsResolve env = true := by
    intro k ld hld
    obtain ⟨rbsK, rbodyK⟩ := (rbs, rbody)
    obtain ⟨-, hds⟩ := instLamsAt_stripLams (fvsP ++ xFvs) hlinstP
      (by rw [hspineLen]; exact hstripR)
    have hkN : k < rP + nF := by
      rcases Nat.lt_or_ge k (rP + nF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instLamsAt_length _ hlinstP, hspineLen]; omega)] at hld
        exact nomatch hld
    obtain ⟨b, hb⟩ : ∃ b, rbs[k]? = some b := by
      have := Expr.stripLams_length (rP + nF) hstripR
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 := hds k b hb
    rw [hld] at h1
    obtain rfl := Option.some.inj h1
    rw [← Expr.instSpine_eq_instSeq]
    refine instSpine_constsResolve _ ?_ ?_
    · exact (Expr.constsResolve_stripLams (rP + nF) hstripR hRres).1
        b (List.mem_of_getElem? hb)
    · intro a ha
      exact hspineRes a (List.mem_of_mem_take ha)
  have hannRes : ∀ (k : Nat) (fv : Expr),
      (fvsP ++ xFvs)[k]? = some fv →
      (Expr.fvarTypeD fv).constsResolve env = true := by
    intro k fv hfv
    have hmem := List.mem_of_getElem? hfv
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
      obtain ⟨nm, hsh⟩ := hfvsPShape j fv hj
      have h1 := hfvsPres fv hm
      rw [hsh] at h1 ⊢
      simpa [Expr.constsResolve, Expr.fvarTypeD] using h1
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
      obtain ⟨nm, hsh⟩ := hxShape j fv hj
      have h1 := hxFvsRes fv hm
      rw [hsh] at h1 ⊢
      simpa [Expr.constsResolve, Expr.fvarTypeD] using h1
  -- frame bookkeeping for the tower recursion
  have hrbsLen : rbs.length = rP + nF := Expr.stripLams_length _ hstripR
  have hzipFst : ((fvsP ++ xFvs).zip (rbs.map (·.2.2))).map Prod.fst =
      fvsP ++ xFvs :=
    List.map_fst_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hzipSnd : ((fvsP ++ xFvs).zip (rbs.map (·.2.2))).map (·.2) =
      rbs.map (·.2.2) :=
    List.map_snd_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hfvmsLen : ((fvsP ++ xFvs).zip (rbs.map (·.2.2))).length =
      rP + nF := by
    rw [List.length_zip, hspineLen, List.length_map, hrbsLen]
    simp
  -- the tower spec from the transported stage facts and the bottom
  have hbot := Hbot ψ
  have htower := TowerOk.of_stages (cval := val')
    (env := (⟨c₀ :: env.consts⟩ : Env)) (φ := ψ)
    (bL := Expr.mkAppN (.const P (cvA.levelParams.map .param))
      (fvsP ++ crest2X.getAppArgs.drop (RecRule.ctorParams rule) ++
        [Expr.mkAppN (.const (RecRule.ctor rule)
            (cvj.levelParams.map Level.param))
          (fvsP.take (RecRule.ctorParams rule) ++ xFvs)]))
    (lrest := lrestL)
    (fvms := (fvsP ++ xFvs).zip (rbs.map (·.2.2)))
    (ldoms := ldoms)
    (Ok := FramePref m.val env ψ (fvsP ++ xFvs))
    (Hty := by
      intro k xs fv m ld hxs hfv hld hOk
      have hfv' : (fvsP ++ xFvs)[k]? = some fv := by
        have h0 := congrArg (·[k]?) hzipFst
        simp only [List.getElem?_map] at h0
        rw [← h0, hfv]
        rfl
      obtain ⟨A, h1, h2, h3, h4⟩ := hstage k xs fv ld hxs hfv' hld hOk
      -- transport across the fresh extension
      have hannR := hannRes k fv hfv'
      have hWfv : WScoped k (Expr.fvarTypeD fv) := by
        rcases Nat.lt_or_ge k rP with hkn | hkn
        · have hfvL : fvsP[k]? = some fv := by
            rw [List.getElem?_append_left (by omega)] at hfv'
            exact hfv'
          obtain ⟨hfw, -⟩ := openPisAtFvars_wf rP 0 hopenP
            (WScoped.of_not_hasFvar hTcl) hTb
            (Expr.LeavesBounded.of_not_hasFvar hTcl)
          obtain ⟨nm, hsh⟩ := hfvsPShape k fv hfvL
          rw [Nat.zero_add] at hsh
          have hW := (hfw fv (List.mem_of_getElem? hfvL)).1
          rw [hsh] at hW ⊢
          simp only [WScoped] at hW ⊢
          exact hW.2
        · rw [List.getElem?_append_right (by omega), hfvsPLen] at hfv'
          have hWcrRp : WScoped rP crestP := by
            obtain ⟨-, h0⟩ := instPisAt_wscoped (D := rP) (fvsP.take cnP)
              hcinstP (WScoped.of_not_hasFvar hCcl)
              (by
                intro a ha
                obtain ⟨hfw, -⟩ := openPisAtFvars_wf rP 0 hopenP
                  (WScoped.of_not_hasFvar hTcl) hTb
                  (Expr.LeavesBounded.of_not_hasFvar hTcl)
                have h1 := (hfw a (List.mem_of_mem_take ha)).1
                rwa [Nat.zero_add] at h1)
            exact h0
          obtain ⟨cmid, hCpre, hCmidStrip⟩ :=
            Expr.stripPis_add cnP nF hC_strip
          have hlenTakeC : (fvsP.take cnP).length = cnP := by
            rw [List.length_take, hfvsPLen]; omega
          have hbcr : crestP.looseBVarsBounded 0 = true := by
            have hchar := (instPisAt_stripPis (fvsP.take cnP) hcinstP
              (by rw [hlenTakeC]; exact hCpre)).1
            rw [hchar]
            refine instSeq_bclosed ?_ ?_
            · intro a ha
              obtain ⟨j, hj⟩ := List.getElem?_of_mem
                (List.mem_of_mem_take ha)
              obtain ⟨nm, hsh⟩ := hfvsPShape j a hj
              rw [hsh]
              rfl
            · rw [hlenTakeC]
              have h0 := stripPis_body_bounded cnP hCpre hCb
              simpa using h0
          have hLcr : Expr.LeavesBounded crestP := by
            have hchar := (instPisAt_stripPis (fvsP.take cnP) hcinstP
              (by rw [hlenTakeC]; exact hCpre)).1
            rw [hchar]
            refine LeavesBounded_instSeq _ _ ?_ ?_
            · exact Expr.LeavesBounded.of_not_hasFvar
                (stripPis_body_hasFvar cnP hCpre hCcl)
            · intro a ha
              obtain ⟨hfw, -⟩ := openPisAtFvars_wf rP 0 hopenP
                (WScoped.of_not_hasFvar hTcl) hTb
                (Expr.LeavesBounded.of_not_hasFvar hTcl)
              exact (hfw a (List.mem_of_mem_take ha)).2.2
          obtain ⟨hxWf, -⟩ := openPisAtFvars_wf nF rP hopenX hWcrRp
            hbcr hLcr
          obtain ⟨nm, hsh⟩ := hxShape (k - rP) fv hfv'
          have hW := (hxWf fv (List.mem_of_getElem? hfv')).1
          rw [hsh] at hW ⊢
          simp only [WScoped] at hW ⊢
          rw [show rP + (k - rP) = k from by omega] at hW ⊢
          exact hW.2
      refine ⟨A, ?_, ?_, ?_, h4⟩
      · rw [interp_mono (cval := val') hfresh _ _ _ hannR,
          interp_cval_ext hagree _ _ _]
        exact h1
      · intro e hee
        rw [interp_erasedEq hee _ _,
          interp_mono (cval := val') hfresh _ _ _
            (hldomsRes k ld hld),
          interp_cval_ext hagree _ _ _]
        exact h2 ld (Expr.ErasedEq.rfl _)
      · exact AnnotOk.mono hfresh _ _ _ hannR
          (AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm)
            _ _ _ h3))
    (Hbot := by
      intro xs hxs hOk
      rw [hfvmsLen] at hxs
      have h := hbot xs hxs hOk
      rw [hfvmsLen]
      -- identify the two spellings of the canonical body
      have hlenTakeC : (fvsP.take cnP).length = cnP := by
        rw [List.length_take, hfvsPLen]; omega
      have hcombined : Expr.instPisAt (fvsP.take cnP ++ xFvs) cvj.type =
          some (cdomsP ++ xFvs.map Expr.fvarTypeD, crest2X) :=
        instPisAt_append_of (fvsP.take cnP) hcinstP hxInst
      have hspineLenC : (fvsP.take cnP ++ xFvs).length = cnP + nF := by
        rw [List.length_append, hlenTakeC, hxLen]
      have hcrest2 : crest2X =
          instSeq (fvsP.take cnP ++ xFvs) (cnP + nF - 1) cbody := by
        have h1 := (instPisAt_stripPis (fvsP.take cnP ++ xFvs) hcombined
          (by rw [hspineLenC]; exact hC_strip)).1
        rw [hspineLenC] at h1
        exact h1
      have hidxNil : crest2X.getAppArgs.drop
          (RecRule.ctorParams rule) = [] := by
        rw [hcrest2, hcbody, Expr.instSeq_mkAppN,
          Expr.instSeq_eq_self _ _ (by rfl), Expr.getAppArgs_mkAppN]
        rw [show (Expr.const dN dus).getAppArgs = [] from rfl,
          List.nil_append]
        refine List.drop_eq_nil_of_le ?_
        rw [hcp, List.length_map]
        omega
      rw [hidxNil, List.append_nil, hcp]
      exact h)
    ((fvsP ++ xFvs).zip (rbs.map (·.2.2))) 0 [] ldoms
    (RecRule.rhs rule) (RecRule.rhs rule)
    (by rw [Nat.zero_add])
    rfl rfl rfl
    (by
      intro j p hp
      have h0 := congrArg (·[j]?) hzipFst
      simp only [List.getElem?_map] at h0
      have hp1 : (fvsP ++ xFvs)[j]? = some p.1 := by
        rw [← h0, hp]
        rfl
      rcases Nat.lt_or_ge j rP with hj | hj
      · rw [List.getElem?_append_left (by omega)] at hp1
        obtain ⟨nm, hsh⟩ := hfvsPShape j p.1 hp1
        rw [Nat.zero_add] at hsh
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add]
        exact hsh
      · rw [List.getElem?_append_right (by omega), hfvsPLen] at hp1
        obtain ⟨nm, hsh⟩ := hxShape (j - rP) p.1 hp1
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add, hsh]
        congr 1
        omega)
    (Expr.ErasedEq.rfl _)
    (by
      rw [hzipFst]
      exact hlinstP)
    (by
      refine ⟨rbs, rbody, ?_, hzipSnd⟩
      rw [hfvmsLen]
      exact hstripR)
    (fun j v fv hjv _ => nomatch hjv)
  have hrho : (fun i' => ([] : List V).getD i' SetTheory.empty) =
      rho0 V := by
    funext i'
    rfl
  rw [hrho] at htower
  obtain ⟨⟨Rv, hL, hR⟩, hAL⟩ := TowerOk.out htower hwf
    (AnnotOk.mono hfresh _ 0 (rho0 V) hRres
      (AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm)
        _ 0 (rho0 V) (hArhs ψ)))
  exact ⟨hAL, Rv, hL, hR⟩

/-- The projection instance of `rule_eq_of_bottom_ext`: the rule
prefix *is* the constructor's parameter count, so the canonical body's
index list is empty and its constructor spine is the whole frame. -/
theorem proj_rule_eq_of_bottom
    {env : Env} (m : EnvModel V env) (F : Nat)
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {val' : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ'' : Name → Nat,
      val' n ψ'' = m.val n ψ'')
    {P : Name} {nP nF : Nat}
    {rule : RecRule} {cvA cvj : ConstantVal}
    (hfP₁ : (⟨c₀ :: env.consts⟩ : Env).find? P = some c₀)
    (hfj : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    (hfirep : RecRule.fire rule = .plain)
    (hcp : RecRule.ctorParams rule = nP)
    (hnf : RecRule.nfields rule = nF)
    {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) = some (rbs, rbody))
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    {dN : Name} {dus : List Level} {dargs : List Expr}
    (hcbody : cbody = Expr.mkAppN (.const dN dus) dargs)
    (hdargs : dargs.length = nP)
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvs : List Expr} {crest2X : Expr}
    {ldoms : List Expr} {lrestL : Expr}
    (hopenP : openPisAtFvars nP cvA.type 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt fvsP cvj.type = some (cdomsP, crestP))
    (hdeParsP : DefEqListOk F env (nP + nF)
      (fvsP.map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars nF crestP nP = some (xFvs, crest2X))
    (hlinstP : Expr.instLamsAt (fvsP ++ xFvs) (RecRule.rhs rule) =
      some (ldoms, lrestL))
    (hdeLamP : DefEqListOk F env (nP + nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms)
    (hTcl : cvA.type.hasFvar = false)
    (hTb : cvA.type.looseBVarsBounded 0 = true)
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hTres : cvA.type.constsResolve env = true)
    (hCres : cvj.type.constsResolve env = true)
    (hRres : (RecRule.rhs rule).constsResolve env = true)
    (hrhsw : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvA.type)
    (hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m.val env ψ'' cvA.type = some T)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m.val env ψ'' cvj.type = some T)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) (RecRule.rhs rule))
    (hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V m.val env ψ'' (RecRule.rhs rule) = some L)
    (Hbot : ∀ (ψ : Name → Nat) (xs : List V), xs.length = nP + nF →
      FramePref m.val env ψ (fvsP ++ xFvs) xs →
      (∃ w, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
          (fun l => xs.getD l SetTheory.empty)
          (Expr.mkAppN (.const P (cvA.levelParams.map .param))
            ((fvsP ++ xFvs).take nP ++
              [Expr.mkAppN (.const (RecRule.ctor rule)
                  (cvj.levelParams.map .param))
                (fvsP ++ xFvs)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrestL →
          interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
            (fun l => xs.getD l SetTheory.empty) e = some w) ∧
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ (nP + nF)
        (fun l => xs.getD l SetTheory.empty)
        (Expr.mkAppN (.const P (cvA.levelParams.map .param))
          ((fvsP ++ xFvs).take nP ++
            [Expr.mkAppN (.const (RecRule.ctor rule)
                (cvj.levelParams.map .param))
              (fvsP ++ xFvs)]))) :
    ∃ fvms bL, ruleLhsParts P cvA nP rule cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = nP + RecRule.nfields rule ∧
      (closeLamsAt fvms bL).constsResolve
        (⟨c₀ :: env.consts⟩ : Env) = true ∧
      ∀ ψ'' : Name → Nat,
        AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ'' 0 (rho0 V)
          (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (RecRule.rhs rule) = some Rv := by
  have hfvsPLen : fvsP.length = nP := (openPisAtFvars_spec nP 0 hopenP).2.1
  have htakeP : fvsP.take nP = fvsP := by
    rw [← hfvsPLen]; exact List.take_length
  have htakeSp : (fvsP ++ xFvs).take nP = fvsP := by
    rw [List.take_append_of_le_length (by omega), htakeP]
  refine rule_eq_of_bottom_ext m F hfresh hagree (Nat.le_refl nP) hfP₁ hfj
    hfirep hcp hnf hstripR hC_strip hcbody hdargs hopenP
    (by rw [htakeP]; exact hcinstP)
    (fun ψ => ctor_pkg_plain (xFvsP := xFvs) m F hopenP hTcl hTb
      (hAty ψ) (by rw [htakeP]; exact hcinstP)
      (by rw [htakeP]; exact hdeParsP)
      (Nat.le_refl nP) hCcl hCb (hACty ψ) (hICty ψ))
    hopenX hlinstP hdeLamP hTcl hTb hCcl hCb hTres hCres hRres hrhsw
    hrhsb hAty hIty hArhs hIrhs ?_
  intro ψ xs hxs hpref
  have h := Hbot ψ xs hxs hpref
  rw [htakeSp] at h
  rw [htakeP]
  exact h


/-- The modeled projection rule's obligation: `proj_rule_eq_of_bottom`
at the bottom fact the checked `proj_i.iota` theorem supplies. -/
theorem proj_rule_eq
    {env : Env} (m : EnvModel V env) (F : Nat)
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {val' : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ'' : Name → Nat,
      val' n ψ'' = m.val n ψ'')
    {f f₀ : Name → Name}
    (hff₀ : ∀ n, (env.find? n).isSome = true → f n = f₀ n)
    (hro₀ : RenameOk m.val env f₀)
    (hro₁ : RenameOk val' (⟨c₀ :: env.consts⟩ : Env) f)
    {P : Name} {nP nF i : Nat} (hi : i < nF)
    {rule : RecRule} {cvA cvj cvt : ConstantVal}
    (hfP₁ : (⟨c₀ :: env.consts⟩ : Env).find? P = some c₀)
    (hlpsP : c₀.toConstantVal.levelParams = cvA.levelParams)
    (hfj : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    {cimP : ConstantInfo}
    (hfPm : env.find? (f P) = some cimP)
    (hPmlps : cimP.toConstantVal.levelParams = cvA.levelParams)
    (heqfind : env.find? eqName = some eqA)
    (heqval₁ : ∀ ψ'' : Name → Nat, val' eqName ψ'' = eqVal V ψ'')
    {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V m.val env ψ'' cvt.type = some Pv ∧
      m.val thmName ψ'' ∈ˢ Pv)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSres : cvt.type.constsResolve env = true)
    (hfirep : RecRule.fire rule = .plain)
    (hcp : RecRule.ctorParams rule = nP)
    (hnf : RecRule.nfields rule = nF)
    {rbs : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) = some (rbs, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
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
         [Expr.mkAppN (.const (f (RecRule.ctor rule))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    {dN : Name} {dus : List Level} {dargs : List Expr}
    (hcbody : cbody = Expr.mkAppN (.const dN dus) dargs)
    (hdargs : dargs.length = nP)
    -- the kernel pins over the base environment
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvs : List Expr} {crest2X : Expr}
    {ldoms : List Expr} {lrestL : Expr}
    (hopenP : openPisAtFvars nP cvA.type 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt fvsP cvj.type = some (cdomsP, crestP))
    (hdeParsP : DefEqListOk F env (nP + nF)
      (fvsP.map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars nF crestP nP = some (xFvs, crest2X))
    (hlinstP : Expr.instLamsAt (fvsP ++ xFvs) (RecRule.rhs rule) =
      some (ldoms, lrestL))
    (hdeLamP : DefEqListOk F env (nP + nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms)
    -- well-formedness over the base environment
    (hTcl : cvA.type.hasFvar = false)
    (hTb : cvA.type.looseBVarsBounded 0 = true)
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hTres : cvA.type.constsResolve env = true)
    (hCres : cvj.type.constsResolve env = true)
    (hRres : (RecRule.rhs rule).constsResolve env = true)
    (hrhsw : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvA.type)
    (hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m.val env ψ'' cvA.type = some T)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m.val env ψ'' cvj.type = some T)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V m.val env ψ'' 0 (rho0 V) (RecRule.rhs rule))
    (hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V m.val env ψ'' (RecRule.rhs rule) = some L) :
    ∃ fvms bL, ruleLhsParts P cvA nP rule cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = nP + RecRule.nfields rule ∧
      (closeLamsAt fvms bL).constsResolve
        (⟨c₀ :: env.consts⟩ : Env) = true ∧
      ∀ ψ'' : Name → Nat,
        AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ'' 0 (rho0 V)
          (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ''
            (RecRule.rhs rule) = some Rv :=
  proj_rule_eq_of_bottom m F hfresh hagree hfP₁ hfj hfirep hcp hnf
    hstripR hC_strip hcbody hdargs hopenP hcinstP hdeParsP hopenX hlinstP
    hdeLamP hTcl hTb hCcl hCb hTres hCres hRres hrhsw hrhsb hAty hIty
    hACty hICty hArhs hIrhs
    (fun ψ => proj_bottom m F hfresh hagree hff₀ hro₀ hro₁ hi hfP₁
      hlpsP hfj hfPm hPmlps heqfind heqval₁ hthm_mem hthm_annot hSw hSres
      hC_strip hS_strip hsdoms hsbody hstripR hrbody hopenP hcinstP
      hdeParsP hopenX hlinstP hTcl hTb hTres (hAty ψ) hCcl hCb hCres
      (hACty ψ) (hICty ψ) (ψ := ψ))
