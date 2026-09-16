module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.AbstractRange

public section

/-!
# The copy's telescope, syntactically (task #315 L-B, DESIGN §U.23)

`mkCopy` stores a copy's former as `closeTelescope pbs 0 tyI` — the
block's first former's parameter binders closed around the container's
type instantiated at the pin's components.  The reading of such a term
goes through `openPisAtFvars`, whose action on a `∀`-telescope is known
(`openPisAtFvars_mkPisB`: the openers depend on the binders only, the
body is `instSeq` of the openers), and the bulk abstraction's round
trip is known modulo annotations (`eraseAnnots_openAbstract`).  What
this module adds is the bridge: `closeTelescope` over fvar-free binder
domains IS the `∀`-telescope over the body's bulk abstraction
(`closeTelescope_eq_mkPisB`), plus the small facts the reading needs —
`instPis` as an `instPisAt` residual, loose-variable bounds through
`instPis` and out of `mkAppN`, and `WScoped` out of `mkAppN`.
-/

namespace ConLeche

open Expr

/-- `abstract1` on an fvar-free term is the identity. -/
theorem Expr.abstract1_of_not_hasFvar :
    ∀ (e : Expr) (d k : Nat), e.hasFvar = false → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k h <;> simp_all [hasFvar, abstract1]

/-- **The lowest variable last**: the bulk abstraction of `n + 1`
variables from `i` is the abstraction of the `n` variables above `i`,
then `i` at cut `c + n` — `abstractRange_succ` from the other end. -/
theorem Expr.abstractRange_succ_low :
    ∀ (e : Expr) (i n c : Nat),
      e.abstractRange i (n + 1) c = (e.abstractRange (i + 1) n c).abstract1 i (c + n) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro i n c
    simp only [abstractRange]
    by_cases h1 : i ≤ idx ∧ idx < i + (n + 1)
    · rw [if_pos h1]
      by_cases h2 : i + 1 ≤ idx ∧ idx < i + 1 + n
      · rw [if_pos h2]
        simp only [abstract1]
        congr 1
        omega
      · rw [if_neg h2]
        have hidx : idx = i := by omega
        simp only [abstract1, if_pos hidx]
        congr 1
        omega
    · rw [if_neg h1]
      have h2 : ¬ (i + 1 ≤ idx ∧ idx < i + 1 + n) := by omega
      rw [if_neg h2]
      simp only [abstract1]
      rw [if_neg (by omega)]
  | bvar _ => intro i n c; simp [abstractRange, abstract1]
  | sort _ => intro i n c; simp [abstractRange, abstract1]
  | const _ _ => intro i n c; simp [abstractRange, abstract1]
  | lit _ => intro i n c; simp [abstractRange, abstract1]
  | app f a ihf iha =>
    intro i n c
    simp only [abstractRange, abstract1, ihf, iha]
  | lam ty b _ ihty ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | forallE ty b _ ihty ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | letE ty v b ihty ihv ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihv, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | proj _ _ x ih =>
    intro i n c
    simp only [abstractRange, abstract1, ih]

/-- `mkPisB` at the empty binder list. -/
theorem mkPisB_nil (e : Expr) : mkPisB [] e = e := (mkPisB_eq_foldr [] e).symm

/-- `mkPisB` at a cons. -/
theorem mkPisB_cons (b : Expr × BinderMeta) (bs : List (Expr × BinderMeta)) (e : Expr) :
    mkPisB (b :: bs) e = .forallE b.1 (mkPisB bs e) b.2 := by
  rw [← mkPisB_eq_foldr, ← mkPisB_eq_foldr]
  rfl

/-- A `∀`-telescope over fvar-free domains under `abstract1`: the
domains stay, the body is abstracted under the binders. -/
theorem mkPisB_abstract1 :
    ∀ (bs : List (Expr × BinderMeta)) (X : Expr) (d k : Nat),
      (∀ b ∈ bs, b.1.hasFvar = false) →
      (mkPisB bs X).abstract1 d k = mkPisB bs (X.abstract1 d (k + bs.length))
  | [], X, d, k, _ => by
    rw [mkPisB_nil, mkPisB_nil]
    rfl
  | b :: bs, X, d, k, h => by
    rw [mkPisB_cons, mkPisB_cons]
    show Expr.forallE (b.1.abstract1 d k) ((mkPisB bs X).abstract1 d (k + 1)) b.2
      = Expr.forallE b.1 (mkPisB bs (X.abstract1 d (k + (b :: bs).length))) b.2
    rw [Expr.abstract1_of_not_hasFvar _ _ _ (h b List.mem_cons_self),
      mkPisB_abstract1 bs X d (k + 1) (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')),
      List.length_cons, show k + 1 + bs.length = k + (bs.length + 1) from by omega]

/-- **`closeTelescope` is the telescope over the bulk abstraction** when
the binder domains carry no free variables (the first former's binders,
read off a closed type): one `abstract1` per binder, innermost first,
is `abstractRange` of the body under the binders. -/
theorem closeTelescope_eq_mkPisB :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (e : Expr),
      (∀ b ∈ bs, b.1.hasFvar = false) →
      closeTelescope bs i e = mkPisB bs (e.abstractRange i bs.length 0)
  | [], i, e, _ => by
    rw [mkPisB_nil]
    simp [closeTelescope, abstractRange_zero]
  | (dom, bm) :: bs, i, e, h => by
    simp only [closeTelescope]
    rw [closeTelescope_eq_mkPisB bs (i + 1) e (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      mkPisB_abstract1 bs _ i 0 (fun b hb => h b (List.mem_cons_of_mem _ hb)), Nat.zero_add,
      List.length_cons, Expr.abstractRange_succ_low e i bs.length 0, Nat.zero_add, mkPisB_cons]

/-- An fvar-free telescope has fvar-free domains and body. -/
theorem hasFvar_mkPisB :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
      (mkPisB bs body).hasFvar = false →
      (∀ b ∈ bs, b.1.hasFvar = false) ∧ body.hasFvar = false
  | [], body, h => ⟨fun _ hb => absurd hb (by simp), by rwa [mkPisB_nil] at h⟩
  | b :: bs, body, h => by
    rw [mkPisB_cons] at h
    have h' : (b.1.hasFvar || (mkPisB bs body).hasFvar) = false := h
    simp only [Bool.or_eq_false_iff] at h'
    obtain ⟨hall, hb⟩ := hasFvar_mkPisB bs body h'.2
    refine ⟨fun b' hb' => ?_, hb⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact h'.1
    · exact hall b' hb'

/-- `instPis` is the residual of an `instPisAt` run. -/
theorem instPis_instPisAt :
    ∀ (as : List Expr) (e r : Expr), Expr.instPis e as = some r →
      ∃ ds, Expr.instPisAt as e = some (ds, r)
  | [], e, r, h => by
    simp only [Expr.instPis, Option.some.injEq] at h
    exact ⟨[], by simp [Expr.instPisAt, h]⟩
  | a :: as, e, r, h => by
    cases e with
    | forallE ty body bm =>
      simp only [Expr.instPis] at h
      obtain ⟨ds, hds⟩ := instPis_instPisAt as _ r h
      exact ⟨ty :: ds, by simp [Expr.instPisAt, hds]⟩
    | _ => simp [Expr.instPis] at h

/-- Instantiating a bounded telescope at bounded arguments stays
bounded. -/
theorem looseBVarsBounded_instPis :
    ∀ (as : List Expr) (e r : Expr),
      e.looseBVarsBounded 0 = true → (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      Expr.instPis e as = some r → r.looseBVarsBounded 0 = true
  | [], e, r, he, _, h => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    exact he
  | a :: as, e, r, he, has, h => by
    cases e with
    | forallE ty body bm =>
      simp only [Expr.instPis] at h
      have hb : body.looseBVarsBounded 1 = true := by
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
        exact he.2
      exact looseBVarsBounded_instPis as _ r
        (looseBVarsBounded_instantiate1_gen (has a List.mem_cons_self) hb)
        (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) h
    | _ => simp [Expr.instPis] at h

/-- A bounded application chain has a bounded head and bounded
arguments. -/
theorem looseBVarsBounded_of_mkAppN {k : Nat} :
    ∀ {xs : List Expr} {f : Expr}, (Expr.mkAppN f xs).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ x ∈ xs, x.looseBVarsBounded k = true
  | [], f, h => ⟨h, fun _ hx => absurd hx (by simp)⟩
  | x :: xs, f, h => by
    obtain ⟨hf, hxs⟩ := looseBVarsBounded_of_mkAppN (xs := xs) (f := .app f x) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hf
    refine ⟨hf.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf.2
    · exact hxs y hy

/-- A scoped application chain has a scoped head and scoped
arguments. -/
theorem WScoped_of_mkAppN {d : Nat} :
    ∀ {xs : List Expr} {f : Expr}, Expr.WScoped d (Expr.mkAppN f xs) →
      Expr.WScoped d f ∧ ∀ x ∈ xs, Expr.WScoped d x
  | [], f, h => ⟨h, fun _ hx => absurd hx (by simp)⟩
  | x :: xs, f, h => by
    obtain ⟨hf, hxs⟩ := WScoped_of_mkAppN (xs := xs) (f := .app f x) h
    simp only [Expr.WScoped] at hf
    refine ⟨hf.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf.2
    · exact hxs y hy

end ConLeche
