module

public import ConLeche.Verify.Denote.Rename
public import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InferLemmas

public section

/-!
# Opening a telescope, and substituting a spine into what is left

**The thing that moves a spine between two descriptions of the same
telescope.**  Both folds and both bottoms need the *residual* of a
`∀`-telescope after `k` arguments, and the two sides describe it
differently:

* the pins describe it **syntactically**, as `stripPis`' body with `k`
  loose bvars;
* the laws consume it **semantically**, as a `Term` with the use
  site's spine `xs` already substituted.

Composing the two is: open the `k` binders at fresh variables
(`Expr.instSeq` at `openFvars`, so the existing `instSeq_*` algebra
applies verbatim), denote, then substitute `xs` — which is
`Term.instSeq`, the missing half.

**Why `Term.instSeq` mirrors `Expr.instSeq` clause for clause**
(descending cuts, the same `t - 1`): the two are applied to the *same*
telescope, one before and one after `denote`, and every index fact is
then a transcription rather than a re-derivation.  The one place they
differ is `instSeq_bvar`, and the difference is instructive:
`Expr.instantiate1` does **not** lift, so the `Expr` lemma needs
`looseBVarsBounded 0` on every argument; `Term.inst` does, so the
`Term` lemma needs nothing and pays instead by producing
`liftN c x` — the lifts the consumer's own `inst` then absorbs.
-/

namespace ConLeche.Term
namespace Term

/-! ## `Term.instSeq` -/

/-- Instantiate a spine at descending cuts, outermost argument first —
the term-side counterpart of `ConLeche.Expr.instSeq`. -/
@[expose] def instSeq : List Term → Nat → Term → Term
  | [], _, e => e
  | a :: as, t, e => instSeq as (t - 1) (e.inst a t)

@[simp] theorem instSeq_nil (t : Nat) (e : Term) : instSeq [] t e = e := rfl

theorem instSeq_cons (a : Term) (as : List Term) (t : Nat) (e : Term) :
    instSeq (a :: as) t e = instSeq as (t - 1) (e.inst a t) := rfl

/-- A closed term is untouched. -/
theorem instSeq_eq_self_of_closed {e : Term} (h : Closed e) :
    ∀ (as : List Term) (t : Nat), instSeq as t e = e := by
  intro as
  induction as with
  | nil => intro t; rfl
  | cons a as ih => intro t; rw [instSeq_cons, inst_eq_self_of_closed h, ih]

@[simp] theorem instSeq_sort (as : List Term) (t u : Nat) :
    instSeq as t (.sort u) = .sort u :=
  instSeq_eq_self_of_closed (e := .sort u) trivial as t

@[simp] theorem instSeq_const (as : List Term) (t : Nat) (c : BConst)
    (us : List Nat) : instSeq as t (.const c us) = .const c us :=
  instSeq_eq_self_of_closed (e := .const c us) trivial as t

end Term
end ConLeche.Term

namespace ConLeche.Verify

open ConLeche.Term

/-! ## The checker's opener, tied to the fold machinery

`openPisAtFvars` is how every *iota* pin is stated — the checked
`iota_j` theorem's telescope is opened at free variables and the
statement's parts are read off with `getAppFn`/`getAppArgs` — while the
capability pins use `stripPis` and the folds were built on
`Expr.instSeq (openFvars d k)`.  The two openers agree: both peel
outermost-first, giving the `j`-th binder the variable at index
`d + j`.  This section is that agreement, so the bottoms inherit
everything the folds built rather than re-deriving it against a
second opener.

`openPisAtFvars` opens with the binder's *own* name and domain and
`openFvars` with canonical ones; `denote` reads neither
(`ConLeche/Verify/Denote.lean`), so the two bodies are `ErasedEq` and
that is exactly the tolerance the denotation has. -/

/-- A telescope that opens at a free variable strips.  **The `fvar`
restriction is not cosmetic**: for a general `v` the statement is
false, since `(.bvar 0).instantiate1 v 0 = v` may be a `∀` while
`.bvar 0` is not; the checker only ever opens at variables. -/
theorem stripPis_instantiate1_fvar_isSome_rev {i : Nat}
    {ty : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat),
      ((e.instantiate1 (.fvar i ty) j).stripPis k).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro e j _; rfl
  | succ k ih =>
    intro e j h
    cases e with
    | forallE ty' body m =>
      simp only [Expr.instantiate1, Expr.stripPis, Option.isSome_map] at h ⊢
      exact ih (j + 1) h
    | bvar l =>
      simp only [Expr.instantiate1] at h
      split at h
      · simp only [Expr.stripPis] at h; exact nomatch h
      · split at h <;> (simp only [Expr.stripPis] at h; exact nomatch h)
    | _ => simp only [Expr.instantiate1, Expr.stripPis] at h; exact nomatch h

/-- **The checker's opener, read as a strip plus a canonical
opening.**  `openPisAtFvars` succeeding gives the `stripPis` the fold
machinery wants, an opened body `ErasedEq` to the canonical one, and
the opening variables at their expected indices. -/
theorem openPisAtFvars_stripPis :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      ∃ bs body₀, e.stripPis k = some (bs, body₀) ∧
        fvs.length = k ∧
        (∀ j, j < k → ∃ ty, fvs[j]? = some (.fvar (d + j) ty)) ∧
        Expr.ErasedEq body
          (Expr.instSeq (openFvars d k) (k - 1) body₀) := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl, fun j hj => absurd hj (by omega),
      Expr.ErasedEq.rfl _⟩
  | succ k ih =>
    intro e d fvs body h
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨bs', body₀', hstrip', hlen', hidx', herased'⟩ := ih hop
        have hsome : (bodyE.stripPis k).isSome = true :=
          stripPis_instantiate1_fvar_isSome_rev k 0 (by rw [hstrip']; rfl)
        obtain ⟨⟨bs, body₀⟩, hstrip⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨hbody0, -⟩ := Expr.stripPis_instantiate1_eq k 0 hstrip hstrip'
        refine ⟨(dom, mb) :: bs, body₀, by simp [Expr.stripPis, hstrip],
          by simp [hlen'], ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => exact ⟨dom, by simp⟩
          | succ j =>
            obtain ⟨ty', hj'⟩ := hidx' j (by omega)
            refine ⟨ty', ?_⟩
            rw [List.getElem?_cons_succ, hj']
            congr 2
            omega
        · rw [openFvars_succ, Nat.add_sub_cancel, Expr.instSeq]
          refine Expr.ErasedEq.trans herased' ?_
          rw [hbody0]
          simp only [Nat.zero_add]
          exact Expr.instSeq_erasedEq _ (k - 1)
            (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl _)
              (show Expr.ErasedEq (Expr.fvar d dom)
                (Expr.fvar d (.sort .zero)) from rfl))

/-! ## The opened statement -/

/-- The opened body is the strip body instantiated at the collected
openers — *exactly*, annotations included (the ErasedEq form is
`openPisAtFvars_stripPis`; the pinned-spine transfers need
equality). -/
theorem openPisAtFvars_instSeq :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr}
      {bs : List (Expr × BinderMeta)} {body₀ : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      e.stripPis k = some (bs, body₀) →
      body = Expr.instSeq fvs (k - 1) body₀ := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body bs body₀ h hs
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := hs
    rfl
  | succ k ih =>
    intro e d fvs body bs body₀ h hs
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.stripPis] at hs
        cases hs1 : bodyE.stripPis k with
        | none => rw [hs1] at hs; exact nomatch hs
        | some p1 =>
          rw [hs1] at hs
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hs
          obtain ⟨-, rfl⟩ := hs
          obtain ⟨q1, hq1⟩ := Option.isSome_iff_exists.mp
            (Expr.stripPis_instantiate1_isSome
              (v := .fvar d dom) k 0 (by rw [hs1]; rfl))
          obtain ⟨hbody1, -⟩ := Expr.stripPis_instantiate1_eq k 0 hs1 hq1
          have hihb := ih hop (show Expr.stripPis k
            (bodyE.instantiate1 (Expr.fvar d dom)) =
              some (q1.1, q1.2) from by rw [hq1])
          rw [Nat.zero_add] at hbody1
          rw [hihb, hbody1]
          show _ = Expr.instSeq (Expr.fvar d dom :: p.1) (k + 1 - 1) _
          rw [show Expr.instSeq (Expr.fvar d dom :: p.1) (k + 1 - 1)
              p1.2 = Expr.instSeq p.1 (k + 1 - 1 - 1)
              (p1.2.instantiate1 (.fvar d dom) (k + 1 - 1)) from rfl,
            Nat.add_sub_cancel]

end ConLeche.Verify
