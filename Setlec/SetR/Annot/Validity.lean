import Setlec.SetR.Annot.Pass
import Setlec.SetBase.Weaken

/-!
# Validity (regularity) for `Infer`: **refuted** (task #151, tier A — B5′'s check)

Tier B's repair **B5′** (`Setlec/SetR/DESIGN.md`, finding B5) proposes to
supply the λ-codomain numeral from a *metatheorem* rather than from a
premise or a kernel check:

> if `Infer Δ b B` then `B` has a sort — `∃ v, HasSort Δ B v`

That would give `Annotates`' λ clause its codomain numeral relationally,
with no I7 premise, no kernel change and no runtime cost.  This module is
the check tier A owed, and the verdict is **negative**:

**`ValidInfer` is false for the family as landed** — mechanized, at the
empty environment, in a *sorted* context, against a concrete derivation
(`validity_refuted`).  The failing clause is **I8** (application), and
the reason is not the one the hazard note anticipated.

## The case map (what is free, and where it stops)

| clause | status |
|---|---|
| I1 `sort` | **free** — `hasSort_sort`: the type is `.sort (u+1)`, sorted by I1 + `DefEq.refl` |
| I2 `bvar` | **free modulo the context invariant** — `CtxSorted` below; maintained across the two binder clauses by M1's `weakenHead` (`CtxSorted.cons`) |
| I3 `const` | **an environment obligation** — the type is the stored type's denotation; the *type front door* runs `ensureSort` (`Kernel/Checker.lean:272,380`), so `DeclR` carries the fact and an `EnvS` field can expose it.  Not derivable from I3's own premises; nothing here refutes it |
| I4/I5 `litNat`/`litStr` | **basis pins** — the types are `⟦Nat⟧`/`⟦String⟧`, and `natLitSupported`/`strLitSupported` pin their stored types.  Same shape as I3 |
| I6 `pi` | **free** — `hasSort_sort` again (the type is a sort) |
| **I7 `lam`** | **free, and it is exactly B5′'s payoff** — `hasSort_pi_of` builds `HasSort Δ (.pi A B) (imax u v)` from I6's own shape, where `v` is delivered by the *induction hypothesis at the body* (`Infer (A :: Δ) b B`).  B5′ is right about this clause: validity would hand the λ its codomain numeral for free |
| I8 `app` | **REFUTED** — below |
| I9 `proj` | not reached (the type is `piResidualV` of a pinned entry's type; plausible, unaudited) |
| I10 `letE` | **free** — the type is the IH's, at `Infer Δ (b.inst v) B` |

## Why I8 fails, and why no repair of I8 works

I8's conclusion type is `B.inst a`, where `B` comes from the premise
`DefEq Δ tf (.pi A B)` — a *conversion*, not a derivation about `.pi A B`.
The hazard note predicted the obstacle would be substitution
admissibility (which the family indeed lacks — tier A's finding A1).
Substitution is necessary but **not sufficient**: before substituting one
must first obtain `HasSort (A :: Δ) B v`, and the only thing available is
the induction hypothesis `HasSort Δ tf w` at the *converted* type.
Getting from one to the other is `HasSort` **crossing a `DefEq`**, and
that is the campaign's known-impossible move — T3's "common root", T4's
`AnnotOkV`-cannot-cross-`DefEq` record, the reason repair C
(`Infer.conv`) was rejected in the first place.  It is impossible here
for the same structural reason: `DefEq.symm` forces any one-directional
preservation statement into a biconditional, and `DefEq.ofRed` +
`Red.zeta` then relates a sorted term to an unsorted one in one
premise-free step.

`hasSort_not_defEq_stable` mechanizes that general statement;
`validity_refuted` mechanizes the consequence for validity itself, by
pushing the same junk through `DefEq.piCong` into a `.pi`'s codomain and
then through I8.

## The countermodel, in one line

`junkTy = let (_ : prf) := prf; Sort 1` is `DefEq`-equal to `Sort 1`
(`Red.zeta` is premise-free) but is **not inferable at all** at the empty
environment, hence unsorted.  `DefEq.piCong` moves it into a codomain,
I8 substitutes it into its conclusion, and the resulting `Infer`
derivation has an unsorted type.  Nothing about the environment is used
beyond blocking I3/I4/I5 — the empty environment satisfies `EnvS.empty`,
the context `[.sort 0]` is `CtxSorted`, and the valuation may be taken to
satisfy `CvalAnnot` — so the refutation survives every hypothesis
validity could reasonably carry.

## Scope of the refutation, stated honestly

This refutes validity **for the relation**, which is what B5′ needs: the
annotation pass is a theorem about derivations, so a derivation without
the property is a counterexample.  It does **not** show that a
`--set-model` checker run can *produce* such a derivation — the bridge's
image is a sub-family that is not characterized anywhere, and
premise-exactness deliberately keeps the relation larger than that image
(design §0).  A validity restricted to the bridge's image would need that
characterization first, which is a new metatheory, not a lemma.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

section Validity

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ## The statements -/

/-- **Validity / regularity**, B5′'s proposed metatheorem: every inferred
type has a sort. -/
def ValidInfer (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : Prop :=
  ∀ (Δ : List VExpr) (e T : VExpr), Infer μ env cval φ Δ e T →
    ∃ v, HasSort μ env cval φ Δ T v

/-- The context invariant I2 needs: every entry, read at the ambient
depth, is sorted. -/
def CtxSorted (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) : Prop :=
  ∀ (i : Nat) (A : VExpr), Δ[i]? = some A →
    ∃ v, HasSort μ env cval φ Δ (A.liftN (i + 1)) v

/-! ## The free clauses

I1 and I6 conclude at a sort; I7 builds its `∀` from I6's own shape, with
the codomain numeral coming from the induction hypothesis at the body —
the clause B5′ is *about*. -/

/-- I1/I6: a sort is sorted, one level up. -/
theorem hasSort_sort {Δ : List VExpr} {u : Nat} :
    HasSort μ env cval φ Δ (.sort u) (u + 1) :=
  ⟨.sort (u + 1), Infer.sort, DefEq.refl⟩

/-- **I7's clause, and B5′'s payoff.**  Given I7's own domain premises and
a sorting of the body's inferred type — which is exactly what validity's
induction hypothesis at `Infer (A :: Δ) b B` would deliver — the λ's type
`.pi A B` is sorted, by I6.  The codomain numeral `v` the two-regime
interpretation wants is *the second component of this fact*, obtained with
no I7 premise and no kernel check.

So B5′'s architecture is sound at the clause it was designed for; what
fails is validity itself, one clause over (I8). -/
theorem hasSort_pi_of {Δ : List VExpr} {A B tA : VExpr} {u v : Nat}
    (hA : Infer μ env cval φ Δ A tA)
    (hu : DefEq μ env cval φ Δ tA (.sort u))
    (hB : HasSort μ env cval φ (A :: Δ) B v) :
    HasSort μ env cval φ Δ (.pi A B) (imax u v) := by
  obtain ⟨tB, hBI, hBD⟩ := hB
  exact ⟨.sort (imax u v), Infer.pi hA hu hBI hBD, DefEq.refl⟩

/-- I2's clause is the context invariant, read off: the inferred type of a
variable is the entry lifted to the ambient depth. -/
theorem hasSort_bvar_type {Δ : List VExpr} {i : Nat} {A : VExpr}
    (hΔ : CtxSorted μ env cval φ Δ) (hi : Δ[i]? = some A) :
    ∃ v, HasSort μ env cval φ Δ (A.liftN (i + 1)) v :=
  hΔ i A hi

/-- The context invariant is **maintained** by the two binder clauses:
I6 and I7 extend the context by a domain they have just sorted, and every
older entry's sorting rides along on M1's `weakenHead`.  So I2 costs the
induction nothing beyond threading `CtxSorted`. -/
theorem CtxSorted.cons (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {A : VExpr} {u : Nat}
    (hΔ : CtxSorted μ env cval φ Δ) (hA : HasSort μ env cval φ Δ A u) :
    CtxSorted μ env cval φ (A :: Δ) := by
  intro i A' hi
  match i with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    obtain ⟨tA, hI, hD⟩ := hA
    exact ⟨u, tA.lift, hI.weakenHead hcl A, hD.weakenHead hcl A⟩
  | n + 1 =>
    simp only [List.getElem?_cons_succ] at hi
    obtain ⟨v, t, hI, hD⟩ := hΔ n A' hi
    refine ⟨v, t.lift, ?_, hD.weakenHead hcl A⟩
    have hIw := hI.weakenHead hcl A
    rwa [show (A'.liftN (n + 1)).lift = A'.liftN (n + 1 + 1) from
      VExpr.liftN_liftN_add A' (n + 1) 1 0] at hIw

/-! ## The junk type

`Red.zeta` is **premise-free**: `Red Δ (.letE T x b) (b.inst x)` holds for
every `T`, `x`, `b` whatsoever.  So an arbitrary `let` node is
`DefEq`-equal to its contractum while being, in general, not inferable at
all.  That gap is the whole refutation. -/

/-- `let (_ : prf) := prf; Sort 1` — `DefEq`-equal to `Sort 1`, inferable
nowhere. -/
def junkTy : VExpr := .letE .prf .prf (.sort 1)

@[simp] theorem junkTy_inst (a : VExpr) (k : Nat) :
    junkTy.inst a k = junkTy := rfl

/-- The junk is `DefEq` to `Sort 1`, in **any** environment and context,
by one premise-free zeta step. -/
theorem defEq_junkTy {Δ : List VExpr} :
    DefEq μ env cval φ Δ (.sort 1) junkTy :=
  DefEq.symm (DefEq.ofRed (Red.zeta (T := .prf) (v := .prf) (b := .sort 1)))

/-! ## Nothing is inferable at the empty environment except by the
structural clauses

I3 needs a successful lookup, I4/I5 need the literal-support guards; the
empty environment refutes all three, so inversion at a subject that is not
one of the seven structural shapes leaves no clause at all. -/

/-- At the empty environment the three leaf clauses cannot fire — I3
needs a successful lookup, I4/I5 the literal-support guards — so every
`Infer` subject is one of the seven *structural* shapes.

(The inversion is stated with a general subject on purpose: `cases` on a
derivation whose subject is a fixed non-constructor term fails, because
`Infer.const`'s subject `cval n ψ` is an application of a variable and
dependent elimination cannot decide it against a literal.  Generalizing
the subject and refuting the leaf clauses from the environment is the
way through — the same overlap the campaign records at R6's `Infer`
inversion.) -/
theorem infer_shape_empty {Δ : List VExpr} {e t : VExpr}
    (h : Infer μ Env.empty cval φ Δ e t) :
    (∃ u, e = .sort u) ∨ (∃ i, e = .bvar i) ∨ (∃ A B, e = .pi A B) ∨
      (∃ A b, e = .lam A b) ∨ (∃ f a, e = .app f a) ∨
      (∃ i p, e = .proj i p) ∨ (∃ T x b, e = .letE T x b) := by
  cases h with
  | sort => exact Or.inl ⟨_, rfl⟩
  | bvar => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | const hfind => exact absurd hfind (by simp [Env.empty, Env.find?])
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | pi => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | lam => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  | app => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | proj => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))
  | letE => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩)))))

/-- `.prf` has no type at the empty environment: it is none of the seven
shapes. -/
theorem not_infer_prf {Δ : List VExpr} {t : VExpr} :
    ¬ Infer μ Env.empty cval φ Δ .prf t := by
  intro h
  rcases infer_shape_empty h with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    | ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, he⟩ <;> exact nomatch he

/-- I10's first premise, exposed: a typed `let` node has a typed
annotation. -/
theorem infer_letE_annot_empty {Δ : List VExpr} {e t T x b : VExpr}
    (h : Infer μ Env.empty cval φ Δ e t) (he : e = .letE T x b) :
    ∃ tT, Infer μ Env.empty cval φ Δ T tT := by
  cases h with
  | const hfind => exact absurd hfind (by simp [Env.empty, Env.find?])
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | letE hT => cases he; exact ⟨_, hT⟩
  | sort | bvar | pi | lam | app | proj => exact nomatch he

/-- The junk type has no type at the empty environment: the only clause
whose subject is a `let` is I10, and its first premise types `.prf`. -/
theorem not_infer_junkTy {Δ : List VExpr} {t : VExpr} :
    ¬ Infer μ Env.empty cval φ Δ junkTy t := by
  intro h
  obtain ⟨_, hT⟩ := infer_letE_annot_empty h (T := .prf) (x := .prf)
    (b := .sort 1) rfl
  exact not_infer_prf hT

/-- Hence the junk type is **unsorted**. -/
theorem junkTy_unsorted {Δ : List VExpr} :
    ¬ ∃ v, HasSort μ Env.empty cval φ Δ junkTy v := by
  rintro ⟨_, _, hI, -⟩
  exact not_infer_junkTy hI

/-! ## The general wall: `HasSort` cannot cross a `DefEq` -/

/-- **Sortedness is not `DefEq`-stable**, and therefore no version of I8
can obtain its codomain's sorting from the induction hypothesis at the
converted type.  `Sort 1` is sorted, `junkTy` is not, and one premise-free
zeta step relates them.

This is the same impossibility as T4's "`AnnotOkV` cannot cross a
`DefEq`": `DefEq.symm` turns any one-directional preservation claim into a
biconditional, and `DefEq.ofRed` supplies a step whose two sides differ in
the property. -/
theorem hasSort_not_defEq_stable :
    ¬ ∀ (Δ : List VExpr) (a b : VExpr), DefEq μ Env.empty cval φ Δ a b →
        (∃ v, HasSort μ Env.empty cval φ Δ a v) →
        ∃ v, HasSort μ Env.empty cval φ Δ b v := by
  intro h
  exact junkTy_unsorted
    (h [] (.sort 1) junkTy defEq_junkTy ⟨2, hasSort_sort⟩)

/-! ## The counterexample to validity

`DefEq.piCong` carries the junk into a codomain, and I8 substitutes it
into its own conclusion.  Every ingredient is a landed constructor; the
derivation is four rule applications deep. -/

/-- The context of the counterexample — sorted (`ctxSorted_ctx`), so the
refutation is not an artifact of an ill-formed context. -/
def cxCtx : List VExpr := [.sort 0]

/-- The function of the counterexample: `fun (_ : Prop) => Prop`, whose
inferred type is `(_ : Sort 0) → Sort 1`. -/
def cxFun : VExpr := .lam (.sort 0) (.sort 0)

theorem infer_cxFun :
    Infer μ Env.empty cval φ cxCtx cxFun (.pi (.sort 0) (.sort 1)) :=
  Infer.lam Infer.sort DefEq.refl Infer.sort
    (fun _ _ => DefEq.refl) (fun _ _ => Infer.sort)
    (fun _ _ => DefEq.refl)

/-- **The counterexample.**  A well-formed `Infer` derivation, in a sorted
context at the empty environment, whose inferred type has no sort. -/
theorem infer_cx :
    Infer μ Env.empty cval φ cxCtx (.app cxFun (.bvar 0)) junkTy :=
  Infer.app infer_cxFun (DefEq.piCong DefEq.refl defEq_junkTy)
    (Infer.bvar (A := .sort 0) rfl) DefEq.refl

/-- The counterexample's context is sorted, so validity cannot be rescued
by a context invariant. -/
theorem ctxSorted_cx : CtxSorted μ Env.empty cval φ cxCtx := by
  intro i A hi
  match i with
  | 0 =>
    simp only [cxCtx, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨1, hasSort_sort⟩
  | n + 1 => simp [cxCtx] at hi

/-- **B5′ is refuted**: validity fails for the family as landed, at I8. -/
theorem validity_refuted : ¬ ValidInfer μ Env.empty cval φ :=
  fun h => junkTy_unsorted (h cxCtx _ _ infer_cx)

/-! ### What the counterexample really says

The *same* subject also infers a perfectly sorted type, by taking I8's
conversion premise to be `DefEq.refl` instead of the `piCong` step
(`infer_cx_good`).  So the failure is not that the term is bad: it is that

* `Infer`'s type slot is determined only **up to `DefEq`** (the rule
  quantifies `A` and `B` existentially over a conversion, which is
  premise-exactly what the checker's `whnf`-then-match does), and
* `HasSort` is **not `DefEq`-stable** (`hasSort_not_defEq_stable`).

Any property of the *inferred type* that is not `DefEq`-stable is
therefore not a theorem of this family — validity is one instance, and the
statement of that general fact is the useful takeaway. -/
theorem infer_cx_good :
    Infer μ Env.empty cval φ cxCtx (.app cxFun (.bvar 0)) (.sort 1) :=
  Infer.app infer_cxFun DefEq.refl (Infer.bvar (A := .sort 0) rfl) DefEq.refl

/-- The sorted reading of the same subject, for contrast. -/
theorem hasSort_cx_good :
    HasSort μ Env.empty cval φ cxCtx (.sort 1) 2 :=
  hasSort_sort

end Validity

end Setlec.SetR
