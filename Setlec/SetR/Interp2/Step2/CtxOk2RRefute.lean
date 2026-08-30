import Setlec.SetR.Interp2.Step2.InferQ
import Setlec.SetR.Sound.Main

/-!
# `CtxOk2R` is refuted — the two currencies disagree on an
empty-domain λ

`Step2/InferQ.lean` states `CtxOk2R` (the bridge from `CtxOk2`, the
annotated context correspondence, to `CtxOkR`, the relational one) and
records that its author believes it false, for a *relational* reason:
`CtxOkR`'s leaf package is `∃ T', Infer … ∧ DefEq … T' T`, a
derivation, while `CtxOk2`'s is an `interp2` equation.

This file refutes it, and the mechanized reason is **cheaper and more
structural** than the relational one: `CtxOk2` states its leaf
agreement *under `Sat2`* — satisfaction in the **annotated**
(`interp2`) currency — while `CtxOkR` is a derivation, whose only
semantic reading is via `Sat` in the **collapse** (`interp`) currency.
The two currencies do **not** agree on which contexts are inhabited:
at an empty-domain λ,

* `interp2` says `lamR v ∅ F = ∅` (`lamR_pos_empty`, `v ≠ 0`) —
  the annotation, not the vacuous value test, decides;
* `interp` says `lamC ∅ F = pt` (`lamC_empty`) — the #100
  countermodel, and `lamR_pos_empty`'s own docstring names it.

So a context entry `⟪fun (_ : Empty) => Prop⟫` is **uninhabited in
`interp2` and inhabited in `interp`**.  `Sat2` is then unsatisfiable,
`CtxOk2`'s whole semantic conjunct is vacuous, and `CtxOk2` holds for
*any* leaf annotation whatsoever — while `CtxOkR` still owes a real
`Infer`/`DefEq` pair, which soundness (`Infer.sound`, `DefEq.sound`,
run at `ρ ≡ ptTag`) turns into `ptTag ∈ˢ univ 0`.  False.

`ctxOk2R_refuted` is that argument.  Its only premise is an arbitrary
`m : EnvS2U V env` — no environment shape, no fuel, no mode, no level
assignment, and no unproved side condition.

## Reachability

Read the counterexample as a statement about the **quantifier**:
`CtxOk2R` ranges over *every* `Δa`, and `CtxOk2` puts no
well-formedness condition on `Δa` at all (no `CtxAnn`, no
`AnnotOk2`, no relation to `Δa.map erase` beyond the one the
conclusion is trying to establish).  Any `Δa` with an
`interp2`-uninhabited entry makes the hypothesis vacuous.  That much
is unconditional and is what the theorem below exhibits.

What makes the entry *decisive* rather than merely vacuous is that it
must be uninhabited in `interp2` while `interp` still inhabits its
erasure — otherwise `Sat` is unsatisfiable too and soundness has
nothing to say (this is why an honest `⟪Empty⟫` entry does **not**
refute: it is empty in both currencies).  The λ entry is the smallest
shape with that property, and it is a `#100`-flavoured one: the
currencies part company exactly at the empty-domain binder.

The entry is not one `CtxOk2.open` can build from a checker-accepted
subject (a λ is not a `Sort`, so it is not a binder domain).  So this
refutes `CtxOk2R` **as stated** — which is what a residue means — and
not a hypothetical repair that first restricts `Δa`.  See
`ctxOk2R_refuted_nonvacuous` below for the same contradiction with the
`interp2` equation holding *non-vacuously*, at the cost of one
`denote2` premise.

Per the campaign's standing practice (`Interp2/EnvS2Refute.lean`'s
`AcvalDefnUniform`/`AcvalThmUniform`), the refuted shape is restated
here as `CtxOk2RShape` so the refutation survives any repair of the
original.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The refuted shape, restated

A standalone copy of `Step2/InferQ.lean`'s `CtxOk2R`, so that the
refutation below keeps its subject if the original is amended. -/

/-- `CtxOk2R` as of seal 7, restated so the refutation is permanent. -/
def CtxOk2RShape {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {Δa : List AVExpr} {e : Expr},
    CtxOk2 m μ φ F d Δa e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e

/-- The original implies the restatement — the two are the same
sentence, checked rather than asserted. -/
theorem CtxOk2RShape.of {env : Env} {m : EnvS2U V env} {μ : CheckMode}
    {φ : Name → Nat} (h : CtxOk2R m μ φ) : CtxOk2RShape m μ φ :=
  fun hC => h hC

/-! ## The separating entry -/

/-- `⟪fun (_ : Empty) => Prop⟫`: the annotated denotation of a λ whose
domain is the empty basis type.  The one shape on which the two
currencies disagree about inhabitation. -/
def emptyLamA : AVExpr := .lam 1 (.const .empty []) (.sort 0)

/-- **In the annotated currency it is empty** (`lamR_pos_empty`). -/
theorem interp2_emptyLamA (ρ : Nat → V) :
    interp2 V ρ emptyLamA = (empty : V) := by
  show lamR 1 (bval2 V .empty []) _ = _
  exact lamR_pos_empty (by decide) _

/-- **In the collapse currency its erasure is the proof point**
(`lamC_empty`) — the #100 countermodel, and the whole of the gap. -/
theorem interp_emptyLamA_erase (ρ : Nat → V) :
    interp V ρ emptyLamA.erase = (pt : V) := by
  show lamC (bval V .empty []) _ = _
  exact lamC_empty _

/-- `Sat2` cannot reach past the entry: it is uninhabited over
`interp2`. -/
theorem not_sat2_emptyLamA {Δa : List AVExpr} {ρ : Nat → V}
    (hΔ : Δa[0]? = some emptyLamA) (h : Sat2 V Δa ρ) : False := by
  have := h 0 emptyLamA hΔ
  rw [interp2_emptyLamA] at this
  exact not_mem_empty _ this

/-- `Sat` does reach past its erasure: `pt` is inhabited by `ptTag`. -/
theorem sat_emptyLamA_erase :
    Sat V [emptyLamA.erase] (fun _ => (ptTag : V)) := by
  intro i A hi
  cases i with
  | zero =>
    obtain rfl : A = emptyLamA.erase := (by simpa using hi : _ = A).symm
    rw [interp_emptyLamA_erase]
    exact ptTag_mem_pt
  | succ k => simp at hi

/-- `ptTag` is not a truth value: it has `∅` as a member, and every
member of a member of `univ 0` is `pt`. -/
theorem ptTag_not_mem_univ_zero : ¬ (ptTag : V) ∈ˢ (univ 0 : V) :=
  fun h => pt_ne_empty (mem_univ_zero h empty_mem_ptTag).symm

/-! ## The refutation -/

/-- **`CtxOk2R` is false.**  At depth `1`, with the single context
entry `emptyLamA` and the subject `.fvar 0 n Prop`:

* `CtxOk2` holds — its leaf agreement is guarded by `Sat2`, which
  `emptyLamA` makes unsatisfiable, and the two syntactic components
  (`denote2` of `Prop`, the context lookup) are immediate;
* `CtxOkR` cannot — its leaf package is an `Infer`/`DefEq` pair, and
  `Sat` *is* satisfiable at `emptyLamA.erase`, so `Infer.sound` and
  `DefEq.sound` deliver `ptTag ∈ˢ univ 0`.

No premise beyond an arbitrary `m : EnvS2U V env`. -/
theorem ctxOk2R_refuted {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) (F : Nat) (n : Name)
    (h : CtxOk2RShape m μ φ) : False := by
  have hleaf : (Expr.fvar 0 n (.sort .zero)).fvarLeaves
      = [(0, n, Expr.sort .zero)] := by
    simp [Expr.fvarLeaves]
  -- the annotated correspondence, vacuously
  have hC2 : CtxOk2 m μ φ F 1 [emptyLamA]
      (.fvar 0 n (.sort .zero)) := by
    refine ⟨rfl, ?_⟩
    intro l hl
    rw [hleaf] at hl
    obtain rfl : l = (0, n, Expr.sort .zero) := by simpa using hl
    refine ⟨Nat.zero_lt_one, trivial, .sort 0, emptyLamA,
      denote2_sortQ, rfl, fun ρ hρ => ?_⟩
    exact absurd hρ (fun hs => not_sat2_emptyLamA rfl hs)
  -- the relational correspondence, forced
  obtain ⟨-, hCR⟩ := h hC2
  obtain ⟨-, -, T, hden, T', hI, hD⟩ :=
    hCR (0, n, Expr.sort .zero) (by rw [hleaf]; simp)
  obtain rfl : T = .sort 0 := by
    rw [denote_sort] at hden
    exact (Option.some.inj hden).symm
  -- and soundness reads it in the collapse currency
  have hsat : Sat V ([emptyLamA].map AVExpr.erase)
      (fun _ => (ptTag : V)) := by
    simpa using sat_emptyLamA_erase (V := V)
  have h1 := (Infer.sound (V := V) (m.base.toHyp φ) hI _ hsat).2
  have h2 := DefEq.sound (V := V) (m.base.toHyp φ) hD _ hsat
  rw [interp_bvar, h2, interp_sort] at h1
  exact ptTag_not_mem_univ_zero h1

/-! ## The same contradiction without the vacuity

The refutation above is a statement about `CtxOk2R`'s quantifier: it
never has to *satisfy* the leaf agreement, only to observe that
`Sat2` cannot.  A reader who suspects the vacuity is the whole story
should read this second version, where the `interp2` agreement holds
**for every `ρ`, unconditionally** — the annotated context entry and
the leaf's annotation genuinely denote the same set — and the
contradiction is unchanged.

It costs one premise: the leaf's type annotation must `denote2` to
`⟪Empty⟫`.  That is the pinned empty basis type
(`Setlec/SetR/DESIGN.md`; "Empty is a basis type"), so the premise is
discharged by any environment that has the pin, at
`ty = .const emptyName []`.  What the pair says is exactly the
finding: `⟪Empty⟫` and `⟪fun (_ : Empty) => Prop⟫` are **equal over
`interp2`** and **different over `interp`**, so an `interp2` equation
carries no `DefEq` and no `interp` fact — the wall, in the direction
seal 3 did not test. -/
theorem ctxOk2R_refuted_nonvacuous {env : Env} (m : EnvS2U V env)
    (μ : CheckMode) (φ : Name → Nat) (F : Nat) (n : Name)
    (ty : Expr) (hfv : ty.fvarLeaves = [])
    (hby : Expr.fvarsBelow 0 ty)
    (hden2 : denote2 μ m.acval env φ F 1 ty
      = some (.const .empty []))
    (h : CtxOk2RShape m μ φ) : False := by
  have hleaf : (Expr.fvar 0 n ty).fvarLeaves = [(0, n, ty)] := by
    rw [Expr.fvarLeaves, hfv]
  have hC2 : CtxOk2 m μ φ F 1 [emptyLamA] (.fvar 0 n ty) := by
    refine ⟨rfl, ?_⟩
    intro l hl
    rw [hleaf] at hl
    obtain rfl : l = (0, n, ty) := by simpa using hl
    refine ⟨Nat.zero_lt_one, hby, .const .empty [], emptyLamA,
      hden2, rfl, fun ρ _ => ?_⟩
    -- the agreement, for every `ρ`: both sides are `∅`
    rw [interp2_emptyLamA]
    rfl
  obtain ⟨-, hCR⟩ := h hC2
  obtain ⟨-, -, T, hden, T', hI, hD⟩ :=
    hCR (0, n, ty) (by rw [hleaf]; simp)
  obtain rfl : T = .const .empty [] := by
    have he := denote2_erase m.acval_erase (d := 1) ty hden2
    rw [he] at hden
    exact (Option.some.inj hden).symm
  have hsat : Sat V ([emptyLamA].map AVExpr.erase)
      (fun _ => (ptTag : V)) := by
    simpa using sat_emptyLamA_erase (V := V)
  have h1 := (Infer.sound (V := V) (m.base.toHyp φ) hI _ hsat).2
  have h2 := DefEq.sound (V := V) (m.base.toHyp φ) hD _ hsat
  rw [interp_bvar, h2] at h1
  exact not_mem_empty _ h1

/-! ## The residue, negated

`CtxOk2R` itself, not just the restatement: the negation at every
`m`, `μ` and `φ`, so a consumer that instantiates it is provably
inconsistent. -/

/-- **`CtxOk2R` is unsatisfiable.**  There is no environment
invariant, mode or level assignment at which the bridge holds. -/
theorem not_ctxOk2R {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) : ¬ CtxOk2R m μ φ :=
  fun h => ctxOk2R_refuted m μ φ 0 .anonymous (CtxOk2RShape.of h)

/-! ## The alternative repair, costed

`CtxOk2R` was the *cheap* way out: leave `WhnfCoreClaims2B`,
`WhnfClaims2B` and `DefEqClaims2B` on `CtxOkR`-of-erasures and bridge
at the one clause that mixes them.  It is refuted, so the repair the
dispatch quarter originally proposed — put `CtxOk2` in **all four**
claims — is the remaining option.  That is a statement change and
belongs to the junction; what follows is only its measured price, so
the junction decides with numbers.  Nothing here is wired in.

**How much of the two reduction quarters actually reads `CtxOkR`.**
Counting uses of the kit rather than occurrences of the word (the
hypothesis is threaded on ~120 lines; almost none of them look at
it):

| use | `Whnf` | `DefEqRun` | supplied by `CtxOk2`? |
|---|---|---|---|
| `of_subset` | 10 | 24 | yes — `CtxOk2.of_subset` |
| leaf re-assembly `⟨hC.1, … hC.2 l …⟩` | 7 | 0 | yes — `of_cover` |
| `of_fvarLeaves_nil` | 0 | 8 | **missing**, one line |
| `openCong` | 0 | 5 | **no** — the one real reader |

So of the 54 kit uses, **41** are pure re-plumbing along
`fvarLeaves` and are already in the `CtxOk2` kit; **8** need a
`CtxOk2` twin of `of_fvarLeaves_nil`, which is
`⟨hlen, fun l hl => nomatch …⟩` and carries no content; and **5 are a
genuine read**.

**The exemption argument, and what it costs.**  The five are all
`CtxOkR.openCong`, at the `∀`- and `λ`-congruence clauses: the
checker opens the two binders' bodies with *each side's own*
annotation, so the second body is denoted in a context whose head is
the **left** domain while the opened variable's annotation denotes to
the **right** one.  `CtxOkR` absorbs that with the relation's own
equality — `openCong`'s new-variable package is
`⟨A₁.liftN 1, Infer.bvar rfl, hdom.weakenHead …⟩`, i.e. a bare
`DefEq A₁ A₂` — and `CtxOk2` has no such move: its kit stops at
`CtxOk2Open`, which opens with the binder's *own* annotation.

This is where `CtxOkR` is genuinely stronger, and it is the only
place.  It is also, on this campaign's newly adopted rule, an
exemption that must survive the other repairs in the same seal, and
it does not obviously do so: the annotated `openCong` is available —
`DefEqClaims2B`'s conclusion is exactly the domains' `interp2`
equality — but only **graded**, under `AnnotOk2` of both domains
(R2).  So substituting `CtxOk2` for `CtxOkR` in the four claims turns
one bare `DefEq` premise into a graded semantic one at five sites,
and the junction's real question is whether the congruence clauses
hold `AnnotOk2` of both domains there.  They are the same two facts
`DefEqClaims2B` already takes as premises at its top level, so the
answer is plausibly yes — but it is a fact about those five clauses,
not about this file, and it is not checked here.

**What the repair does not fix.**  Note that moving all four claims
to `CtxOk2` also *removes* the counterexample above rather than
answering it: `CtxOk2R` disappears, and with it the demand to turn a
`Sat2`-guarded equation into a `Sat`-satisfiable derivation.  The
currency mismatch the counterexample exhibits
(`interp2 ⟪λ(_:Empty). Prop⟫ = ∅` while
`interp ⟪λ(_:Empty). Prop⟫.erase = pt`) is not repaired by it and
stays a live fact about any statement that mixes the two lanes. -/

end Setlec.SetR.Interp2
