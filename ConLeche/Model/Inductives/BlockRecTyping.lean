module

import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Model.Annot.EnvModelM
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Capstone
import ConLeche.Semantics.Tower.BlockRecTower
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.CtxOkKit

public section

/-!
# `ResidueOk` from the rule stage's TYPING certificates

`targetRule` (`Kernel/Inductives/RecCheck.lean`) closes with
two runs at the CONSTRUCTORS' environment `envT`, at the depth
`d = rP + nF + nR` of the opened frame

```
p⃗ (the rP stretch)   f⃗ (the constructor's fields)   ih⃗ (the openers)
```

namely

```lean
let tyB ← opsT.inferType envT depth bodyO
unless ← opsT.isDefEq envT depth tyB concl do throw …
```

with `concl` the recursor's OWN conclusion instantiated at the rule's
prefix, the constructor's index expressions and the major `C_J p⃗ f⃗`.
`ResidueOk` (`Semantics/Tower/BlockRecTower.lean`) is what the three
regimes consume of those two runs:

```lean
def ResidueOk (V) (Rb : AnnotTerm) (ihvals : List V) (ρ' : Nat → V) (B : V) : Prop :=
  WellDenoted V (consList ihvals ρ') Rb ∧ interp V (consList ihvals ρ') Rb ∈ˢ B
```

This file is the hop between the two, in three parts.

* **The certified hop** (`residueOk_of_certs`): `InferClaim` at the
  residue plus `DefEqClaim` between the inferred type and the
  conclusion, both at the frame's context `Δa`, give membership at
  every `Δa`-satisfying valuation, packaged as
  `ResidueOk`; the only difference from `checkConstantVal_reads`
  (`BlockRecRead.lean`) is that the context is not nil.
* **The frame's valuation** (`sat_blockFrame`): the context is
  `ihdoms.reverse ++ (pdoms ++ fdoms).reverse` and `Sat` at it is two
  applications of `sat_of_spineFit` — the graph kit's own
  `SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs)` for the prefix and
  the fields, and one `SpineFit` for the `ih` openers.  The second is
  where the kit pays: the opener's value must lie in the opener's
  DOMAIN (the graph's value at the call target).
* **The frame's context** (`ctxOk_blockFrame`): the frame is opened by
  THREE `openPisAtFvars` calls at the consecutive offsets `0`, `rP`
  and `rP + nF`, so the openers' concatenation is an
  `∃ ty, x = .fvar i ty` list and `ctxOk_of_openers`
  (`Model/IndFrame.lean`) applies unchanged.

The two runs are premises here; they are fields of the stage's rule
record (`TargetRuleRun.hty`/`hdeq`, `Verify/Inductives/RecCheckRun.lean`).  The other premises are the seam to the
readings: `hdoms` (opener `i`'s stored type reads to the context entry
at that slot — the type readings plus the per-binder
`checkBlockDefEqList`), `hokΔ` (the context's own grading), and the `ih`
openers' `SpineFit`, which is the regime's to pay.

**The grade is checked, not assumed**: the stage runs
`opsT.inferType`, which at `μ = .verified` is `inferTypeCore
.verified`, and `Rules.inferTypeCore_bridge` (`Verify/Rules/Bridge.lean`)
sends that to `Infer env .full` — never `.io`, which only
`inferTypeCoreIO` reaches.  So the residue's typing is at the grade an
argument inversion at `.full` needs, with no grade side condition.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The certified hop — `InferClaim` + `DefEqClaim` at a context -/

/-! ## 2. The frame's valuation — `Sat` at `ih⃗ ⊕ f⃗ ⊕ p⃗` -/

/-- **The opened frame's context is satisfied by the frame's own
values.**  The frame is three telescopes deep and `Sat` at it is two
`sat_of_spineFit`s: the graph kit hands over
`SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs)` at the decoding's own spine,
and the `ih` openers' fit is the one thing the kit has to pay for: the
opener's value must lie in the opener's DOMAIN — the graph's value at
the call target (`gGraph_mem_B`).

The context's orientation is `Sat`'s own: innermost first, so the
`ih` block comes first and each telescope is reversed. -/
theorem sat_blockFrame {ρ₀ : Nat → V} {pdoms fdoms ihdoms : List AnnotTerm}
    {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse)
      (consList ihvals (consList (xs ++ fs) ρ₀)) :=
  sat_of_spineFit (by simpa using sat_of_spineFit (Sat_nil V ρ₀) hsp) hih

/-- The frame's context has the frame's own length — the `Δa.length = d`
half of `CtxOk`, read off the two telescopes. -/
theorem sat_blockFrame_length {pdoms fdoms ihdoms : List AnnotTerm}
    {rP nF nR : Nat} (hp : pdoms.length = rP) (hf : fdoms.length = nF)
    (hi : ihdoms.length = nR) :
    (ihdoms.reverse ++ (pdoms ++ fdoms).reverse).length = rP + nF + nR := by
  simp only [List.length_append, List.length_reverse, hp, hf, hi]
  omega

/-! ## 3. The frame's context — three openings at consecutive offsets -/

/-! ## 4. `CtxOk` at the rule frame -/

/-- A term whose free variables are among the openers has bounded leaf
annotations as soon as the OPENERS do — `Expr.LeavesBounded`, which
`InferClaim` asks of every subject, read off the frame once. -/
theorem leavesBounded_of_openers {fvs : List Expr} {e : Expr}
    (hlbF : ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    Expr.LeavesBounded e := fun l hl => hlbF _ (hleaf l hl)

/-! ## 5. `ResidueOk`, assembled at the rule frame -/

/-! ## 5. THE RECURSOR TYPE'S BINDER SHAPE — `BlockRecSplitOne`

`BlockRecSplitOne` (`BlockRecPreRun.lean`) is what the recursor model
reads OFF a fitting spine of `rec_c`'s binder data: the prefix, the
eliminated member's index values and the major, with the parameters'
fit and the member's own index fit.

It is a fact about the STORED type, and this section states it once.
`BlockRecTyShapeOne` says: `rec_c`'s binder data is `rP c` binders, then
the eliminated member's index telescope, then one more; its first `nP`
binders CARRY the block's parameter telescope — an `↔` between FITS,
not a syntactic equality, because the recursor stream stores its own
copy of the parameter binders and only their READINGS are tied; a fit
of the index stretch is a fit of the member's own telescope at the
parameter frame; and the last binder reads as the member's former
applied to the parameters and to the index values.

**Each clause is stated in the direction(s) that have producers.**  The
parameter clause is an `↔` because both of its directions are the
certified hop (`prefixDoms_spineFit` with its two openings swapped)
followed by the members' own parameter agreement, itself an `↔`.  The
INDEX clause is an implication.  Every clause is a reading of the
recursor's own type; nothing here is about the recursion or a rule.

**The index clause is bounded by the prefix's own FIT.**
`targetRecTy` stores the stream's recursor type AS IS and never
compares its index binders with the member's telescope — not
syntactically, and not by an `isDefEq` of its own.  The only tie is
the MAJOR's domain `T_m p⃗ ı⃗` being TYPE-CORRECT (the per-argument
`isDefEq`s inside `checkConstantVal`'s inference), and a `DefEqClaim`
concludes only at the frames satisfying the opened context.  At a
prefix spine that fits nothing, a defeq-but-differently-spelled index
binder (`(fun β => β) α` for `α`, which the checker accepts) reads to
an application off its own domain, so an unbounded clause is false.

* **forward** (a fit of the recursor's index domains is a fit of the
  member's telescope) is `spineFit_of_major_grading` below: the
  MAJOR's domain is `T_m p⃗ ı⃗` on the nose, so its reading is a spine
  against the member's FORMER, and a spine graded against a λ-tower
  fits the tower's own domains.  The recursor's index binders are not
  looked at at all — which is exactly why this direction works.
* **backward** (a fit of the member's telescope is a fit of the
  recursor's index domains) is not stated: its only run source would
  be the per-argument `isDefEq` inside the major domain's inference,
  and reading that off needs an inversion of `inferTypeCore` through a
  Π-tower and an application spine.  (The converse the model does
  use, `blockRecIdxConv_run`, comes from stage (b'')'s own
  certificate, not from this inference.)

The MAJOR clause keeps its all-frames quantification, and that is not
an oversight: it is genuinely syntactic.  `targetRecTy` pins the
major's domain to `.const T_m lvls` applied to the prefix and index
BINDERS, so its reading is `mkAppN (acval T_m ψ) (bvars)` and `interp`
folds it into `app`s at every frame, with the bvars landing on the
spine by position. -/

section TyShape

open ConLeche.Semantics

/-! ### List kit -/

theorem list_eq_singleton {α : Type u} {l : List α} (h : l.length = 1) : ∃ z, l = [z] := by
  match l with
  | [] => exact absurd h (by simp)
  | [z] => exact ⟨z, rfl⟩
  | _ :: _ :: _ => exact absurd h (by simp)

theorem list_drop_last {α : Type u} [Inhabited α] {l : List α} {n : Nat}
    (h : l.length = n + 1) : l = l.take n ++ [l.getD n default] := by
  obtain ⟨z, hz⟩ := list_eq_singleton (l := l.drop n) (by rw [List.length_drop, h]; omega)
  have hgz : l.getD n default = z := by
    rw [List.getD_eq_getElem?_getD,
      show l[n]? = (l.drop n)[0]? from by simp [List.getElem?_drop], hz]
    rfl
  rw [hgz, ← hz, List.take_append_drop]

/-! ### Fit kit -/

/-- **A fit of `rp + nI + 1` binders, decomposed** — the prefix, the
index stretch and the ONE last value, each at its own frame. -/
theorem spineFit_split_three {Ds : List AnnotTerm} {ρ : Nat → V} {ys : List V}
    {rp nI : Nat} (hlen : Ds.length = rp + nI + 1) (hfit : SpineFit ρ Ds ys) :
    ∃ (xs is : List V) (mj : V), ys = xs ++ (is ++ [mj]) ∧
      xs.length = rp ∧ is.length = nI ∧
      SpineFit ρ (Ds.take rp) xs ∧
      SpineFit (consList xs ρ) ((Ds.drop rp).take nI) is ∧
      mj ∈ˢ interp V (consList is (consList xs ρ)) ((Ds.drop rp).getD nI default) := by
  have hdrop : (Ds.drop rp).length = nI + 1 := by rw [List.length_drop, hlen]; omega
  have hD : Ds = Ds.take rp
      ++ ((Ds.drop rp).take nI ++ [(Ds.drop rp).getD nI default]) := by
    rw [← list_drop_last hdrop, List.take_append_drop]
  rw [hD] at hfit
  obtain ⟨xs, rest, hyeq, h1, h2⟩ := spineFit_append_inv hfit
  obtain ⟨is, mjs, hreq, h3, h4⟩ := spineFit_append_inv h2
  have hxl : xs.length = rp := by
    rw [h1.length_eq, List.length_take]; omega
  have hisl : is.length = nI := by
    rw [h3.length_eq, List.length_take]; omega
  obtain ⟨mj, rfl⟩ := list_eq_singleton (l := mjs) (by rw [h4.length_eq, List.length_singleton])
  exact ⟨xs, is, mj, by rw [hyeq, hreq], hxl, hisl, h1, h3, h4.1⟩

/-! ### The shape -/

/-! ### The index clause's PAYABLE half

The shape's index clause is an implication, and this is the direction
it is stated in — the only one with a producer.  It is the whole
semantic content of the clause: a spine graded against the member's
FORMER — which is a λ-tower over the member's parameter and index
telescope — fits that telescope, because every application node's
product carries the abstraction's own domain
(`spineFit_of_wellDenoted_lams`, `lamR_mem_piR_dom`).  The major's
domain is `T_m p⃗ ı⃗` on the nose (`targetRecTy` pins it
syntactically), so its READING is that spine and the grading is the
recursor type's own (`piTeleAV_graded` at the major's position).

Nothing here looks at the recursor's index BINDERS: their domains are
the stream's own copies and the checker never compares them with the
member's telescope.  What carries the fit is the major, and that is
why the clause is bounded by the prefix's fit — off a fitting prefix
the grading is not available either. -/

end TyShape

end ConLeche.Model
