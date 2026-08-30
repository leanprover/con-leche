import Setlec.SetR.Interp2.EnvS2U
import Setlec.SetR.Annot.SortCoh.Discharge

/-!
# The install keys, over `interp2` — the statements

The last statement work before the fourteen's swap. Written against
`EnvS2U` (seal 36) and carrying the Θ lane's env-extension fact as a
named hypothesis until that lane confirms its strengthening.

## The enabler comes first, because everything waits on it

The keys survey found that the keys are **not** the bottleneck: two
obligations bite before any of them, and both are about `denote2`
rather than about semantics. Seal 34's R2 ruling removed one (the
uniqueness form, frozen at seal 36). This file states the other.

`denote2` runs `inferTypeCore`/`whnf` **in `env`** (through
`sortOfE`/`lamSortE`), so transporting any annotated fact across an
install needs run stability. v1 needs no analogue — `denote` touches
`env` only through `find?` — which is why the gap was invisible from
that side.

Seal 35's fit check: the Θ lane's `EnvExtendStable`
(`Annot/SortCoh/Discharge.lean`) covers three of `denote2`'s four
needs directly. The fourth fails only because `sortOfE` **chains** —
`inferTypeCore` on `e` yields `t`, then `whnf` runs on `t` — and (E)'s
`inferTypeCore` conjunct does not expose `ConstsBound env₀ t`. That
fact exists inside (E)'s discharge (its docstring records the motive
*"strengthened by output-boundness"*); the cross-lane request is to
expose it.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable (V : Type w) [SetTheory V]

/-- **The Θ lane's fact, with the conjunct seal 35 asked it to
expose.**  Carried as a named hypothesis, *frozen on Θ*: when that
lane strengthens `EnvExtendStable`, this becomes its corollary and is
deleted rather than proved here.

Stating it separately rather than assuming the amendment lets the
keys be written now **and** makes the dependency visible to anyone
reading them — the `CertifiedConfigTT` pattern, at a cross-lane
seam.

**Θ has since landed the amendment** (its branch, pending that lane's
own merge): `EnvExtendStable`'s `inferTypeCore` conjunct now also
concludes `ConstsBound env₀` of the output type, a pure strengthening
with no consumers affected. **So this definition is scheduled for
deletion, not for proof** — when the amendment reaches master, every
use below is replaced by the conjunct and this `def` goes. It is kept
only so the keys compile in the interval.

*That is the value of naming a cross-lane dependency instead of
assuming it: the hypothesis has a landing date rather than a
believer.* -/
def InferOutputBound (μ : CheckMode) (env₀ : Env) : Prop :=
  ∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    Setlec.inferTypeCore μ env₀ f d e = .ok x → ConstsBound env₀ x

/-- **R1, stated: `denote2` is stable under environment extension.**
The composition seal 35 priced — (E) over `denote2`'s finitely many
internal calls, with `FindPreserved` for the `.const` clause and the
literal-support guards, and `InferOutputBound` for `sortOfE`'s chain.

An **equation**, not an implication, for the reason
`denote2_acval_congr` is one: an install must not be able to assume
silently that an annotation exists on one side and not the other. -/
def Denote2EnvExtend (μ : CheckMode) (env₀ env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (e : Expr), ConstsBound env₀ e →
    denote2 μ acval env₀ φ F d e = denote2 μ acval env φ F d e

/-! ## The keys

Each is its v1 counterpart with the **conclusion** moved to the
annotated currency; every premise of every key is already V-free
(the survey checked this at each definition site), so the hypothesis
sides are reused verbatim and are not restated here.

Stated in dependency order, cheapest first — which the survey
established is *not* the same as the order they are usually listed
in. -/

/-- **`ReducePinS`, over `interp2`** — the survey's cheapest key: its
entire V content is one `DefEq.sound` application at a one-entry
context, and `natOpGuard`-style presence conjuncts are syntactic.

**No `μ`**, and as with `DivModV2` the absence is informative: the
obligation is value-level throughout, so it cannot reintroduce the
`μ.verified` premise seal 10 withdrew. -/
def ReducePin2 (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat)
    (c : Name) : Prop :=
  (env.find? (Setlec.reduceElemName c)).isSome = true ∧
    ∀ (ρ : Nat → V) (x : V),
      x ∈ˢ interp2 V ρ (acval (Setlec.reduceElemName c) φ) →
      SetTheory.app (interp2 V ρ (acval c φ)) x = x

/-- **`MemberKeyS`/`StdAxiomKeyS`'s shared block, over `interp2`** —
the survey found them to be the same three-part per-`ψ` obligation:
the type denotes, the leaf inhabits it, and the type is truthful.

**The fuel is existential, and the trap-check is why.** Every standard
axiom's type and every block member's type is a `∀`, and
`denote2_one_forallE` is `none` at fuel `1` — so a caller-chosen `F`
would make this **false**, exactly as it made `EnvS2.acval_defn`'s
original form false (STOP 2). The `∃ F' ≥ F` shape is that repair,
reused. -/
def MemberBlock2 (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (ψ : Name → Nat)
    (cv : ConstantVal) : Prop :=
  ∀ F : Nat, ∃ F' ta, F ≤ F' ∧
    denote2 μ acval env ψ F' 0 cv.type = some ta ∧
    ∀ ρ : Nat → V,
      interp2 V ρ (acval cv.name ψ) ∈ˢ interp2 V ρ ta ∧
      AnnotOk2 V ρ ta

/-- **`DeclBasisS`/`DeclIndS`, over `interp2`.**  Statable at all only
because R6 was withdrawn (seal 36): `Nonempty` eliminates into `Prop`,
so an `EnvS2U` builder gets the base witness and constructs the extra
fields against it. -/
def DeclStep2 (env₂ : Env) : Prop :=
  Nonempty (EnvS2U V env₂)

/-! ## The three sweeps on these statements

**1. Smallest fuel.** The only conclusion asserting a `denote2`
success is `MemberBlock2`'s, and it carries the existential slack for
the reason recorded at its docstring — a `∀`-typed subject cannot
annotate at fuel `1`. `ReducePin2` and `DeclStep2` assert no `denote2`
success at all. `Denote2EnvExtend` is an **equation between two runs**,
so it asserts success on neither side.

**2. Vacuity.** `ReducePin2` and `MemberBlock2` inherit their
premises from the v1 keys, which are discharged today, so their
premise sets are known inhabited. `DeclStep2` is `Nonempty` of a
structure whose only exhibited inhabitant is `EnvS2U.empty` — **that
is a real vacuity exposure and it is the batch's first job to close
it**, by building an `EnvS2U` at a non-empty environment.
`Denote2EnvExtend`'s premise `ConstsBound env₀ e` is inhabited at any
closed leaf.

**3. Tombstones.** A file added, none edited.

*The one honest gap: `DeclStep2` at a non-empty environment is not
known inhabited, and every earlier vacuity failure in this campaign
had exactly that shape — `EnvS2.empty` masking a false field for four
seals. It is recorded here rather than discovered later.*
-/

end Setlec.SetR.Interp2
