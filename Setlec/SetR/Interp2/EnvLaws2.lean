import Setlec.SetR.Interp2.Claims2C

/-!
# The three missing `interp2` environment laws — statements, queued

Seal 12's finding, stated. Three of the eight capstone residues —
`ReduceNatStep2`, `IotaStep2B`, `ProjStep2B` — are blocked not on
proofs but on **environment laws that do not exist over `interp2`**.
Each has a v1 counterpart stated over `denote`/`interp`/`cval`, and
the erasure link cannot carry it: `interp2` is the two-regime
annotation-driven interpretation, **not** `interp ∘ erase`. v1 escapes
by concluding a `Red` whose soundness consumes its law elsewhere; the
interp2 claims conclude the equality directly, so the law must be
present in the environment.

## Status of this file, stated plainly

These are **first-draft statements, not settled ones**, and they are
deliberately *not* wired into `EnvS2` yet. This campaign's own
evidence is that a statement is validated by the consumer that
discharges it — three generations of `Claims2` were refuted, every one
by a consumer, never by inspection. So each law below is derived from
what its residue visibly needs, with the v1 shape as the guide, and
each is expected to move before it is adopted.

The adoption path is the one `AcvalParams2` took: named as a `Prop`
here, diagnosed by its consumer, then promoted to an `EnvS2` field
when the install tier can establish it (`EnvS2.acval_params`). By T5
the supplier is named in each docstring and is the install tier in
every case.

## The trap-checks, applied in advance

Each law asserts a `denote2` **success** as a conclusion, so the
smallest-fuel rule applies: *false unless the subject carries no
`.forallE`/`.lam` node.* A recursor's RHS and a `Nat` operation's
defining equations both may. So every one is stated with the
existential fuel slack (`∃ F', F ≤ F' ∧ …`) that seals 7 and 12
established as the correct shape — **not** at a caller-chosen fuel.
Seal 11's caveat stands: this check passing is not a clean bill of
health.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantVal ConstantInfo
  RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-- **Law 1 — the structural-`Nat` operations, over `interp2`.**
Consumer: `ReduceNatStep2`, whose *fuel* half is already settled
(`natOpResult_leaf`: literal acceleration is closed on leaves, so it
is the one genuinely fuel-preserving exit) and whose **semantic**
conjunct has no supplier at all.

v1 shape: `NatOpsV` (`Sound/Motives.lean:218`), over `denote … 2` at
the two-slot context and `interp` at `cons`-extended valuations.

Supplier: the install tier, at the `hheadNat` obligation of
`EnvS.cons` (`Install/Cons.lean`), which already establishes the v1
law for a structural-`Nat` operation head. -/
def NatOpsV2 (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ c ∈ natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    natOpGuard env c = true ∧
    ∀ eq ∈ natOpEquations 0 c, ∀ F : Nat, ∃ F' L R, F ≤ F' ∧
      denote2 μ acval env φ F' 2 eq.1 = some L ∧
      denote2 μ acval env φ F' 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp2 V ρ (acval natName (Level.substFn φ [] [])) →
        y ∈ˢ interp2 V ρ (acval natName (Level.substFn φ [] [])) →
        interp2 V (cons y (cons x ρ)) L
          = interp2 V (cons y (cons x ρ)) R

/-- **Law 2 — the fired modeled-iota rule, over `interp2`.**

**INSUFFICIENT AS DRAFTED — do not build on this (seal 22).** The map
found that this transposes about six lines of `RecRuleLawV`'s
fifty-five and **omits the fired equality entirely**. Its consumer
`IotaStep2C`/`IotaStep2D` concludes an `interp2` equality, and nothing
in the tier other than that equality can supply it. So this law as
written does not discharge the residue it was drafted for.

Two further corrections. The third conjunct is **not**
`RecRuleLawV`'s truthfulness transport, which is conditional and lands
on the *applied reduct*; it is the transpose of the install bottoms'
own *input* `_hrhsKey`, an unconditional fact about the bare `R`. And
the claim below that "only the interpretation moves" is false for two
conjuncts: `TeleFitV` becomes `TeleFit2`, a **currency change**
(`V`-valued and kinded, not `VExpr`-indexed), and `IotaIndexPinV` has
**no counterpart at all**.

Kept, unfrozen and unconsumed, as the record of what a
consumer-derived draft misses.
Consumer: `IotaStep2B`.

This is the slot the campaign has been calling `RecRulesV2` since the
tier-C inventory, and has deliberately kept **absent** from `EnvS2`
rather than guessed consumer-side — T5: *a fired-law premise must be
stated by its supplier.* This file is that statement's first draft,
not its adoption.

v1 shape: `RecRulesV` / `RecRuleLawV` (`Sound/Motives.lean:145`,
`:207`), whose `rP ≤ mI` conjunct and level-instantiated RHS
denotation carry over unchanged; only the interpretation moves.

Note the RHS is taken at `instantiateLevelParams`, so this law meets
`Denote2InstLevels` — seal 12's open metatheorem — head on. That is
not an accident of drafting: the *same* crossing blocks the delta
exit, and settling it once serves both.

Supplier: the install tier, at `EnvS.cons`'s `hheadRec` obligation. -/
def RecRulesV2 (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ us : List Level, us.length = cv.levelParams.length →
        ∀ F : Nat, ∃ F' R, F ≤ F' ∧
          denote2 μ acval env φ F' 0
              ((RecRule.rhs rl).instantiateLevelParams
                cv.levelParams us)
            = some R ∧
          ∀ ρ : Nat → V, AnnotOk2 V ρ R

/-- **Law 3 — the native pair projection, over `interp2`.**
Consumer: `ProjStep2B`.

Derived from the consumer rather than transposed, because v1's
`ProjOkT` (`Verify/EnvPreds.lean:106`) is **syntactic** — it says the
entry is a pinned pair entry with its block stored, and says nothing
semantic. The semantic content `ProjStep2B` needs is that `interp2`'s
own `.proj` clause (`sfst`/`ssnd`) agrees with the field the checker
selects when the scrutinee has whnf'd to a constructor application.

That is why this one is the least settled of the three: it is the only
law with no v1 sentence to transpose, and the campaign has a standing
finding (`proj-unification-limits`) that modeled types can never get
first-class `.proj`, so its scope is the **native** pair alone.

Supplier: the install tier, at `EnvS.cons`'s `hheadProj` /
`hheadProjPair` obligations. -/
def ProjPairV2 (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (i : Nat) (d F : Nat) (fst snd : Expr) (fa sa : AVExpr),
    i < 2 →
    denote2 μ acval env φ F d fst = some fa →
    denote2 μ acval env φ F d snd = some sa →
    ∀ (pa : AVExpr),
      (∀ ρ : Nat → V,
        interp2 V ρ pa = spair (interp2 V ρ fa) (interp2 V ρ sa)) →
      ∀ ρ : Nat → V,
        interp2 V ρ (.proj i pa)
          = if i = 0 then interp2 V ρ fa else interp2 V ρ sa

/-- **PARKED — do not pursue (seal 33).**  Kept as the record of a
supplier that named the wrong side of its consumer's runs.

Two independent reasons, either sufficient:

* **It names the run's *subject*.** The conclusion is about `e`; `t` is
  bound and does not occur in it. Every annotation `.app` consumes is a
  run's *output*, and the subject's annotation is already a premise of
  `InferClaims2E` — so this supplies nothing at the clause it was
  priced against. `Denote2TotalR` (the `e ↦ t` repair) is the part that
  works and is kept; it discharges the inference existence factor via
  `inferExists2E_of_totalR`.
* **It would collide with seal 10.** Proving it needs `lamSortE`
  defined at every λ node, which the checker computes only under
  `mode.verified` — the premise seal 10 deliberately *withdrew* from
  the claims to recover the `.noModel` lane. A supplier that
  reintroduces it undoes a landed result.

Doubtful provability plus a collision with a landed seal is a
do-not-chase. The remaining gap it was meant to fill — the `∀`'s
annotation at `.app` — has **nothing to condition on** (no later run
has that `∀` as subject) and can come only from a
reduction-preservation fact, which lives inside generation five's
induction.

*Original docstring follows.*

**The existence supplier generation six needs**, and the outcome of
pricing its `.app` clause.

Generation six's specification said existence would be *"localized to
the declaration level, where checked declarations genuinely supply the
runs"*. Pricing `.app` first, as instructed, shows **that is not
enough**: `infer_app_claim2D` consumes two annotations — the head's
inferred type `tfa` and the `whnf`'d `∀`'s `pa` — and **both are
intermediate terms computed during checking, neither a declaration**.
Under generation six both become premises, so `.app` must supply them,
and a declaration-scoped supply cannot.

**The repair keeps the discipline rather than abandoning it.** Make
the supply *run-conditioned* instead of declaration-scoped: an
annotation exists for any term the checker **successfully ran on**.
That is itself a dual-success statement — it conditions on a given
run and predicts nothing — so it is legitimate exactly where a budget
hypothesis was not.

Why it should be provable: a successful `inferTypeCore` on `e` visits
every binder node of `e`, so each `sortOfE`/`lamSortE` the annotation
needs is a run that already succeeded at *some* fuel; `knotFuelMono`
lifts each to a common maximum over the finitely many nodes. That is
the shape of the proof, not a proof.

Named, not frozen: the fuel is existential (`denote2` on a binder
cannot answer at fuel `1`), and the smallest-fuel rule is therefore
satisfied by construction rather than by luck. -/
def Denote2Total (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (e t : Expr),
    Setlec.inferTypeCore μ env F d e = .ok t →
    ∃ F' ea, denote2 μ m.acval env φ F' d e = some ea

/-! ## `IotaIndexPin2` — the third option, priced

Seal 22 left the choice between a full transpose and a minimal law
hanging on one bounded question: *can `IotaIndexPin2` be stated at
all, given that `TeleFit2`'s residual is a bare `V`?*

**Answered, and seal 22's framing was wrong in an instructive way.**

*The squashing countermodel does apply — to any `V`-side
formulation.* Task #107's witness (`T._model := fun _ => PUnit'`,
field `{v // v = p}`, `proj_0 := fun p _ => ⟨p, rfl⟩` — iota and eta
both provable, every install check passing, contradictory forced
values) says a bare `V` does not determine a destructor. Distinct
constructor spines interpret to equal values, so **no `V`-side fact
recovers a spine.** A pin stated about `TeleFit2`'s residual is
therefore not merely hard, it is not statable.

*But the pin was never a `V`-side fact in v1 either.*
`IotaIndexPinV` decomposes `restC` **syntactically** — `restC` is a
`VExpr`, because `TeleFitV` is `VExpr`-indexed — and only then
compares `interp` of the pieces. So the faithful transpose is an
**`AVExpr` fact**, not a workaround for the squash but the same
construction one currency over. `AVExpr.mkAppN` exists
(`Annot/Syntax.lean:162`); `interp2_mkAppN` and `denote2_mkAppN_swap`
exist.

*The tension worth recording:* `TeleFit2`'s value-level design is a
genuine improvement over v1 — `AnnotOk2_redex_fits` derives fits from
the subject's `AnnotOk2` with **no runtime walk** — and it is
*precisely* that choice which removes the syntactic residual the pin
needs. The resolution is that the two serve different jobs: fits
guard **memberships**, where value-level is right; the pin guards
**index agreement**, where syntax-level is right. They should not
share a residual.

Stated, not frozen: the residual's source is still open (an
`AVExpr`-indexed fit beside `TeleFit2`, or the consumer's own
decomposition through `denote2_mkAppN_swap`), and the three
grep-negative gaps are unbuilt. -/
def IotaIndexPin2 (ρ : Nat → V) (restC : AVExpr) (cnP mI rP : Nat)
    (xs : List AVExpr) : Prop :=
  ∃ (H : AVExpr) (cargs : List AVExpr),
    restC = AVExpr.mkAppN H cargs ∧
    (mI = rP ∨ cargs.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp2 V ρ (cargs.getD (cnP + i) default)
        = interp2 V ρ (xs.getD (rP + i) default)

/-! ## The queue

These three join the five install keys (`DivModPinS`, `ReducePinS`,
`StdAxiomKeyS`, `DeclBasisS`, `DeclIndS`) and `MemberKeyS` as the
install-tier campaign's work. The ordering that the evidence suggests:

1. **`Denote2InstLevels` first**, because `RecRulesV2` and the delta
   exit both meet it, and because seal 12 recorded a live doubt about
   whether it is true at all — `piResultIsProp`/`piResultNeverZero`
   make a run level-sensitive. If it is false, `RecRulesV2` above is
   the wrong statement and better to know before it is adopted.
2. **`NatOpsV2`**, which has the most complete v1 counterpart and a
   supplier obligation that already exists.
3. **`ProjPairV2`** last, being the least settled.
-/

end Setlec.SetR.Interp2
