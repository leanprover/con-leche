import Setlec.SetR.Interp2.Step2.Routed
import Setlec.SetR.Interp2.Step2.Whnf
import Setlec.SetR.Interp2.Step2.DefEq
import Setlec.SetR.Interp2.Claims2B
import Setlec.SetR.Interp2.Claims2C
import Setlec.SetR.Interp2.Claims2D
import Setlec.SetR.Bridge.Decl

/-!
# `DefEqStep2`, discharged against the run

The definitional-equality quarter.  `isDefEqCore` at `fuel + 1` is
`defeqBody` at `pureFns … fuel`, which is `defeqLoop` on its **own**
private budget (`defeqLoopFuel`, `@[irreducible]`), which iterates
`defeqStep` with the continuation abstracted.  That is the checker's
own factoring and this file inherits it verbatim from the v1 lane
(`Bridge/DefEq.lean`): the body is proved once with the continuation's
contract as a hypothesis, and the loop is one induction on the
*budget* — never on the knot's `fuel`, which the loop does not
decrement.

What changes against v1 is only the *product*: v1 builds a `DefEq`
derivation, this lane concludes an `interp2` equality, and the
semantic content of every rule is already proved in `Step2/DefEq.lean`.
The case analysis is the same — and it transferred *verbatim*, which
is the first finding: the seven-block dispatch and the seventeen-case
stuck block are the same proof script with the product swapped.

## What is closed

The loop's budget recursion; the syntactic fast path; both `whnfCore`
rewrites; all four lazy-delta decisions with the same-head
short-circuit's plumbing; and ten of the stuck block's seventeen
cases — `sort`/`sort`, `lit`/`lit`, both `Nat.zero` orders, both
`Nat.succ` orders, `fvar`/`fvar`, `const`/`const`, and the `∀`, `λ`
and `proj` congruences.

## Three findings

1. **Relational facts are free here.**  `checkBridge` is a theorem at
   every `EnvR`, `EnvS2` contains an `EnvS`, and `EnvS.toEnvR`
   converts — so `CtxOkR.openCong`'s `DefEq` premise, which the
   annotated currency cannot produce itself, costs one line
   (`defeqR_at`).  `Dispatch.lean`'s STOP note is one-directional:
   `DefEq → interp2` does not exist, `interp2`-lane consumers of
   `DefEq` are fully served.
2. **The Θ lane does not reach the binder congruences.**
   `SortOfAgreeR` carries `PairedLeaves`, and `defeqStep` opens a
   binder congruence with *each side's own* annotation — so both
   opened bodies carry an `fvar` leaf at index `d` with different
   types and `PairedLeaves` fails exactly there.  The codomain-numeral
   agreement the congruences need is therefore its own obligation
   (`BinderSortAgree2`), not a `SortOfAgreeR` instance.
3. **`Claims2`'s fuel index costs one obligation per quarter.**  The
   claim at `fuel + 1` reads its subjects through `denote2 … (fuel+1)`
   while every sub-claim reads them through `denote2 … fuel`, so the
   step needs `denote2` to survive one step *down* the ladder; the
   upward direction is a theorem (`knotFuelMono`), the downward one is
   refutable at small fuel.  See `Denote2FuelDownM`.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode CheckM Env Expr Name Level isDefEqCore whnfCore
  defeqStep defeqLoop defeqBody defeqLoopFuel pureFns)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `denote2`, clause by clause

The canonical annotation pass has no unfolding lemmas of its own yet
(`Annot/Canon.lean` states only `denote2_erase`), and every case of the
stuck block reads one.  They are all `rw [denote2]`. -/

theorem denote2_sort (acval : Name → (Name → Nat) → AVExpr)
    (fuel d : Nat) (u : Level) :
    denote2 μ acval env φ fuel d (.sort u)
      = some (.sort (u.eval φ)) := by
  rw [denote2]

theorem denote2_fvar (acval : Name → (Name → Nat) → AVExpr)
    (fuel d idx : Nat) (n : Name) (ty : Expr) :
    denote2 μ acval env φ fuel d (.fvar idx n ty)
      = some (.bvar (d - 1 - idx)) := by
  rw [denote2]

theorem denote2_const {acval : Name → (Name → Nat) → AVExpr}
    {fuel d : Nat} {n : Name} {us : List Level}
    {ci : Setlec.ConstantInfo} (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    denote2 μ acval env φ fuel d (.const n us)
      = some (acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) := by
  rw [denote2, hf]
  simp [hlen]

theorem denote2_app (acval : Name → (Name → Nat) → AVExpr)
    (fuel d : Nat) (f a : Expr) :
    denote2 μ acval env φ fuel d (.app f a)
      = (do
        let fa ← denote2 μ acval env φ fuel d f
        let aa ← denote2 μ acval env φ fuel d a
        some (.app fa aa)) := by
  rw [denote2]

theorem denote2_proj (acval : Name → (Name → Nat) → AVExpr)
    (fuel d : Nat) (s : Name) (i : Nat) (e : Expr) :
    denote2 μ acval env φ fuel d (.proj s i e)
      = (do
        let ea ← denote2 μ acval env φ fuel d e
        if i < 2 then some (.proj i ea) else none) := by
  rw [denote2]

theorem denote2_forallE (acval : Name → (Name → Nat) → AVExpr)
    (fuel d : Nat) (n : Name) (ty body : Expr)
    (mb : Setlec.BinderMeta) :
    denote2 μ acval env φ fuel d (.forallE n ty body mb)
      = (do
        let ta ← denote2 μ acval env φ fuel d ty
        let ba ← denote2 μ acval env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty))
        let u ← sortOfE μ env φ fuel d ty
        let v ← sortOfE μ env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty))
        some (.pi u v ta ba)) := by
  rw [denote2]

theorem denote2_lam (acval : Name → (Name → Nat) → AVExpr)
    (fuel d : Nat) (n : Name) (ty body : Expr)
    (mb : Setlec.BinderMeta) :
    denote2 μ acval env φ fuel d (.lam n ty body mb)
      = (do
        let ta ← denote2 μ acval env φ fuel d ty
        let ba ← denote2 μ acval env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty))
        let v ← lamSortE μ env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty))
        some (.lam v ta ba)) := by
  rw [denote2]

/- **`denote2_bvar` used to be stated here** and is not any more — the
one deletion in this file, recorded rather than silent.  Importing
`Claims2B` (seal 7) puts this file and `Step2/Whnf.lean` in one scope
for the first time, and that file states the *identical* lemma under
the *identical* name (`Step2/Whnf.lean:319`); Lean rejects the
duplicate, and rejects `private` shadowing of it too.  Nothing
referenced this copy — it was unused even here — and the content
survives verbatim in the other quarter, so no statement is lost.  The
duplication is an integration finding: two quarters, written in
parallel, named the same `denote2` clause lemma. -/

theorem denote2_natLit {acval : Name → (Name → Nat) → AVExpr}
    {fuel d n : Nat} (hg : Setlec.natLitSupported env = true) :
    denote2 μ acval env φ fuel d (.lit (.natVal n))
      = some (natLitT2
          (acval Setlec.natZeroName (Level.substFn φ [] []))
          (acval Setlec.natSuccName (Level.substFn φ [] [])) n) := by
  rw [denote2, if_pos hg]

/-! ## `denote2`, inverted

The stuck block reads its subjects' annotations apart; the `do`-block
clauses above are stated once in the shape the cases consume. -/

theorem denote2_app_inv {acval : Name → (Name → Nat) → AVExpr}
    {fuel d : Nat} {f a : Expr} {ea : AVExpr}
    (h : denote2 μ acval env φ fuel d (.app f a) = some ea) :
    ∃ fa aa, denote2 μ acval env φ fuel d f = some fa ∧
      denote2 μ acval env φ fuel d a = some aa ∧ ea = .app fa aa := by
  rw [denote2] at h
  cases hf : denote2 μ acval env φ fuel d f with
  | none => rw [hf] at h; exact nomatch h
  | some fa =>
    cases ha : denote2 μ acval env φ fuel d a with
    | none => rw [hf, ha] at h; exact nomatch h
    | some aa =>
      rw [hf, ha] at h
      exact ⟨fa, aa, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote2_proj_inv {acval : Name → (Name → Nat) → AVExpr}
    {fuel d : Nat} {s : Name} {i : Nat} {e : Expr} {ea : AVExpr}
    (h : denote2 μ acval env φ fuel d (.proj s i e) = some ea) :
    ∃ ia, denote2 μ acval env φ fuel d e = some ia ∧ i < 2 ∧
      ea = .proj i ia := by
  rw [denote2] at h
  cases he : denote2 μ acval env φ fuel d e with
  | none => rw [he] at h; exact nomatch h
  | some ia =>
    rw [he] at h
    replace h : (if i < 2 then some (AVExpr.proj i ia) else none)
        = some ea := h
    split at h
    · next hlt => exact ⟨ia, rfl, hlt, (Option.some.inj h).symm⟩
    · exact nomatch h

theorem denote2_forallE_inv {acval : Name → (Name → Nat) → AVExpr}
    {fuel d : Nat} {n : Name} {ty bd : Expr} {mb : Setlec.BinderMeta}
    {ea : AVExpr}
    (h : denote2 μ acval env φ fuel d (.forallE n ty bd mb) = some ea) :
    ∃ ta ba u v, denote2 μ acval env φ fuel d ty = some ta ∧
      denote2 μ acval env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) = some ba ∧
      sortOfE μ env φ fuel d ty = some u ∧
      sortOfE μ env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) = some v ∧
      ea = .pi u v ta ba := by
  rw [denote2] at h
  cases ht : denote2 μ acval env φ fuel d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denote2 μ acval env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      cases hu : sortOfE μ env φ fuel d ty with
      | none => rw [ht, hb, hu] at h; exact nomatch h
      | some u =>
        cases hv : sortOfE μ env φ fuel (d + 1)
            (bd.instantiate1 (.fvar d n ty)) with
        | none => rw [ht, hb, hu, hv] at h; exact nomatch h
        | some v =>
          rw [ht, hb, hu, hv] at h
          exact ⟨ta, ba, u, v, rfl, rfl, rfl, rfl,
            (Option.some.inj h).symm⟩

theorem denote2_lam_inv {acval : Name → (Name → Nat) → AVExpr}
    {fuel d : Nat} {n : Name} {ty bd : Expr} {mb : Setlec.BinderMeta}
    {ea : AVExpr}
    (h : denote2 μ acval env φ fuel d (.lam n ty bd mb) = some ea) :
    ∃ ta ba v, denote2 μ acval env φ fuel d ty = some ta ∧
      denote2 μ acval env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) = some ba ∧
      lamSortE μ env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) = some v ∧
      ea = .lam v ta ba := by
  rw [denote2] at h
  cases ht : denote2 μ acval env φ fuel d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denote2 μ acval env φ fuel (d + 1)
        (bd.instantiate1 (.fvar d n ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      cases hv : lamSortE μ env φ fuel (d + 1)
          (bd.instantiate1 (.fvar d n ty)) with
      | none => rw [ht, hb, hv] at h; exact nomatch h
      | some v =>
        rw [ht, hb, hv] at h
        exact ⟨ta, ba, v, rfl, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote2_natLit_inv {acval : Name → (Name → Nat) → AVExpr}
    {fuel d n : Nat} {ea : AVExpr}
    (h : denote2 μ acval env φ fuel d (.lit (.natVal n)) = some ea) :
    Setlec.natLitSupported env = true ∧
      ea = natLitT2
        (acval Setlec.natZeroName (Level.substFn φ [] []))
        (acval Setlec.natSuccName (Level.substFn φ [] [])) n := by
  rw [denote2] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

/-- `Nat.zero`, canonically annotated: `natLitT2 … 0` *is* the leaf. -/
theorem denote2_natZeroConst {acval : Name → (Name → Nat) → AVExpr}
    (hg : Setlec.natLitSupported env = true) {fuel d : Nat} :
    denote2 μ acval env φ fuel d (.const Setlec.natZeroName [])
      = some (acval Setlec.natZeroName (Level.substFn φ [] [])) := by
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? Setlec.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [Setlec.natZeroOk, Bool.and_eq_true] at h2
        simpa [Setlec.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [Setlec.natZeroOk] at h2
    rw [denote2_const hf (by simp [hlp]), hlp]

/-- `Nat.succ`, canonically annotated. -/
theorem denote2_natSuccConst {acval : Name → (Name → Nat) → AVExpr}
    (hg : Setlec.natLitSupported env = true) {fuel d : Nat} :
    denote2 μ acval env φ fuel d (.const Setlec.natSuccName [])
      = some (acval Setlec.natSuccName (Level.substFn φ [] [])) := by
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? Setlec.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [Setlec.natSuccOk, Bool.and_eq_true] at h3
        simpa [Setlec.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [Setlec.natSuccOk] at h3
    rw [denote2_const hf (by simp [hlp]), hlp]

/-! ## Residue 1 — the fuel index

**A finding, not a wish.**  `Claims2` ties `denote2`'s fuel to the
*checker's* fuel: the claim at `fuel + 1` reads its subjects through
`denote2 … (fuel + 1)`, while every sub-claim the mutual step consumes
reads them through `denote2 … fuel`.  So the step needs the canonical
annotation to survive one step *down* the fuel ladder.

Its upward twin is a theorem here (`knotFuelMono` gives
`inferTypeCore`/`whnf` monotonicity, hence `sortOfE`/`lamSortE`, hence
`denote2`), so the residue is equivalent to **definedness at the
sub-fuel** and nothing more — an annotation that exists at both fuels
is the same annotation.  As a naked statement it is refutable at small
fuel (`denote2 … 0 d (.forallE …)` is `none` because `sortOfE` at fuel
`0` throws), which is exactly why it is routed rather than proved: the
repair is a `Claims2` re-index (read every subject at the *outer*
fuel), and that is a junction decision about a sealed statement, not a
consumer's.

It is consumed **once**, at the top of `defeq_claims2`; everything
inside the loop runs at `fuel` throughout. -/
/-- **Note (fold-in).**  `Step2/Whnf.lean` states the same obligation
independently, over a bare `acval` rather than an `EnvS2`, and
*refutes* it (`denote2_fuelDown_false`).  The two were written by
separate discharges that never saw each other and arrived at the same
statement — which is the strongest evidence available that the fuel
index is a real defect in `Claims2` and not an artefact of one
quarter's proof strategy.  Kept under a distinct name only to avoid the
clash; the repair (re-indexing `Claims2`) retires both.

**Retired at seal 6 — do not attempt to discharge it.**  It is refuted
(`denote2_fuelDown_false`) and it is also *unnecessary*: R1 gave the
annotation its own fuel binder, and `defeq_claims2A` below hands the
subjects' annotations to the loop at the very fuel they arrive at.  The
amended chain (`defeq_claims2A` → `defeqStep_claim2A` →
`defeqStuck_claim2A` → `defEqStep2BP_of`) never mentions it.  This
declaration and its two consumers, `defeq_claims2` and
`defeqStep2_of`, stay as the tombstone. -/
def Denote2FuelDownM (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ (d : Nat) (e : Expr) {ea : AVExpr},
    denote2 μ m.acval env φ (fuel + 1) d e = some ea →
    denote2 μ m.acval env φ fuel d e = some ea

/-! ## The loop and its continuation -/

/-- The continuation's contract — `DefEqClaims2`'s own shape at the
loop's remaining budget.  The depth is fixed, not quantified:
`defeqLoop` hands `defeqStep` a continuation already applied to the
ambient depth.  The clauses that *do* go deeper (the `∀`/`λ`
congruences) recurse through the claim at `fuel`, not through the
continuation. -/
def DefEqCont2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AVExpr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **One iteration of the lazy-delta loop**, with the continuation
abstracted exactly as the checker abstracts it. -/
def DefEqStepAt2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool},
    DefEqCont2 μ m φ fuel d k →
    ∀ {a b : Expr} {Δa : List AVExpr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
      ∀ {aa ba : AVExpr},
        denote2 μ m.acval env φ fuel d a = some aa →
        denote2 μ m.acval env φ fuel d b = some ba →
        ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- The lazy-delta loop satisfies the contract at every budget.  The
recursion is on the **private budget**, which is the only thing the
loop decrements. -/
theorem defeqLoop_cont2 {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2 μ m φ fuel) :
    ∀ (budget d : Nat),
      DefEqCont2 μ m φ fuel d
        (defeqLoop μ (pureFns μ env fuel) env d budget) := by
  intro budget
  induction budget with
  | zero =>
    intro d a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d a b Δa h
    rw [defeqLoop] at h
    exact hstep (ih d) h

/-- **`DefEqClaims2` at `fuel + 1`**, modulo the step and the fuel
index. -/
theorem defeq_claims2 {m : EnvS2U V env} {fuel : Nat}
    (hfd : Denote2FuelDownM μ m φ fuel)
    (hstep : DefEqStepAt2 μ m φ fuel) :
    DefEqClaims2 μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb hCa hCb aa ba hda hdb
  rw [Setlec.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_cont2 hstep defeqLoopFuel d h hwa hba hLa hwb hbb hLb
    hCa hCb (hfd d a hda) (hfd d b hdb)

/-! ## The step's obligations, at the checker's own boundaries

`defeqStep` calls five functions this lane cares about.  One of them
(`whnfCore`) is the sibling claim; the other four become named
obligations, together with the stuck configuration. -/

/-- **Residue 2 — the delta identity.**  v1's `denote_delta_stepR`
transposed: unfolding a definition head does not move the canonical
annotation, so a delta step neither changes the accumulated equation
nor re-enters the claim.

The v1 proof runs `delta_coreR` — head substitution plus weakening of
the stored body's denotation.  Its `denote2` twin needs the same two
lemmas over `denote2` (level-parameter substitution and depth
weakening), and `Annot/Canon.lean` states **neither**: `denote2_erase`
is its only law today.  `EnvS2.acval_defn` supplies the head fact at
depth `0` and no level instantiation, which is the base case; the
supplier for the rest is the canonical-annotation lane, not this
quarter. -/
def Denote2Delta2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {x y : Expr} {xa : AVExpr},
    Setlec.unfoldDefinition env x = some y →
    denote2 μ m.acval env φ fuel d x = some xa →
    denote2 μ m.acval env φ fuel d y = some xa

/-- **Residue 3 — the hoisted proof irrelevance.**  A positive
`proofIrrel` verdict is an `interp2` equality.  The rule is proved
(`deqStep2_proofIrrel`); what is missing is the *run* side — the
verdict runs two `inferTypeCore`s and an `isPropType`, so consuming it
needs `InferClaims2` at the two inferred types together with a
sort-level reading of the `Prop` test.  That is the `Infer` quarter's
product, not this one's. -/
def ProofIrrel2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.proofIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 4 — the literal acceleration.**  A `reduceNat` step and
its (moved) annotation, in the `ReduceNatStepR` shape.  Out of scope by
the campaign's own routing: the `Nat`-op machinery has not been
transposed to `interp2`. -/
def ReduceNat2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    denote2 μ m.acval env φ fuel d e = some ea →
    ∃ ea₂, denote2 μ m.acval env φ fuel d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e₂

/-- **Residue 5 — the same-head spine short-circuit.**  `defeqSpine`'s
verdict is `defeqStep`'s second entry point into the argument-list
congruence; it compares two *unfoldable-headed* spines, so the head
equality is `acval`-level and the arguments run through `defEqList`.
The rule is `deqStep2_appCong` iterated; the run side needs the
`defEqList` transposition, which is the same object `DefEqStuck2`'s
`.app` case needs and is stated once, there. -/
def DefEqSpine2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.defeqSpineP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **The stuck configuration.**  `defeqStep` reached its last block —
neither side reduced, neither is a proof, neither head unfolds — so the
verdict came from a leaf comparison, a congruence or `stuckIrrel`.

A *case restriction*, not a stage split: the hypothesis is
`defeqStep`'s own call with the earlier moves' negative outcomes
recorded, so a consumer applies it to the untouched original and it
composes where a mid-body lemma cannot. -/
def DefEqStuck2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
    Setlec.unfoldableHead env a' = false →
    Setlec.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b' →
    ∀ {aa' ba' : AVExpr},
      denote2 μ m.acval env φ fuel d a' = some aa' →
      denote2 μ m.acval env φ fuel d b' = some ba' →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa' = interp2 V ρ ba'

/-! ## The two packages -/

/-- The frame conditions of a `whnfCore` reduct, with its canonical
annotation and the interpretation equality. -/
theorem whnfCore_package2 {m : EnvS2U V env} {fuel d : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa : AVExpr}
    (ihwc : WhnfCoreClaims2 μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a)
    (hda : denote2 μ m.acval env φ fuel d a = some aa) :
    ∃ aa', denote2 μ m.acval env φ fuel d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' := by
  obtain ⟨aa', hda', hR⟩ := ihwc hw hws hb hLb hC hda
  exact ⟨aa', hda', fun ρ hρ => (hR ρ hρ).1,
    whnfCore_WScoped m.base.wf fuel hw hws,
    whnfCore_looseBVars m.base.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.base.wf fuel hw l hl),
    CtxOkR.of_subset (whnfCore_fvarLeaves m.base.wf fuel hw) hC⟩

/-- Unfolding one side and continuing: the reduct's frame conditions
and its (identical) annotation, packaged for the four delta
branches. -/
theorem delta_package2 {m : EnvS2U V env} {fuel : Nat}
    (hdel : Denote2Delta2 μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {x y : Expr} {xa : AVExpr}
    (hu : Setlec.unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) x)
    (hx : denote2 μ m.acval env φ fuel d x = some xa) :
    denote2 μ m.acval env φ fuel d y = some xa ∧ Expr.WScoped d y ∧
      y.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded y ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) y :=
  ⟨hdel hu hx, unfoldDefinition_WScoped m.base.wf hu hws,
    unfoldDefinition_looseBVars m.base.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.base.wf hu l hl),
    CtxOkR.of_subset (unfoldDefinition_fvarLeaves m.base.wf hu) hC⟩

/-! ## The step, as one proof

The delta moves are where the identity pays inside a proof rather than
in prose: unfolding a side does not change its annotation, so the
continuation is handed *the same* `AVExpr` and the accumulated equation
does not grow. -/

/-- **`DefEqStepAt2`**, modulo the five obligations above. -/
theorem defeqStep_claim2 {m : EnvS2U V env} {fuel : Nat}
    (ihwc : WhnfCoreClaims2 μ m φ fuel)
    (hdel : Denote2Delta2 μ m φ fuel)
    (hnat : ReduceNat2 μ m φ fuel) (hpi : ProofIrrel2 μ m φ fuel)
    (hstk : DefEqStuck2 μ m φ fuel)
    (hspine : DefEqSpine2 μ m φ fuel) :
    DefEqStepAt2 μ m φ fuel := by
  intro d k hk a b Δa h hwa hba hLa hwb hbb hLb hCa hCb aa ba hda hdb
    ρ hρ
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold,
    Setlec.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · cases hwca : whnfCore μ env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore μ env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨aa', hda', hEa, hwa', hba', hLa', hCa'⟩ :=
      whnfCore_package2 ihwc hwca hwa hba hLa hCa hda
    obtain ⟨ba', hdb', hEb, hwb', hbb', hLb', hCb'⟩ :=
      whnfCore_package2 ihwc hwcb hwb hbb hLb hCb hdb
    -- from here every verdict is the middle equation
    suffices hmid : interp2 V ρ aa' = interp2 V ρ ba' from
      ((hEa ρ hρ).trans hmid).trans (hEb ρ hρ).symm
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · cases hir : Setlec.proofIrrelP μ env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' ρ hρ
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : Setlec.reduceNatP μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨w, hw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda'
          exact (hEw ρ hρ).trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw hdb' ρ hρ)
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : Setlec.reduceNatP μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨w, hw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hw ρ
            hρ).trans (hEw ρ hρ).symm
        | none, hnb, h =>
        cases hha : Setlec.unfoldableHead env a' <;>
          cases hhb : Setlec.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca hwcb
            (by simpa using ‹¬(a' == b') = true›) hir hna hnb hha hhb
            hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda' hdb' ρ hρ
        · cases hub : Setlec.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2 hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hd2 ρ hρ
        · cases hua : Setlec.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2 hdel hua hwa' hba' hLa' hCa' hda'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hdb' ρ hρ
        · have hboth : ∀ {x : CheckM Bool},
              (match Setlec.unfoldDefinition env a',
                  Setlec.unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              interp2 V ρ aa' = interp2 V ρ ba' := by
            intro x hbb2
            cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : Setlec.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_package2 hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_package2 hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB hdA hdB ρ hρ
          cases hlt1 : Setlec.ReducibilityHint.lt
              (Setlec.headHint env b') (Setlec.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : Setlec.ReducibilityHint.lt
                (Setlec.headHint env a') (Setlec.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (Setlec.ReducibilityHint.sameRegular
                    (Setlec.headHint env a') (Setlec.headHint env b') &&
                  Setlec.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : Setlec.defeqSpineP μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' ρ hρ
                | false => exact hboth (x := pure false) h
            · cases hub : Setlec.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_package2 hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hd2
                  ρ hρ
          · cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_package2 hdel hua hwa' hba' hLa' hCa' hda'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hdb'
                ρ hρ

/-! ## The stuck configuration — the seventeen cases

`defeqStep`'s last block: neither side reduced, neither is a proof,
neither head unfolds.  `split at h` delivers the cases in the checker's
own order, and every *fallthrough* of cases 3–16 is `stuckIrrel`, which
`hfall` names once. -/

/-- **Residue 6 — `stuckIrrel`.**  The last fallback: the capability
rescues (`structEta`, `structUnit`, `pairEta`) and the fallback copy of
proof irrelevance.  Out of scope by the campaign's routing — the fired
capability laws over `interp2` (a `CapsOkV2`) do not exist and must be
stated by their supplier. -/
def StuckIrrel2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.stuckIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 7 — the string-literal expansion.**  v1's
`denote_strLitCtorR` + `frame_strLitCtorR` transposed: the constructor
form of a string literal carries the *literal's own* canonical
annotation and is closed.  Needs `denote2` over `charListT2`, which is
the canonical-annotation lane's to supply. -/
def Denote2StrLit2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ (d : Nat) (st : String) {sa : AVExpr},
    Setlec.strLitSupported env = true →
    denote2 μ m.acval env φ fuel d (.lit (.strVal st)) = some sa →
    denote2 μ m.acval env φ fuel d
        (Setlec.strLitToConstructor st) = some sa ∧
      Expr.WScoped d (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).fvarLeaves = []

/-- **Residue 8 — the canonical valuation is level-insensitive.**  The
`acval` twin of `EnvS.val_params`, which `EnvS2` does not carry:
`denote_const_congrR`'s only ingredient, and the sole thing the
`const`/`const` case needs beyond `Level.isEquivList` soundness.  A
missing *environment field*, not a missing proof — its supplier is the
`EnvS2` seal. -/
def AcvalParams2 {env : Env} (m : EnvS2U V env) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      m.acval n ψ₁ = m.acval n ψ₂

/-- **Residue 8 is discharged.**  `EnvS2.acval_params` was added to
the structure for exactly this — the quarter's own diagnosis was that
the gap is a missing *field*, not a missing proof, and it was right.
Kept as a named theorem rather than inlined so that
`defEqStep2BP_of`'s hypothesis list can shed it without the reader
losing the trail. -/
theorem acvalParams2 {env : Env} (m : EnvS2U V env) : AcvalParams2 m :=
  m.acval_params

/-- **Residue 9 — the binder codomain numerals agree.**

`deqStep2_piCong`/`deqStep2_lamCong` are stated at a **shared**
codomain numeral, because `interp2`'s `pi`/`lam` clauses read it; the
two sides' numerals come from two independent `sortOfE`/`lamSortE`
runs, so the congruences need them equal.

**This is not `SortOfAgreeR`.**  The Θ lane's claim carries
`PairedLeaves a b` — every `fvar` leaf with a given index has the same
annotation across both sides — and `defeqStep` opens a binder
congruence with *each side's own* annotation, so the two opened bodies
carry `(d, n₁, ty₁)` and `(d, n₂, ty₂)` and `PairedLeaves` **fails at
index `d`**, exactly where the congruence needs it.  So the obligation
is stated here in the shape its consumer has, and reporting the gap is
the point: the sort-coherence lane's paired discipline does not reach
the one site in `defeqStep` that opens two annotations at one index. -/
def BinderSortAgree2 (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  (∀ {d : Nat} {a b : Expr} {u v : Nat},
      isDefEqCore μ env fuel d a b = .ok true →
      sortOfE μ env φ fuel d a = some u →
      sortOfE μ env φ fuel d b = some v → u = v) ∧
  (∀ {d : Nat} {a b : Expr} {u v : Nat},
      isDefEqCore μ env fuel d a b = .ok true →
      lamSortE μ env φ fuel d a = some u →
      lamSortE μ env φ fuel d b = some v → u = v)

/-- **Residue 10 — the stuck spine congruence.**  `defEqList` over
`interp2`, plus `denote2`'s `mkAppN` inversion.  Neither exists: v1
rides `denote_mkAppN_inv`, `frame_spineR` and `defEqL_of_defEqListR`
(`Bridge/Spine.lean`), and `Annot/Canon.lean` states no spine law for
`denote2` at all. -/
def AppCongrStuck2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    Setlec.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 11 — the η certificate.**  `deqStep2_eta` is proved; what
is missing is the run side, which infers the stuck side's type and
whnfs it to a `∀` — an `InferClaims2` product plus the type's `piR`
reading, i.e. the same shape `ProofIrrel2` needs and for the same
reason. -/
def EtaCert2 (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty bd b : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr},
    Setlec.etaCertP μ env fuel d n ty bd mb b = .ok true →
    Expr.WScoped d (.lam n ty bd mb) →
    (Expr.lam n ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.lam n ty bd mb) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d (.lam n ty bd mb) = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-! ## Two facts that are free -/

/-- **The v1 defeq claim is free at an `EnvS2`.**  `checkBridge` is a
theorem at every `EnvR`, `EnvS2` contains an `EnvS`, and `EnvS.toEnvR`
converts — so the *relational* verdict a binder congruence needs for
`CtxOkR.openCong` costs nothing.  This is the seam `Dispatch.lean`'s
STOP note flagged in the other direction: relational facts flow **into**
the annotated lane freely; it is `DefEq → interp2` that does not
exist. -/
theorem defeqR_at (m : EnvS2U V env) (fuel : Nat) :
    DefEqClaimsR (mode := μ) m.base.toEnvR φ fuel :=
  (checkBridge (mode := μ) m.base.toEnvR φ fuel).2.2.1

/-- The same constant at level-equivalent instantiations has one
canonical annotation. -/
theorem acval_const_congr2 {m : EnvS2U V env} (hap : AcvalParams2 m)
    {fuel d : Nat} {n : Name} {us us' : List Level} {aa ba : AVExpr}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denote2 μ m.acval env φ fuel d (.const n us) = some aa)
    (hdb : denote2 μ m.acval env φ fuel d (.const n us') = some ba) :
    aa = ba := by
  rw [denote2] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine hap n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-- **The binder congruence's two premises**, shared by the `∀` and `λ`
cases: the domain equality, and the opened bodies' equality read in the
*left* domain's own value set.  This is where `CtxOkR.openCong` fires,
and its `DefEq` premise is the free relational fact `defeqR_at`
supplies. -/
theorem binder_congr2 {m : EnvS2U V env} {fuel : Nat}
    (ihd : DefEqClaims2 μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {n₁ n₂ : Name}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AVExpr}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₂)
    (hta₁ : denote2 μ m.acval env φ fuel d ty₁ = some ta₁)
    (hva₁ : denote2 μ m.acval env φ fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some ba₁)
    (hta₂ : denote2 μ m.acval env φ fuel d ty₂ = some ta₂)
    (hva₂ : denote2 μ m.acval env φ fuel (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some ba₂)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ta₁ = interp2 V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp2 V ρ ta₁ →
        interp2 V (cons x ρ) ba₁ = interp2 V (cons x ρ) ba₂ := by
  have hcl := m.base.cval_closed
  have hAe₁ : denote m.base.cval env φ d ty₁ = some ta₁.erase :=
    denote2_erase m.acval_erase d ty₁ hta₁
  have hAe₂ : denote m.base.cval env φ d ty₂ = some ta₂.erase :=
    denote2_erase m.acval_erase d ty₂ hta₂
  have hDA : DefEq μ env m.base.cval φ (Δa.map AVExpr.erase)
      ta₁.erase ta₂.erase :=
    defeqR_at m fuel hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂
      hAe₁ hAe₂
  obtain ⟨hwo₁, hbo₁, hLo₁, hCo₁⟩ :=
    frame_openR (n := n₁) (A := ta₁.erase) hcl hwt₁ hbt₁ hwb₁ hbb₁
      hLt₁ hLb₁ hCt₁ hCb₁ hAe₁
  have hCo₂ : CtxOkR μ m.base.cval env φ (d + 1)
      (ta₁.erase :: Δa.map AVExpr.erase)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) :=
    CtxOkR.openCong (n := n₂) hcl hCb₂ hCt₂ hAe₂ hwt₂.fvarsBelow hDA
  refine ⟨ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      ρ hρ, ?_⟩
  intro x hx
  refine ihd (Δa := ta₁ :: Δa) hdd hwo₁ hbo₁ hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (Setlec.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) (fun l hl => ?_)
    hCo₁ hCo₂ hva₁ hva₂ (cons x ρ) (Sat2_cons V hρ hx)
  rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
  · exact hLb₂ l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbt₂
    · exact hLt₂ l h3

/-- **`DefEqStuck2`**: ten of the seventeen cases closed here, seven
routed. -/
theorem defeqStuck_claim2 {m : EnvS2U V env} {fuel : Nat}
    (ihd : DefEqClaims2 μ m φ fuel) (hsi : StuckIrrel2 μ m φ fuel)
    (hstr : Denote2StrLit2 μ m φ fuel) (hap : AcvalParams2 m)
    (hbs : BinderSortAgree2 μ env φ fuel)
    (happ : AppCongrStuck2 μ m φ fuel) (heta : EtaCert2 μ m φ fuel) :
    DefEqStuck2 μ m φ fuel := by
  intro d Δa _k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb aa' ba' hda hdb ρ hρ
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold, Setlec.defeq_def,
    Setlec.defEqList_fold, Setlec.etaCert_fold] at h
  rw [if_neg (by simpa using hab), hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : Setlec.stuckIrrelP μ env fuel d a' b' = .ok true →
      interp2 V ρ aa' = interp2 V ρ ba' := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ
  clear hab hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort
  · rename_i u v
    rw [denote2_sort] at hda hdb
    obtain rfl : aa' = AVExpr.sort (u.eval φ) :=
      (Option.some.inj hda).symm
    obtain rfl : ba' = AVExpr.sort (v.eval φ) :=
      (Option.some.inj hdb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [Setlec.liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true => rw [Level.isEquiv_sound hle φ]
  -- 2: lit/lit
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : aa' = ba' := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  -- 3: `lit 0` against `Nat.zero`
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
      rw [denote2_natZeroConst hg] at hdb
      obtain rfl : ba' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0`
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
      rw [denote2_natZeroConst hg] at hda
      obtain rfl : aa' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hda).symm
      rfl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hdb
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwb hbb hLb hCb
        exact deqStep2_appCong rfl
          (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
            (CtxOkR.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves]))
            hCx (denote2_natLit hg) hxa ρ hρ)
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)`
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hda
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwa hba hLa hCa
        exact deqStep2_appCong rfl
          (ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOkR.of_fvarLeaves_nil hCb.1 (by simp [Expr.fvarLeaves]))
            hxa (denote2_natLit hg) ρ hρ)
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr d st hg hda
      exact ihd h hwc hbc hLc hwb hbb hLb
        (CtxOkR.of_fvarLeaves_nil hCa.1 hnil) hCb hdc hdb ρ hρ
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr d st hg hdb
      exact ihd h hwa hba hLa hwc hbc hLc hCa
        (CtxOkR.of_fvarLeaves_nil hCb.1 hnil) hda hdc ρ hρ
    · exact hfall h
  -- 9: the same de Bruijn level
  · rename_i i n₁ t₁ j n₂ t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denote2_fvar] at hda hdb
      obtain rfl : aa' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hda).symm
      obtain rfl : ba' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [Setlec.liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : aa' = ba' := acval_const_congr2 hap hle hda hdb
          rfl
    · exact hfall h
  -- 11: ∀-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, _u₁, v₁, hta₁, hva₁, -, hv₁, rfl⟩ :=
        denote2_forallE_inv hda
      obtain ⟨ta₂, ba₂, _u₂, v₂, hta₂, hva₂, -, hv₂, rfl⟩ :=
        denote2_forallE_inv hdb
      obtain rfl : v₁ = v₂ := hbs.1 h hv₁ hv₂
      obtain ⟨hDA, hDB⟩ := binder_congr2 ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ ρ hρ
      exact deqStep2_piCong hDA hDB
  -- 12: λ-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, v₁, hta₁, hva₁, hv₁, rfl⟩ :=
        denote2_lam_inv hda
      obtain ⟨ta₂, ba₂, v₂, hta₂, hva₂, hv₂, rfl⟩ :=
        denote2_lam_inv hdb
      obtain rfl : v₁ = v₂ := hbs.2 h hv₁ hv₂
      obtain ⟨hDA, hDB⟩ := binder_congr2 ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ ρ hρ
      exact deqStep2_lamCong hDA hDB
  -- 13: the stuck spine congruence
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore μ env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : Setlec.defEqListP μ env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          exact happ hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb
            hda hdb ρ hρ
    · exact hfall h
  -- 14: the stuck projection congruence
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore μ env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        obtain ⟨ia₁, he₁, -, rfl⟩ := denote2_proj_inv hda
        obtain ⟨ia₂, he₂, -, rfl⟩ := denote2_proj_inv hdb
        simp only [Expr.WScoped] at hwa hwb
        simp only [Expr.looseBVarsBounded] at hba hbb
        exact deqStep2_projCong (ihd hde hwa hba
          (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
          hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
          he₁ he₂ ρ hρ)
    · exact hfall h
  -- 15: one-sided λ on the left
  · rename_i n₁ ty₁ bd₁ mb₁ hnl
    cases he : Setlec.etaCertP μ env fuel d n₁ ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact heta he hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ
    | false => exact hfall h
  -- 16: one-sided λ on the right
  · rename_i n₂ ty₂ bd₂ mb₂ hnl
    cases he : Setlec.etaCertP μ env fuel d n₂ ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (heta he hwb hbb hLb hwa hba hLa hCb hCa hdb hda ρ hρ).symm
    | false => exact hfall h
  -- 17: distinct stuck heads
  · exact hfall h

/-! ## The assembly

`DefEqStep2` quantifies its environment, valuation and fuel, so the
residues appear here in their quantified form.  Eleven of them, each
named above with the reason it is routed rather than proved. -/

/-- **`DefEqStep2`, modulo the eleven routed obligations.**

Closed here: the loop's budget recursion, the syntactic fast path, both
`whnfCore` rewrites, all four lazy-delta decisions and the same-head
branch's plumbing, and ten of the stuck block's seventeen cases —
`sort`/`sort`, `lit`/`lit`, both `Nat.zero` orders, both `Nat.succ`
orders, `fvar`/`fvar`, `const`/`const`, and the `∀`, `λ` and `proj`
congruences. -/
theorem defeqStep2_of
    (hfd : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), Denote2FuelDownM μ m φ fuel)
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), Denote2Delta2 μ m φ fuel)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2 μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2 μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2 μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2 μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), Denote2StrLit2 μ m φ fuel)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel : Nat),
      BinderSortAgree2 μ env φ fuel)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2 μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2 μ m φ fuel) :
    DefEqStep2 μ V := by
  intro env m φ fuel ihwc _ihw ihd _ihi
  exact defeq_claims2 (hfd env m φ fuel)
    (defeqStep_claim2 ihwc (hdel env m φ fuel) (hnat env m φ fuel)
      (hpi env m φ fuel)
      (defeqStuck_claim2 ihd (hsi env m φ fuel) (hstr env m φ fuel)
        (hap env m) (hbs env φ fuel) (happ env m φ fuel)
        (heta env m φ fuel))
      (hspine env m φ fuel))

/-! ## Seal 6 (+ STOP 2) — the quarter re-pointed

Everything above stays as the sealed shape; what follows is the same
seven blocks against the amended claims.  Three things changed, and
each one is a finding rather than a re-typing.

**R1 removes this file's third finding outright.**  The annotation
fuel is now the claim's own binder, so `defeq_claims2A` hands the two
subject annotations to the loop *verbatim*: nothing is ever moved down
a decrement.  `Denote2FuelDownM` is therefore **not consumed anywhere
below** — not discharged, not weakened, simply never asked for.  (It
stays refuted; `denote2_fuelMono`'s existence is what makes the
re-index harmless, not what discharges the old residue.)

**STOP 2's correction is what the two `whnfCore` rewrites need.**  A
reduct may need more annotation fuel than its subject did, so the
reduction claim's reduct lives at some `F' ≥ F`.  `defeqStep` reduces
*both* sides, so the two sides come back at two different fuels; they
are re-joined at `max` by `denote2_fuelMono`, which returns the *same*
`AVExpr` and so leaves every equality already proved untouched.  The
`max` idiom works here without a snag, and the delta and `reduceNat`
residues take the same `∃ F' ≥ F` shape for the same reason (the
corrected `acval_defn` is R3-shaped, so a delta step cannot promise
the body's annotation at the head's own fuel).

**R2's grading is what this quarter cannot pay.**  `WhnfCoreClaims2A`
concludes under `AnnotOk2 V ρ ea`, and the quarter consumes it at
exactly two sites — the two `whnfCore` rewrites at the top of
`defeqStep`, one per subject.  `DefEqClaims2A` is stated *ungraded*,
and none of its other premises implies `AnnotOk2` of a subject's
annotation: `denote2` performs no membership check at an `app` node,
and `WScoped`/`looseBVarsBounded`/`LeavesBounded`/`CtxOkR` are all
syntactic.  So the ungraded amended claim is **not provable by this
route**, and the currency below is `DefEqClaims2AP`: each subject's
`AnnotOk2` as a *premise*, never a conclusion.

`DeqS`'s grading survives that intact — no `AnnotOk2` crosses an
equality, so `deqStep2_symm`/`deqStep2_trans` are still the one-liners
of `Step2/DefEq.lean`.  What the premises cost is that the claim
declines to speak about junk-annotated subjects, which is exactly what
R2 established about β at kind `0`; and the binder congruences pay for
them from the node's own `AnnotOk2` (`AnnotOk2_pi`/`AnnotOk2_lam`),
which is why the seven blocks go through unchanged otherwise. -/

/-- The sealed (refuted) head-normalisation shape implies the
corrected one at `F' := F`.  Kept so the discharge below, which is
written against `WhnfCoreClaims2B`, can also be driven from a
`WhnfCoreClaims2A` if the junction ever wants it. -/
theorem whnfCoreClaims2B_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : WhnfCoreClaims2A μ m φ fuel) :
    WhnfCoreClaims2B μ m φ fuel := by
  intro d e e' Δa hw hws hb hLb hC F ea hd
  obtain ⟨ea', hd', hR⟩ := h hw hws hb hLb hC hd
  exact ⟨F, ea', Nat.le_refl F, hd', hR⟩

/-- **The claim this quarter can deliver.**  `DefEqClaims2A` with each
subject's `AnnotOk2` as a premise — the price of R2, paid at the two
`whnfCore` rewrites and nowhere else. -/
def DefEqClaims2AP (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- The ungraded amended claim is stronger: dropping premises is
free.  Stated so the two currencies are related in the tree and the
junction can see exactly what the grading costs. -/
theorem defEqClaims2AP_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : DefEqClaims2A μ m φ fuel) : DefEqClaims2AP μ m φ fuel := by
  intro d a b Δa hr hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
    ρ hρ _ _
  exact h hr hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ

/-! ### The loop and its continuation, amended -/

/-- The continuation's contract at the amended shape: the annotation
fuel is the continuation's own binder, and each subject's `AnnotOk2`
is a premise.  The depth is still fixed, not quantified. -/
def DefEqCont2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AVExpr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **One iteration**, amended.  (Seal 6's `μ.verified` premise sat
here too; the R4 spike deleted it — it was only threaded on to the
loop induction below.) -/
def DefEqStepAt2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool},
    DefEqCont2A μ m φ d k →
    ∀ {a b : Expr} {Δa : List AVExpr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
      ∀ {F : Nat} {aa ba : AVExpr},
        denote2 μ m.acval env φ F d a = some aa →
        denote2 μ m.acval env φ F d b = some ba →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
          interp2 V ρ aa = interp2 V ρ ba

/-- The loop satisfies the amended contract at every budget.  The
recursion is still on the **private budget** (`defeqLoopFuel` is
`@[irreducible]` and the loop does not touch the knot's fuel); the
amendment changed the payload, not the discipline. -/
theorem defeqLoop_cont2A {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2A μ m φ fuel) :
    ∀ (budget d : Nat),
      DefEqCont2A μ m φ d
        (defeqLoop μ (pureFns μ env fuel) env d budget) := by
  intro budget
  induction budget with
  | zero =>
    intro d a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d a b Δa h
    rw [defeqLoop] at h
    exact hstep (ih d) h

/-- **`DefEqClaims2AP` at `fuel + 1`**, modulo the step — and modulo
*nothing else*.  Compare `defeq_claims2`: the fuel-down residue is
gone, because `hda`/`hdb` are handed on at the very fuel they arrive
at.  This is R1's whole payoff, in two lines. -/
theorem defeq_claims2A {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2A μ m φ fuel) :
    DefEqClaims2AP μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
  rw [Setlec.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_cont2A hstep defeqLoopFuel d h hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb

/-! ### The step's obligations, re-quantified

Every residue that mentions an annotation gets `F` as its own binder.
The two that produce a *reduct* get R3's `∃ F' ≥ F` on top, because the
repaired `acval_defn` cannot promise a definition's body at the head's
own fuel — the residues inherit STOP 2 exactly where the claims do.
The five that only *compare* take each subject's `AnnotOk2`, matching
the currency `DefEqClaims2AP` is stated in. -/

/-- **Residue 2, amended — the delta identity.**  Unfolding a
definition head does not move the canonical annotation; what STOP 2
adds is that the body may need more fuel to annotate than the head did,
which is `EnvS2.acval_defn`'s repaired shape at depth `0`.  The
*checker's* fuel does not appear at all — a simplification R1 makes
visible, since the old statement only ever mentioned it to index the
annotation. -/
def Denote2Delta2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {x y : Expr} {xa : AVExpr},
    Setlec.unfoldDefinition env x = some y →
    denote2 μ m.acval env φ F d x = some xa →
    ∃ F', F ≤ F' ∧ denote2 μ m.acval env φ F' d y = some xa

/-- **Residue 3, amended — the hoisted proof irrelevance.** -/
def ProofIrrel2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.proofIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 4, amended — the literal acceleration.**  A reduct, so
R3's slack; and the continuation needs the reduct's `AnnotOk2`, so the
equality is graded exactly like a reduction claim's. -/
def ReduceNat2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {F : Nat}
    {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    denote2 μ m.acval env φ F d e = some ea →
    ∃ F' ea₂, F ≤ F' ∧
      denote2 μ m.acval env φ F' d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
        interp2 V ρ ea = interp2 V ρ ea₂ ∧ AnnotOk2 V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e₂

/-- **Residue 5, amended — the same-head spine short-circuit.** -/
def DefEqSpine2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.defeqSpineP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **The stuck configuration**, amended.  The two subjects arrive at
one annotation fuel because the step joins the two reducts at `max`
before entering the block. -/
def DefEqStuck2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
    Setlec.unfoldableHead env a' = false →
    Setlec.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b' →
    ∀ {F : Nat} {aa' ba' : AVExpr},
      denote2 μ m.acval env φ F d a' = some aa' →
      denote2 μ m.acval env φ F d b' = some ba' →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa' → AnnotOk2 V ρ ba' →
        interp2 V ρ aa' = interp2 V ρ ba'

/-! ### The two packages, amended -/

/-- The frame conditions of a `whnfCore` reduct, its annotation **at
the reduct's own fuel**, and the graded interpretation equality. -/
theorem whnfCore_package2A {m : EnvS2U V env} {fuel F d : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa : AVExpr}
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a)
    (hda : denote2 μ m.acval env φ F d a = some aa) :
    ∃ F' aa', F ≤ F' ∧
      denote2 μ m.acval env φ F' d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa →
        interp2 V ρ aa = interp2 V ρ aa' ∧ AnnotOk2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' := by
  obtain ⟨F', aa', hle, hda', hR⟩ := ihwc hw hws hb hLb hC hda
  exact ⟨F', aa', hle, hda', hR,
    whnfCore_WScoped m.base.wf fuel hw hws,
    whnfCore_looseBVars m.base.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.base.wf fuel hw l hl),
    CtxOkR.of_subset (whnfCore_fvarLeaves m.base.wf fuel hw) hC⟩

/-- Unfolding one side and continuing.  The annotation is *the same*
`AVExpr` — which is why the delta branches need no `AnnotOk2` transport
at all, the subject's own serves the reduct — but it may live one fuel
up, and the other side is lifted to meet it. -/
theorem delta_package2A {m : EnvS2U V env}
    (hdel : Denote2Delta2A μ m φ)
    {F d : Nat} {Δa : List AVExpr} {x y : Expr} {xa : AVExpr}
    (hu : Setlec.unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) x)
    (hx : denote2 μ m.acval env φ F d x = some xa) :
    ∃ F', F ≤ F' ∧ denote2 μ m.acval env φ F' d y = some xa ∧
      Expr.WScoped d y ∧ y.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded y ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) y := by
  obtain ⟨F', hle, hy⟩ := hdel hu hx
  exact ⟨F', hle, hy, unfoldDefinition_WScoped m.base.wf hu hws,
    unfoldDefinition_looseBVars m.base.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.base.wf hu l hl),
    CtxOkR.of_subset (unfoldDefinition_fvarLeaves m.base.wf hu) hC⟩

/-- **`DefEqStepAt2A`**, modulo the five obligations above.  The proof
is the sealed one with two additions: the two reducts are joined at
`max` (`denote2_fuelMono`, same annotation), and the subject's
`AnnotOk2` is spent at the two `whnfCore` rewrites to buy the reducts'.
Every later block is served by the reducts' `AnnotOk2` — including all
four delta branches, where the annotation does not move at all. -/
theorem defeqStep_claim2A {m : EnvS2U V env} {fuel : Nat}
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    (hdel : Denote2Delta2A μ m φ)
    (hnat : ReduceNat2A μ m φ fuel) (hpi : ProofIrrel2A μ m φ fuel)
    (hstk : DefEqStuck2A μ m φ fuel)
    (hspine : DefEqSpine2A μ m φ fuel) :
    DefEqStepAt2A μ m φ fuel := by
  intro d k hk a b Δa h hwa hba hLa hwb hbb hLb hCa hCb F aa ba
    hda hdb ρ hρ hokA hokB
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold,
    Setlec.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · cases hwca : whnfCore μ env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore μ env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨Fa, aa', hFa, hda0, hEa, hwa', hba', hLa', hCa'⟩ :=
      whnfCore_package2A ihwc hwca hwa hba hLa hCa hda
    obtain ⟨Fb, ba', hFb, hdb0, hEb, hwb', hbb', hLb', hCb'⟩ :=
      whnfCore_package2A ihwc hwcb hwb hbb hLb hCb hdb
    obtain ⟨hEA, hokA'⟩ := hEa ρ hρ hokA
    obtain ⟨hEB, hokB'⟩ := hEb ρ hρ hokB
    -- the two reducts, joined at one fuel; the annotations do not move
    have hda' : denote2 μ m.acval env φ (max Fa Fb) d a' = some aa' :=
      denote2_fuelMono (Nat.le_max_left Fa Fb) d a' hda0
    have hdb' : denote2 μ m.acval env φ (max Fa Fb) d b' = some ba' :=
      denote2_fuelMono (Nat.le_max_right Fa Fb) d b' hdb0
    -- from here every verdict is the middle equation
    suffices hmid : interp2 V ρ aa' = interp2 V ρ ba' from
      (hEA.trans hmid).trans hEB.symm
    clear hEA hEB hEa hEb hda hdb hda0 hdb0 hokA hokB
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · cases hir : Setlec.proofIrrelP μ env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' ρ hρ hokA' hokB'
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : Setlec.reduceNatP μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨F₂, w, hle₂, hw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda'
          obtain ⟨hEw1, hokw⟩ := hEw ρ hρ hokA'
          exact hEw1.trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw
              (denote2_fuelMono hle₂ d b' hdb') ρ hρ hokw hokB')
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : Setlec.reduceNatP μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨F₂, w, hle₂, hw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb'
          obtain ⟨hEw1, hokw⟩ := hEw ρ hρ hokB'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
            (denote2_fuelMono hle₂ d a' hda') hw ρ hρ hokA'
            hokw).trans hEw1.symm
        | none, hnb, h =>
        cases hha : Setlec.unfoldableHead env a' <;>
          cases hhb : Setlec.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca
            hwcb (by simpa using ‹¬(a' == b') = true›) hir hna hnb
            hha hhb hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
            hdb' ρ hρ hokA' hokB'
        · cases hub : Setlec.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
              (denote2_fuelMono hle₂ d a' hda') hd2 ρ hρ hokA' hokB'
        · cases hua : Setlec.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
              (denote2_fuelMono hle₂ d b' hdb') ρ hρ hokA' hokB'
        · have hboth : ∀ {x : CheckM Bool},
              (match Setlec.unfoldDefinition env a',
                  Setlec.unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              interp2 V ρ aa' = interp2 V ρ ba' := by
            intro x hbb2
            cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : Setlec.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨FA, hleA, hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨FB, hleB, hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB
                (denote2_fuelMono (Nat.le_max_left FA FB) d a₂ hdA)
                (denote2_fuelMono (Nat.le_max_right FA FB) d b₂ hdB)
                ρ hρ hokA' hokB'
          cases hlt1 : Setlec.ReducibilityHint.lt
              (Setlec.headHint env b') (Setlec.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : Setlec.ReducibilityHint.lt
                (Setlec.headHint env a') (Setlec.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (Setlec.ReducibilityHint.sameRegular
                    (Setlec.headHint env a') (Setlec.headHint env b') &&
                  Setlec.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : Setlec.defeqSpineP μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' ρ hρ hokA' hokB'
                | false => exact hboth (x := pure false) h
            · cases hub : Setlec.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
                  (denote2_fuelMono hle₂ d a' hda') hd2 ρ hρ hokA'
                  hokB'
          · cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
                (denote2_fuelMono hle₂ d b' hdb') ρ hρ hokA' hokB'

/-! ### The stuck configuration, amended — the seventeen cases -/

/-- **Residue 6, amended — `stuckIrrel`.** -/
def StuckIrrel2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.stuckIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 7, amended — the string-literal expansion.**  This is a
`denote2` success in *conclusion* position, so STOP 2's rule applies
and the answer is that it is safe: `strLitToConstructor`
(`Kernel/Core.lean:324`) builds nothing but `.app`, `.const` and
`.lit (.natVal _)` nodes, and `denote2`'s clauses for those three are
fuel-free — no `sortOfE`, no `lamSortE`, no run.  So the constructor
form annotates at *every* fuel its literal does, and the fixed `F` here
is not the defect that killed the reduction claims.  Checked, not
assumed: the rule's exemption is "unless every term it asserts a
`denote2` success for is binder-free", and this one is. -/
def Denote2StrLit2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (st : String) {sa : AVExpr},
    Setlec.strLitSupported env = true →
    denote2 μ m.acval env φ F d (.lit (.strVal st)) = some sa →
    denote2 μ m.acval env φ F d
        (Setlec.strLitToConstructor st) = some sa ∧
      Expr.WScoped d (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).fvarLeaves = []

/-- **Residue 9, amended — the binder codomain numerals agree.**  The
run's fuel and the annotation's are now two binders, because the
verdict comes from `isDefEqCore` at the checker's fuel while the two
numerals come from `denote2`'s walk at the claim's `F`.  In the sealed
version they were forced equal, which was R1's defect in miniature —
the numerals a caller actually holds never come from the run's fuel. -/
def BinderSortAgree2A (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel F : Nat) : Prop :=
  (∀ {d : Nat} {a b : Expr} {u v : Nat},
      isDefEqCore μ env fuel d a b = .ok true →
      sortOfE μ env φ F d a = some u →
      sortOfE μ env φ F d b = some v → u = v) ∧
  (∀ {d : Nat} {a b : Expr} {u v : Nat},
      isDefEqCore μ env fuel d a b = .ok true →
      lamSortE μ env φ F d a = some u →
      lamSortE μ env φ F d b = some v → u = v)

/-- **Residue 10, amended — the stuck spine congruence.** -/
def AppCongrStuck2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    Setlec.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 11, amended — the η certificate.** -/
def EtaCert2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty bd b : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr},
    Setlec.etaCertP μ env fuel d n ty bd mb b = .ok true →
    Expr.WScoped d (.lam n ty bd mb) →
    (Expr.lam n ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.lam n ty bd mb) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d (.lam n ty bd mb) = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- **The binder congruence's two premises**, amended.  The four
`AnnotOk2` inputs are exactly what `AnnotOk2_pi`/`AnnotOk2_lam` hand
back from the two nodes, which is why the grading costs the congruences
nothing: the codomain's truthfulness is already *in* the node's.  The
right-hand body is read at the left domain's value set, so the domain
equality is proved first and transports the membership. -/
theorem binder_congr2A {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2AP μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {n₁ n₂ : Name}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AVExpr}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₂)
    (hta₁ : denote2 μ m.acval env φ F d ty₁ = some ta₁)
    (hva₁ : denote2 μ m.acval env φ F (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some ba₁)
    (hta₂ : denote2 μ m.acval env φ F d ty₂ = some ta₂)
    (hva₂ : denote2 μ m.acval env φ F (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some ba₂)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ)
    (hoT₁ : AnnotOk2 V ρ ta₁) (hoT₂ : AnnotOk2 V ρ ta₂)
    (hoB₁ : ∀ x, x ∈ˢ interp2 V ρ ta₁ → AnnotOk2 V (cons x ρ) ba₁)
    (hoB₂ : ∀ x, x ∈ˢ interp2 V ρ ta₂ → AnnotOk2 V (cons x ρ) ba₂) :
    interp2 V ρ ta₁ = interp2 V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp2 V ρ ta₁ →
        interp2 V (cons x ρ) ba₁ = interp2 V (cons x ρ) ba₂ := by
  have hcl := m.base.cval_closed
  have hAe₁ : denote m.base.cval env φ d ty₁ = some ta₁.erase :=
    denote2_erase m.acval_erase d ty₁ hta₁
  have hAe₂ : denote m.base.cval env φ d ty₂ = some ta₂.erase :=
    denote2_erase m.acval_erase d ty₂ hta₂
  have hDA : DefEq μ env m.base.cval φ (Δa.map AVExpr.erase)
      ta₁.erase ta₂.erase :=
    defeqR_at m fuel hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂
      hAe₁ hAe₂
  obtain ⟨hwo₁, hbo₁, hLo₁, hCo₁⟩ :=
    frame_openR (n := n₁) (A := ta₁.erase) hcl hwt₁ hbt₁ hwb₁ hbb₁
      hLt₁ hLb₁ hCt₁ hCb₁ hAe₁
  have hCo₂ : CtxOkR μ m.base.cval env φ (d + 1)
      (ta₁.erase :: Δa.map AVExpr.erase)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) :=
    CtxOkR.openCong (n := n₂) hcl hCb₂ hCt₂ hAe₂ hwt₂.fvarsBelow hDA
  have hdom : interp2 V ρ ta₁ = interp2 V ρ ta₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      ρ hρ hoT₁ hoT₂
  refine ⟨hdom, ?_⟩
  intro x hx
  refine ihd (Δa := ta₁ :: Δa) hdd hwo₁ hbo₁ hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (Setlec.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) (fun l hl => ?_)
    hCo₁ hCo₂ hva₁ hva₂ (cons x ρ) (Sat2_cons V hρ hx) (hoB₁ x hx)
    (hoB₂ x (hdom ▸ hx))
  rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
  · exact hLb₂ l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbt₂
    · exact hLt₂ l h3

/-- **`DefEqStuck2A`**: the same ten of the seventeen cases, amended.
Every `AnnotOk2` the block needs it gets from the node it is looking
at — `AnnotOk2_app` for the two `Nat.succ` orders, `AnnotOk2_pi` and
`AnnotOk2_lam` for the congruences, `AnnotOk2_proj` for `proj`, and
for both string cases the constructor form *is* the literal's own
annotation, so the premise transfers unchanged.  R2 costs this block
nothing. -/
theorem defeqStuck_claim2A {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2AP μ m φ fuel) (hsi : StuckIrrel2A μ m φ fuel)
    (hstr : Denote2StrLit2A μ m φ) (hap : AcvalParams2 m)
    (hbs : BinderSortAgree2A μ env φ fuel F)
    (happ : AppCongrStuck2A μ m φ fuel) (heta : EtaCert2A μ m φ fuel) :
    ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
      {a b a' b' : Expr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      (a == b) = false →
      whnfCore μ env fuel d a = .ok a' →
      whnfCore μ env fuel d b = .ok b' →
      (a' == b') = false →
      Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
      Setlec.unfoldableHead env a' = false →
      Setlec.unfoldableHead env b' = false →
      Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a' →
      Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b' →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b' →
      ∀ {aa' ba' : AVExpr},
        denote2 μ m.acval env φ F d a' = some aa' →
        denote2 μ m.acval env φ F d b' = some ba' →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          AnnotOk2 V ρ aa' → AnnotOk2 V ρ ba' →
          interp2 V ρ aa' = interp2 V ρ ba' := by
  intro d Δa _k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb aa' ba' hda hdb ρ hρ hokA hokB
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold, Setlec.defeq_def,
    Setlec.defEqList_fold, Setlec.etaCert_fold] at h
  rw [if_neg (by simpa using hab), hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : Setlec.stuckIrrelP μ env fuel d a' b' = .ok true →
      interp2 V ρ aa' = interp2 V ρ ba' := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ hokA hokB
  clear hab hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort
  · rename_i u v
    rw [denote2_sort] at hda hdb
    obtain rfl : aa' = AVExpr.sort (u.eval φ) :=
      (Option.some.inj hda).symm
    obtain rfl : ba' = AVExpr.sort (v.eval φ) :=
      (Option.some.inj hdb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [Setlec.liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true => rw [Level.isEquiv_sound hle φ]
  -- 2: lit/lit
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : aa' = ba' := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  -- 3: `lit 0` against `Nat.zero`
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
      rw [denote2_natZeroConst hg] at hdb
      obtain rfl : ba' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0`
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
      rw [denote2_natZeroConst hg] at hda
      obtain rfl : aa' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hda).symm
      rfl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hdb
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwb hbb hLb hCb
        simp only [natLitT2, AnnotOk2_app] at hokA
        rw [AnnotOk2_app] at hokB
        exact deqStep2_appCong rfl
          (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
            (CtxOkR.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves]))
            hCx (denote2_natLit hg) hxa ρ hρ hokA.2.1 hokB.2.1)
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)`
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hda
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwa hba hLa hCa
        rw [AnnotOk2_app] at hokA
        simp only [natLitT2, AnnotOk2_app] at hokB
        exact deqStep2_appCong rfl
          (ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOkR.of_fvarLeaves_nil hCb.1 (by simp [Expr.fvarLeaves]))
            hxa (denote2_natLit hg) ρ hρ hokA.2.1 hokB.2.1)
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hda
      exact ihd h hwc hbc hLc hwb hbb hLb
        (CtxOkR.of_fvarLeaves_nil hCa.1 hnil) hCb hdc hdb ρ hρ hokA
        hokB
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hdb
      exact ihd h hwa hba hLa hwc hbc hLc hCa
        (CtxOkR.of_fvarLeaves_nil hCb.1 hnil) hda hdc ρ hρ hokA hokB
    · exact hfall h
  -- 9: the same de Bruijn level
  · rename_i i n₁ t₁ j n₂ t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denote2_fvar] at hda hdb
      obtain rfl : aa' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hda).symm
      obtain rfl : ba' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [Setlec.liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : aa' = ba' := acval_const_congr2 hap hle hda hdb
          rfl
    · exact hfall h
  -- 11: ∀-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, _u₁, v₁, hta₁, hva₁, -, hv₁, rfl⟩ :=
        denote2_forallE_inv hda
      obtain ⟨ta₂, ba₂, _u₂, v₂, hta₂, hva₂, -, hv₂, rfl⟩ :=
        denote2_forallE_inv hdb
      obtain rfl : v₁ = v₂ := hbs.1 h hv₁ hv₂
      rw [AnnotOk2_pi] at hokA hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2A ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ ρ hρ hokA.1 hokB.1 hokA.2 hokB.2
      exact deqStep2_piCong hDA hDB
  -- 12: λ-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, v₁, hta₁, hva₁, hv₁, rfl⟩ :=
        denote2_lam_inv hda
      obtain ⟨ta₂, ba₂, v₂, hta₂, hva₂, hv₂, rfl⟩ :=
        denote2_lam_inv hdb
      obtain rfl : v₁ = v₂ := hbs.2 h hv₁ hv₂
      rw [AnnotOk2_lam] at hokA hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2A ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ ρ hρ hokA.1 hokB.1 hokA.2.1 hokB.2.1
      exact deqStep2_lamCong hDA hDB
  -- 13: the stuck spine congruence
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore μ env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : Setlec.defEqListP μ env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          exact happ hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb
            hda hdb ρ hρ hokA hokB
    · exact hfall h
  -- 14: the stuck projection congruence
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore μ env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        obtain ⟨ia₁, he₁, -, rfl⟩ := denote2_proj_inv hda
        obtain ⟨ia₂, he₂, -, rfl⟩ := denote2_proj_inv hdb
        simp only [Expr.WScoped] at hwa hwb
        simp only [Expr.looseBVarsBounded] at hba hbb
        rw [AnnotOk2_proj] at hokA hokB
        exact deqStep2_projCong (ihd hde hwa hba
          (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
          hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
          he₁ he₂ ρ hρ hokA.1 hokB.1)
    · exact hfall h
  -- 15: one-sided λ on the left
  · rename_i n₁ ty₁ bd₁ mb₁ hnl
    cases he : Setlec.etaCertP μ env fuel d n₁ ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact heta he hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ
        hokA hokB
    | false => exact hfall h
  -- 16: one-sided λ on the right
  · rename_i n₂ ty₂ bd₂ mb₂ hnl
    cases he : Setlec.etaCertP μ env fuel d n₂ ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (heta he hwb hbb hLb hwa hba hLa hCb hCa hdb hda ρ hρ
        hokB hokA).symm
    | false => exact hfall h
  -- 17: distinct stuck heads
  · exact hfall h

/-! ### The assembly, amended

Ten residues, one fewer than the seal: `Denote2FuelDownM` is not among
them, and nothing replaced it. -/

/-- The definitional-equality quarter in the currency it can deliver:
`DefEqStep2B` with `DefEqClaims2A` replaced by `DefEqClaims2AP` on both
sides of the arrow — the `AnnotOk2` premises, and nothing else. -/
def DefEqStep2BP (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2AP μ m φ fuel → InferClaims2A μ m φ fuel →
    DefEqClaims2AP μ m φ (fuel + 1)

/-- **The quarter, modulo the ten routed obligations.**

Closed here, exactly as at the seal: the loop's budget recursion, the
syntactic fast path, both `whnfCore` rewrites *and their fuel join*,
all four lazy-delta decisions with the same-head short-circuit's
plumbing, and ten of the stuck block's seventeen cases.

Not closed, and this is the quarter's report to the junction: the
conclusion is `DefEqClaims2AP`, not `DefEqClaims2A`.  `defeqStep`
begins by reducing **both** subjects, R2 puts a reduction claim's
equality under the subject's `AnnotOk2`, and an ungraded defeq claim
has no `AnnotOk2` to spend — nor can it derive one, since `denote2`
checks no membership at an `app` node and every other premise of the
claim is syntactic.  So the exemption `Claims2A` granted the defeq
claim from R2 needs the same second look the reduction claims' from R3
got.  `defEqStep2B_toAP` below localises the gap to those two premises
and nothing else. -/
theorem defEqStep2BP_of
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2A μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2A μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2A μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2A μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2A μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2A μ m φ fuel) :
    DefEqStep2BP μ V := by
  intro env m φ fuel ihwc _ihw ihd _ihi
  refine defeq_claims2A (defeqStep_claim2A ihwc (hdel env m φ)
    (hnat env m φ fuel) (hpi env m φ fuel) ?_ (hspine env m φ fuel))
  intro d Δa k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb F aa' ba' hda hdb
  exact defeqStuck_claim2A ihd (hsi env m φ fuel) (hstr env m φ)
    (hap env m) (hbs env φ fuel F) (happ env m φ fuel)
    (heta env m φ fuel) h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb hda hdb

/-- **The gap, localised in two premises.**  Feed the quarter the
*sealed* ungraded induction hypothesis — `DefEqClaims2A`, exactly as
`DefEqStep2B` supplies it — and it still delivers, in the graded
currency.  So nothing in the seven blocks needs the ungraded claim as
an input; the ungraded claim is unavailable only as an *output*, and
only because the two `whnfCore` rewrites consume an `AnnotOk2` that a
`DefEqClaims2A` does not carry. -/
theorem defEqStep2B_toAP (h : DefEqStep2BP μ V) :
    ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
      WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
      DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
      DefEqClaims2AP μ m φ (fuel + 1) := by
  intro env m φ fuel ihwc ihw ihd ihi
  exact h env m φ fuel ihwc ihw (defEqClaims2AP_of_A ihd) ihi

/-! ## The fold-in: `DefEqClaims2AP` is the canonical claim

STOP 3 was adopted.  `Claims2B.lean` now carries this quarter's graded
statement as `DefEqClaims2B`, verbatim, and `CheckStep2B` and the four
routed quarters are stated with it — the induction cannot close with
an ungraded hypothesis and a graded conclusion, so the family had to
become uniform rather than the defeq slot staying special.

The two names are the same statement, so the bridge is definitional
and the quarter's deliverable *is* the canonical one.  Kept as an
explicit theorem rather than a `rfl`-alias so that a future change to
either statement fails here, loudly, instead of silently re-pointing
the assembly. -/

/-- The quarter's deliverable, at the canonical claim. -/
theorem defEqStep2B_of (h : DefEqStep2BP μ V) : DefEqStep2B μ V := by
  intro env m φ fuel ihwc ihw ihd ihi
  exact h env m φ fuel ihwc ihw ihd ihi


/-! ## Seal 14 — the quarter re-pointed at generation four

`Claims2C` hoists every `AnnotOk2` a claim takes or gives above the
`∀ ρ`.  For this quarter both of them are **premises**, so the change
is a pure relief: anything the `…A`/`…BP` lane proved from a ρ-local
`AnnotOk2` can be proved from the hoisted one by specialising it at
that `ρ`, and the seven blocks transpose without a new idea.

**What the relief buys, and why the generation exists.**  A `∀`/`λ`
congruence opens the *right* body in the *left* domain's context, and
`CtxOk2.openCong` (`Step2/Dispatch.lean`) — the annotated transpose of
the `CtxOkR.openCong` this lane still uses — asks for `AnnotOk2` of
**both** domains at *every* satisfying valuation.  `not_openCongLocal`
refutes the ρ-local lemma premise-free, so no proof could have supplied
it from generation three.  `binder_ctxOk2_openCong` below pays that
premise **from `DefEqClaims2C` alone**, at the shape the congruence
sites hold: `hok₁`/`hok₂` *are* the claim's two hoisted premises, and
`hdom` *is* its conclusion partially applied.  The gate is paid.

*The distinction that stays on the record.*  Generation four fixes the
**quantifier**; the **currency** (`CtxOkR` → `CtxOk2` in the claims) is
generation five, and until then the congruence proofs below still fire
`CtxOkR.openCong`.  `binder_ctxOk2_openCong` therefore takes both
context hypotheses — `CtxOkR` for the recursive call, `CtxOk2` for
`openCong` — which is exactly the seam generation five closes, and
nothing else. -/

/-! ### The two transports the hoist needs -/

/-! ### The head transfer lives in `Step2/Dispatch.lean`

`Sat2_cons_congr` was written here and `Sat2.head_congr` in the
supplier's kit, with identical statements — the **seventh** collision
of this campaign and the third in this file alone.  Deleted here; the
kit is in this file's import closure. -/

/-! ### `AnnotOk2.hoist_app` / `hoist_proj` live in `Step2/Dispatch.lean`

Added here for the stuck block and, simultaneously, to the supplier's
hoist kit — the **sixth** collision of this campaign.  The kit is the
right home: it is where `hoist_pi`/`hoist_lam` already lived and where
the other quarters look.  Deleted here; `Dispatch.lean` is in this
file's import closure. -/

/-! ### The loop and its continuation, hoisted -/

/-- The continuation's contract, hoisted.  The depth is still fixed:
`defeqLoop` hands `defeqStep` a continuation already applied to the
ambient depth. -/
def DefEqCont2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AVExpr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **One iteration of the lazy-delta loop**, hoisted. -/
def DefEqStepAt2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool},
    DefEqCont2C μ m φ d k →
    ∀ {a b : Expr} {Δa : List AVExpr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
      ∀ {F : Nat} {aa ba : AVExpr},
        denote2 μ m.acval env φ F d a = some aa →
        denote2 μ m.acval env φ F d b = some ba →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ aa = interp2 V ρ ba

/-- The loop satisfies the hoisted contract at every budget.  The
recursion is still on the **private budget**. -/
theorem defeqLoop_cont2C {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2C μ m φ fuel) :
    ∀ (budget d : Nat),
      DefEqCont2C μ m φ d
        (defeqLoop μ (pureFns μ env fuel) env d budget) := by
  intro budget
  induction budget with
  | zero =>
    intro d a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d a b Δa h
    rw [defeqLoop] at h
    exact hstep (ih d) h

/-- **`DefEqClaims2C` at `fuel + 1`**, modulo the step — and modulo
nothing else, exactly as in the `…A` lane. -/
theorem defeq_claims2C {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2C μ m φ fuel) :
    DefEqClaims2C μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
  rw [Setlec.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_cont2C hstep defeqLoopFuel d h hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb

/-! ### The step's obligations, hoisted

`Denote2Delta2A`, `Denote2StrLit2A`, `AcvalParams2` and
`BinderSortAgree2A` mention no `AnnotOk2` at all and are reused
verbatim; the seven that do are restated here.  Reusing rather than
re-stating is the point: a residue that does not carry the grading
cannot be affected by a change to where the grading is quantified, and
saying so is cheaper than four more definitions. -/

/-- **Residue 3, hoisted — proof irrelevance.** -/
def ProofIrrel2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.proofIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 4, hoisted — the literal acceleration.**  It produces a
reduct, so it delivers the reduct's `AnnotOk2` in the hoisted form,
matching `WhnfCoreClaims2C` clause for clause. -/
def ReduceNat2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {F : Nat}
    {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    denote2 μ m.acval env φ F d e = some ea →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
    ∃ F' ea₂, F ≤ F' ∧
      denote2 μ m.acval env φ F' d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea₂) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e₂

/-- **Residue 5, hoisted — the same-head spine short-circuit.** -/
def DefEqSpine2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.defeqSpineP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **The stuck configuration**, hoisted.  Its two `AnnotOk2` were
ρ-local at the `…A` lane and are hoisted here for the reason its
consumer needs them hoisted: the `∀`/`λ` cases inside it are the very
sites `not_openCongLocal` refutes at one valuation. -/
def DefEqStuck2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
    Setlec.unfoldableHead env a' = false →
    Setlec.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b' →
    ∀ {F : Nat} {aa' ba' : AVExpr},
      denote2 μ m.acval env φ F d a' = some aa' →
      denote2 μ m.acval env φ F d b' = some ba' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa') →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba') →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa' = interp2 V ρ ba'

/-- **Residue 6, hoisted — `stuckIrrel`.** -/
def StuckIrrel2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.stuckIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 10, hoisted — the stuck spine congruence.** -/
def AppCongrStuck2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    Setlec.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 11, hoisted — the η certificate.** -/
def EtaCert2C (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty bd b : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr},
    Setlec.etaCertP μ env fuel d n ty bd mb b = .ok true →
    Expr.WScoped d (.lam n ty bd mb) →
    (Expr.lam n ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.lam n ty bd mb) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d (.lam n ty bd mb) = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-! ### The `whnfCore` package, hoisted -/

/-! ### `whnfCore_package2C` lives in `Step2/Whnf.lean`

Written here and in the head-normalisation quarter simultaneously,
with **byte-identical statements** — the fourth name collision of this
campaign and the starkest: not merely the same name, the same lemma.
The `…B` predecessor was written once, in `Whnf.lean`; both quarters
needed the `…C` repackaging and neither could see the other.

Deleted here, kept there, where it packages `whnfCore`'s own claim.
The two call sites below take `m` explicitly, that copy having bound it
so.

*The recurring lesson, now with four instances: parallel quarters
converge on the same helper, and the collision surfaces at the fold
rather than at authoring.  The cost is one deletion each time and the
benefit is two independent checks of the same statement — on this
occasion, two independent proofs of it.* -/

theorem defeqStep_claim2C {m : EnvS2U V env} {fuel : Nat}
    (ihwc : WhnfCoreClaims2C μ m φ fuel)
    (hdel : Denote2Delta2A μ m φ)
    (hnat : ReduceNat2C μ m φ fuel) (hpi : ProofIrrel2C μ m φ fuel)
    (hstk : DefEqStuck2C μ m φ fuel)
    (hspine : DefEqSpine2C μ m φ fuel) :
    DefEqStepAt2C μ m φ fuel := by
  intro d k hk a b Δa h hwa hba hLa hwb hbb hLb hCa hCb F aa ba
    hda hdb hokA hokB ρ hρ
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold,
    Setlec.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · cases hwca : whnfCore μ env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore μ env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨Fa, aa', hFa, hda0, hokA', hEa, hwa', hba', hLa', hCa'⟩ :=
      whnfCore_package2C m ihwc hwca hwa hba hLa hCa hda hokA
    obtain ⟨Fb, ba', hFb, hdb0, hokB', hEb, hwb', hbb', hLb', hCb'⟩ :=
      whnfCore_package2C m ihwc hwcb hwb hbb hLb hCb hdb hokB
    have hEA := hEa ρ hρ
    have hEB := hEb ρ hρ
    -- the two reducts, joined at one fuel; the annotations do not move
    have hda' : denote2 μ m.acval env φ (max Fa Fb) d a' = some aa' :=
      denote2_fuelMono (Nat.le_max_left Fa Fb) d a' hda0
    have hdb' : denote2 μ m.acval env φ (max Fa Fb) d b' = some ba' :=
      denote2_fuelMono (Nat.le_max_right Fa Fb) d b' hdb0
    -- from here every verdict is the middle equation
    suffices hmid : interp2 V ρ aa' = interp2 V ρ ba' from
      (hEA.trans hmid).trans hEB.symm
    clear hEA hEB hEa hEb hda hdb hda0 hdb0 hokA hokB
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · cases hir : Setlec.proofIrrelP μ env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' hokA' hokB' ρ hρ
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : Setlec.reduceNatP μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨F₂, w, hle₂, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda' hokA'
          exact (hEw ρ hρ).trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw
              (denote2_fuelMono hle₂ d b' hdb') hokw hokB' ρ hρ)
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : Setlec.reduceNatP μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨F₂, w, hle₂, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb' hokB'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
            (denote2_fuelMono hle₂ d a' hda') hw hokA' hokw ρ
            hρ).trans (hEw ρ hρ).symm
        | none, hnb, h =>
        cases hha : Setlec.unfoldableHead env a' <;>
          cases hhb : Setlec.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca
            hwcb (by simpa using ‹¬(a' == b') = true›) hir hna hnb
            hha hhb hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
            hdb' hokA' hokB' ρ hρ
        · cases hub : Setlec.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
              (denote2_fuelMono hle₂ d a' hda') hd2 hokA' hokB' ρ hρ
        · cases hua : Setlec.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
              (denote2_fuelMono hle₂ d b' hdb') hokA' hokB' ρ hρ
        · have hboth : ∀ {x : CheckM Bool},
              (match Setlec.unfoldDefinition env a',
                  Setlec.unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              interp2 V ρ aa' = interp2 V ρ ba' := by
            intro x hbb2
            cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : Setlec.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨FA, hleA, hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨FB, hleB, hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB
                (denote2_fuelMono (Nat.le_max_left FA FB) d a₂ hdA)
                (denote2_fuelMono (Nat.le_max_right FA FB) d b₂ hdB)
                hokA' hokB' ρ hρ
          cases hlt1 : Setlec.ReducibilityHint.lt
              (Setlec.headHint env b') (Setlec.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : Setlec.ReducibilityHint.lt
                (Setlec.headHint env a') (Setlec.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (Setlec.ReducibilityHint.sameRegular
                    (Setlec.headHint env a') (Setlec.headHint env b') &&
                  Setlec.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : Setlec.defeqSpineP μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' hokA' hokB' ρ hρ
                | false => exact hboth (x := pure false) h
            · cases hub : Setlec.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_package2A hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2
                  (denote2_fuelMono hle₂ d a' hda') hd2 hokA'
                  hokB' ρ hρ
          · cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_package2A hdel hua hwa' hba' hLa' hCa' hda'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
                (denote2_fuelMono hle₂ d b' hdb') hokA' hokB' ρ hρ


/-! ### The stuck configuration, hoisted — the seventeen cases -/

/-- **The binder congruence's two premises**, hoisted.  The four
`AnnotOk2` inputs are exactly what `AnnotOk2.hoist_pi`/`hoist_lam`
hand back from the two nodes — the domain's hoisted form and the
codomain's hoisted form *in the extended context* — which is why the
hoist costs the congruences nothing beyond one transport.

That transport is the only new step in the whole quarter.
`hoist_pi hokB` gives the right codomain over `ta₂ :: Δa`, and the
recursion happens over `ta₁ :: Δa`; `Sat2.head_congr` moves it across
the domain equality, which is itself ρ-uniform because it is `ihd`'s
conclusion before its `ρ`.  The `…A` lane did the same move at a single
valuation (`hoB₂ x (hdom ▸ hx)`); hoisting it changes the transport's
shape, not its content. -/
theorem binder_congr2C {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2C μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {n₁ n₂ : Name}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AVExpr}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) bd₂)
    (hta₁ : denote2 μ m.acval env φ F d ty₁ = some ta₁)
    (hva₁ : denote2 μ m.acval env φ F (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some ba₁)
    (hta₂ : denote2 μ m.acval env φ F d ty₂ = some ta₂)
    (hva₂ : denote2 μ m.acval env φ F (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some ba₂)
    (hoT₁ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₁)
    (hoT₂ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₂)
    (hoB₁ : ∀ σ : Nat → V, Sat2 V (ta₁ :: Δa) σ → AnnotOk2 V σ ba₁)
    (hoB₂ : ∀ σ : Nat → V, Sat2 V (ta₂ :: Δa) σ → AnnotOk2 V σ ba₂)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ta₁ = interp2 V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp2 V ρ ta₁ →
        interp2 V (cons x ρ) ba₁ = interp2 V (cons x ρ) ba₂ := by
  have hcl := m.base.cval_closed
  have hAe₁ : denote m.base.cval env φ d ty₁ = some ta₁.erase :=
    denote2_erase m.acval_erase d ty₁ hta₁
  have hAe₂ : denote m.base.cval env φ d ty₂ = some ta₂.erase :=
    denote2_erase m.acval_erase d ty₂ hta₂
  have hDA : DefEq μ env m.base.cval φ (Δa.map AVExpr.erase)
      ta₁.erase ta₂.erase :=
    defeqR_at m fuel hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂
      hAe₁ hAe₂
  obtain ⟨hwo₁, hbo₁, hLo₁, hCo₁⟩ :=
    frame_openR (n := n₁) (A := ta₁.erase) hcl hwt₁ hbt₁ hwb₁ hbb₁
      hLt₁ hLb₁ hCt₁ hCb₁ hAe₁
  have hCo₂ : CtxOkR μ m.base.cval env φ (d + 1)
      (ta₁.erase :: Δa.map AVExpr.erase)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) :=
    CtxOkR.openCong (n := n₂) hcl hCb₂ hCt₂ hAe₂ hwt₂.fvarsBelow hDA
  have hdom : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ ta₁ = interp2 V σ ta₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      hoT₁ hoT₂
  refine ⟨hdom ρ hρ, ?_⟩
  intro x hx
  refine ihd (Δa := ta₁ :: Δa) hdd hwo₁ hbo₁ hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (Setlec.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) (fun l hl => ?_)
    hCo₁ hCo₂ hva₁ hva₂ hoB₁
    (fun σ hσ => hoB₂ σ (Sat2.head_congr hdom hσ)) (cons x ρ)
    (Sat2_cons V hρ hx)
  rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
  · exact hLb₂ l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbt₂
    · exact hLt₂ l h3

/-- **The generation's gate, paid.**  `CtxOk2.openCong` — the annotated
`openCong` seal 11's context move needs at all five congruence sites —
is dischargeable from `DefEqClaims2C` and nothing else.  Its `hok₁` and
`hok₂` are *literally* the claim's two hoisted premises, and its `hdom`
is the claim's conclusion with `ρ` and `Sat2` still abstracted; the
`AnnotOk2` arguments `hdom` also takes are discarded, because the
hoisted premises already supply them at every `ρ`.

`not_openCongLocal` shows there is no version of this lemma the
generation-three claim could have paid, *even with the left domain
fully certified*.  So this theorem is the mechanized answer to the one
question generation four exists to settle, at the site that asked it.

**What it does not claim.**  Generation four moves the quantifier, not
the currency: `DefEqClaims2C` still takes `CtxOkR` of the two domains,
so both context hypotheses appear here.  That is generation five's
seam, and it is the *only* thing separating this statement from the
congruence proof above using `CtxOk2.openCong` in place of
`CtxOkR.openCong`. -/
theorem binder_ctxOk2_openCong {m : EnvS2U V env} {fuel F d : Nat}
    {Δa : List AVExpr} {n₂ : Name} {ty₁ ty₂ bd₂ : Expr}
    {ta₁ ta₂ : AVExpr}
    (ihd : DefEqClaims2C μ m φ fuel)
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty₂)
    (hKb₂ : CtxOk2 m μ φ F d Δa bd₂)
    (hKt₂ : CtxOk2 m μ φ F d Δa ty₂)
    (hta₁ : denote2 μ m.acval env φ F d ty₁ = some ta₁)
    (hta₂ : denote2 μ m.acval env φ F d ty₂ = some ta₂)
    (hoT₁ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₁)
    (hoT₂ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₂) :
    CtxOk2 m μ φ F (d + 1) (ta₁ :: Δa)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) :=
  CtxOk2.openCong hKb₂ hKt₂ hta₂ hoT₁ hoT₂
    (fun σ hσ _ _ => ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂
      hta₁ hta₂ hoT₁ hoT₂ σ hσ)

/-- **The gate is not vacuously paid.**  Every premise of
`binder_ctxOk2_openCong` *except the induction hypothesis and the
checker's own verdict* is met at a concrete one-binder instance:
`d = 0`, `Δa = []`, both domains `⟪Sort 0⟫`, right body `.bvar 0`.  So
the discharge above is a real one, not an implication out of
contradictory hypotheses — the trap that seal 11 warns comes back clean
without being a clean bill of health, applied here anyway.

`ihd` and `hdt` stay parameters deliberately.  A `DefEqClaims2C` at a
fuel large enough for a positive `isDefEqCore` verdict is exactly what
the campaign is building; manufacturing one here would be circular, and
taking `fuel = 0` — where the claim holds vacuously — makes `hdt`
unsatisfiable and the witness worthless.  Naming that is the honest
report; the remaining premises are the ones a congruence site has to
find, and they are all met. -/
theorem binder_ctxOk2_openCong_sat (m : EnvS2U V env) (fuel F : Nat)
    (nm : Name) (ihd : DefEqClaims2C μ m φ fuel)
    (hdt : isDefEqCore μ env fuel 0 (.sort .zero) (.sort .zero)
      = .ok true) :
    CtxOk2 m μ φ F 1 [AVExpr.sort 0]
      ((Expr.bvar 0).instantiate1 (.fvar 0 nm (.sort .zero))) :=
  binder_ctxOk2_openCong (ta₁ := .sort 0) (ta₂ := .sort 0) ihd hdt
    (by simp [Expr.WScoped]) rfl
    (fun l hl => by simp [Expr.fvarLeaves] at hl)
    (CtxOkR.nil (by simp [Expr.fvarLeaves]))
    (by simp [Expr.WScoped]) rfl
    (fun l hl => by simp [Expr.fvarLeaves] at hl)
    (CtxOkR.nil (by simp [Expr.fvarLeaves]))
    (CtxOk2.of_fvarLeaves_nil rfl (by simp [Expr.fvarLeaves]))
    (CtxOk2.of_fvarLeaves_nil rfl (by simp [Expr.fvarLeaves]))
    (by rw [denote2]; rfl) (by rw [denote2]; rfl)
    (fun _ _ => by simp) (fun _ _ => by simp)

/-- **`DefEqStuck2C`**: the same ten of the seventeen cases, hoisted.
Every `AnnotOk2` the block needs it gets from the node it is looking
at, in hoisted form — `AnnotOk2.hoist_app` for the two `Nat.succ`
orders, `hoist_pi`/`hoist_lam` for the congruences, `hoist_proj` for
`proj`, and for both string cases the constructor form *is* the
literal's own annotation, so the premise transfers unchanged. -/
theorem defeqStuck_claim2C {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2C μ m φ fuel) (hsi : StuckIrrel2C μ m φ fuel)
    (hstr : Denote2StrLit2A μ m φ) (hap : AcvalParams2 m)
    (hbs : BinderSortAgree2A μ env φ fuel F)
    (happ : AppCongrStuck2C μ m φ fuel) (heta : EtaCert2C μ m φ fuel) :
    ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
      {a b a' b' : Expr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      (a == b) = false →
      whnfCore μ env fuel d a = .ok a' →
      whnfCore μ env fuel d b = .ok b' →
      (a' == b') = false →
      Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
      Setlec.unfoldableHead env a' = false →
      Setlec.unfoldableHead env b' = false →
      Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a' →
      Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b' →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b' →
      ∀ {aa' ba' : AVExpr},
        denote2 μ m.acval env φ F d a' = some aa' →
        denote2 μ m.acval env φ F d b' = some ba' →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa') →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba') →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ aa' = interp2 V ρ ba' := by
  intro d Δa _k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb aa' ba' hda hdb hokA hokB ρ hρ
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold, Setlec.defeq_def,
    Setlec.defEqList_fold, Setlec.etaCert_fold] at h
  rw [if_neg (by simpa using hab), hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : Setlec.stuckIrrelP μ env fuel d a' b' = .ok true →
      interp2 V ρ aa' = interp2 V ρ ba' := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  clear hab hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort
  · rename_i u v
    rw [denote2_sort] at hda hdb
    obtain rfl : aa' = AVExpr.sort (u.eval φ) :=
      (Option.some.inj hda).symm
    obtain rfl : ba' = AVExpr.sort (v.eval φ) :=
      (Option.some.inj hdb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [Setlec.liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true => rw [Level.isEquiv_sound hle φ]
  -- 2: lit/lit
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : aa' = ba' := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  -- 3: `lit 0` against `Nat.zero`
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
      rw [denote2_natZeroConst hg] at hdb
      obtain rfl : ba' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0`
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
      rw [denote2_natZeroConst hg] at hda
      obtain rfl : aa' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hda).symm
      rfl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hdb
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwb hbb hLb hCb
        refine deqStep2_appCong rfl
          (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
            (CtxOkR.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves]))
            hCx (denote2_natLit hg) hxa (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA := hokA σ hσ
          simp only [natLitT2, AnnotOk2_app] at hA
          exact hA.2.1
        · have hB := hokB σ hσ
          rw [AnnotOk2_app] at hB
          exact hB.2.1
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)`
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hda
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwa hba hLa hCa
        refine deqStep2_appCong rfl
          (ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOkR.of_fvarLeaves_nil hCb.1 (by simp [Expr.fvarLeaves]))
            hxa (denote2_natLit hg) (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA := hokA σ hσ
          rw [AnnotOk2_app] at hA
          exact hA.2.1
        · have hB := hokB σ hσ
          simp only [natLitT2, AnnotOk2_app] at hB
          exact hB.2.1
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hda
      exact ihd h hwc hbc hLc hwb hbb hLb
        (CtxOkR.of_fvarLeaves_nil hCa.1 hnil) hCb hdc hdb hokA
        hokB ρ hρ
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hdb
      exact ihd h hwa hba hLa hwc hbc hLc hCa
        (CtxOkR.of_fvarLeaves_nil hCb.1 hnil) hda hdc hokA hokB ρ hρ
    · exact hfall h
  -- 9: the same de Bruijn level
  · rename_i i n₁ t₁ j n₂ t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denote2_fvar] at hda hdb
      obtain rfl : aa' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hda).symm
      obtain rfl : ba' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [Setlec.liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : aa' = ba' := acval_const_congr2 hap hle hda hdb
          rfl
    · exact hfall h
  -- 11: ∀-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, _u₁, v₁, hta₁, hva₁, -, hv₁, rfl⟩ :=
        denote2_forallE_inv hda
      obtain ⟨ta₂, ba₂, _u₂, v₂, hta₂, hva₂, -, hv₂, rfl⟩ :=
        denote2_forallE_inv hdb
      obtain rfl : v₁ = v₂ := hbs.1 h hv₁ hv₂
      obtain ⟨hoT₁, hoB₁⟩ := AnnotOk2.hoist_pi hokA
      obtain ⟨hoT₂, hoB₂⟩ := AnnotOk2.hoist_pi hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2C ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      exact deqStep2_piCong hDA hDB
  -- 12: λ-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, v₁, hta₁, hva₁, hv₁, rfl⟩ :=
        denote2_lam_inv hda
      obtain ⟨ta₂, ba₂, v₂, hta₂, hva₂, hv₂, rfl⟩ :=
        denote2_lam_inv hdb
      obtain rfl : v₁ = v₂ := hbs.2 h hv₁ hv₂
      obtain ⟨hoT₁, hoB₁⟩ := AnnotOk2.hoist_lam hokA
      obtain ⟨hoT₂, hoB₂⟩ := AnnotOk2.hoist_lam hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2C ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      exact deqStep2_lamCong hDA hDB
  -- 13: the stuck spine congruence
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore μ env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : Setlec.defEqListP μ env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          exact happ hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb
            hda hdb hokA hokB ρ hρ
    · exact hfall h
  -- 14: the stuck projection congruence
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore μ env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        obtain ⟨ia₁, he₁, -, rfl⟩ := denote2_proj_inv hda
        obtain ⟨ia₂, he₂, -, rfl⟩ := denote2_proj_inv hdb
        simp only [Expr.WScoped] at hwa hwb
        simp only [Expr.looseBVarsBounded] at hba hbb
        exact deqStep2_projCong (ihd hde hwa hba
          (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
          hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
          (CtxOkR.of_subset
          (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
          he₁ he₂ (AnnotOk2.hoist_proj hokA)
          (AnnotOk2.hoist_proj hokB) ρ hρ)
    · exact hfall h
  -- 15: one-sided λ on the left
  · rename_i n₁ ty₁ bd₁ mb₁ hnl
    cases he : Setlec.etaCertP μ env fuel d n₁ ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact heta he hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA
        hokB ρ hρ
    | false => exact hfall h
  -- 16: one-sided λ on the right
  · rename_i n₂ ty₂ bd₂ mb₂ hnl
    cases he : Setlec.etaCertP μ env fuel d n₂ ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (heta he hwb hbb hLb hwa hba hLa hCb hCa hdb hda hokB
        hokA ρ hρ).symm
    | false => exact hfall h
  -- 17: distinct stuck heads
  · exact hfall h

/-! ### The assembly, hoisted

Ten residues, exactly as at the `…A` lane: four of them
(`Denote2Delta2A`, `Denote2StrLit2A`, `AcvalParams2`,
`BinderSortAgree2A`) are literally the same objects, because they
carry no `AnnotOk2` for the generation to move. -/

/-- **The quarter's deliverable at generation four.**

Closed here, exactly as at the `…A` lane: the loop's budget recursion,
the syntactic fast path, both `whnfCore` rewrites and their fuel join,
all four lazy-delta decisions with the same-head short-circuit's
plumbing, and ten of the stuck block's seventeen cases.

And, unlike the `…A` lane, the conclusion is the **canonical claim**:
`DefEqClaims2C` is already stated with the two `AnnotOk2` as premises,
so there is no `…P` currency left over and no `defEqStep2B_toAP`-style
gap note to write.  Generation three's report to the junction —
"the conclusion is `DefEqClaims2AP`, not `DefEqClaims2A`" — is
answered by the statement itself. -/
theorem defEqStep2C_of
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2C μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2C μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2C μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2C μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2C μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2C μ m φ fuel) :
    DefEqStep2C μ V := by
  intro env m φ fuel ihwc _ihw ihd _ihi
  refine defeq_claims2C (defeqStep_claim2C ihwc (hdel env m φ)
    (hnat env m φ fuel) (hpi env m φ fuel) ?_ (hspine env m φ fuel))
  intro d Δa k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb F aa' ba' hda hdb
  exact defeqStuck_claim2C ihd (hsi env m φ fuel) (hstr env m φ)
    (hap env m) (hbs env φ fuel F) (happ env m φ fuel)
    (heta env m φ fuel) h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb hda hdb


/-! ### The seven hoists are weakenings, mechanized

Each hoisted residue is *implied by* its `…A` twin: the hoisted premise
specialises to the ρ-local one.  Recorded as theorems rather than as
prose because the direction is the whole safety argument of this
generation for the suppliers — a hoisted premise is a **stronger**
hypothesis, so no supplier who has already discharged the `…A` shape
owes anything new, and nobody can have been handed extra work
silently.

The reverse implications do **not** hold, and must not be added:
`not_openCongLocal` is precisely the statement that a ρ-local
`AnnotOk2` cannot be recovered from a valuation-by-valuation one. -/

theorem proofIrrel2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : ProofIrrel2A μ m φ fuel) : ProofIrrel2C μ m φ fuel := by
  intro d a b Δa hr hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
    hokA hokB ρ hρ
  exact h hr hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ (hokA ρ hρ)
    (hokB ρ hρ)

theorem defEqSpine2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : DefEqSpine2A μ m φ fuel) : DefEqSpine2C μ m φ fuel := by
  intro d a b Δa hr hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
    hokA hokB ρ hρ
  exact h hr hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ (hokA ρ hρ)
    (hokB ρ hρ)

theorem stuckIrrel2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : StuckIrrel2A μ m φ fuel) : StuckIrrel2C μ m φ fuel := by
  intro d a b Δa hr hwa hba hLa hwb hbb hLb hCa hCb F aa ba hda hdb
    hokA hokB ρ hρ
  exact h hr hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ (hokA ρ hρ)
    (hokB ρ hρ)

theorem appCongrStuck2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : AppCongrStuck2A μ m φ fuel) : AppCongrStuck2C μ m φ fuel := by
  intro d a b Δa hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb F aa ba
    hda hdb hokA hokB ρ hρ
  exact h hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ
    (hokA ρ hρ) (hokB ρ hρ)

theorem etaCert2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : EtaCert2A μ m φ fuel) : EtaCert2C μ m φ fuel := by
  intro d n ty bd b mb Δa he hwa hba hLa hwb hbb hLb hCa hCb F aa ba
    hda hdb hokA hokB ρ hρ
  exact h he hwa hba hLa hwb hbb hLb hCa hCb hda hdb ρ hρ (hokA ρ hρ)
    (hokB ρ hρ)

theorem defEqStuck2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : DefEqStuck2A μ m φ fuel) : DefEqStuck2C μ m φ fuel := by
  intro d Δa k a b a' b' hs hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb F aa' ba' hda hdb hokA hokB ρ hρ
  exact h hs hab hwca hwcb hab' hir hna hnb hha hhb hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb ρ hρ (hokA ρ hρ) (hokB ρ hρ)

/-- The literal acceleration also has to re-package its *output*: the
`…A` shape delivers reduct-`AnnotOk2` and the equality together under
one `∀ ρ`, the hoisted one delivers them apart.  Both come from the
same application. -/
theorem reduceNat2C_of_A {m : EnvS2U V env} {fuel : Nat}
    (h : ReduceNat2A μ m φ fuel) : ReduceNat2C μ m φ fuel := by
  intro d e e₂ Δa F ea hr hws hb hLb hC hde hok
  obtain ⟨F', ea₂, hle, hd2, hR, hw2, hb2, hL2, hC2⟩ :=
    h hr hws hb hLb hC hde
  exact ⟨F', ea₂, hle, hd2, fun ρ hρ => (hR ρ hρ (hok ρ hρ)).2,
    fun ρ hρ => (hR ρ hρ (hok ρ hρ)).1, hw2, hb2, hL2, hC2⟩

/-- **The quarter's deliverable from the `…A` residues.**  Generation
four costs the ten suppliers nothing: hand `defEqStep2C_of` exactly the
obligations the `…A` lane already routed and it delivers the canonical
generation-four claim. -/
theorem defEqStep2C_of_A
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2A μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2A μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2A μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2A μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2A μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2A μ m φ fuel) :
    DefEqStep2C μ V :=
  defEqStep2C_of hdel
    (fun env m φ fuel => reduceNat2C_of_A (hnat env m φ fuel))
    (fun env m φ fuel => proofIrrel2C_of_A (hpi env m φ fuel))
    (fun env m φ fuel => defEqSpine2C_of_A (hspine env m φ fuel))
    (fun env m φ fuel => stuckIrrel2C_of_A (hsi env m φ fuel))
    hstr hap hbs
    (fun env m φ fuel => appCongrStuck2C_of_A (happ env m φ fuel))
    (fun env m φ fuel => etaCert2C_of_A (heta env m φ fuel))


/-! # Generation five — the definitional-equality quarter, one currency

`Claims2D` carries `CtxOk2D` in all four claims, so the seam this
quarter has been carrying since seal 11 — `CtxOkR` for the recursive
call and `CtxOk2` for `openCong`, at the same site, with
`not_ctxOk2R` forbidding the bridge — **closes**.  The visible effect
is at the two binder congruences: `binder_congr2D` below builds the
opened contexts with `CtxOk2D.openS` and `CtxOk2D.openCongC` and
touches no erasure at all, where `binder_congr2C` had to run
`denote2_erase`, `defeqR_at`, `frame_openR` and `CtxOkR.openCong` to
get the same two objects.  Seven lines become two.

The cost is the fuel index.  `CtxOkR` is fuel-free, `CtxOk2D` is not,
so every place this quarter joins two fuels — the two `whnfCore`
reducts at `max`, the four δ branches, the two `reduceNat` branches —
now moves the *context* with `CtxOk2D.fuelMono` as well as the
annotation with `denote2_fuelMono`.  That is mechanical and it is the
whole of the extra work.
-/

/-- The continuation's contract, in one currency.  The context
hypotheses move inside `∀ {F}` — the reordering `Claims2D` forces on
every consumer. -/
def DefEqCont2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AVExpr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **One iteration of the lazy-delta loop**, in one currency. -/
def DefEqStepAt2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool},
    DefEqCont2D μ m φ d k →
    ∀ {a b : Expr} {Δa : List AVExpr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      ∀ {F : Nat} {aa ba : AVExpr},
        CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
        denote2 μ m.acval env φ F d a = some aa →
        denote2 μ m.acval env φ F d b = some ba →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ aa = interp2 V ρ ba

/-- The loop satisfies the contract at every budget. -/
theorem defeqLoop_cont2D {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2D μ m φ fuel) :
    ∀ (budget d : Nat),
      DefEqCont2D μ m φ d
        (defeqLoop μ (pureFns μ env fuel) env d budget) := by
  intro budget
  induction budget with
  | zero =>
    intro d a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d a b Δa h
    rw [defeqLoop] at h
    exact hstep (ih d) h

/-- **`DefEqClaims2D` at `fuel + 1`**, modulo the step. -/
theorem defeq_claims2D {m : EnvS2U V env} {fuel : Nat}
    (hstep : DefEqStepAt2D μ m φ fuel) :
    DefEqClaims2D μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb F aa ba hCa hCb hda hdb
  rw [Setlec.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_cont2D hstep defeqLoopFuel d h hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb

/-! ### The step's obligations, in one currency

`Denote2Delta2A`, `Denote2StrLit2A`, `AcvalParams2` and
`BinderSortAgree2A` mention no context at all and are reused verbatim
for the second generation running — the same argument as at seal 14,
now for the currency rather than the quantifier. -/

/-- **Residue 3 — proof irrelevance.** -/
def ProofIrrel2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.proofIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 4 — the literal acceleration.** -/
def ReduceNat2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {F : Nat}
    {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk2D m μ φ F d Δa e →
    denote2 μ m.acval env φ F d e = some ea →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
    ∃ F' ea₂, F ≤ F' ∧
      denote2 μ m.acval env φ F' d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea₂) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOk2D m μ φ F' d Δa e₂

/-- **Residue 5 — the same-head spine short-circuit.** -/
def DefEqSpine2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.defeqSpineP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **The stuck configuration**, in one currency. -/
def DefEqStuck2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
    Setlec.unfoldableHead env a' = false →
    Setlec.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    ∀ {F : Nat} {aa' ba' : AVExpr},
      CtxOk2D m μ φ F d Δa a' → CtxOk2D m μ φ F d Δa b' →
      denote2 μ m.acval env φ F d a' = some aa' →
      denote2 μ m.acval env φ F d b' = some ba' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa') →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba') →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa' = interp2 V ρ ba'

/-- **Residue 6 — `stuckIrrel`.** -/
def StuckIrrel2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.stuckIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 10 — the stuck spine congruence.** -/
def AppCongrStuck2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    Setlec.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a → CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 11 — the η certificate.** -/
def EtaCert2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty bd b : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr},
    Setlec.etaCertP μ env fuel d n ty bd mb b = .ok true →
    Expr.WScoped d (.lam n ty bd mb) →
    (Expr.lam n ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa (.lam n ty bd mb) →
      CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d (.lam n ty bd mb) = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- The δ package, in one currency: the annotation does not move but
the context does — one `fuelMono` and one `of_subset`. -/
theorem delta_package2D {m : EnvS2U V env}
    (hdel : Denote2Delta2A μ m φ)
    {F d : Nat} {Δa : List AVExpr} {x y : Expr} {xa : AVExpr}
    (hu : Setlec.unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x) (hC : CtxOk2D m μ φ F d Δa x)
    (hx : denote2 μ m.acval env φ F d x = some xa) :
    ∃ F', F ≤ F' ∧ denote2 μ m.acval env φ F' d y = some xa ∧
      Expr.WScoped d y ∧ y.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded y ∧ CtxOk2D m μ φ F' d Δa y := by
  obtain ⟨F', hle, hy⟩ := hdel hu hx
  exact ⟨F', hle, hy, unfoldDefinition_WScoped m.base.wf hu hws,
    unfoldDefinition_looseBVars m.base.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.base.wf hu l hl),
    (CtxOk2D.fuelMono hle hC).of_subset
      (unfoldDefinition_fvarLeaves m.base.wf hu)⟩

/-- **`DefEqStepAt2D`**, modulo the five obligations above.  Structure
identical to the `…C` lane; every `denote2_fuelMono` on an annotation
is now accompanied by a `CtxOk2D.fuelMono` on the context that goes
with it. -/
theorem defeqStep_claim2D {m : EnvS2U V env} {fuel : Nat}
    (ihwc : WhnfCoreClaims2D μ m φ fuel)
    (hdel : Denote2Delta2A μ m φ)
    (hnat : ReduceNat2D μ m φ fuel) (hpi : ProofIrrel2D μ m φ fuel)
    (hstk : DefEqStuck2D μ m φ fuel)
    (hspine : DefEqSpine2D μ m φ fuel) :
    DefEqStepAt2D μ m φ fuel := by
  intro d k hk a b Δa h hwa hba hLa hwb hbb hLb F aa ba hCa hCb
    hda hdb hokA hokB ρ hρ
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold,
    Setlec.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · cases hwca : whnfCore μ env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore μ env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨Fa, aa', hFa, hda0, hokA', hEa, hwa', hba', hLa',
      hCa0⟩ :=
      whnfCore_package2D m ihwc hwca hwa hba hLa hCa hda hokA
    obtain ⟨Fb, ba', hFb, hdb0, hokB', hEb, hwb', hbb', hLb',
      hCb0⟩ :=
      whnfCore_package2D m ihwc hwcb hwb hbb hLb hCb hdb hokB
    have hEA := hEa ρ hρ
    have hEB := hEb ρ hρ
    -- the two reducts, joined at one fuel; the annotations do not move
    have hda' : denote2 μ m.acval env φ (max Fa Fb) d a' = some aa' :=
      denote2_fuelMono (Nat.le_max_left Fa Fb) d a' hda0
    have hdb' : denote2 μ m.acval env φ (max Fa Fb) d b' = some ba' :=
      denote2_fuelMono (Nat.le_max_right Fa Fb) d b' hdb0
    -- …and so do the two contexts
    have hCa' : CtxOk2D m μ φ (max Fa Fb) d Δa a' :=
      CtxOk2D.fuelMono (Nat.le_max_left Fa Fb) hCa0
    have hCb' : CtxOk2D m μ φ (max Fa Fb) d Δa b' :=
      CtxOk2D.fuelMono (Nat.le_max_right Fa Fb) hCb0
    -- from here every verdict is the middle equation
    suffices hmid : interp2 V ρ aa' = interp2 V ρ ba' from
      (hEA.trans hmid).trans hEB.symm
    clear hEA hEB hEa hEb hda hdb hda0 hdb0 hokA hokB hCa0 hCb0
      hCa hCb
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · cases hir : Setlec.proofIrrelP μ env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' hokA' hokB' ρ hρ
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : Setlec.reduceNatP μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨F₂, w, hle₂, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda' hokA'
          exact (hEw ρ hρ).trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2
              (CtxOk2D.fuelMono hle₂ hCb') hw
              (denote2_fuelMono hle₂ d b' hdb') hokw hokB' ρ hρ)
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : Setlec.reduceNatP μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨F₂, w, hle₂, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb' hokB'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2
            (CtxOk2D.fuelMono hle₂ hCa') hC2
            (denote2_fuelMono hle₂ d a' hda') hw hokA' hokw ρ
            hρ).trans (hEw ρ hρ).symm
        | none, hnb, h =>
        cases hha : Setlec.unfoldableHead env a' <;>
          cases hhb : Setlec.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca
            hwcb (by simpa using ‹¬(a' == b') = true›) hir hna hnb
            hha hhb hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
            hdb' hokA' hokB' ρ hρ
        · cases hub : Setlec.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2D hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2
              (CtxOk2D.fuelMono hle₂ hCa') hC2
              (denote2_fuelMono hle₂ d a' hda') hd2 hokA' hokB' ρ hρ
        · cases hua : Setlec.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package2D hdel hua hwa' hba' hLa' hCa' hda'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2
              (CtxOk2D.fuelMono hle₂ hCb') hd2
              (denote2_fuelMono hle₂ d b' hdb') hokA' hokB' ρ hρ
        · have hboth : ∀ {x : CheckM Bool},
              (match Setlec.unfoldDefinition env a',
                  Setlec.unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              interp2 V ρ aa' = interp2 V ρ ba' := by
            intro x hbb2
            cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : Setlec.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨FA, hleA, hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_package2D hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨FB, hleB, hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_package2D hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB
                (CtxOk2D.fuelMono (Nat.le_max_left FA FB) hCA)
                (CtxOk2D.fuelMono (Nat.le_max_right FA FB) hCB)
                (denote2_fuelMono (Nat.le_max_left FA FB) d a₂ hdA)
                (denote2_fuelMono (Nat.le_max_right FA FB) d b₂ hdB)
                hokA' hokB' ρ hρ
          cases hlt1 : Setlec.ReducibilityHint.lt
              (Setlec.headHint env b') (Setlec.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : Setlec.ReducibilityHint.lt
                (Setlec.headHint env a') (Setlec.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (Setlec.ReducibilityHint.sameRegular
                    (Setlec.headHint env a') (Setlec.headHint env b') &&
                  Setlec.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : Setlec.defeqSpineP μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' hokA' hokB' ρ hρ
                | false => exact hboth (x := pure false) h
            · cases hub : Setlec.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_package2D hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2
                  (CtxOk2D.fuelMono hle₂ hCa') hC2
                  (denote2_fuelMono hle₂ d a' hda') hd2 hokA'
                  hokB' ρ hρ
          · cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨F₂, hle₂, hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_package2D hdel hua hwa' hba' hLa' hCa' hda'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2
                (CtxOk2D.fuelMono hle₂ hCb') hd2
                (denote2_fuelMono hle₂ d b' hdb') hokA' hokB' ρ hρ


/-! ### The stuck configuration, one currency — seventeen cases -/

/-- An application's argument frame, in the new currency.  The
transpose of `frame_appArgR`; the context half is `CtxOk2D.app_arg`
and nothing else, so the helper exists only to keep the two `simp
only` unfoldings out of the stuck block. -/
theorem frame_appArg2D {m : EnvS2U V env} {F d : Nat}
    {Δa : List AVExpr} {f x : Expr}
    (hws : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f x))
    (hC : CtxOk2D m μ φ F d Δa (.app f x)) :
    Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOk2D m μ φ F d Δa x := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2,
    fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]), hC.app_arg⟩

/-- **The binder congruence's two premises, in one currency — the
generation's payoff, in the flesh.**

`binder_congr2C` had to manufacture the opened contexts through the
*erasure*: `denote2_erase` twice, `defeqR_at` to turn the checker's
verdict into a `DefEq` on erased annotations, `frame_openR` for the
left body and `CtxOkR.openCong` for the right.  All of that existed
only because the recursive call read `CtxOkR` while `openCong` read
`CtxOk2`, and `not_ctxOk2R` forbids translating between them.

Under one currency the two objects are two kit calls:
`CtxOk2D.openS` on the left (its own domain) and
`CtxOk2D.openCongC` on the right (the *left* domain, across the
domains' semantic agreement).  `hdom` is `ihd`'s own conclusion,
computed once and used for both the congruence's first component and
`openCongC`'s transport — which is exactly the reuse seal 14 predicted
and could not take. -/
theorem binder_congr2D {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2D μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {n₁ n₂ : Name}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AVExpr}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOk2D m μ φ F d Δa ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOk2D m μ φ F d Δa bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOk2D m μ φ F d Δa ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOk2D m μ φ F d Δa bd₂)
    (hta₁ : denote2 μ m.acval env φ F d ty₁ = some ta₁)
    (hva₁ : denote2 μ m.acval env φ F (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some ba₁)
    (hta₂ : denote2 μ m.acval env φ F d ty₂ = some ta₂)
    (hva₂ : denote2 μ m.acval env φ F (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some ba₂)
    (hoT₁ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₁)
    (hoT₂ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOk2 V σ ta₂)
    (hoB₁ : ∀ σ : Nat → V, Sat2 V (ta₁ :: Δa) σ → AnnotOk2 V σ ba₁)
    (hoB₂ : ∀ σ : Nat → V, Sat2 V (ta₂ :: Δa) σ → AnnotOk2 V σ ba₂)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ta₁ = interp2 V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp2 V ρ ta₁ →
        interp2 V (cons x ρ) ba₁ = interp2 V (cons x ρ) ba₂ := by
  have hdom : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ ta₁ = interp2 V σ ta₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      hoT₁ hoT₂
  have hLo₁ : Expr.LeavesBounded
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bd₁ 0 hl with h2 | h2
    · exact hLb₁ l h2
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbt₁
      · exact hLt₁ l h3
  have hLo₂ : Expr.LeavesBounded
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
    · exact hLb₂ l h2
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbt₂
      · exact hLt₂ l h3
  refine ⟨hdom ρ hρ, ?_⟩
  intro x hx
  exact ihd (Δa := ta₁ :: Δa) hdd
    (Expr.WScoped.instantiate1 hwt₁ 0 hwb₁)
    (Setlec.looseBVarsBounded_instantiate1 bd₁ 0 hbb₁) hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (Setlec.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) hLo₂
    (CtxOk2D.openS hCt₁ hCb₁ hta₁ hoT₁)
    (CtxOk2D.openCongC hCb₂ hCt₂ hta₂ hoT₂ hdom)
    hva₁ hva₂ hoB₁
    (fun σ hσ => hoB₂ σ (Sat2.head_congr hdom hσ)) (cons x ρ)
    (Sat2_cons V hρ hx)

/-- **`DefEqStuck2D`**: the same ten of the seventeen cases.  Every
context move is a kit call — `of_fvarLeaves_nil` at the two literal
cases and the two string cases, `app_arg` at the two `Nat.succ`
orders, `forallE_ty`/`forallE_body`, `lam_ty`/`lam_body` at the
congruences, `proj_arg` at the projection. -/
theorem defeqStuck_claim2D {m : EnvS2U V env} {fuel F : Nat}
    (ihd : DefEqClaims2D μ m φ fuel) (hsi : StuckIrrel2D μ m φ fuel)
    (hstr : Denote2StrLit2A μ m φ) (hap : AcvalParams2 m)
    (hbs : BinderSortAgree2A μ env φ fuel F)
    (happ : AppCongrStuck2D μ m φ fuel) (heta : EtaCert2D μ m φ fuel) :
    ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
      {a b a' b' : Expr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      (a == b) = false →
      whnfCore μ env fuel d a = .ok a' →
      whnfCore μ env fuel d b = .ok b' →
      (a' == b') = false →
      Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
      (if !a'.hasFvar && !b'.hasFvar then
        Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
      Setlec.unfoldableHead env a' = false →
      Setlec.unfoldableHead env b' = false →
      Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a' →
      Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b' →
      ∀ {aa' ba' : AVExpr},
        CtxOk2D m μ φ F d Δa a' → CtxOk2D m μ φ F d Δa b' →
        denote2 μ m.acval env φ F d a' = some aa' →
        denote2 μ m.acval env φ F d b' = some ba' →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa') →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba') →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ aa' = interp2 V ρ ba' := by
  intro d Δa _k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb aa' ba' hCa hCb hda hdb hokA hokB ρ hρ
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold, Setlec.defeq_def,
    Setlec.defEqList_fold, Setlec.etaCert_fold] at h
  rw [if_neg (by simpa using hab), hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : Setlec.stuckIrrelP μ env fuel d a' b' = .ok true →
      interp2 V ρ aa' = interp2 V ρ ba' := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  clear hab hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort
  · rename_i u v
    rw [denote2_sort] at hda hdb
    obtain rfl : aa' = AVExpr.sort (u.eval φ) :=
      (Option.some.inj hda).symm
    obtain rfl : ba' = AVExpr.sort (v.eval φ) :=
      (Option.some.inj hdb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [Setlec.liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true => rw [Level.isEquiv_sound hle φ]
  -- 2: lit/lit
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : aa' = ba' := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  -- 3: `lit 0` against `Nat.zero`
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
      rw [denote2_natZeroConst hg] at hdb
      obtain rfl : ba' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0`
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
      rw [denote2_natZeroConst hg] at hda
      obtain rfl : aa' = m.acval Setlec.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hda).symm
      rfl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hda
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hdb
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArg2D hwb hbb hLb hCb
        refine deqStep2_appCong rfl
          (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
            (CtxOk2D.of_fvarLeaves_nil hCa.length
              (by simp [Expr.fvarLeaves]))
            hCx (denote2_natLit hg) hxa (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA := hokA σ hσ
          simp only [natLitT2, AnnotOk2_app] at hA
          exact hA.2.1
        · have hB := hokB σ hσ
          rw [AnnotOk2_app] at hB
          exact hB.2.1
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)`
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote2_natLit_inv hdb
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denote2_app_inv hda
        rw [denote2_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval Setlec.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArg2D hwa hba hLa hCa
        refine deqStep2_appCong rfl
          (ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOk2D.of_fvarLeaves_nil hCb.length
              (by simp [Expr.fvarLeaves]))
            hxa (denote2_natLit hg) (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA := hokA σ hσ
          rw [AnnotOk2_app] at hA
          exact hA.2.1
        · have hB := hokB σ hσ
          simp only [natLitT2, AnnotOk2_app] at hB
          exact hB.2.1
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hda
      exact ihd h hwc hbc hLc hwb hbb hLb
        (CtxOk2D.of_fvarLeaves_nil hCa.length hnil) hCb hdc hdb
        hokA hokB ρ hρ
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr F d st hg hdb
      exact ihd h hwa hba hLa hwc hbc hLc hCa
        (CtxOk2D.of_fvarLeaves_nil hCb.length hnil) hda hdc hokA
        hokB ρ hρ
    · exact hfall h
  -- 9: the same de Bruijn level
  · rename_i i n₁ t₁ j n₂ t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denote2_fvar] at hda hdb
      obtain rfl : aa' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hda).symm
      obtain rfl : ba' = AVExpr.bvar (d - 1 - i) :=
        (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [Setlec.liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : aa' = ba' := acval_const_congr2 hap hle hda hdb
          rfl
    · exact hfall h
  -- 11: ∀-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, _u₁, v₁, hta₁, hva₁, -, hv₁, rfl⟩ :=
        denote2_forallE_inv hda
      obtain ⟨ta₂, ba₂, _u₂, v₂, hta₂, hva₂, -, hv₂, rfl⟩ :=
        denote2_forallE_inv hdb
      obtain rfl : v₁ = v₂ := hbs.1 h hv₁ hv₂
      obtain ⟨hoT₁, hoB₁⟩ := AnnotOk2.hoist_pi hokA
      obtain ⟨hoT₂, hoB₂⟩ := AnnotOk2.hoist_pi hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2D ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.forallE_ty
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.forallE_body
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.forallE_ty
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.forallE_body
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      exact deqStep2_piCong hDA hDB
  -- 12: λ-congruence
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, v₁, hta₁, hva₁, hv₁, rfl⟩ :=
        denote2_lam_inv hda
      obtain ⟨ta₂, ba₂, v₂, hta₂, hva₂, hv₂, rfl⟩ :=
        denote2_lam_inv hdb
      obtain rfl : v₁ = v₂ := hbs.2 h hv₁ hv₂
      obtain ⟨hoT₁, hoB₁⟩ := AnnotOk2.hoist_lam hokA
      obtain ⟨hoT₂, hoB₂⟩ := AnnotOk2.hoist_lam hokB
      obtain ⟨hDA, hDB⟩ := binder_congr2D ihd hdt h
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.lam_ty
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.lam_body
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.lam_ty
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.lam_body
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      exact deqStep2_lamCong hDA hDB
  -- 13: the stuck spine congruence
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore μ env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : Setlec.defEqListP μ env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          exact happ hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb
            hda hdb hokA hokB ρ hρ
    · exact hfall h
  -- 14: the stuck projection congruence
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore μ env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        obtain ⟨ia₁, he₁, -, rfl⟩ := denote2_proj_inv hda
        obtain ⟨ia₂, he₂, -, rfl⟩ := denote2_proj_inv hdb
        simp only [Expr.WScoped] at hwa hwb
        simp only [Expr.looseBVarsBounded] at hba hbb
        exact deqStep2_projCong (ihd hde hwa hba
          (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
          hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
          hCa.proj_arg hCb.proj_arg
          he₁ he₂ (AnnotOk2.hoist_proj hokA)
          (AnnotOk2.hoist_proj hokB) ρ hρ)
    · exact hfall h
  -- 15: one-sided λ on the left
  · rename_i n₁ ty₁ bd₁ mb₁ hnl
    cases he : Setlec.etaCertP μ env fuel d n₁ ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact heta he hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA
        hokB ρ hρ
    | false => exact hfall h
  -- 16: one-sided λ on the right
  · rename_i n₂ ty₂ bd₂ mb₂ hnl
    cases he : Setlec.etaCertP μ env fuel d n₂ ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (heta he hwb hbb hLb hwa hba hLa hCb hCa hdb hda hokB
        hokA ρ hρ).symm
    | false => exact hfall h
  -- 17: distinct stuck heads
  · exact hfall h

/-- **The quarter's deliverable at generation five.**  Ten routed
residues, the same ten as at the `…C` lane — the currency move retires
none of *this* quarter's obligations (it retires the `whnfCore`
quarter's `BetaCert2`), but it removes the erasure machinery from the
two congruences and the `CtxOk2`/`CtxOkR` double hypothesis from
`binder_ctxOk2_openCong`, which no longer needs to exist. -/
theorem defEqStep2D_of
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2D μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2D μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2D μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2D μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2D μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2D μ m φ fuel) :
    DefEqStep2D μ V := by
  intro env m φ fuel ihwc _ihw ihd _ihi
  refine defeq_claims2D (defeqStep_claim2D ihwc (hdel env m φ)
    (hnat env m φ fuel) (hpi env m φ fuel) ?_ (hspine env m φ fuel))
  intro d Δa k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb F aa' ba' hCa hCb hda hdb
  exact defeqStuck_claim2D ihd (hsi env m φ fuel) (hstr env m φ)
    (hap env m) (hbs env φ fuel F) (happ env m φ fuel)
    (heta env m φ fuel) h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb hda hdb

/-- **`defEqStep2E_of` — the defeq quarter against generation six.**

**This quarter was predicted nearly free and it is** (seal 31:
`DefEqClaims2D` has taken both annotations as premises since
generation four's hoist, so it was already dual-success).  The
prediction is exactly right about *defeq's own* factor —
`defEqClaims2D_of_2E` needs **no** existence residue at all, only the
fuel split instantiated at `F' := F` — and exactly wrong about the
quarter: `defeqStep_claim2D` consumes `ihwc : WhnfCoreClaims2D`, so
the quarter still needs `WhnfCoreExists2E`.

*The free claim is not the free quarter.*  A claim that produces
nothing can still be proved by a quarter that consumes a producer. -/
theorem defEqStep2E_of
    (hex : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), Exists2E μ m φ fuel)
    (hdel : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hnat : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2D μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2D μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2D μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2D μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (happ : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2D μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2D μ m φ fuel) :
    DefEqStep2E μ V := by
  intro env m φ fuel ihwc ihw ihd ihi
  obtain ⟨j1, j2, j3, j4⟩ :=
    claims2D_of_2E (hex env m φ fuel) ihwc ihw ihd ihi
  exact defEqClaims2E_of_2D
    (defEqStep2D_of hdel hnat hpi hspine hsi hstr hap hbs happ heta
      env m φ fuel j1 j2 j3 j4)

end Setlec.SetR.Interp2
