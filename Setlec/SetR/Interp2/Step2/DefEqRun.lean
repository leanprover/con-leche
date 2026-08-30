import Setlec.SetR.Interp2.Step2.Routed
import Setlec.SetR.Interp2.Step2.DefEq
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
   refutable at small fuel.  See `Denote2FuelDown`.
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

theorem denote2_bvar (acval : Name → (Name → Nat) → AVExpr)
    (fuel d i : Nat) :
    denote2 μ acval env φ fuel d (.bvar i) = none := by
  simp [denote2]

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
def Denote2FuelDown (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def DefEqCont2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def DefEqStepAt2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
theorem defeqLoop_cont2 {m : EnvS2 V env} {fuel : Nat}
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
theorem defeq_claims2 {m : EnvS2 V env} {fuel : Nat}
    (hfd : Denote2FuelDown μ m φ fuel)
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
def Denote2Delta2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def ProofIrrel2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def ReduceNat2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def DefEqSpine2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def DefEqStuck2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
theorem whnfCore_package2 {m : EnvS2 V env} {fuel d : Nat}
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
theorem delta_package2 {m : EnvS2 V env} {fuel : Nat}
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
theorem defeqStep_claim2 {m : EnvS2 V env} {fuel : Nat}
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
def StuckIrrel2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def Denote2StrLit2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def AcvalParams2 {env : Env} (m : EnvS2 V env) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      m.acval n ψ₁ = m.acval n ψ₂

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
def AppCongrStuck2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
def EtaCert2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
theorem defeqR_at (m : EnvS2 V env) (fuel : Nat) :
    DefEqClaimsR (mode := μ) m.base.toEnvR φ fuel :=
  (checkBridge (mode := μ) m.base.toEnvR φ fuel).2.2.1

/-- The same constant at level-equivalent instantiations has one
canonical annotation. -/
theorem acval_const_congr2 {m : EnvS2 V env} (hap : AcvalParams2 m)
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
theorem binder_congr2 {m : EnvS2 V env} {fuel : Nat}
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
theorem defeqStuck_claim2 {m : EnvS2 V env} {fuel : Nat}
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
    (hfd : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), Denote2FuelDown μ m φ fuel)
    (hdel : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), Denote2Delta2 μ m φ fuel)
    (hnat : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2 μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2 μ m φ fuel)
    (hspine : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2 μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2 μ m φ fuel)
    (hstr : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), Denote2StrLit2 μ m φ fuel)
    (hap : ∀ (env : Env) (m : EnvS2 V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel : Nat),
      BinderSortAgree2 μ env φ fuel)
    (happ : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2 μ m φ fuel)
    (heta : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
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

end Setlec.SetR.Interp2
