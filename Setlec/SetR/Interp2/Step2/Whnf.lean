import Setlec.SetR.Interp2.Step2.Loop
import Setlec.SetR.Interp2.Step2.Levels
import Setlec.SetR.Interp2.Claims2B
import Setlec.SetR.Bridge.WhnfCore

/-!
# `WhnfCoreStep2` / `WhnfStep2` — the discharge, and its two STOPs

The head-normalisation quarters of `CheckStep2`, aimed at
`Interp2/Step2/Routed.lean`'s `WhnfCoreStep2` and `WhnfStep2` with
`Bridge/WhnfCore.lean` as the template.  The case split transfers
verbatim — it is the same checker — but **the sealed claims cannot be
threaded through it**, for two independent reasons, one of them
refuted here mechanically.

## STOP 1 — the annotation's fuel is tied to the checker's

`WhnfCoreClaims2 μ m φ fuel` reads the subject's annotation at
`denote2 … fuel …`: the *same* numeral that indexes the checker call.
The knot decrements that numeral (`whnfCore … (fuel+1)` calls
`whnfCore … fuel`) and every reduction clause recurses, so the step
from `fuel` to `fuel + 1` must move a `denote2` fact from `fuel + 1`
down to `fuel` before the induction hypothesis will accept it.  That
move is `Denote2FuelDown`, and it is **false**: `denote2` is
`denote` *fused with the checker's own sort computation*, so the
annotation of any binder is undefined until the fuel suffices to run
`inferTypeCore` and `whnf` on it.  `denote2_fuelDown_false` below
exhibits the collapse at the smallest witness — at fuel `1` the
reduction loop cannot even take its first `whnfCore` step
(`whnf_one_error`), so `sortOfE` is `none` everywhere and no `∀`/`λ`
has an annotation at all, while at fuel `2` the smallest closed `∀`
does.

The repair is a *strengthening* and it is one binder wide:
**quantify the annotation fuel independently of the checker's**
(`WhnfCoreClaims2F` / `WhnfClaims2F` below).  Every recursive use then
instantiates the induction hypothesis at the *same* `F` the goal
carries and no fuel moves at all; and `WhnfCoreClaims2F.toClaims2`
checks that the repaired claim still implies the sealed one, so
nothing downstream loses.  Wiring it in edits `Claims2.lean`, which is
a junction decision, not a consumer's — the seal-3 precedent
(`Dispatch.lean`'s `CtxOk2`) is followed exactly.

## STOP 2 — the `interp2` equality is stated ungraded

`WhnfCoreClaims2` concludes

```
interp2 ρ ea = interp2 ρ ea' ∧ (AnnotOk2 ρ ea → AnnotOk2 ρ ea')
```

— the equality **outside** the truthfulness premise.  The quarter's
own Tier-A suppliers do not have that shape: `AnnotOk2_zeta`,
`AnnotOk2_beta_pos` and `AnnotOk2_beta_zero` all conclude
`interp2 ρ ea = interp2 ρ ea' ∧ AnnotOk2 ρ ea'` *from* `AnnotOk2 ρ ea`
(`Step2/WhnfCore.lean`'s docstring calls this "the claim's two
conjuncts exactly"; it is one implication away from being that).

For ζ the difference is harmless — the ζ equality really is
premise-free, and `whnfStep2_zeta_eq` below proves it so.  For β it is
not.  `interp2_beta_pos` needs `⟦a⟧ ∈ˢ ⟦A⟧` (off the domain
`app` is the canonical junk `∅`, `interp2_app_off_dom`), and that much
the clause's *own certificate* supplies through `InferClaims2` and
`DefEqClaims2`, exactly as `denote_beta_stepR` does on the v1 lane.
But `interp2_beta_zero` — the kind-`0` branch — needs the λ's whole
fibre package (`hbody`, `hB`), i.e. `AnnotOk2` of the redex's head,
and `whnfCoreBody` never infers the head: it whnf's it.  So the
kind-`0` β branch has **no supplier for the ungraded equality**, and
its graded twin is the one the design already built.

The repair is a *weakening*, and it is the shape the suppliers
already have: move the equality inside the premise
(`WhnfCoreClaims2R` below).  Unlike STOP 1's it changes what
downstream consumers get, so it is even more clearly a junction call.

## What is landed here

* the STOP-1 refutation, mechanically (`denote2_fuelDown_false`) and
  its ingredients, which are of independent interest: at fuel ≤ 1 the
  canonical annotation of every binder is `none`;
* the repaired claims, with `toClaims2` checking that repair 1 loses
  nothing;
* the clauses that need **neither** repair, at the sealed shape: the
  six leaves and `.bvar` (`whnfCore_leaf_claim2`, `denote2_bvar`);
* the ζ clause in the repaired currency, modulo one named residue
  (`Denote2Inst1`) whose v1 counterpart is `denote_beta` — evidence,
  not assertion, that repair 1 removes the fuel move and leaves only
  suppliers that already exist on the other lane;
* the routed obligations, at the checker's own function boundaries:
  `IotaStep2` (out of scope by campaign rule — the fired modeled-iota
  law over `interp2` is the migrating iota bottoms' to state),
  `ProjStep2`, `ReduceNatStep2`, `Delta2`, `Denote2Inst1` and
  `BetaCert2`;
* and, on top of those, **both quarters discharged in the repaired
  currency**: `whnfCoreStep2R_of` (`whnfCore_claims2R`, all nine
  cases) and `whnfStep2R_of` (`whnf_claims2R`, the budget induction
  over the loop's three exits).

**Read the tail before this list.**  Repair 1 was half a repair — the
*reduct's* annotation was still pinned to the subject's fuel — and the
`…R` lane above inherits that defect.  The file's last section
("STOP 2, and the corrected currency") carries the finished quarters
against `Claims2B.lean`: **`whnfCoreStep2B_of : WhnfCoreStep2B μ V`
and `whnfStep2B_of : WhnfStep2B μ V`.**  Two of the routed obligations
listed above are refuted there and replaced (`Delta2` → `Delta2B`,
`ProjStep2` → `ProjStep2B`); `ReduceNatStep2` survives verbatim.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level BinderMeta Literal whnf
  whnfCore whnfBody whnfLoop whnfStep whnfLoopFuel pureFns
  inferTypeCore iotaRecP reduceNatP unfoldDefinition)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## STOP 1: the annotation collapses below the loop's first step

`whnf` at fuel `1` runs its loop body once and that body's first move
is `whnfCore` at fuel `0`, which throws.  So `sortOfE` — infer, whnf
to a sort, evaluate — is `none` for *every* subject at fuel `1`, and
with it the annotation of every binder. -/

/-- At fuel `1` the reduction loop cannot take its first step. -/
theorem whnf_one_error (d : Nat) (t : Expr) :
    whnf μ env 1 d t
      = .error (.internal "fuel exhausted: whnfCore") := by
  obtain ⟨n, hn⟩ := Setlec.whnfLoopFuel_succ
  rw [Setlec.whnf_succ, whnfBody, hn, whnfLoop, whnfStep]
  simp [Setlec.whnfCore_def, Setlec.whnfCore_zero, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind]

/-- Hence no sort computes at fuel `1`. -/
theorem sortOfE_one (d : Nat) (e : Expr) :
    sortOfE μ env φ 1 d e = none := by
  rw [sortOfE]
  cases (inferTypeCore μ env 1 d e).toOption with
  | none => rfl
  | some t => simp [whnf_one_error, Except.toOption]

theorem lamSortE_one (d : Nat) (e : Expr) :
    lamSortE μ env φ 1 d e = none := by
  rw [lamSortE]
  cases (inferTypeCore μ env 1 d e).toOption with
  | none => rfl
  | some t => exact sortOfE_one d t

/-- …and no `∀` has a canonical annotation there. -/
theorem denote2_one_forallE
    {acval : Name → (Name → Nat) → AVExpr} (d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    denote2 μ acval env φ 1 d (.forallE n ty body mb) = none := by
  rw [denote2]
  simp [sortOfE_one]

/-- …nor any `λ`. -/
theorem denote2_one_lam
    {acval : Name → (Name → Nat) → AVExpr} (d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    denote2 μ acval env φ 1 d (.lam n ty body mb) = none := by
  rw [denote2]
  simp [lamSortE_one]

/-! ### …but one step up it does not

Fuel `2` is the first at which the loop returns: its `whnfCore` runs
at fuel `1`, whose leaf clauses are `pure`.  That is enough for the
smallest closed `∀`. -/

theorem whnf_two_sort (d : Nat) (u : Level) :
    whnf μ env 2 d (.sort u) = .ok (.sort u) := by
  obtain ⟨n, hn⟩ := Setlec.whnfLoopFuel_succ
  rw [Setlec.whnf_succ, whnfBody, hn, whnfLoop, whnfStep]
  simp [Setlec.whnfCoreBody, Setlec.reduceNat, unfoldDefinition,
    Expr.getAppFn, pure, Except.pure, Bind.bind, Except.bind]

theorem infer_two_sort (d : Nat) (u : Level) :
    inferTypeCore μ env 2 d (.sort u) = .ok (.sort (.succ u)) := by
  rw [Setlec.inferTypeCore_succ]
  simp [Setlec.inferBody, Setlec.viewM, Expr.view, pure, Except.pure,
    Bind.bind, Except.bind]

theorem sortOfE_two_sort (d : Nat) (u : Level) :
    sortOfE μ env φ 2 d (.sort u) = some (u.eval φ + 1) := by
  rw [sortOfE, infer_two_sort]
  simp only [Except.toOption]
  rw [whnf_two_sort]
  simp [Level.eval]

theorem denote2_two_sort {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) : denote2 μ acval env φ 2 d (.sort .zero)
      = some (.sort 0) := by
  rw [denote2]; simp [Level.eval]

/-- The witness: `∀ _ : Sort 0, Sort 0` annotates at fuel `2`. -/
theorem denote2_two_forallE {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (n : Name) (mb : BinderMeta) :
    denote2 μ acval env φ 2 d
        (.forallE n (.sort .zero) (.sort .zero) mb)
      = some (.pi 1 1 (.sort 0) (.sort 0)) := by
  rw [denote2, Expr.instantiate1_sort, denote2_two_sort,
    denote2_two_sort, sortOfE_two_sort, sortOfE_two_sort]
  simp [Level.eval]

/-- **The move the sealed claims need**, named so that its falsity is
on the record rather than in prose: the induction hypothesis speaks
about `denote2` at `fuel` and the goal hands it a fact at
`fuel + 1`. -/
def Denote2FuelDown (μ : CheckMode)
    (acval : Name → (Name → Nat) → AVExpr) (env : Env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e : Expr} {ea : AVExpr},
    denote2 μ acval env φ (fuel + 1) d e = some ea →
    denote2 μ acval env φ fuel d e = some ea

/-- **STOP 1, mechanically.**  Downward fuel transfer of the canonical
annotation fails, for every mode, environment, level assignment and
annotated valuation — already at `fuel = 1`, on a closed `∀` of
sorts. -/
theorem denote2_fuelDown_false
    (acval : Name → (Name → Nat) → AVExpr) :
    ¬ Denote2FuelDown μ acval env φ 1 := by
  intro h
  have hw := h (denote2_two_forallE (μ := μ) (env := env) (φ := φ)
    (acval := acval) 0 .anonymous default)
  rw [denote2_one_forallE] at hw
  exact nomatch hw

/-! ## The repaired claims

Two changes, independently motivated, each stated here and neither
wired into `Claims2.lean`.

`…F` is repair 1 alone — the annotation fuel `F` universally
quantified *inside* the claim, so that the knot's decrement never has
to be followed.  It is a strengthening: `toClaims2` recovers the
sealed claim by taking `F := fuel`.

`…R` adds repair 2 — the `interp2` equality graded on the subject's
truthfulness, which is the shape `AnnotOk2_zeta` /
`AnnotOk2_beta_pos` / `AnnotOk2_beta_zero` conclude in.  It is a
weakening and has no `toClaims2`. -/

/-- Repair 1 for the `whnfCore` claim. -/
def WhnfCoreClaims2F (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea' ∧
          (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea')

/-- Repair 1 for the loop claim. -/
def WhnfClaims2F (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea' ∧
          (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea')

/-- Repair 1 loses nothing: the sealed claim is the `F := fuel`
instance. -/
theorem WhnfCoreClaims2F.toClaims2 {m : EnvS2 V env} {fuel : Nat}
    (h : WhnfCoreClaims2F μ m φ fuel) :
    WhnfCoreClaims2 μ m φ fuel := by
  intro d e e' Δa hr hw hb hL hC ea hea
  exact h hr hw hb hL hC hea

theorem WhnfClaims2F.toClaims2 {m : EnvS2 V env} {fuel : Nat}
    (h : WhnfClaims2F μ m φ fuel) : WhnfClaims2 μ m φ fuel := by
  intro d e e' Δa hr hw hb hL hC ea hea
  exact h hr hw hb hL hC hea

/-- Repairs 1 **and** 2 for the `whnfCore` claim: the graded
conclusion the Tier-A step lemmas actually deliver. -/
def WhnfCoreClaims2R (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- Repairs 1 and 2 for the loop claim. -/
def WhnfClaims2R (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-! ## The clauses that need neither repair

The six leaves return their subject, so the reduct's annotation *is*
the subject's and both conjuncts are `whnfStep2_id` — at the sealed
shape, at any annotation fuel, and with no induction hypothesis.
`.bvar` is outside the annotated fragment and closes by definedness
alone. -/

/-- `denote2` has no clause for a loose `bvar`. -/
theorem denote2_bvar {acval : Name → (Name → Nat) → AVExpr}
    (F d i : Nat) :
    denote2 μ acval env φ F d (.bvar i) = none := by
  rw [denote2.eq_def]

/-- **The `.bvar` clause.**  Vacuous on the annotation side. -/
theorem whnfCore_bvar_claim2 (m : EnvS2 V env) {F d i : Nat}
    {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.bvar i) = some ea) :
    False := by
  rw [denote2_bvar] at hea; exact nomatch hea

/-- **The six leaf clauses**, at the sealed conclusion shape and at an
arbitrary annotation fuel — so this lemma serves `WhnfCoreClaims2`,
`WhnfCoreClaims2F` and `WhnfCoreClaims2R` alike. -/
theorem whnfCore_leaf_claim2 (m : EnvS2 V env) {F fuel d : Nat}
    {e e' : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx n ty, e = .fvar idx n ty) ∨
      (∃ n ty body bi, e = .forallE n ty body bi) ∨
      (∃ n ty body mb, e = .lam n ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore μ env (fuel + 1) d e = .ok e')
    (hea : denote2 μ m.acval env φ F d e = some ea) :
    ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea' ∧
        (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea') := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, n, ty, rfl⟩ |
      ⟨n, ty, body, bi, rfl⟩ | ⟨n, ty, body, mb, rfl⟩ |
      ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCoreR_sort, whnfCoreR_fvar, whnfCoreR_forallE,
        whnfCoreR_lam, whnfCoreR_const, whnfCoreR_lit,
        Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  exact ⟨ea, hea, fun ρ _ => whnfStep2_id (V := V) ea⟩

/-! ## ζ

The one reduction clause whose `interp2` equality really is
premise-free — `interp2`'s `letE` clause *is* the contractum's
reading — so ζ survives STOP 2 and is proved here ungraded.  What it
needs from outside is the annotated substitution law, `Denote2Inst1`:
the canonical annotation of `body.instantiate1 v` is the annotated
body's `inst` at the annotated value.  Its v1 counterpart is
`denote_beta` (`Verify/Denote/Inst.lean`); the annotated version is
the `SortSubstStable` lane's business, because the numerals have to
survive the substitution. -/

/-- Graded steps compose. -/
theorem step2_trans {ρ : Nat → V} {a b c : AVExpr}
    (h1 : AnnotOk2 V ρ a →
      interp2 V ρ a = interp2 V ρ b ∧ AnnotOk2 V ρ b)
    (h2 : AnnotOk2 V ρ b →
      interp2 V ρ b = interp2 V ρ c ∧ AnnotOk2 V ρ c) :
    AnnotOk2 V ρ a →
      interp2 V ρ a = interp2 V ρ c ∧ AnnotOk2 V ρ c := by
  intro hok
  obtain ⟨e1, o1⟩ := h1 hok
  obtain ⟨e2, o2⟩ := h2 o1
  exact ⟨e1.trans e2, o2⟩

/-- **The ζ equality, ungraded.**  Unlike `AnnotOk2_zeta`'s first
conjunct this needs no invariant. -/
theorem whnfStep2_zeta_eq {ρ : Nat → V} (Ta va ba : AVExpr) :
    interp2 V ρ (.letE Ta va ba) = interp2 V ρ (ba.inst va) := by
  rw [interp2_letE, interp2_inst0]

/-- **The annotated substitution residue.**  Supplier: the
`Annot/SimSubst.lean` lane (`SortSubstStable`), which is where the
canonical numerals' survival under the checker's own substitutions is
being settled; v1's counterpart is `denote_beta`. -/
def Denote2Inst1 (μ : CheckMode)
    (acval : Name → (Name → Nat) → AVExpr) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {n : Name} {ty val body : Expr}
    {ta va ba : AVExpr},
    denote2 μ acval env φ F d ty = some ta →
    denote2 μ acval env φ F d val = some va →
    denote2 μ acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some ba →
    denote2 μ acval env φ F d (body.instantiate1 val)
      = some (ba.inst va)

/-- **The ζ clause in the repaired currency** — the evidence that
repair 1 is the whole of STOP 1 at this clause: the induction
hypothesis is used at the goal's own `F`, no fuel moves, and the only
outside input is `Denote2Inst1`. -/
theorem whnfCore_letE_claim2F (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1 μ m.acval env φ)
    (ihwc : WhnfCoreClaims2F μ m φ fuel)
    {d : Nat} {nn : Name} {tt vv bb e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.letE nn tt vv bb) = .ok e')
    (hws : Expr.WScoped d (.letE nn tt vv bb))
    (hb : (Expr.letE nn tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE nn tt vv bb))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.letE nn tt vv bb))
    {F : Nat} {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.letE nn tt vv bb)
      = some ea) :
    ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea' ∧
        (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea') := by
  rw [Setlec.whnfCore_succ] at h
  simp only [Setlec.whnfCoreBody, Setlec.whnfCore_def] at h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  -- destructure the subject's annotation
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (bb.instantiate1 (.fvar d nn tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  -- the frame conditions of the contractum
  have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (bb.instantiate1 vv) :=
    fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
  have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (bb.instantiate1 vv) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
  obtain ⟨ea', hea', hstep⟩ :=
    ihwc h hwred hbred hLred hCred (hinst hta hva hba)
  refine ⟨ea', hea', fun ρ hρ => ⟨?_, ?_⟩⟩
  · rw [whnfStep2_zeta_eq, (hstep ρ hρ).1]
  · intro hok
    exact (hstep ρ hρ).2 (AnnotOk2_zeta V hok).2

/-- The ζ clause again, in the graded currency the assembly runs
in. -/
theorem whnfCore_letE_claim2R (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1 μ m.acval env φ)
    (ihwc : WhnfCoreClaims2R μ m φ fuel)
    {d : Nat} {nn : Name} {tt vv bb e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.letE nn tt vv bb) = .ok e')
    (hws : Expr.WScoped d (.letE nn tt vv bb))
    (hb : (Expr.letE nn tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE nn tt vv bb))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.letE nn tt vv bb))
    {F : Nat} {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.letE nn tt vv bb)
      = some ea) :
    ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
        interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  rw [Setlec.whnfCore_succ] at h
  simp only [Setlec.whnfCoreBody, Setlec.whnfCore_def] at h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (bb.instantiate1 (.fvar d nn tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (bb.instantiate1 vv) :=
    fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
  have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (bb.instantiate1 vv) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
  obtain ⟨ea', hea', hstep⟩ :=
    ihwc h hwred hbred hLred hCred (hinst hta hva hba)
  refine ⟨ea', hea', fun ρ hρ => step2_trans (fun hok => ?_)
    (hstep ρ hρ)⟩
  exact AnnotOk2_zeta V hok

/-! ## The routed obligations

Stated at the checker's own function boundaries, in the repaired
currency, exactly as `Bridge/WhnfCore.lean` states `IotaStepR`,
`ProjStepR` and `ReduceNatStepR`. -/

/-- **The ι clause — out of scope by campaign rule.**  A fired
recursor application's reduct denotes, with the frame conditions the
recursive `whnfCore` call needs, and moves the interpretation only as
the fired modeled-iota law over `interp2` allows.  That law is the
migrating iota bottoms' to state (the T5 rule), so this consumer only
names the shape it will be used at. -/
def IotaStep2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e'' : Expr} {Δa : List AVExpr},
    iotaRecP μ env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e'' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea') ∧
        Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e'' ∧
        CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e''

/-- **The projection clause**, whole — at clause granularity for the
reason `ProjStepR` records: the clause whnf's its scrutinee and
expands string literals before the table is consulted, so a
reduct-granular obligation would leave two unproved steps outside it
rather than one inside. -/
def ProjStep2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {sn : Name} {i : Nat} {pe e' : Expr}
    {Δa : List AVExpr},
    whnfCore μ env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.proj sn i pe) →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d (.proj sn i pe) = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- **The literal-acceleration obligation** — the loop's first exit,
whose `Nat`-op machinery is not transposed to `interp2` yet. -/
def ReduceNatStep2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr},
    reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e₂ = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea') ∧
        Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₂ ∧
        CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e₂

/-- **The delta exit.**  Free *in principle* — `EnvS2.acval_defn` says
the unfolded body carries the constant's own canonical annotation
(`whnfStep2_delta`) — but the loop unfolds a *spine*, and the step
from the body's annotation to the applied spine's needs the annotated
`mkAppN` inversion that the v1 lane has as `denote_mkAppN_inv` and
this one does not.  Named rather than guessed. -/
def Delta2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {F : Nat} {ea : AVExpr},
    unfoldDefinition env e = some e' →
    denote2 μ m.acval env φ F d e = some ea →
    denote2 μ m.acval env φ F d e' = some ea

/-! ## The loop quarter, discharged

`whnfStep` is three moves and `whnfLoop` iterates it on its **own**
budget (`whnfLoopFuel`, `@[irreducible]`), so — exactly as the map
prescribes and `whnfLoop_claimR` does — the discharge is an induction
on that budget with the knot's `fuel` fixed.  In the repaired currency
nothing else is in the way: the three exits are `WhnfCoreClaims2R` at
`fuel`, `ReduceNatStep2` and `Delta2`, and the accumulated fact is the
graded step composed along the chain.

This closes `WhnfStep2`'s content modulo its two named residues. -/

/-- `whnfCore_packageR`'s transpose: the reduct's annotation fact
together with the frame conditions the loop's next iteration needs. -/
theorem whnfCore_package2R (m : EnvS2 V env) {fuel d F : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa : AVExpr}
    (ihwc : WhnfCoreClaims2R μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a)
    (haa : denote2 μ m.acval env φ F d a = some aa) :
    ∃ aa', denote2 μ m.acval env φ F d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa →
        interp2 V ρ aa = interp2 V ρ aa' ∧ AnnotOk2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' := by
  obtain ⟨aa', haa', hD⟩ := ihwc hw hws hb hLb hC haa
  exact ⟨aa', haa', hD, whnfCore_WScoped m.base.wf fuel hw hws,
    whnfCore_looseBVars m.base.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.base.wf fuel hw l hl),
    CtxOkR.of_subset (whnfCore_fvarLeaves m.base.wf fuel hw) hC⟩

/-- **The budget induction.**  Every iteration of the reduction loop
moves the annotated interpretation only as the three exits allow. -/
theorem whnfLoop_claim2R (m : EnvS2 V env) {fuel : Nat}
    (ihwc : WhnfCoreClaims2R μ m φ fuel)
    (hnat : ReduceNatStep2 μ m φ fuel) (hdelta : Delta2 μ m φ) :
    ∀ (budget : Nat) {d : Nat} {Δa : List AVExpr} {e e' : Expr},
      whnfLoop (pureFns μ env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
      ∀ {F : Nat} {ea : AVExpr},
        denote2 μ m.acval env φ F d e = some ea →
        ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
          ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
            interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δa e e' h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δa e e' h hws hb hLb hC F ea hea
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, Setlec.whnfCore_def] at h
    cases hwc : whnfCore μ env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨ea₁, hea₁, hD₁, hws₁, hb₁, hLb₁, hC₁⟩ :=
      whnfCore_package2R m ihwc hwc hws hb hLb hC hea
    cases hrn : reduceNatP μ env fuel d e₁ with
    | error err =>
      rw [Setlec.reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [Setlec.reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨ea₂, hea₂, hD₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hea₁
      obtain ⟨ea', hea', hD₃⟩ := ih h hws₂ hb₂ hLb₂ hC₂ hea₂
      exact ⟨ea', hea', fun ρ hρ =>
        step2_trans (step2_trans (hD₁ ρ hρ) (hD₂ ρ hρ)) (hD₃ ρ hρ)⟩
    | none, h =>
      dsimp only at h
      cases hud : unfoldDefinition env e₁ with
      | none =>
        rw [hud] at h
        exact ⟨ea₁, (Except.ok.inj h) ▸ hea₁, hD₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        obtain ⟨ea', hea', hD₃⟩ :=
          ih h (unfoldDefinition_WScoped m.base.wf hud hws₁)
            (unfoldDefinition_looseBVars m.base.wf hud hb₁)
            (fun l hl => hLb₁ l
              (unfoldDefinition_fvarLeaves m.base.wf hud l hl))
            (CtxOkR.of_subset
              (unfoldDefinition_fvarLeaves m.base.wf hud) hC₁)
            (hdelta hud hea₁)
        exact ⟨ea', hea', fun ρ hρ =>
          step2_trans (hD₁ ρ hρ) (hD₃ ρ hρ)⟩

/-- **`WhnfClaims2R` at `fuel + 1`** — the loop run at its own budget;
`whnfBody` *is* the loop. -/
theorem whnf_claims2R (m : EnvS2 V env) {fuel : Nat}
    (ihwc : WhnfCoreClaims2R μ m φ fuel)
    (hnat : ReduceNatStep2 μ m φ fuel) (hdelta : Delta2 μ m φ) :
    WhnfClaims2R μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb hC F ea hea
  rw [Setlec.whnf_succ, whnfBody] at h
  exact whnfLoop_claim2R m ihwc hnat hdelta whnfLoopFuel h hws hb hLb
    hC hea

/-- **The `WhnfStep2` quarter, routed.**  In the repaired currency the
loop needs neither the defeq nor the inference claim (`whnf_claimsR`
records the same), so the quarter is exactly: the `whnfCore` claim at
`fuel`, plus the two named exits. -/
theorem whnfStep2R_of
    (hnat : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2 μ m φ fuel)
    (hdelta : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Delta2 μ m φ) :
    ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
      WhnfCoreClaims2R μ m φ fuel → WhnfClaims2R μ m φ (fuel + 1) :=
  fun env m φ fuel ihwc =>
    whnf_claims2R m ihwc (hnat env m φ fuel) (hdelta env m φ)

/-! ## The application clause

Three sub-cases, from `whnf_app_inv`, exactly as `whnfCore_app_claimR`
splits them: β (certified), ι (routed) and stuck.  All three begin
with the head's own reduction through the induction hypothesis.

The β sub-case is where STOP 2 bites and where its cost is visible:
the redex's own `AnnotOk2` closes the **positive-kind** branch outright
(`AnnotOk2_beta_pos`), and the kind-`0` branch needs the argument's
domain membership on top — the fact `whnfCoreBody`'s own certificate
records and the v1 lane extracts with `ihi`/`ihd`.  Extracting it here
needs `InferClaims2`/`DefEqClaims2` *in the repaired currency* (STOP 1
hits all four claims, not just this quarter's two), so it is named at
the clause boundary rather than guessed. -/

/-- **The β site's argument certificate, in the annotated currency.**
Supplier: the inference and defeq quarters under repair 1; v1's
counterpart is the `ihi`/`ihd` composition inside
`denote_beta_stepR`. -/
def BetaCert2 (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {a ty ta : Expr} {F : Nat}
    {aa tya : AVExpr},
    inferTypeCore μ env fuel d a = .ok ta →
    Setlec.isDefEqCore μ env fuel d ta ty = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty →
    denote2 μ m.acval env φ F d a = some aa →
    denote2 μ m.acval env φ F d ty = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ aa ∈ˢ interp2 V ρ tya

/-- **The `.app` clause of the `whnfCore` quarter**, in the repaired
currency. -/
theorem whnfCore_app_claim2R (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1 μ m.acval env φ)
    (hcert : BetaCert2 μ m φ fuel) (hiota : IotaStep2 μ m φ fuel)
    (ihwc : WhnfCoreClaims2R μ m φ fuel)
    {d : Nat} {f a e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.app f a))
    {F : Nat} {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.app f a) = some ea) :
    ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
        interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) f :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  rw [denote2] at hea
  rcases hfa : denote2 μ m.acval env φ F d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote2 μ m.acval env φ F d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨f', hwf, hcase⟩ := Setlec.whnf_app_inv h
  obtain ⟨fa', hfa', hDf, hwf', hbf', hLf', hCf'⟩ :=
    whnfCore_package2R m ihwc hwf hws.1 hb.1 hLf hCf hfa
  have hiapp : denote2 μ m.acval env φ F d (.app f' a)
      = some (.app fa' aa) := by rw [denote2, hfa', haa]; rfl
  have hDapp : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (.app fa aa) →
      interp2 V ρ (.app fa aa) = interp2 V ρ (.app fa' aa) ∧
        AnnotOk2 V ρ (.app fa' aa) := by
    intro ρ hρ hok
    rw [AnnotOk2_app] at hok
    obtain ⟨hokf, hoka, v', A, B, h1, h2, h3⟩ := hok
    obtain ⟨heq, hokf'⟩ := hDf ρ hρ hokf
    refine ⟨by rw [interp2_app, interp2_app, heq], ?_⟩
    rw [AnnotOk2_app]
    exact ⟨hokf', hoka, v', A, B, heq ▸ h1, h2, h3⟩
  have hwapp : Expr.WScoped d (.app f' a) := by
    simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩
  have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hbf', hb.2⟩
  have hLapp : Expr.LeavesBounded (.app f' a) := fun l hl => by
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hLf' l hl
    · exact hLa l hl
  have hCapp : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.app f' a) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hCf'.2 l hl
    · exact hCa.2 l hl
  rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, ta, hta, hde⟩ |
    ⟨e'', hio, hwe''⟩ | rfl
  · -- β
    rw [denote2] at hfa'
    rcases htya : denote2 μ m.acval env φ F d ty with _ | tya
    · rw [htya] at hfa'; exact nomatch hfa'
    rw [htya] at hfa'
    rcases hbb : denote2 μ m.acval env φ F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hbb] at hfa'; exact nomatch hfa'
    rw [hbb] at hfa'
    rcases hkind : lamSortE μ env φ F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hkind] at hfa'; exact nomatch hfa'
    rw [hkind] at hfa'
    obtain rfl : fa' = .lam v tya ba := (Option.some.inj hfa').symm
    simp only [Expr.WScoped] at hwf'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLf' l (by simp [Expr.fvarLeaves, hl])
    have hCty : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
        ty :=
      CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
        hCf'
    have hwred : Expr.WScoped d (body.instantiate1 a) :=
      Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2
    have hbred : (body.instantiate1 a).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2
    have hLred : Expr.LeavesBounded (body.instantiate1 a) :=
      fun l hl => by
        rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
        · exact hLf' l (by simp [Expr.fvarLeaves, h2])
        · exact hLa l h2
    have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
        (body.instantiate1 a) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact hCf'.2 l (by simp [Expr.fvarLeaves, h2])
      · exact hCa.2 l h2
    obtain ⟨ea', hea', hD⟩ :=
      ihwc hbeta hwred hbred hLred hCred (hinst htya haa hbb)
    refine ⟨ea', hea', fun ρ hρ => step2_trans (hDapp ρ hρ) ?_⟩
    refine step2_trans (fun hok => ?_) (hD ρ hρ)
    by_cases hv : v = 0
    · subst hv
      exact AnnotOk2_beta_zero V hok
        (hcert hta hde hws.2 hb.2 hLa hCa hwf'.1 hbf'.1 hLty hCty
          haa htya ρ hρ)
    · exact AnnotOk2_beta_pos V hv hok
  · -- ι
    obtain ⟨ea₂, hea₂, hstep, hwe, hbe, hLe, hCe⟩ :=
      hiota hio hwapp hbapp hLapp hCapp hiapp
    obtain ⟨ea', hea', hD⟩ := ihwc hwe'' hwe hbe hLe hCe hea₂
    exact ⟨ea', hea', fun ρ hρ =>
      step2_trans (step2_trans (hDapp ρ hρ) (hstep ρ hρ)) (hD ρ hρ)⟩
  · -- stuck
    exact ⟨_, hiapp, hDapp⟩

/-! ## `WhnfCoreClaims2R` at `fuel + 1`

The nine cases assembled.  Six leaves and `.bvar` need nothing; ζ
needs `Denote2Inst1`; `.app` needs that plus `BetaCert2` and
`IotaStep2`; `.proj` is routed whole. -/

/-- **The `WhnfCoreStep2` quarter, routed**, in the repaired
currency. -/
theorem whnfCore_claims2R (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1 μ m.acval env φ)
    (hcert : BetaCert2 μ m φ fuel) (hiota : IotaStep2 μ m φ fuel)
    (hproj : ProjStep2 μ m φ fuel)
    (ihwc : WhnfCoreClaims2R μ m φ fuel) :
    WhnfCoreClaims2R μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb hC F ea hea
  match e with
  | .sort u =>
    obtain ⟨ea', hea', hD⟩ :=
      whnfCore_leaf_claim2 (Δa := Δa) m (Or.inl ⟨u, rfl⟩) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .fvar idx n ty =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inl ⟨idx, n, ty, rfl⟩)) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .forallE n ty body bi =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .lam n ty body mb =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩)))) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .const n us =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩))))) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .lit l =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))))) h hea
    exact ⟨ea', hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .bvar i => rw [denote2_bvar] at hea; exact nomatch hea
  | .letE nn tt vv bb =>
    exact whnfCore_letE_claim2R m hinst ihwc h hws hb hLb hC hea
  | .app f a =>
    exact whnfCore_app_claim2R m hinst hcert hiota ihwc h hws hb hLb
      hC hea
  | .proj sn i pe => exact hproj h hws hb hLb hC hea

/-- **`WhnfCoreStep2`, routed.**  The quarter's analogue in the
repaired currency: the four residues plus the induction hypothesis.
(The defeq and inference claims are not consumed — the β certificate
is what would consume them, and it is `BetaCert2`.) -/
theorem whnfCoreStep2R_of
    (hinst : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Denote2Inst1 μ m.acval env φ)
    (hcert : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), BetaCert2 μ m φ fuel)
    (hiota : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2 μ m φ fuel)
    (hproj : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2 μ m φ fuel) :
    ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
      WhnfCoreClaims2R μ m φ fuel →
        WhnfCoreClaims2R μ m φ (fuel + 1) :=
  fun env m φ fuel ihwc =>
    whnfCore_claims2R m (hinst env m φ) (hcert env m φ fuel)
      (hiota env m φ fuel) (hproj env m φ fuel) ihwc

/-! ## Closing note — what the two STOPs cost

Both quarters are discharged above **in the repaired currency**, and
the residues that remain are the ones the campaign already owns:
`IotaStep2` (the migrating iota bottoms'), `ProjStep2` and
`ReduceNatStep2` (v1's `ProjStepR` / `ReduceNatStepR` transposed),
`Denote2Inst1` (the `SortSubstStable` lane's), `Delta2` (an annotated
`mkAppN` inversion) and `BetaCert2` (the other two quarters, once they
are repaired too).  None of them is this seal's to state.

**Correction (STOP 2, below).**  The sentence that stood here — "and
none is refuted" — was wrong, and wrong in the way this campaign keeps
being wrong: it was written from the residues' provenance rather than
checked against the smallest fuel.  `Delta2` is refuted
(`delta2_refuted`) and `ProjStep2` is refuted (`projStep2_refuted`),
both by the witness that killed `EnvS2.acval_defn`.  The corrected
forms are `Delta2B`/`ProjStep2B`; `ReduceNatStep2` and `BetaCert2` do
survive, and `natOpResult_leaf` is why the first of those is not luck.

What *is* refuted is the sealed statement, twice:

1. `denote2_fuelDown_false` — mechanically, and the defect is in all
   four claims of `Claims2.lean`, not only this quarter's two: every
   body recurses through the knot at `fuel` while its claim reads the
   annotation at `fuel + 1`.  The four seals so far did not meet it
   because their clauses (`infer_sort_claim2`, `infer_fvar_claim2`,
   `infer_bvar_claim2`) are the three that do **not** recurse.
2. the ungraded `interp2` equality, which the kind-`0` β branch cannot
   supply and which the quarter's own Tier-A lemmas
   (`AnnotOk2_zeta`, `AnnotOk2_beta_pos`, `AnnotOk2_beta_zero`) do not
   have.  Repair 2 is exactly their shape.

*Rule: when a claim fuses a checker-computed object into its
statement, the object's own fuel must be quantified separately from
the checker's — the knot decrements one and not the other.  And a
claim's conclusion should be read off the suppliers it names, not
written first and matched later.*
-/

/-! # STOP 2, and the corrected currency

Repair 1 was half a repair.  It freed the **subject's** annotation
fuel from the run's, but left the **reduct's** annotation pinned to
the subject's numeral — and reduction manufactures binder nodes the
subject never paid for.  `EnvS2Refute.lean` refutes
`WhnfCoreClaims2A`/`WhnfClaims2A` on exactly that
(`whnfClaims2A_delta_refuted`), and `Claims2B.lean` corrects them: the
reduct annotates at some `F' ≥ F` of the prover's choosing.

## Where the fuel actually goes, stated once

`denote2` spends fuel at **two nodes only**, `.forallE` and `.lam`,
through `sortOfE`/`lamSortE`.  Every other clause — `.sort`, `.fvar`,
`.const`, `.app`, `.letE`, `.proj`, both literals — is fuel-free: it
returns the same answer at fuel `0` as at any other.  So the rule
governing every entry below is exact:

> a reduct needs strictly more fuel than its subject **iff** it
> carries a binder node whose sort computation the subject's own
> annotation did not already pay for.

That single criterion sorts this quarter's nine cases and three loop
exits without guesswork, and it is what makes `F ≤ F'` the right
slack rather than a hedge: the slack is needed, it is never needed
downward, and it is never tied to the run's fuel.

## What the `…R` lane keeps

`WhnfCoreClaims2R`/`WhnfClaims2R` and everything proved against them
stay where they are.  They were not wrong about anything they claimed
— the grading (R2) and the free annotation fuel (R1) both survive
unchanged — they were *incomplete*, and the diff between the `…R` and
`…2B` proofs below is exactly the missing repair, one existential
wide.  Every interpretation-level step transfers untouched, because
`denote2_fuelMono` returns the **same** `AVExpr` at the larger fuel:
lifting an annotation never disturbs the grading premise. -/

open Setlec (ConstantInfo ConstantVal ReducibilityHint natOpResult)

/-! ## The residues, re-audited against the criterion

Four of this quarter's six named residues assert a `denote2` success
for a **reduct**, at a fuel their consumer chooses.  By the criterion
above each is false as soon as that reduct can carry a binder, and one
of them — `Delta2` — is refuted below on its own terms, with no run
and no `EnvS2` field involved.  That is worth stating plainly: the
`EnvS2.acval_defn` repair was necessary but not sufficient, because
this quarter's own residue restated the same defect one level down.

The two that need **no** change:

* `BetaCert2` — it concludes a *membership*, not an annotation, and
  reads both annotations as hypotheses.
* `ReduceNatStep2` — the one genuinely fuel-preserving exit, and not
  by luck: `natOpResult_leaf` below checks that literal acceleration
  is closed on leaves, so its reduct annotates at **every** fuel. -/

/-- **`Delta2` is false.**  The subject is a bare constant, whose
`denote2` clause is fuel-free and so answers at fuel `1`; the reduct
is the stored λ body, which `denote2_one_lam` says has no annotation
there at all.  The same witness as `acvalDefnUniform_lam_refuted`, one
level further out: repairing `EnvS2` did not repair this. -/
theorem delta2_refuted (m : EnvS2 V env) {n n' : Name}
    {us : List Level} {cv : ConstantVal} {ty body : Expr}
    {mb : BinderMeta} {hint : ReducibilityHint}
    (hf : env.find? n
      = some (.defnInfo cv (.lam n' ty body mb) hint))
    (hlen : us.length = cv.levelParams.length) :
    ¬ Delta2 μ m φ := by
  intro h
  have hud : unfoldDefinition env (.const n us)
      = some ((Expr.lam n' ty body mb).instantiateLevelParams
        cv.levelParams us) := by
    simp only [unfoldDefinition, Expr.getAppFn, hf,
      Expr.getAppArgs, Expr.mkAppN, if_pos hlen]
  have hea : denote2 μ m.acval env φ 1 0 (.const n us)
      = some (m.acval n (Level.substFn φ cv.levelParams us)) := by
    rw [denote2, hf]
    simp only [ConstantInfo.toConstantVal]
    simp [hlen]
  have hcon := h hud hea
  simp only [Expr.instantiateLevelParams, denote2_one_lam] at hcon
  exact nomatch hcon

/-- **`ProjStep2` is false**, by the same criterion and a run any
bundled structure supplies: `.proj sn i pe` with `pe` a constant
annotates at fuel `1`, and a function-valued field does not. -/
theorem projStep2_refuted (m : EnvS2 V env) {fuel d i : Nat}
    {sn n' : Name} {pe ty body : Expr} {mb : BinderMeta}
    {Δa : List AVExpr} {ea : AVExpr}
    (hrun : whnfCore μ env (fuel + 1) d (.proj sn i pe)
      = .ok (.lam n' ty body mb))
    (hws : Expr.WScoped d (.proj sn i pe))
    (hb : (Expr.proj sn i pe).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.proj sn i pe))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.proj sn i pe))
    (hea : denote2 μ m.acval env φ 1 d (.proj sn i pe) = some ea) :
    ¬ ProjStep2 μ m φ fuel := by
  intro h
  obtain ⟨ea', hea', -⟩ := h (Δa := Δa) hrun hws hb hLb hC hea
  rw [denote2_one_lam] at hea'
  exact nomatch hea'

/-- **Literal acceleration is closed on leaves.**  Every result of the
kernel's `Nat` fast path is a `Nat` literal or a `Bool` constructor
constant — never a binder.  This is why `ReduceNatStep2` survives the
correction unchanged. -/
theorem natOpResult_leaf {c : Name} {a b : Nat} {e : Expr}
    (h : natOpResult c a b = some e) :
    (∃ v, e = .lit (.natVal v)) ∨ ∃ nm, e = .const nm [] := by
  unfold natOpResult at h
  by_cases h1 : c = Setlec.natPredName
  · rw [if_pos h1] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h1] at h
  by_cases h2 : c = Setlec.natAddName
  · rw [if_pos h2] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h2] at h
  by_cases h3 : c = Setlec.natSubName
  · rw [if_pos h3] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h3] at h
  by_cases h4 : c = Setlec.natMulName
  · rw [if_pos h4] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h4] at h
  by_cases h5 : c = Setlec.natPowName
  · rw [if_pos h5] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h5] at h
  by_cases h6 : c = Setlec.natDivName
  · rw [if_pos h6] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h6] at h
  by_cases h7 : c = Setlec.natModName
  · rw [if_pos h7] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h7] at h
  by_cases h8 : c = Setlec.natGcdName
  · rw [if_pos h8] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h8] at h
  by_cases h9 : c = Setlec.natLandName
  · rw [if_pos h9] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h9] at h
  by_cases h10 : c = Setlec.natLorName
  · rw [if_pos h10] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h10] at h
  by_cases h11 : c = Setlec.natXorName
  · rw [if_pos h11] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h11] at h
  by_cases h12 : c = Setlec.natShiftLeftName
  · rw [if_pos h12] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h12] at h
  by_cases h13 : c = Setlec.natShiftRightName
  · rw [if_pos h13] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h13] at h
  by_cases h14 : c = Setlec.natLog2Name
  · rw [if_pos h14] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h14] at h
  by_cases h15 : c = Setlec.natBeqName
  · rw [if_pos h15] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h15] at h
  by_cases h16 : c = Setlec.natBleName
  · rw [if_pos h16] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h16] at h
  exact nomatch h

/-- …and a leaf's annotation does not depend on the fuel at all. -/
theorem denote2_leaf_fuelFree {acval : Name → (Name → Nat) → AVExpr}
    {F F' d : Nat} {e : Expr}
    (hleaf : (∃ v, e = .lit (.natVal v)) ∨ ∃ nm, e = .const nm []) :
    denote2 μ acval env φ F d e = denote2 μ acval env φ F' d e := by
  rcases hleaf with ⟨v, rfl⟩ | ⟨nm, rfl⟩ <;> simp only [denote2]

/-! ### The four residues in the corrected shape -/

/-- `Denote2Inst1` with the slack.  The reduct replaces an **fvar
leaf** by an arbitrary term, so every binder node in `body` now runs
`lamSortE`/`sortOfE` over a larger subject and `inferTypeCore` must
descend into `val` instead of reading a leaf's stored type.  The
hypotheses pay for the *opened* body's cost, not the substituted
one's.  (Unlike `Delta2` I have no refutation: at `F = 1` the third
hypothesis forces the opened body binder-free and the conclusion
holds, so a witness would live at `F ≥ 2`.) -/
def Denote2Inst1B (μ : CheckMode)
    (acval : Name → (Name → Nat) → AVExpr) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {n : Name} {ty val body : Expr}
    {ta va ba : AVExpr},
    denote2 μ acval env φ F d ty = some ta →
    denote2 μ acval env φ F d val = some va →
    denote2 μ acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some ba →
    ∃ F', F ≤ F' ∧
      denote2 μ acval env φ F' d (body.instantiate1 val)
        = some (ba.inst va)

/-- `IotaStep2` with the slack: a fired rule's RHS may carry binder
nodes the major's spine did not, and the spine can be all leaves
(`Nat.rec M z s (Nat.succ Nat.zero)` annotates at fuel `1`). -/
def IotaStep2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e'' : Expr} {Δa : List AVExpr},
    iotaRecP μ env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e'' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea') ∧
        Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e'' ∧
        CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e''

/-- `ProjStep2` with the slack — `projStep2_refuted` is why. -/
def ProjStep2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {sn : Name} {i : Nat} {pe e' : Expr}
    {Δa : List AVExpr},
    whnfCore μ env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.proj sn i pe) →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d (.proj sn i pe) = some ea →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- `Delta2` with the slack — `delta2_refuted` is why.  The annotation
itself does not move: the unfolded body carries the constant's own
leaf (`EnvS2.acval_defn`, in its repaired existential form).  Only the
fuel does. -/
def Delta2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {F : Nat} {ea : AVExpr},
    unfoldDefinition env e = some e' →
    denote2 μ m.acval env φ F d e = some ea →
    ∃ F', F ≤ F' ∧ denote2 μ m.acval env φ F' d e' = some ea

/-! ## The nine cases, corrected

Everything below is its `…R` counterpart with one existential threaded
through.  The interpretation-level reasoning is untouched — the
`AnnotOk2` transports, the β kind split, `step2_trans` — because
`denote2_fuelMono` returns the **same** `AVExpr` at the larger fuel,
so lifting an annotation never disturbs the grading premise. -/

/-- `whnfCore_package2R` with the slack. -/
theorem whnfCore_package2B (m : EnvS2 V env) {fuel d F : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa : AVExpr}
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a)
    (haa : denote2 μ m.acval env φ F d a = some aa) :
    ∃ F' aa', F ≤ F' ∧
      denote2 μ m.acval env φ F' d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa →
        interp2 V ρ aa = interp2 V ρ aa' ∧ AnnotOk2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a' := by
  obtain ⟨F', aa', hle, haa', hD⟩ := ihwc hw hws hb hLb hC haa
  exact ⟨F', aa', hle, haa', hD, whnfCore_WScoped m.base.wf fuel hw hws,
    whnfCore_looseBVars m.base.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.base.wf fuel hw l hl),
    CtxOkR.of_subset (whnfCore_fvarLeaves m.base.wf fuel hw) hC⟩

/-- **The ζ clause**, corrected: `Denote2Inst1B` moves the fuel once,
the induction hypothesis once more, and `Nat.le_trans` composes. -/
theorem whnfCore_letE_claim2B (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1B μ m.acval env φ)
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    {d : Nat} {nn : Name} {tt vv bb e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.letE nn tt vv bb) = .ok e')
    (hws : Expr.WScoped d (.letE nn tt vv bb))
    (hb : (Expr.letE nn tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE nn tt vv bb))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.letE nn tt vv bb))
    {F : Nat} {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.letE nn tt vv bb)
      = some ea) :
    ∃ F' ea', F ≤ F' ∧
      denote2 μ m.acval env φ F' d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
        interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  rw [Setlec.whnfCore_succ] at h
  simp only [Setlec.whnfCoreBody, Setlec.whnfCore_def] at h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (bb.instantiate1 (.fvar d nn tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (bb.instantiate1 vv) :=
    fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
  have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (bb.instantiate1 vv) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
  obtain ⟨F₁, hle₁, hred⟩ := hinst hta hva hba
  obtain ⟨F₂, ea', hle₂, hea', hstep⟩ :=
    ihwc h hwred hbred hLred hCred hred
  refine ⟨F₂, ea', Nat.le_trans hle₁ hle₂, hea', fun ρ hρ =>
    step2_trans (fun hok => ?_) (hstep ρ hρ)⟩
  exact AnnotOk2_zeta V hok

/-- **The `.app` clause**, corrected.  Three sub-cases; the head's own
reduction moves the fuel first in all three, and `denote2_fuelMono`
carries the *argument's* annotation up to meet it — unchanged, so the
grading premise survives. -/
theorem whnfCore_app_claim2B (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1B μ m.acval env φ)
    (hcert : BetaCert2 μ m φ fuel) (hiota : IotaStep2B μ m φ fuel)
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    {d : Nat} {f a e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.app f a))
    {F : Nat} {ea : AVExpr}
    (hea : denote2 μ m.acval env φ F d (.app f a) = some ea) :
    ∃ F' ea', F ≤ F' ∧
      denote2 μ m.acval env φ F' d e' = some ea' ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
        interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) f :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  rw [denote2] at hea
  rcases hfa : denote2 μ m.acval env φ F d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote2 μ m.acval env φ F d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨f', hwf, hcase⟩ := Setlec.whnf_app_inv h
  obtain ⟨F₁, fa', hle₁, hfa', hDf, hwf', hbf', hLf', hCf'⟩ :=
    whnfCore_package2B m ihwc hwf hws.1 hb.1 hLf hCf hfa
  have haa₁ : denote2 μ m.acval env φ F₁ d a = some aa :=
    denote2_fuelMono hle₁ d a haa
  have hiapp : denote2 μ m.acval env φ F₁ d (.app f' a)
      = some (.app fa' aa) := by rw [denote2, hfa', haa₁]; rfl
  have hDapp : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (.app fa aa) →
      interp2 V ρ (.app fa aa) = interp2 V ρ (.app fa' aa) ∧
        AnnotOk2 V ρ (.app fa' aa) := by
    intro ρ hρ hok
    rw [AnnotOk2_app] at hok
    obtain ⟨hokf, hoka, v', A, B, h1, h2, h3⟩ := hok
    obtain ⟨heq, hokf'⟩ := hDf ρ hρ hokf
    refine ⟨by rw [interp2_app, interp2_app, heq], ?_⟩
    rw [AnnotOk2_app]
    exact ⟨hokf', hoka, v', A, B, heq ▸ h1, h2, h3⟩
  have hwapp : Expr.WScoped d (.app f' a) := by
    simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩
  have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hbf', hb.2⟩
  have hLapp : Expr.LeavesBounded (.app f' a) := fun l hl => by
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hLf' l hl
    · exact hLa l hl
  have hCapp : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.app f' a) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hCf'.2 l hl
    · exact hCa.2 l hl
  rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, ta, hta, hde⟩ |
    ⟨e'', hio, hwe''⟩ | rfl
  · -- β
    rw [denote2] at hfa'
    rcases htya : denote2 μ m.acval env φ F₁ d ty with _ | tya
    · rw [htya] at hfa'; exact nomatch hfa'
    rw [htya] at hfa'
    rcases hbb : denote2 μ m.acval env φ F₁ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hbb] at hfa'; exact nomatch hfa'
    rw [hbb] at hfa'
    rcases hkind : lamSortE μ env φ F₁ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hkind] at hfa'; exact nomatch hfa'
    rw [hkind] at hfa'
    obtain rfl : fa' = .lam v tya ba := (Option.some.inj hfa').symm
    simp only [Expr.WScoped] at hwf'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLf' l (by simp [Expr.fvarLeaves, hl])
    have hCty : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
        ty :=
      CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
        hCf'
    have hwred : Expr.WScoped d (body.instantiate1 a) :=
      Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2
    have hbred : (body.instantiate1 a).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2
    have hLred : Expr.LeavesBounded (body.instantiate1 a) :=
      fun l hl => by
        rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
        · exact hLf' l (by simp [Expr.fvarLeaves, h2])
        · exact hLa l h2
    have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
        (body.instantiate1 a) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact hCf'.2 l (by simp [Expr.fvarLeaves, h2])
      · exact hCa.2 l h2
    obtain ⟨F₂, hle₂, hred⟩ := hinst htya haa₁ hbb
    obtain ⟨F₃, ea', hle₃, hea', hD⟩ :=
      ihwc hbeta hwred hbred hLred hCred hred
    refine ⟨F₃, ea', Nat.le_trans hle₁
      (Nat.le_trans hle₂ hle₃), hea', fun ρ hρ =>
        step2_trans (hDapp ρ hρ) ?_⟩
    refine step2_trans (fun hok => ?_) (hD ρ hρ)
    by_cases hz : v = 0
    · subst hz
      exact AnnotOk2_beta_zero V hok
        (hcert hta hde hws.2 hb.2 hLa hCa hwf'.1 hbf'.1 hLty hCty
          haa₁ htya ρ hρ)
    · exact AnnotOk2_beta_pos V hz hok
  · -- ι
    obtain ⟨F₂, ea₂, hle₂, hea₂, hstep, hwe, hbe, hLe, hCe⟩ :=
      hiota hio hwapp hbapp hLapp hCapp hiapp
    obtain ⟨F₃, ea', hle₃, hea', hD⟩ :=
      ihwc hwe'' hwe hbe hLe hCe hea₂
    exact ⟨F₃, ea', Nat.le_trans hle₁ (Nat.le_trans hle₂ hle₃),
      hea', fun ρ hρ =>
        step2_trans (step2_trans (hDapp ρ hρ) (hstep ρ hρ))
          (hD ρ hρ)⟩
  · -- stuck
    exact ⟨F₁, _, hle₁, hiapp, hDapp⟩

/-- **`WhnfCoreClaims2B` at `fuel + 1`** — the nine cases.  The seven
that take `F' = F` do so through `whnfCore_leaf_claim2`, reused
verbatim from the `…R` lane: they were never wrong. -/
theorem whnfCore_claims2B (m : EnvS2 V env) {fuel : Nat}
    (hinst : Denote2Inst1B μ m.acval env φ)
    (hcert : BetaCert2 μ m φ fuel) (hiota : IotaStep2B μ m φ fuel)
    (hproj : ProjStep2B μ m φ fuel)
    (ihwc : WhnfCoreClaims2B μ m φ fuel) :
    WhnfCoreClaims2B μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb hC F ea hea
  match e with
  | .sort u =>
    obtain ⟨ea', hea', hD⟩ :=
      whnfCore_leaf_claim2 (Δa := Δa) m (Or.inl ⟨u, rfl⟩) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .fvar idx n ty =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inl ⟨idx, n, ty, rfl⟩)) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .forallE n ty body bi =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .lam n ty body mb =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩)))) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .const n us =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩))))) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .lit l =>
    obtain ⟨ea', hea', hD⟩ := whnfCore_leaf_claim2 (Δa := Δa) m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))))) h hea
    exact ⟨F, ea', Nat.le_refl F, hea', fun ρ hρ hok =>
      ⟨(hD ρ hρ).1, (hD ρ hρ).2 hok⟩⟩
  | .bvar i => rw [denote2_bvar] at hea; exact nomatch hea
  | .letE nn tt vv bb =>
    exact whnfCore_letE_claim2B m hinst ihwc h hws hb hLb hC hea
  | .app f a =>
    exact whnfCore_app_claim2B m hinst hcert hiota ihwc h hws hb
      hLb hC hea
  | .proj sn i pe => exact hproj h hws hb hLb hC hea

/-- **`WhnfCoreStep2B`, routed.**  The quarter's deliverable against
`Claims2B.lean`.  The defeq and inference claims are not consumed —
`BetaCert2` is what would consume them, and it is a residue. -/
theorem whnfCoreStep2B_of
    (hinst : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hcert : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), BetaCert2 μ m φ fuel)
    (hiota : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2B μ m φ fuel)
    (hproj : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2B μ m φ fuel) :
    WhnfCoreStep2B μ V :=
  fun env m φ fuel ihwc _ _ _ =>
    whnfCore_claims2B m (hinst env m φ) (hcert env m φ fuel)
      (hiota env m φ fuel) (hproj env m φ fuel) ihwc

/-- **The budget induction**, corrected.  The chain of exits
accumulates `F ≤ F₁ ≤ F₂ ≤ …` by `Nat.le_trans` and nothing else; the
existential is unbounded, so the chain's length costs nothing.
`ReduceNatStep2` enters **unchanged** — `natOpResult_leaf` is why. -/
theorem whnfLoop_claim2B (m : EnvS2 V env) {fuel : Nat}
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    (hnat : ReduceNatStep2 μ m φ fuel) (hdelta : Delta2B μ m φ) :
    ∀ (budget : Nat) {d : Nat} {Δa : List AVExpr} {e e' : Expr},
      whnfLoop (pureFns μ env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
      ∀ {F : Nat} {ea : AVExpr},
        denote2 μ m.acval env φ F d e = some ea →
        ∃ F' ea', F ≤ F' ∧
          denote2 μ m.acval env φ F' d e' = some ea' ∧
          ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
            interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δa e e' h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δa e e' h hws hb hLb hC F ea hea
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, Setlec.whnfCore_def] at h
    cases hwc : whnfCore μ env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨F₁, ea₁, hle₁, hea₁, hD₁, hws₁, hb₁, hLb₁, hC₁⟩ :=
      whnfCore_package2B m ihwc hwc hws hb hLb hC hea
    cases hrn : reduceNatP μ env fuel d e₁ with
    | error err =>
      rw [Setlec.reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [Setlec.reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨ea₂, hea₂, hD₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hea₁
      obtain ⟨F₃, ea', hle₃, hea', hD₃⟩ :=
        ih h hws₂ hb₂ hLb₂ hC₂ hea₂
      exact ⟨F₃, ea', Nat.le_trans hle₁ hle₃, hea', fun ρ hρ =>
        step2_trans (step2_trans (hD₁ ρ hρ) (hD₂ ρ hρ)) (hD₃ ρ hρ)⟩
    | none, h =>
      dsimp only at h
      cases hud : unfoldDefinition env e₁ with
      | none =>
        rw [hud] at h
        exact ⟨F₁, ea₁, hle₁, (Except.ok.inj h) ▸ hea₁, hD₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        obtain ⟨F₂, hle₂, hea₂⟩ := hdelta hud hea₁
        obtain ⟨F₃, ea', hle₃, hea', hD₃⟩ :=
          ih h (unfoldDefinition_WScoped m.base.wf hud hws₁)
            (unfoldDefinition_looseBVars m.base.wf hud hb₁)
            (fun l hl => hLb₁ l
              (unfoldDefinition_fvarLeaves m.base.wf hud l hl))
            (CtxOkR.of_subset
              (unfoldDefinition_fvarLeaves m.base.wf hud) hC₁)
            hea₂
        exact ⟨F₃, ea', Nat.le_trans hle₁
          (Nat.le_trans hle₂ hle₃), hea', fun ρ hρ =>
            step2_trans (hD₁ ρ hρ) (hD₃ ρ hρ)⟩

/-- **`WhnfClaims2B` at `fuel + 1`.** -/
theorem whnf_claims2B (m : EnvS2 V env) {fuel : Nat}
    (ihwc : WhnfCoreClaims2B μ m φ fuel)
    (hnat : ReduceNatStep2 μ m φ fuel) (hdelta : Delta2B μ m φ) :
    WhnfClaims2B μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb hC F ea hea
  rw [Setlec.whnf_succ, whnfBody] at h
  exact whnfLoop_claim2B m ihwc hnat hdelta whnfLoopFuel h hws hb
    hLb hC hea

/-- **`WhnfStep2B`, routed.**  The loop's deliverable.  It needs
neither the defeq nor the inference claim, and — this is the finding
worth carrying — it needs `ReduceNatStep2` **unchanged**: literal
acceleration is the one exit whose reduct is always a leaf. -/
theorem whnfStep2B_of
    (hnat : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2 μ m φ fuel)
    (hdelta : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Delta2B μ m φ) :
    WhnfStep2B μ V :=
  fun env m φ fuel ihwc _ _ _ =>
    whnf_claims2B m ihwc (hnat env m φ fuel) (hdelta env m φ)

/-! # `Delta2B`, discharged — and what it turned out to cost

The residue's own docstring says the annotation does not move and
"only the fuel does".  That is right, and it is not the whole bill:
`unfoldDefinition` does not hand the loop `value`, it hands it
`value.instantiateLevelParams cv.levelParams us` under a spine, at the
subject's depth.  `EnvS2.acval_defn` speaks about `value`, at depth
`0`, under a *substituted assignment*.  Three crossings, and only two
of them are algebra:

* the spine — `denote2_mkAppN_swap` (`Step2/Levels.lean`), landed;
* depth `0` → `d` — `denote2_depth_of_closed` (ditto), on
  `denote2_shiftFrom` + `EnvS2.acval_closed`, landed;
* `φ` versus `Level.substFn φ …` — **`Denote2InstLevels`**, a
  **residue**.

The third is v1's `denote_instLevels`, which is one induction over
`denote` — and is *not* one induction over `denote2`, because
`denote2`'s binder clauses run `inferTypeCore`/`whnf` on the term
itself: the two sides of the crossing are two runs of the checker on
two different terms.  See `Step2/Levels.lean`'s docstring for the
argument in full.

So the delta exit is routed to **one** obligation, in either of two
equivalent forms:

* `AcvalDefnInst` below — the shape the exit consumes, and the shape
  `EnvS2.acval_defn`/`acval_thm` would take if the junction chose to
  restate them at the *instantiated* value (a strict strengthening:
  the current fields are its identity-substitution instance).  With
  that field, `delta2B_of` discharges `Delta2B` outright and nothing
  else is owed.
* `Denote2InstLevels` — the general crossing, which supplies
  `AcvalDefnInst` from the fields as they stand
  (`acvalDefnInst_of_instLevels`), and which every other consumer of a
  stored value's annotation will need too.

Either way the *rest* of the delta exit is now theorem, not residue. -/

/-- **The unfolding supplier the delta exit actually consumes**: the
stored value's canonical annotation after the head's levels have been
substituted *into* it, which is the term `unfoldDefinition` builds.
Both unfoldable kinds (`defnInfo`, `thmInfo`) in one premise, exactly
as `unfoldDefinition`'s two branches differ only in the field that
supplies the value.

Not refutable by the smallest-fuel test: the fuel is existential, in
`EnvS2.acval_defn`'s own repaired shape. -/
def AcvalDefnInst (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) : Prop :=
  ∀ {F : Nat} {cv : ConstantVal} {value : Expr} {us : List Level},
    ((∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) →
    us.length = cv.levelParams.length →
    ∃ F', F ≤ F' ∧
      denote2 μ m.acval env φ F' 0
          (value.instantiateLevelParams cv.levelParams us)
        = some (m.acval cv.name (Level.substFn φ cv.levelParams us))

/-- Substituting every level parameter by itself does not move the
assignment — the `Level.substFn` twin of `Level.subst_param_self`
(`Verify/InstLevels.lean`), which is where it belongs if anything else
ever wants it. -/
theorem substFn_param_self (ψ : Name → Nat) (ks : List Name) :
    Level.substFn ψ ks (ks.map Level.param) = ψ := by
  funext n
  have h : Level.subst.go ks (ks.map Level.param) n = .param n :=
    Level.subst_param_self ks (.param n)
  rw [← Level.eval_subst_go, h, Level.eval]

/-- **The proposed field is a strengthening, not a different
statement**: `EnvS2.acval_defn`'s current shape is its
identity-substitution instance, so adopting `AcvalDefnInst` in its
place loses nothing.  (The campaign's rule: a repair needs the
positive check as well as the negative one.  This is the "nothing is
lost" half; the "it is satisfiable at a real environment" half is the
install layer's and is not testable here.) -/
theorem acval_defn_of_acvalDefnInst (m : EnvS2 V env)
    (hdi : AcvalDefnInst μ m φ) (F : Nat) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint)
    (hmem : ConstantInfo.defnInfo cv value hint ∈ env.consts) :
    ∃ F', F ≤ F' ∧
      denote2 μ m.acval env φ F' 0 value
        = some (m.acval cv.name φ) := by
  have h := hdi (F := F) (us := cv.levelParams.map Level.param)
    (Or.inl ⟨hint, hmem⟩) (by simp)
  rwa [Expr.instantiateLevelParams_self, substFn_param_self] at h

/-- The two forms of the obligation, related: the general level
crossing turns the fields as they stand into the shape the exit
consumes. -/
theorem acvalDefnInst_of_instLevels (m : EnvS2 V env)
    (hil : Denote2InstLevels μ m) : AcvalDefnInst μ m φ := by
  intro F cv value us hmem hlen
  obtain ⟨F₁, hle₁, h₁⟩ :
      ∃ F₁, F ≤ F₁ ∧
        denote2 μ m.acval env (Level.substFn φ cv.levelParams us) F₁ 0
            value
          = some (m.acval cv.name
            (Level.substFn φ cv.levelParams us)) := by
    rcases hmem with ⟨hint, hm⟩ | hm
    · exact m.acval_defn μ _ F cv value hint hm
    · exact m.acval_thm μ _ F cv value hm
  obtain ⟨F₂, hle₂, h₂⟩ :=
    hil φ cv.levelParams us F₁ 0 value _ h₁
  exact ⟨F₂, Nat.le_trans hle₁ hle₂, h₂⟩

/-- The shared core of `unfoldDefinition`'s two branches — v1's
`delta_coreR` (`Bridge/WhnfCore.lean`) transposed, with the two
crossings v1 does not have to make. -/
private theorem delta2B_core (m : EnvS2 V env)
    {d F : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea : AVExpr}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : ∃ F₁, F ≤ F₁ ∧
      denote2 μ m.acval env φ F₁ 0
          (value.instantiateLevelParams cv.levelParams us)
        = some (m.acval ci.name (Level.substFn φ cv.levelParams us)))
    (hea : denote2 μ m.acval env φ F d e = some ea) :
    ∃ F', F ≤ F' ∧
      denote2 μ m.acval env φ F' d
          (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs)
        = some ea := by
  obtain ⟨F₁, hle, hv0⟩ := hval
  obtain rfl : ci.name = n := by
    rw [Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  refine ⟨F₁, hle, ?_⟩
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    Expr.mkAppN_getApp e
  rw [← he] at hea
  refine denote2_mkAppN_swap e.getAppArgs hle ?_ hea
  intro fa hfa
  rw [hfn, denote2, hfind] at hfa
  simp only [hcvt] at hfa
  rw [if_pos hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  exact denote2_depth_of_closed m.base.wf m.acval_closed
    (by rw [Expr.hasFvar_instantiateLevelParams]; exact hnofv)
    (fun k => m.acval_closed _ _ k) hv0 d

/-- **`Delta2B`, discharged** from the single obligation above.  The
spine, the depth and the frame are theorems; the level crossing is the
whole of what remains. -/
theorem delta2B_of (m : EnvS2 V env) (hdi : AcvalDefnInst μ m φ) :
    Delta2B μ m φ := by
  intro d e e' F ea hud hea
  rw [unfoldDefinition] at hud
  split at hud
  · next n us hfn =>
    split at hud
    · next cv value hint hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact delta2B_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ :=
                m.base.wf _ (find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (hdi (Or.inl ⟨hint, find?_mem hfind⟩) hlen) hea
      · exact nomatch hud
    · next cv value hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact delta2B_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, -, -, ht⟩ :=
                m.base.wf _ (find?_mem hfind)
              exact (ht cv value rfl).1)
          (hdi (Or.inr (find?_mem hfind)) hlen) hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud

/-! # `BetaCert2`, and the seam it lands on

`whnfCoreStep2B_of` is handed all four induction hypotheses and uses
one; the β certificate is what would consume two of the other three.
So the question worth asking before treating `BetaCert2` as a residue
is whether it is a residue at all, or merely `InferClaims2A` and
`DefEqClaims2B` composed at the site where the checker already ran
both (`whnfCoreBody`'s β branch runs `inferTypeCore` on the argument
and `isDefEqCore` against the λ's domain — that *is* the certificate).

**It is the composition, and the composition does not close.**
`betaCert2P_of_claims` below is that composition with every input the
derivation needs made an explicit premise, so the residue's remaining
content is exactly the gap between `BetaCert2P` and `BetaCert2`.
`BetaCert2P` adds three premises and the theorem consumes one further
input; of those four, **one** is a seam and the rest are bookkeeping:

* `μ.verified = true` — the consumer has it (`whnfCore_claims2B`
  binds it from `WhnfCoreClaims2B`);
* `AnnotOk2 ρ tya` — the consumer has it (below);
* `CtxOk2 m μ φ F d Δa a` — **the consumer does not have it**;
* `TypeOk2` (the theorem's `htok`) — a residue of the inference
  quarter, not of this one.

The last two are the two the inference quarter had already met from
its own side:

1. **The context currency.**  `InferClaims2A` reads `CtxOk2` (a
   `denote2` fact plus an `interp2` equation per `fvar` leaf); this
   quarter holds `CtxOkR` on erasures, whose leaf package is a
   *derivation*, `∃ T', Infer … ∧ DefEq …`.  The bridge is `CtxOk2R`
   (`Step2/InferQ.lean`), stated there and believed false.  **The β
   certificate is a second, independent consumer of it** — the seam is
   not the inference `.app` clause's alone, and the repair both sites
   need is the same one (the context currency made uniform across the
   four claims, which was the dispatch quarter's original proposal).
2. **The inferred type's truthfulness.**  `DefEqClaims2B` is graded on
   *both* sides (STOP 3) and `InferClaims2A` concludes `AnnotOk2` of
   the term it typed, never of the type it returned.  That is the
   inference quarter's `TypeOk2`, and it answers the question seal 8
   left open — *"whether `InferClaims2A`'s conclusion needs extending
   is asked against a site that can point at it"*: **yes, and this is
   a second such site.**  (Written out as a premise here rather than
   imported: `TypeOk2` lives in the inference quarter's file, and two
   declarations of one statement is the integration cost seal 9
   measured.)

The λ domain's own truthfulness is **not** a gap: at the call site the
consumer holds `AnnotOk2 ρ (.app (.lam v tya ba) aa)`, and
`AnnotOk2_lam`'s first conjunct is `AnnotOk2 ρ tya`.  It is a premise
below for bookkeeping, not a residue.

Deliberately **not** wired into `whnfCore_app_claim2B`: `BetaCert2P`
carries a premise the consumer cannot supply, and a residue discharged
by weakening it past its consumer is worse than an open one. -/

/-- `BetaCert2` with the two seam premises made explicit — the shape
the two claims actually compose to.  `BetaCert2` is this with
`CtxOk2` and the domain's `AnnotOk2` removed; the first of those is
`CtxOk2R`'s content and the reason this is not a discharge. -/
def BetaCert2P (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {a ty ta : Expr} {F : Nat}
    {aa tya : AVExpr},
    μ.verified = true →
    inferTypeCore μ env fuel d a = .ok ta →
    Setlec.isDefEqCore μ env fuel d ta ty = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty →
    CtxOk2 m μ φ F d Δa a →
    denote2 μ m.acval env φ F d a = some aa →
    denote2 μ m.acval env φ F d ty = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya →
      interp2 V ρ aa ∈ˢ interp2 V ρ tya

/-- **The β certificate is the two claims composed** — the inference
claim types the argument, the defeq claim moves the interpretation
from the inferred type to the λ's domain, and the membership rides
across.  `htok` is the inference quarter's `TypeOk2`, written out
because it lives in that quarter's file. -/
theorem betaCert2P_of_claims (m : EnvS2 V env) {fuel : Nat}
    (htok : ∀ {F f d : Nat} {e t : Expr} {Δa : List AVExpr}
      {ta : AVExpr},
      inferTypeCore μ env f d e = .ok t →
      CtxOk2 m μ φ F d Δa e →
      denote2 μ m.acval env φ F d t = some ta →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta)
    (ihd : DefEqClaims2B μ m φ fuel) (ihi : InferClaims2A μ m φ fuel) :
    BetaCert2P μ m φ fuel := by
  intro d Δa a ty ta F aa tya hv hta hde hwa hba hLa hCa hwty hbty
    hLty hCty hC2 haa htya ρ hρ hoktya
  obtain ⟨F', ta', hle, hta', hcon⟩ := ihi hv hta hwa hba hLa hC2 haa
  have hwta : Expr.WScoped d ta :=
    Setlec.inferTypeCore_WScoped m.base.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.base.wf fuel hta hwa hba hLa
  have hsub := Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hta hwa
  have hLta : Expr.LeavesBounded ta := fun l hl => hLa l (hsub l hl)
  have hCta : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ta :=
    CtxOkR.of_subset hsub hCa
  have hokta : AnnotOk2 V ρ ta' :=
    htok hta (CtxOk2.fuelMono hle hC2) hta' ρ hρ
  have heq := ihd hv hde hwta hbta hLta hwty hbty hLty hCta hCty hta'
    (denote2_fuelMono hle d ty htya) ρ hρ hokta hoktya
  exact heq ▸ (hcon ρ hρ).2

end Setlec.SetR.Interp2
