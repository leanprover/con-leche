import Setlec.SetR.Interp2.Keys2
import Setlec.SetR.Interp2.EnvS2UNe

/-!
# `Denote2EnvExtend`, discharged — and the two directions it needed

Seal 37's enabler: `denote2` is stable under environment extension.
Seal 35 priced the composition as *(E) over `denote2`'s finitely many
internal calls, `FindPreserved` for the `.const` clause and the
literal-support guards, `InferOutputBound` for `sortOfE`'s chain*.

**Attempting the discharge found that premise set two facts short**,
and both are recorded here beside the definitions that name them.
Neither is a defect in `Denote2EnvExtend`: the statement is right for
its consumer.  Both are *exposure* gaps in the supplier — the same
class as seal 35's own `InferOutputBound` request, and named the same
way, as `def`s carrying a landing request rather than as assumptions.

## Finding 1 — the direction

`EnvExtendStable` lifts **forward**: a successful run at the prefix is
reproduced at the extension.  That is the direction the *existential*
`EnvS2` fields needed, because there `denote2` sat in a conclusion.

Seal 34's uniqueness ruling moved `denote2` into the **premises** of
`mem_type2`, `acval_defn` and `acval_thm`.  Transporting an old
constant's field to `env₂` therefore needs *env₂-run ⇒ env₀-run* —
**backward**.  An equation needs both, so no composition of a
one-directional (E) can prove `Denote2EnvExtend`, whatever the
per-clause bookkeeping.

Seal 35's fit check enumerated `denote2`'s *calls* and matched them to
(E)'s conjuncts; it did not check the *direction*, and the direction
had been inverted one seal earlier.

`EnvExtendReflect` below is the missing half.  It is believed true
for the same reason (E) is — a run on prefix-bound material touches
only prefix-bound material — and the honest form of the request is
*"state (E) as an agreement, not as a lifting"*.

## Finding 2 — the literal-support guards are not `find?`-monotone in
the direction the equation needs

The brief named `FindPreserved` as the supplier for the literal
guards.  It supplies `natLitSupported env₀ = true → natLitSupported
env = true` and nothing else, because `find?`-monotonicity runs
prefix-to-extension.  The equation needs the converse, and the
converse is **false in general**: an install that stores the `Nat`
block turns the guard on.

`ConstsBound` cannot rescue this: its `.lit` case is the `| _ => True`
catch-all, so the premise `ConstsBound env₀ e` places no condition on
a literal at all.  `denote2EnvExtend_lit_refuted` exhibits the failure
at a concrete pair on which `FindPreserved` **does** hold, so the
named supplier is present and does not help.

The fact is very likely available inside (E)'s own discharge — the
kernel's `whnf`/`infer`/`annotate` consult `natLitSupportedF` too
(`Kernel/CoreI.lean:831`, `:1858`, `:2291`), so an extension that
flips a guard almost certainly breaks (E) as well.  As with
`InferOutputBound`, the request is therefore **exposure**, not new
content: publish the guard agreement (E)'s discharge already needs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo
  inferTypeCore whnf natLitSupported strLitSupported)

/-! ## The `ConstsBound` kit

`ConstsBound` landed with no lemmas — its only consumer so far took it
as a premise and never took it apart.  These are the clause equations
and the one closure fact `denote2`'s binder cases need. -/

@[simp] theorem constsBound_const {env₀ : Env} {n : Name}
    {us : List Level} :
    ConstsBound env₀ (.const n us) ↔ (env₀.find? n).isSome = true := by
  rw [ConstsBound]

@[simp] theorem constsBound_app {env₀ : Env} {f a : Expr} :
    ConstsBound env₀ (.app f a) ↔
      ConstsBound env₀ f ∧ ConstsBound env₀ a := by
  rw [ConstsBound]

@[simp] theorem constsBound_lam {env₀ : Env} {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    ConstsBound env₀ (.lam n ty b m) ↔
      ConstsBound env₀ ty ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_forallE {env₀ : Env} {n : Name}
    {ty b : Expr} {m : Setlec.BinderMeta} :
    ConstsBound env₀ (.forallE n ty b m) ↔
      ConstsBound env₀ ty ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_letE {env₀ : Env} {n : Name}
    {t v b : Expr} :
    ConstsBound env₀ (.letE n t v b) ↔
      ConstsBound env₀ t ∧ ConstsBound env₀ v ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_proj {env₀ : Env} {s : Name} {i : Nat}
    {e : Expr} :
    ConstsBound env₀ (.proj s i e) ↔ ConstsBound env₀ e := by
  rw [ConstsBound]

@[simp] theorem constsBound_fvar {env₀ : Env} {idx : Nat} {n : Name}
    {ty : Expr} :
    ConstsBound env₀ (.fvar idx n ty) ↔ ConstsBound env₀ ty := by
  rw [ConstsBound]

@[simp] theorem constsBound_sort {env₀ : Env} {u : Level} :
    ConstsBound env₀ (.sort u) := by rw [ConstsBound] <;> simp

@[simp] theorem constsBound_bvar {env₀ : Env} {i : Nat} :
    ConstsBound env₀ (.bvar i) := by rw [ConstsBound] <;> simp

/-- **The literal case is the catch-all.**  Stated, rather than left
implicit, because it is the whole of finding 2: the premise of
`Denote2EnvExtend` says *nothing* about a literal, while `denote2`'s
literal clauses are gated on an environment-global guard. -/
@[simp] theorem constsBound_lit {env₀ : Env} {l : Setlec.Literal} :
    ConstsBound env₀ (.lit l) := by rw [ConstsBound] <;> simp

/-- Instantiation preserves prefix-boundness: every constant leaf of
the result comes from the body or from the substituted term. -/
theorem ConstsBound.instantiate1 {env₀ : Env} {v : Expr}
    (hv : ConstsBound env₀ v) :
    ∀ (e : Expr) (d : Nat), ConstsBound env₀ e →
      ConstsBound env₀ (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    rw [Setlec.Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Setlec.Expr.instantiate1]; simp
  | const n us => intro d h; rw [Setlec.Expr.instantiate1]; exact h
  | fvar idx n ty => intro d h; rw [Setlec.Expr.instantiate1]; exact h
  | lit l => intro d _; rw [Setlec.Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [constsBound_app] at h
    rw [Setlec.Expr.instantiate1, constsBound_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam n ty b m ihty ihb =>
    intro d h
    rw [constsBound_lam] at h
    rw [Setlec.Expr.instantiate1, constsBound_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE n ty b m ihty ihb =>
    intro d h
    rw [constsBound_forallE] at h
    rw [Setlec.Expr.instantiate1, constsBound_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE n t val b iht ihval ihb =>
    intro d h
    rw [constsBound_letE] at h
    rw [Setlec.Expr.instantiate1, constsBound_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s i e ihe =>
    intro d h
    rw [constsBound_proj] at h
    rw [Setlec.Expr.instantiate1, constsBound_proj]
    exact ihe d h

/-! ## Finding 2, mechanized

The pair is as small as the failure allows: the prefix stores nothing,
the extension stores exactly the three declarations `natLitSupported`
inspects.  `FindPreserved` holds — vacuously, which is the point:
the supplier the brief named for this clause is *present*, and the
equation still fails. -/

/-- The extension: the three declarations the `Nat`-literal guard
inspects, and nothing else. -/
def natLitEnv : Env := ⟨[Setlec.natA, Setlec.natZeroA, Setlec.natSuccA]⟩

theorem natLitSupported_natLitEnv :
    natLitSupported natLitEnv = true := by decide

theorem natLitSupported_empty :
    natLitSupported Env.empty = false := by decide

/-- `FindPreserved` holds at the pair — vacuously, at the empty
prefix. -/
theorem findPreserved_empty_natLitEnv :
    FindPreserved Env.empty natLitEnv := by
  intro n ci h
  exact nomatch h

/-- **`Denote2EnvExtend` is false at a pair satisfying its named
supplier.**  The subject is a bare `Nat` literal: `ConstsBound` grades
it by the `| _ => True` catch-all, so the premise is met, while
`denote2`'s literal clause is gated on `natLitSupported` — `none`
before the block is stored, `some` after.

This is finding 2 as a theorem rather than as prose: no amount of
per-clause composition over `EnvExtendStable`, `FindPreserved` and
`InferOutputBound` can close it, because **none of the three mentions
the literal guards in the extension-to-prefix direction**. -/
theorem denote2EnvExtend_lit_refuted (μ : CheckMode)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) :
    ¬ Denote2EnvExtend μ Env.empty natLitEnv acval φ := by
  intro h
  have hh := h 0 0 (.lit (.natVal 0)) constsBound_lit
  have hno : ¬ natLitSupported Env.empty = true := by
    rw [natLitSupported_empty]; exact Bool.noConfusion
  rw [denote2, if_neg hno, denote2,
    if_pos natLitSupported_natLitEnv] at hh
  exact nomatch hh

/-! ## The two named cross-lane hypotheses

Named, not assumed — the `InferOutputBound` pattern of seal 37: a
`def` with a landing request, so that the dependency is visible to
everyone who reads the discharge. -/

/-- **Finding 1's missing half: (E) in the reflecting direction.**
`EnvExtendStable` lifts a successful prefix run to the extension;
`mem_type2`'s uniqueness form (seal 34) needs the converse, because
its `denote2` sits in a *premise*.  Only the two functions `denote2`
actually calls are asked for.

*Request to the Θ lane: state (E) as an agreement rather than as a
lifting.*  The content is believed identical — a run on prefix-bound
material touches only prefix-bound material — and the one-directional
form was chosen for that lane's own consumers. -/
def EnvExtendReflect (μ : CheckMode) (env₀ env : Env) : Prop :=
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    inferTypeCore μ env f d e = .ok x →
    inferTypeCore μ env₀ f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnf μ env f d e = .ok x → whnf μ env₀ f d e = .ok x)

/-- **Finding 2's repair: the literal guards agree.**  `FindPreserved`
gives the prefix-to-extension direction only, and
`denote2EnvExtend_lit_refuted` shows the converse is not optional.

*Request to the Θ lane: expose this beside (E).*  The kernel's own
`whnf`/`infer`/`annotate` clauses consult the same guards, so an
extension that flips one is very unlikely to satisfy (E) either —
i.e. this is an exposure request, not new content, exactly as
`InferOutputBound` was. -/
def LitGuardsAgree (env₀ env : Env) : Prop :=
  natLitSupported env₀ = natLitSupported env ∧
  strLitSupported env₀ = strLitSupported env

/-- The sort computations agree, at both of `denote2`'s entry points. -/
def SortAgree (μ : CheckMode) (env₀ env : Env) (φ : Name → Nat) :
    Prop :=
  (∀ {f d : Nat} {e : Expr}, ConstsBound env₀ e →
    sortOfE μ env₀ φ f d e = sortOfE μ env φ f d e) ∧
  (∀ {f d : Nat} {e : Expr}, ConstsBound env₀ e →
    lamSortE μ env₀ φ f d e = lamSortE μ env φ f d e)

/-! ## `SortAgree`, from (E) + reflect + `InferOutputBound`

This is seal 35's composition, run in both directions: the forward
half is (E)'s `inferTypeCore` and `whnf` conjuncts with
`InferOutputBound` bridging the chain, and the backward half is
`EnvExtendReflect`'s two conjuncts with the *same* bridge — note that
`InferOutputBound` is stated at `env₀` alone, so it serves both. -/

theorem sortAgree_of {μ : CheckMode} {env₀ env : Env} {φ : Name → Nat}
    (hE : EnvExtendStable μ env₀ env)
    (hR : EnvExtendReflect μ env₀ env)
    (hI : InferOutputBound μ env₀) :
    SortAgree μ env₀ env φ := by
  have hsort : ∀ {f d : Nat} {e : Expr}, ConstsBound env₀ e →
      sortOfE μ env₀ φ f d e = sortOfE μ env φ f d e := by
    intro f d e hc
    unfold sortOfE
    rcases hi : inferTypeCore μ env₀ f d e with err | t
    · rcases hi' : inferTypeCore μ env f d e with err' | t'
      · rfl
      · rw [hR.1 hc hi'] at hi
        exact nomatch hi
    · rw [(hE.2.2.1 hc hi).1]
      simp only [Except.toOption]
      have hct : ConstsBound env₀ t := hI hc hi
      rcases hw : whnf μ env₀ f d t with err | w
      · rcases hw' : whnf μ env f d t with err' | w'
        · rfl
        · rw [hR.2 hct hw'] at hw
          exact nomatch hw
      · rw [hE.2.1 hct hw]
  refine ⟨hsort, ?_⟩
  intro f d e hc
  unfold lamSortE
  rcases hi : inferTypeCore μ env₀ f d e with err | t
  · rcases hi' : inferTypeCore μ env f d e with err' | t'
    · rfl
    · rw [hR.1 hc hi'] at hi
      exact nomatch hi
  · rw [(hE.2.2.1 hc hi).1]
    simp only [Except.toOption]
    exact hsort (hI hc hi)

/-! ## The discharge -/

/-- A stored lookup's level parameters do not move. -/
theorem levelParamsAt_congr {env₀ env : Env}
    (hF : FindPreserved env₀ env) {n : Name}
    (h : (env₀.find? n).isSome = true) :
    levelParamsAt env₀ n = levelParamsAt env n := by
  cases hf : env₀.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci => rw [levelParamsAt, levelParamsAt, hf, hF hf]

/-- The string guard pins `List.nil` and `List.cons` in the store. -/
theorem strLitSupported_listNames {env₀ : Env}
    (h : strLitSupported env₀ = true) :
    (env₀.find? listNilName).isSome = true ∧
      (env₀.find? listConsName).isSome = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h
  constructor
  · revert h
    cases env₀.find? listNilName <;> simp [Setlec.listNilTyOk]
  · revert h
    cases env₀.find? listConsName <;> simp [Setlec.listConsTyOk]

/-- **`Denote2EnvExtend`, discharged.**  The premise set is seal 35's
plus the two findings above; every other clause composes exactly as
that seal priced it. -/
theorem denote2_envExtend {μ : CheckMode} {env₀ env : Env}
    {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsAgree env₀ env)
    (hS : SortAgree μ env₀ env φ) :
    Denote2EnvExtend μ env₀ env acval φ := by
  intro F d e
  induction d, e using denote2.induct (env := env₀) with
  | case1 d u => intro _; rw [denote2, denote2]
  | case2 d idx nm ty => intro _; rw [denote2, denote2]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denote2, hf, denote2, hF hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denote2, hf, denote2, hF hf]
  | case5 d n us hf =>
    intro hc
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denote2, denote2, ihty hc.1, ihbody hcb, hS.1 hc.1, hS.1 hcb]
  | case7 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denote2, denote2, ihty hc.1, ihbody hcb, hS.2 hcb]
  | case8 d f a ihf iha =>
    intro hc
    rw [constsBound_app] at hc
    rw [denote2, denote2, ihf hc.1, iha hc.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hc
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    rw [denote2, denote2, ihty hc.1, ihval hc.2.1, ihbody hcb]
  | case10 d sn i e ihe =>
    intro hc
    rw [constsBound_proj] at hc
    rw [denote2, denote2, ihe hc]
  | case11 d n hsup =>
    intro _
    rw [denote2, if_pos hsup, denote2, if_pos (hG.1 ▸ hsup)]
  | case12 d n hsup =>
    intro _
    rw [denote2, if_neg hsup, denote2,
      if_neg (fun h => hsup (hG.1.trans h))]
  | case13 d s hsup =>
    intro _
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denote2, if_pos hsup, denote2, if_pos (hG.2 ▸ hsup),
      levelParamsAt_congr hF hnil, levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro _
    rw [denote2, if_neg hsup, denote2,
      if_neg (fun h => hsup (hG.2.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote2_bvar, denote2_bvar]
    | sort u => exact absurd rfl (hs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## Trap-checks on the two new hypotheses

Both hold on the diagonal, which proves nothing.  The check worth
running is whether they hold at a **non-degenerate** extension — a
hypothesis satisfied only where `env₀ = env` would make the discharge
say nothing about an install. -/

/-- **`LitGuardsAgree` is met at a real extension.**  Section 1's
probe stores a constant and moves neither guard.  Contrast
`natLitEnv`, where the same hypothesis fails — which is exactly
finding 2, and exactly where `Denote2EnvExtend` goes false. -/
theorem litGuardsAgree_probe : LitGuardsAgree Env.empty probeEnv := by
  refine ⟨?_, ?_⟩ <;> decide

/-- …and the probe really does extend the prefix, so the check above
is not the diagonal in disguise. -/
theorem findPreserved_empty_probe :
    FindPreserved Env.empty probeEnv := by
  intro n ci h
  exact nomatch h

end Setlec.SetR.Interp2
