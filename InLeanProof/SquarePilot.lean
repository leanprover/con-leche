module

public import InLeanProof.KnotI
public import ConLeche.Cached.CoreC
import ConLeche.Verify.Cached.DiscC1
import ConLeche.Verify.InferLemmas

/-!
# Pilot: the commuting-square route on `ensureSortI` (task #451, lane P2-0)

The comparison the coordinator asked for, next to the copied-script route
(`ensureSortI_spec`, `InLeanProof/KnotI.lean`).  The square route reuses
`Verify/Cached`'s body theorem **as a theorem**:

1. **An oracle knot** for the cached body: `oracleC F`, every slot the pure
   fueled entry at fuel `F`, the state untouched.
2. **The cached body theorem, generic in its callbacks**: master states
   `ensureSortC_spec` for the concrete knot `coreKnotI … f` with `SSimC` as
   its hypothesis; reused as a theorem it must quantify over a callback
   record that meets the slot triples (`WhnfSpecC`).  Master's script proves
   that unchanged (`ensureSortC_spec_gen`); it is the statement that
   changes, in every `Verify/Cached` body file.
3. **The oracle meets the slot triples** (`oracle_whnfSpec`), from the pure
   checker's scope theorem (`whnf_WScoped`).
4. **The square** (`ensureSort_square`): InLean's run, at the translation,
   is the cached body's run on the oracle at some fuel — a relational proof
   by hand: `vcgen` is unary.
5. **The composition** (`ensureSortI_by_square`): 4, then 2 at the oracle,
   gives the pure answer.

The DESIGN record (lane P2-0) compares the two routes.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## 1. The oracle knot -/

/-- A pure computation at fuel `F`, in the cached monad, the state untouched. -/
@[expose] def liftAt {α : Type} (p : ConLeche.FueledM α) (F : Nat) : ConLeche.Cached.CheckCM α :=
  fun c => match p.val F with
    | .ok v => .ok (v, c)
    | .error x => .error x

/-- **The oracle knot**: every slot is the pure fueled entry at fuel `F`. -/
@[expose] def oracleC (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env) (F : Nat) :
    ConLeche.Cached.CoreFnsI where
  whnfCore c d e := liftAt ((ConLeche.fueledFns mode eager env).whnfCore c d e) F
  whnf d e := liftAt ((ConLeche.fueledFns mode eager env).whnf d e) F
  infer d e := liftAt ((ConLeche.fueledFns mode eager env).infer d e) F
  defeq d a b := liftAt ((ConLeche.fueledFns mode eager env).defeq d a b) F
  defeqE d a b := liftAt ((ConLeche.fueledFns mode eager env).defeqE d a b) F
  inferIO d e := liftAt ((ConLeche.fueledFns mode eager env).inferIO d e) F

/-! ## 2. The cached body theorem, generic in its callbacks -/

/-- The `whnf` slot's triple (`SSimC.whnf_spec`'s statement, for any record). -/
abbrev WhnfSpecC (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : ConLeche.Cached.CoreFnsI) : Prop :=
  ∀ {s₀ : ConLeche.Cached.CState} {d : Nat} {i : ConLeche.Expr},
    CSOK mode eager env s₀ → ConLeche.Expr.WScoped d i →
    ⦃fun s => s = s₀⦄ r.whnf d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((ConLeche.fueledFns mode eager env).whnf d i) r ∧
      ConLeche.Expr.WScoped d r; ⊤⦄

/-- **Master's `ensureSortC_spec`, generic**: the same script, over any
callback record meeting the `whnf` triple. -/
theorem ensureSortC_spec_gen {r : ConLeche.Cached.CoreFnsI} (hk : WhnfSpecC mode eager env r)
    {d : Nat} {i : ConLeche.Expr} {s₀ : ConLeche.Cached.CState} (hs : CSOK mode eager env s₀)
    (hw : ConLeche.Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ConLeche.Cached.ensureSortI r d i
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env d i) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.ensureSort] =>
    vcgen [ConLeche.Cached.ensureSortI, hk hs] <;> finish

/-! ## 3. The oracle meets the slot triple -/

theorem oracle_whnfSpec (henv : ConLeche.EnvWF env) (F : Nat) :
    WhnfSpecC mode eager env (oracleC mode eager env F) := by
  intro s₀ d i hs hw
  rw [triple_iff_run]
  intro v s' hrun
  simp only [oracleC, liftAt] at hrun
  split at hrun
  · rename_i w hp
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hs, ⟨F, hp⟩, ConLeche.whnf_WScoped henv F hp hw⟩
  · simp at hrun

/-! ## 4. The square -/

/-- An InLean triple is a statement about its successful runs
(`triple_iff_run`'s twin). -/
theorem tripleI_run {β : Type} {s₀ : InLean.CState} {c : InLean.CheckCM β}
    {Q : β → InLean.CState → Prop} (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => Q v s'; ⊤⦄) :
    ∀ v s', c s₀ = .ok (v, s') → Q v s' := by
  intro v s' hr
  obtain ⟨h⟩ := h
  have := h s₀ rfl
  rw [StateT.wp_apply_eq, StateT.run, hr] at this
  exact this

/-- **The square for `ensureSortI`**: an InLean run answers, at the
translation, what the cached body answers on the oracle, from any state, at
a fuel the InLean run's `whnf` call fixes. -/
theorem ensureSort_square {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat}
    {i : Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true)
    {u : Level} {s' : InLean.CState} (hrun : ensureSortI r d i s₀ = .ok (u, s')) :
    ∃ F, ∀ c, ConLeche.Cached.ensureSortI (oracleC mode eager env F) d (TrS s₀ i) c =
      .ok (trL u, c) := by
  cases hwh : r.whnf d i s₀ with
  | error x =>
    simp [InLean.ensureSortI, hwh, bind, StateT.bind, Except.bind] at hrun
  | ok p =>
    obtain ⟨w, s₁⟩ := p
    obtain ⟨-, -, -, ⟨F, hF⟩, -, -⟩ := tripleI_run (ih.whnf hs hok hw hc) w s₁ hwh
    refine ⟨F, fun c => ?_⟩
    cases hsw : EO.stripTop w
    case sort u' =>
      simp [InLean.ensureSortI, hwh, hsw, bind, StateT.bind, Except.bind, pure, StateT.pure,
        Except.pure] at hrun
      obtain ⟨rfl, -⟩ := hrun
      have htr : TrS s₁ w = .sort (trL u') := by rw [← TrS_stripTop, hsw, TrS_sort]
      simp only [ConLeche.Cached.ensureSortI, oracleC, liftAt, bind, StateT.bind]
      rw [hF, htr]
      rfl
    all_goals
      simp [InLean.ensureSortI, hwh, hsw, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hrun

/-! ## 5. The composition -/

/-- **The square route's answer**: from InLean's run, the pure `ensureSort`
answers the translated level — `ensureSortI_spec`'s `Runs` conjunct, by the
reused cached theorem. -/
theorem ensureSortI_by_square (henv : ConLeche.EnvWF env) {r : InLean.CoreFnsI}
    (ih : KnotSpecI mode eager env r) {d : Nat} {i : Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true)
    {u : Level} {s' : InLean.CState} (hrun : ensureSortI r d i s₀ = .ok (u, s')) :
    Runs (ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env d (TrS s₀ i)) (trL u) := by
  obtain ⟨F, hsq⟩ := ensureSort_square ih hs hok hw hc hrun
  have hc₀ : CSOK mode eager env ({} : ConLeche.Cached.CState).flushed :=
    flushC_csok CSOKF.empty
  exact (triple_iff_run.1 (ensureSortC_spec_gen (oracle_whnfSpec henv F) hc₀ hw)
    (trL u) _ (hsq _)).2

end InLeanProof
