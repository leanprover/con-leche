module

public import InLeanProof.IndShape
public import InLeanProof.EnvBodiesPres

/-!
# O7: the inductive job's operations and its state residue (task #451, lane O7)

The inductive job (`InLean/Inductives/*`) calls the core through one record,
`sharedOpsC .verified fe` (`InLean/Inductives/BlockTail.lean`), at the
environment the stage runs at, and flushes the core's memos at every
environment transition (`flushC`), where master's cached job flushes.

* `CSOKIF s`: the part of `CSOKI` no flush drops (the free-variable table and
  the level memos), `CSOKF`'s twin; `CSOKIF.flushed`/`flushI_csoki` are
  `CSOKF.flushed`/`flushC_csok`: after a flush the full invariant holds at
  **any** environment.
* `OpsSimI fe L`: the four operations at `fe` simulate master's fueled
  operations (`fueledOpsM .verified`) at `L`, in `KnotSpecI`'s post shape;
  `opsSimI_of` from the knot (`SSimI false L fe` at the limits' fuel), and
  `opsSimI_of_pres` from the environment relation (`ssimI_of_pres`).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## The residue -/

/-- **What a flush keeps** (`CSOKF`'s twin): the free-variable table and the
level memos, the clauses of `CSOKI` that read no environment. -/
structure CSOKIF (s : InLean.CState) : Prop where
  fv : FVTableOK s
  fvClosed : ∀ (n : Nat) (ty : Expr) (cty : ConLeche.Expr), s.fvTys[n]? = some ty →
    TransS s ty = some cty → cty.looseBVarsBounded 0 = true
  lsimp : ∀ u v, s.lsimpC[u]? = some v → ∀ cu, toLevel u = some cu →
    toLevel v = some (ConLeche.Level.simplify cu)
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → ∀ cl cr, toLevel l = some cl → toLevel r = some cr →
    ConLeche.Level.isEquiv cl cr = some b

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

theorem CSOKI.residue {s : InLean.CState} (h : CSOKI mode eager env s) : CSOKIF s :=
  ⟨h.fv, h.fvClosed, h.lsimp, h.eqv⟩

theorem flushI_run (s : InLean.CState) : InLean.flushC s = .ok ((), s.flushed) := rfl

theorem tableOf_flushed (s : InLean.CState) : tableOf s.flushed = tableOf s := rfl

theorem TransS_flushed (s : InLean.CState) : TransS s.flushed = TransS s := rfl

theorem TrS_flushed (s : InLean.CState) : TrS s.flushed = TrS s := rfl

theorem OkS_flushed (s : InLean.CState) : OkS s.flushed = OkS s := rfl

theorem FVTableOK.flushed {s : InLean.CState} (h : FVTableOK s) : FVTableOK s.flushed :=
  ⟨h.cls, h.distinct, h.ty, h.seen, h.range⟩

theorem CSOKIF.flushed {s : InLean.CState} (h : CSOKIF s) : CSOKIF s.flushed :=
  ⟨h.fv.flushed, h.fvClosed, h.lsimp, h.eqv⟩

/-- **After a flush the invariant holds at any environment** (`flushC_csok`'s
twin): the kept clauses are the residue, the dropped memos are empty. -/
theorem flushI_csoki {s : InLean.CState} (h : CSOKIF s) (mode : ConLeche.CheckMode) (eager : Bool)
    (env : ConLeche.Env) : CSOKI mode eager env s.flushed := by
  refine ⟨h.fv.flushed, h.fvClosed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.lsimp, h.eqv, ?_,
    modeMemosOKI_empty⟩ <;> (intros; simp_all [InLean.CState.flushed])

theorem TabLe.flushed {s : InLean.CState} : TabLe s s.flushed := fun _ _ h => h

/-! ## The operations -/

/-- The post of a unary operation (`KnotSpecI`'s). -/
@[expose] def OpPostI (L : ConLeche.Env) (s₀ : InLean.CState) (d : Nat)
    (spec : ConLeche.FueledM ConLeche.Expr) (v : Expr) (s' : InLean.CState) : Prop :=
  CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧ Runs spec (TrS s' v) ∧
    ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true

/-- **InLean's job operations at `fe` simulate master's fueled ones at `L`**
(`fueledOpsM .verified`, what master's pure job runs at). -/
structure OpsSimI (fe : InLean.FEnv) (L : ConLeche.Env) : Prop where
  infer : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI .verified false L s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.opInfer .verified fe d i
    ⦃fun v s' => OpPostI L s₀ d ((ConLeche.fueledOpsM .verified).inferType L d (TrS s₀ i)) v s'; ⊤⦄
  whnf : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI .verified false L s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.opWhnf .verified fe d i
    ⦃fun v s' => OpPostI L s₀ d ((ConLeche.fueledOpsM .verified).whnf L d (TrS s₀ i)) v s'; ⊤⦄
  defeq : ∀ {s₀ : InLean.CState} {d : Nat} {i j : Expr},
    CSOKI .verified false L s₀ → OkS s₀ i = true → OkS s₀ j = true →
    ConLeche.Expr.WScoped d (TrS s₀ i) → ConLeche.Expr.WScoped d (TrS s₀ j) →
    (TrS s₀ i).looseBVarsBounded 0 = true → (TrS s₀ j).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.opDefeq .verified fe d i j
    ⦃fun v s' => CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs ((ConLeche.fueledOpsM .verified).isDefEq L d (TrS s₀ i) (TrS s₀ j)) v; ⊤⦄
  sort : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI .verified false L s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.opSort .verified fe d i
    ⦃fun u s' => CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okLv u = true ∧
      Runs ((ConLeche.fueledOpsM .verified).ensureSort L d (TrS s₀ i)) (trL u); ⊤⦄

/-- **The operations from the knot** at the checker's fuel (the recursion
limit's, `Limits.recDepth`). -/
theorem opsSimI_of {fe : InLean.FEnv} {L : ConLeche.Env}
    (h : SSimI false L fe (fe.limits.recDepth.getD InLean.checkFuel)) : OpsSimI fe L where
  infer hs hok hw hc := tripleI_iff_run.2 fun v s' hr => tripleI_iff_run.1 (h.infer hs hok hw hc) v s' hr
  whnf hs hok hw hc := tripleI_iff_run.2 fun v s' hr => tripleI_iff_run.1 (h.whnf hs hok hw hc) v s' hr
  defeq hs hoka hokb hwa hwb hca hcb := tripleI_iff_run.2 fun v s' hr => tripleI_iff_run.1 (h.defeq hs hoka hokb hwa hwb hca hcb) v s' hr
  sort {s₀ d i} hs hok hw hc := by
    refine tripleI_iff_run.2 fun u s' hr => ?_
    obtain ⟨h1, h2, h3, F, h4⟩ := tripleI_iff_run.1 (ensureSortI_spec h hs hok hw hc) u s' hr
    refine ⟨h1, h2, h3, F, ?_⟩
    rw [ConLeche.ensureSort_atF, ConLeche.ensureSort_def] at h4
    exact h4

/-- **The job's environment premises** at `fe` against `L`: core's
environment laws (`EnvLaws`, what a push reads), the relation,
con-leche's well-formedness and the projection bodies' range (P3b's three). -/
structure JobEnvI (fe : InLean.FEnv) (L : ConLeche.Env) : Prop where
  laws : EnvLaws
  pres : EnvPresI fe L
  wf : ConLeche.EnvWF L
  proj : ProjBodiesInRange fe

theorem JobEnvI.ops {fe : InLean.FEnv} {L : ConLeche.Env} (h : JobEnvI fe L) : OpsSimI fe L :=
  opsSimI_of (ssimI_of_pres h.pres h.wf h.proj _)

end InLeanProof
