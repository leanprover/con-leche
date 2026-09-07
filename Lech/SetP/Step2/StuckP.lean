import Lech.SetP.Step2.IrrelP
import Lech.Verify.Denote.StrLit

/-!
# The stuck fallbacks over `interp2` (task #161, P4 — batch 7)

The defeq quarter (`Step2/DefEqP.lean`) routes seven residues out of
the stuck block.  This file discharges the four *semantic* ones that
do not belong to the basis tier:

| residue | discharge |
|---|---|
| `DefEqSpineP` (5) | `defEqSpineP_of_claims` — outright |
| `AppCongrStuckP` (10) | `appCongrStuckP_of_claims` — outright |
| `EtaCertStepP` (11) | `etaCertStepP_of_claims` — outright, `lamR_eta` |
| `StuckIrrelPQ` (6) | `stuckIrrelP_of_claims` — the proof-irrelevance arm outright, the three certificate arms routed |
| `DenotePStrLit` (7) | `denotePStrLit_of_guard` — outright, by computation |

`ReduceNatStepPQ` (residue 4) is **not** here: the `Nat` literal rows
are the basis tier's.

## What the P currency buys

Three of the five are *cleaner* than their v1 counterparts, for the
same reason `IrrelP.lean`'s proof irrelevance was:

* **T1/T2 (the spines).**  The v1 lane concludes a `DefEq` in the
  relational currency and needs `DefEqL` as a *second* inductive
  currency beside `DenoteSpine`.  Here the conclusion is a plain
  equation between two `interp2` values, so the list recursion
  produces the single equation
  `asa.map (interp2 ρ) = bsa.map (interp2 ρ)` and
  `interp2_mkAppN_congrP` folds it — `DefEqL` has no counterpart and
  no relational rule is invoked at all.  `DefEqSpineP` and
  `AppCongrStuckP` differ **only** in where the head equality comes
  from (`acval_const_congrP` on the nose vs. `ihd` at the head), so
  both are one call to the same `spine_congrP`.

* **T3 (η).**  `lamR_eta` (`Interp2/Ops.lean`) is *regime-uniform*: at
  bit `0` both sides collapse to `pt`, above it both are graphs, and
  the single statement covers both.  So the η discharge needs **no
  case split on the bit** — the v1 lane's two-branch argument
  disappears.  What the bit is used for instead is the *identification*
  of the two annotations: the λ's own `pwBit φ m₁.pw` must be the
  ∀-type's `pwBit φ m₂.pw`, and task #161 P2 put exactly that
  certificate into `etaCert`'s tail (`m₁.pw == m₂.pw` at
  `μ.verifiedChecks`), so a rewrite closes it.  This is the
  extraction idiom of `DefEqP.lean`'s "THE KEY DELTA" blocks, at the η
  site.

## The routed sub-residues

`stuckIrrel`'s cascade tries `structEtaCert` both ways,
`structUnitCert`, then `proofIrrel` (the pinned pair's `pairEtaCert`
that used to lead retired with the `PSigma'` pin, task #175 W6).  The
last arm is `proofIrrelPQ_of_claims` (`Step2/IrrelP.lean`); the first
three are **structure-capability tier** content — a stored structure's
η law and a stored unit-like family's collapse — and are routed as
`StructEtaIrrelP` / `StructUnitIrrelP`.  Their v1 counterparts (`PairEtaCertStepR`,
`StructEtaCertStepR` in `Bridge/StuckIrrel.lean`) are routed at exactly
the same three places, so the ledger is unchanged by the currency swap.

The two *totality* premises the P tier owes — a `denoteP` success this
file cannot produce — are the already-routed `InferReadsP` and
`WhnfReadsP` (`Step2/InferP.lean`); no new totality residue is
created here.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level inferTypeCore whnf
  isDefEqCore isUnitLikeTy)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The spine kit

`DenoteSpine`/`denote_mkAppN_inv` (`Verify/Denote/Tele.lean`) at the
validated reading.  Fuel-free, so the inversion is one induction and
the reconciliation of two readings is `Option.some.inj`. -/

/-- Each expression of a spine reads to the corresponding annotation
(`DenoteSpine`'s P transpose). -/
inductive DenoteSpineP (acval : Name → (Name → Nat) → AVExpr)
    (env : Env) (φ : Name → Nat) (d : Nat) :
    List Expr → List AVExpr → Prop
  | nil : DenoteSpineP acval env φ d [] []
  | cons {a : Expr} {v : AVExpr} {as : List Expr} {vs : List AVExpr} :
      denoteP acval env φ d a = some v →
      DenoteSpineP acval env φ d as vs →
      DenoteSpineP acval env φ d (a :: as) (v :: vs)

/-- A member of a read spine reads (`DenoteSpineP`'s membership form —
the shape the projection clause's `getD` selection needs).  Relocated
from the retired `Step2/ProjPinsP.lean` (task #175 W6). -/
theorem DenoteSpineP.mem {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) :
    ∀ x ∈ as, ∃ v, denoteP acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, ha⟩
    · exact ih x hx'

/-- A read spine has the length of its source. -/
theorem DenoteSpineP.length {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) : as.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- **The application spine, inverted at the validated reading**: the
head and every argument read, and the value is their `AVExpr`
application.  `denote_mkAppN_inv` without the fuel. -/
theorem denoteP_mkAppN_inv {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : AVExpr},
    denoteP acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denoteP acval env φ d f = some fa ∧
      DenoteSpineP acval env φ d as vs ∧ ea = AVExpr.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denoteP_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

/-- **The spine congruence at `interp2`**: equal heads and pointwise
equal arguments give equal applications.  One induction on the
argument list; the `.app` clause of `interp2` is the whole content.
The pointwise hypothesis is carried as an equation between the two
*interpreted* spines — no relational currency is needed. -/
theorem interp2_mkAppN_congrP {ρ : Nat → V} :
    ∀ (asa bsa : List AVExpr) {fa fb : AVExpr},
      interp2 V ρ fa = interp2 V ρ fb →
      asa.map (interp2 V ρ) = bsa.map (interp2 V ρ) →
      interp2 V ρ (AVExpr.mkAppN fa asa)
        = interp2 V ρ (AVExpr.mkAppN fb bsa) := by
  intro asa
  induction asa with
  | nil =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => exact hf
    | cons _ _ => simp at hall
  | cons a as ih =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => simp at hall
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hall
      exact ih bs (by simp only [interp2_app, hf, hall.1]) hall.2

/-- Every argument of a truthful application spine is truthful, and so
is its head.  `AnnotOk2.hoist_app`'s iterate, at `AnnotOkP`. -/
theorem hoistP_spine {Δa : List AVExpr} :
    ∀ (asa : List AVExpr) {fa : AVExpr},
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (AVExpr.mkAppN fa asa)) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ fa) ∧
        ∀ x ∈ asa, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · exact ((AnnotOk2_app V ρ fa a) ▸ (happ ρ hρ).1).1
    · exact ((AnnotValidV_app V ρ fa a) ▸ (happ ρ hρ).2).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fun ρ hρ =>
          ⟨((AnnotOk2_app V ρ fa x) ▸ (happ ρ hρ).1).2.1,
            ((AnnotValidV_app V ρ fa x) ▸ (happ ρ hρ).2).2⟩
      · exact hrest x hx'

/-- The frame conditions of every argument of a spine
(`frame_spineR`, P currency). -/
theorem frame_spineP {m : EnvS2Core V env} {d : Nat} {Δa : List AVExpr}
    {a : Expr} (hws : Expr.WScoped d a)
    (hb : a.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded a)
    (hC : CtxOkP m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOkP m φ d Δa x := fun x hx =>
  ⟨hws.getAppArgs x hx, Lech.looseBVarsBounded_getAppArgs hb x hx,
    fun l hl => hLb l (Lech.fvarLeaves_getAppArgs hx l hl),
    hC.of_subset (fun l hl => Lech.fvarLeaves_getAppArgs hx l hl)⟩

/-- The frame conditions of a spine's head. -/
theorem frame_appFnP {m : EnvS2Core V env} {d : Nat} {Δa : List AVExpr}
    {a : Expr} (hws : Expr.WScoped d a)
    (hb : a.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded a)
    (hC : CtxOkP m φ d Δa a) :
    Expr.WScoped d a.getAppFn ∧
      a.getAppFn.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a.getAppFn ∧ CtxOkP m φ d Δa a.getAppFn :=
  ⟨hws.getAppFn, Lech.looseBVarsBounded_getAppFn hb,
    fun l hl => hLb l (Lech.fvarLeaves_getAppFn l hl),
    hC.of_subset (fun l hl => Lech.fvarLeaves_getAppFn l hl)⟩

/-! ## T1 — `defEqList`'s soundness, and the shared spine congruence -/

/-- **A certified argument list is pointwise equal at `interp2`.**
`defEqL_of_defEqListR`'s P transpose: the list recursion of
`defEqList` (`Kernel/Core.lean:755`), one `DefEqClaims2P` call per
certificate, in the checker's own order. -/
theorem map_interp2_of_defEqListP {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) {d : Nat} {Δa : List AVExpr} :
    ∀ {as bs : List Expr} {asa bsa : List AVExpr},
      Lech.defEqListP μ env fuel d as bs = .ok true →
      (∀ x ∈ as, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) →
      (∀ x ∈ bs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) →
      DenoteSpineP m.acval env φ d as asa →
      DenoteSpineP m.acval env φ d bs bsa →
      (∀ x ∈ asa, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x) →
      (∀ x ∈ bsa, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        asa.map (interp2 V ρ) = bsa.map (interp2 V ρ) := by
  intro as
  induction as with
  | nil =>
    intro bs asa bsa h _ _ hsa hsb _ _ ρ _
    cases hsa
    cases bs with
    | nil => cases hsb; rfl
    | cons _ _ =>
      simp [Lech.defEqListP, Lech.defEqList, pure, Except.pure] at h
  | cons x xs ih =>
    intro bs asa bsa h hfa hfb hsa hsb hoa hob ρ hρ
    cases bs with
    | nil =>
      simp [Lech.defEqListP, Lech.defEqList, pure, Except.pure] at h
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := Lech.defEqList_step_inv h
      cases hsa with | cons hx hsa' => ?_
      cases hsb with | cons hy hsb' => ?_
      obtain ⟨hwx, hbx, hLx, hCx⟩ := hfa x (by simp)
      obtain ⟨hwy, hby, hLy, hCy⟩ := hfb y (by simp)
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · exact ihd hxy hwx hbx hLx hwy hby hLy hCx hCy hx hy
          (hoa _ (by simp)) (hob _ (by simp)) ρ hρ
      · exact ih htail (fun z hz => hfa z (by simp [hz]))
          (fun z hz => hfb z (by simp [hz])) hsa' hsb'
          (fun z hz => hoa z (by simp [hz]))
          (fun z hz => hob z (by simp [hz])) ρ hρ

/-- **The shared spine congruence.**  Both `DefEqSpineP` and
`AppCongrStuckP` are this lemma; they differ only in the provenance of
`hhead` (a reading identity for the constant short-circuit, a
`DefEqClaims2P` verdict for the stuck congruence). -/
theorem spine_congrP {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) {d : Nat} {a b : Expr}
    {Δa : List AVExpr} {aa ba : AVExpr}
    (hlist : Lech.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOkP m φ d Δa a) (hCb : CtxOkP m φ d Δa b)
    (hda : denoteP m.acval env φ d a = some aa)
    (hdb : denoteP m.acval env φ d b = some ba)
    (hokA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa)
    (hokB : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba)
    (hhead : ∀ {fa fb : AVExpr},
      denoteP m.acval env φ d a.getAppFn = some fa →
      denoteP m.acval env φ d b.getAppFn = some fb →
      (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ fa) →
      (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ fb) →
      ∀ σ : Nat → V, Sat2 V Δa σ → interp2 V σ fa = interp2 V σ fb)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ aa = interp2 V ρ ba := by
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (Lech.Expr.mkAppN_getApp a).symm] at hda
  rw [show b = Expr.mkAppN b.getAppFn b.getAppArgs from
    (Lech.Expr.mkAppN_getApp b).symm] at hdb
  obtain ⟨fa, asa, hfa, hspa, rfl⟩ := denoteP_mkAppN_inv hda
  obtain ⟨fb, bsa, hfb, hspb, rfl⟩ := denoteP_mkAppN_inv hdb
  obtain ⟨hoha, hoa⟩ := hoistP_spine asa hokA
  obtain ⟨hohb, hob⟩ := hoistP_spine bsa hokB
  exact interp2_mkAppN_congrP asa bsa (hhead hfa hfb hoha hohb ρ hρ)
    (map_interp2_of_defEqListP ihd hlist (frame_spineP hwa hba hLa hCa)
      (frame_spineP hwb hbb hLb hCb) hspa hspb hoa hob ρ hρ)

/-- **Residue 5 discharged** — the lazy-delta same-head short-circuit.
The head equality is *on the nose*: `Level.isEquiv` is sound for
`eval`, and a constant's validated annotation reads nothing but its own
level parameters (`acval_const_congrP`), so the two instantiations are
indistinguishable to the reading. -/
theorem defEqSpineP_of_claims {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) (hap : AcvalParamsP m) :
    DefEqSpineP μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨n, us, us', hfa, hfb, -, hlev, hlist⟩ := Lech.defeqSpine_inv h
  refine spine_congrP ihd hlist hwa hba hLa hwb hbb hLb hCa hCb hda hdb
    hokA hokB (fun {ga gb} hga hgb _ _ σ _ => ?_) ρ hρ
  rw [hfa] at hga
  rw [hfb] at hgb
  rw [acval_const_congrP hap hlev hga hgb]

/-! ## T2 — the stuck spine congruence -/

/-- **Residue 10 discharged** — head defeq plus argument-list defeq
gives equality of the applications.  `frame_spineR`'s argument at
`interp2`: the head equality is `ihd`'s verdict, and `spine_congrP`
does the rest. -/
theorem appCongrStuckP_of_claims {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) :
    AppCongrStuckP μ m φ fuel := by
  intro d a b Δa hhd hlist _hlen
    hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb hokA hokB ρ hρ
  obtain ⟨hwfa, hbfa, hLfa, hCfa⟩ := frame_appFnP hwa hba hLa hCa
  obtain ⟨hwfb, hbfb, hLfb, hCfb⟩ := frame_appFnP hwb hbb hLb hCb
  exact spine_congrP ihd hlist hwa hba hLa hwb hbb hLb hCa hCb hda hdb
    hokA hokB
    (fun {_ _} hga hgb hoha hohb σ hσ =>
      ihd hhd hwfa hbfa hLfa hwfb hbfb hLfb hCfa hCfb hga hgb
        hoha hohb σ hσ) ρ hρ

/-! ## T4 — `stuckIrrel`'s cascade

`stuckIrrel` (`Kernel/Core.lean`) is four attempts in order:
`structEtaCert` both ways, `structUnitCert`, then `proofIrrel`.  The
dispatch is not a rule — it is the *bridge's* order — and it is
discharged here arm for arm.  The "wrong way round" arm is `.symm`,
and the last arm is `proofIrrelPQ_of_claims`. -/

/-- **A stored structure's η certificate**, routed: `a` is the
constructor applied to `b`'s installed projections.  Discharged at the
**structure-capability tier** (the stored `EtaLaw` the caps pipeline
installs), not here — `StructEtaCertStepR`'s exact position. -/
def StructEtaIrrelP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Lech.structEtaCertP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **A stored unit-like family collapses its inhabitants**, routed.
Discharged at the **structure-capability tier**: the content is the
`unitlike` capability's own law, read off the install, exactly as
`structUnitCert_stepR` reads it off `DefEq.structUnit`.  (Note the
asymmetry with `UnitIrrelPQ` in `Step2/IrrelP.lean`: that one is
`isUnitLikeTy` on both *whnf'd inferred types*, this one is the
certificate's own telescope walk — two different obligations of the
same tier.) -/
def StructUnitIrrelP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Lech.structUnitCertP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 6 discharged**, modulo the two structure-tier
certificates: the cascade's dispatch order, arm for arm, with the
proof-irrelevance arm closed outright by `proofIrrelPQ_of_claims`. -/
theorem stuckIrrelP_of_claims {m : EnvS2Core V env}
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hsss : SortSemAtIOSP m μ φ fuel)
    (hreads : InferReadsIOSP m μ φ fuel)
    (hunit : UnitIrrelPQ μ m φ fuel)
    (hseta : StructEtaIrrelP μ m φ fuel)
    (hsunit : StructUnitIrrelP μ m φ fuel) :
    StuckIrrelPQ μ m φ fuel := by
  have hpi : ProofIrrelPQ μ m φ fuel :=
    proofIrrelPQ_of_claims ihis hsss hreads hunit
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  simp only [Lech.stuckIrrelP, Lech.stuckIrrel, Bind.bind,
    Except.bind, Lech.structEtaCert_fold,
    Lech.structUnitCert_fold, Lech.proofIrrel_fold] at h
  cases h3 : Lech.structEtaCertP μ env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true =>
    exact hseta h3 hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  | false =>
  cases h4 : Lech.structEtaCertP μ env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true =>
    exact (hseta h4 hwb hbb hLb hwa hba hLa hCb hCa hdb hda hokB hokA
      ρ hρ).symm
  | false =>
  cases h5 : Lech.structUnitCertP μ env fuel d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok r5 =>
  rw [h5] at h
  dsimp only at h
  cases r5 with
  | true =>
    exact hsunit h5 hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  | false =>
    exact hpi h hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ

/-! ## T5 — the string-literal expansion

`DenotePStrLit` turns out to be a **purely syntactic** fact about
`denoteP`: `strLitToConstructor` (`Kernel/Core.lean:324`) builds
nothing but `.app`, `.const` and `.lit (.natVal _)` nodes, all three of
whose `denoteP` clauses are binder-free, and the `strVal` clause is
*defined* to be the corresponding `charListT2` spine.  So no `interp2`
semantics is involved and nothing routes to the basis tier: the
discharge is `denote_strLitToConstructorV`'s walk
(`Verify/Denote/StrLit.lean`) transposed clause for clause, over the
same pinned shapes (`char_shape`, `stringOfList_shape`, `listNil_shape`,
`listCons_shape`, `charOfNat_shape` are facts about `Env` alone and are
reused verbatim). -/

/-- A stored constant with no level parameters reads as its leaf at the
empty substitution (`denote_const_nolevelsV`'s transpose; note the P
clause keeps `Level.substFn φ [] []` rather than collapsing it to `φ`,
which is exactly what the `strVal` clause writes). -/
private theorem denoteP_const_nolevelsP
    {acval : Name → (Name → Nat) → AVExpr} {c : Name}
    {ci : Lech.ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denoteP acval env φ d (.const c [])
      = some (acval c (Level.substFn φ [] [])) := by
  rw [denoteP_const hf (by simp [hlp]), hlp]

/-- `List.nil.{0} Char`, read. -/
private theorem denoteP_nilTermP {acval : Name → (Name → Nat) → AVExpr}
    (hg : Lech.strLitSupported env = true) (d : Nat) :
    denoteP acval env φ d
        (.app (.const Lech.listNilName [.zero])
          (.const Lech.charName []))
      = some (.app (acval Lech.listNilName
          (Level.substFn φ (levelParamsAt env Lech.listNilName)
            [.zero]))
        (acval Lech.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciN, p, nm, mb, hfN, hlpN, -⟩ := listNil_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciN.toConstantVal.levelParams
      = levelParamsAt env Lech.listNilName := by
    simp [levelParamsAt, hfN]
  rw [denoteP, denoteP_const hfN (by simp [hlpN]),
    denoteP_const_nolevelsP hfC hlpC d, hlpa]
  rfl

/-- `List.cons.{0} Char`, read. -/
private theorem denoteP_consTermP {acval : Name → (Name → Nat) → AVExpr}
    (hg : Lech.strLitSupported env = true) (d : Nat) :
    denoteP acval env φ d
        (.app (.const Lech.listConsName [.zero])
          (.const Lech.charName []))
      = some (.app (acval Lech.listConsName
          (Level.substFn φ (levelParamsAt env Lech.listConsName)
            [.zero]))
        (acval Lech.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciC', p, -, -, -, -, -, -, hfC', hlpC', -⟩ := listCons_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciC'.toConstantVal.levelParams
      = levelParamsAt env Lech.listConsName := by
    simp [levelParamsAt, hfC']
  rw [denoteP, denoteP_const hfC' (by simp [hlpC']),
    denoteP_const_nolevelsP hfC hlpC d, hlpa]
  rfl

/-- **The character-list expression reads as `charListT2`.** -/
private theorem denoteP_strLitListP
    {acval : Name → (Name → Nat) → AVExpr}
    (hg : Lech.strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denoteP acval env φ d (Lech.strLitList cs)
        = some (charListT2
          (.app (acval Lech.listNilName
            (Level.substFn φ (levelParamsAt env Lech.listNilName)
              [.zero]))
            (acval Lech.charName (Level.substFn φ [] [])))
          (.app (acval Lech.listConsName
            (Level.substFn φ (levelParamsAt env Lech.listConsName)
              [.zero]))
            (acval Lech.charName (Level.substFn φ [] [])))
          (acval Lech.charOfNatName (Level.substFn φ [] []))
          (acval Lech.natZeroName (Level.substFn φ [] []))
          (acval Lech.natSuccName (Level.substFn φ [] []))
          cs) := by
  have hnat : Lech.natLitSupported env = true := by
    simp only [Lech.strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciF, nm, mb, hfF, hlpF, -⟩ := charOfNat_shape hg
  intro cs
  induction cs with
  | nil =>
    rw [Lech.strLitList, charListT2]; exact denoteP_nilTermP hg d
  | cons c cs ih =>
    rw [Lech.strLitList, charListT2, denoteP, denoteP,
      denoteP_consTermP hg d, denoteP,
      denoteP_const_nolevelsP hfF hlpF d, denoteP_natLit hnat, ih]
    rfl

/-- **Residue 7 discharged** — a string literal's constructor form has
the literal's own validated reading, at every depth, together with the
four frame conditions (all free: the form is closed). -/
theorem denotePStrLit_of_guard {m : EnvS2Core V env} :
    DenotePStrLit m φ := by
  intro d st sa hg hsa
  obtain ⟨ciO, nm, mb, hfO, hlpO, -⟩ := stringOfList_shape hg
  refine ⟨?_, Lech.strLitToConstructor_WScoped st d,
    Lech.strLitToConstructor_looseBVars st 0, fun l hl => ?_, ?_⟩
  · rw [Lech.strLitToConstructor_eq, denoteP,
      denoteP_const_nolevelsP hfO hlpO d, denoteP_strLitListP hg d]
    rw [denoteP, if_pos hg] at hsa
    exact hsa
  · rw [Lech.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · exact Lech.strLitToConstructor_fvarLeaves st

/-! ## T3 — the η certificate

`etaCert` (`Kernel/Core.lean:1027`) infers the stuck side's type,
reduces it to a `∀`, defeqs the domains, defeqs the λ's opened body
against `app b x`, and — task #161 P2 — certifies `m₁.pw == m₂.pw`
at `μ.verifiedChecks`.  Read at `interp2` those are exactly `lamR_eta`'s
premises:

* the certificate identifies the two **data**, hence the two **bits**,
* `ihd` at the domains identifies the two **domains**,
* `ihi` + `ihw` put `⟦b⟧` **in the product** those two name,
* `ihd` at the opened body makes `⟦λ⟧`'s fibre **`app ⟦b⟧ x`**,

and `lamR_eta` closes it in one step, *for both regimes at once*: at
bit `0` it is `lamR_zero` against `eq_pt_of_mem_piR_zero`, above it
`eq_graph_app_of_mem_piSet`, and the statement does not distinguish
them.  The v1 lane's `etaCert_stepR` needs the relational `DefEq.eta`
rule for the same content; here there is no rule, only the law. -/

/-- **Residue 11 discharged.**  `hμ` is the mode hypothesis
`defeqStuck_claimP` already carries — the bit certificate is only
written by a verified-mode run — and the two totality factors are the
routed `InferReadsP`/`WhnfReadsP`; no new residue. -/
theorem etaCertStepP_of_claims {m : EnvS2Core V env}
    (hμ : μ.verifiedChecks = true)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hir : InferReadsIOSP m μ φ fuel) (hwr : WhnfReadsP m μ φ fuel) :
    EtaCertStepP μ m φ fuel := by
  intro d n ty bd b mb Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨tb, n₂, ty₂, fb, m₂, htb, hwtb, hdty, hdbody, hpw⟩ :=
    Lech.etaCert_inv h
  simp only [Expr.WScoped] at hwa
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hLbd : Expr.LeavesBounded bd := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkP m φ d Δa ty :=
    hCa.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  have hCbd : CtxOkP m φ d Δa bd :=
    hCa.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  -- the λ's own reading, and its two gradings
  obtain ⟨ta, bda, hta, hbda, rfl⟩ := denoteP_lam_inv hda
  have hokTa : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ ta := fun σ hσ =>
    ⟨((AnnotOk2_lam V σ (pwBit φ mb.pw) ta bda) ▸ (hokA σ hσ).1).1,
      ((AnnotValidV_lam V σ (pwBit φ mb.pw) ta bda) ▸ (hokA σ hσ).2).1⟩
  have hcons : ∀ σ : Nat → V, cons (σ 0) (fun j => σ (j + 1)) = σ := by
    intro σ; funext i; cases i with | zero => rfl | succ i => rfl
  have hokBda : ∀ σ : Nat → V, Sat2 V (ta :: Δa) σ →
      AnnotOkP V σ bda := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · have := ((AnnotOk2_lam V _ (pwBit φ mb.pw) ta bda) ▸
        (hokA _ (Sat2_tail hσ)).1).2.1 (σ 0) (hσ 0 ta rfl)
      rwa [hcons σ] at this
    · have := ((AnnotValidV_lam V _ (pwBit φ mb.pw) ta bda) ▸
        (hokA _ (Sat2_tail hσ)).2).2 (σ 0) (hσ 0 ta rfl)
      rwa [hcons σ] at this
  -- `b`'s inferred type, its reduct, and both readings
  obtain ⟨tba, htba⟩ :=
    hir htb hwb hbb hLb (LeafReadsP.of_ctxOkP hCb) hdb
  have htbW : Expr.WScoped d tb :=
    Lech.inferTypeIO_WScoped m.wf fuel htb hwb
  have htbB : tb.looseBVarsBounded 0 = true :=
    Lech.inferTypeIO_looseBVars m.wf fuel htb hwb hbb hLb
  have htbL : Expr.LeavesBounded tb := fun l hl =>
    hLb l (Lech.inferTypeIO_fvarLeaves m.wf fuel htb hwb l hl)
  have hCtb : CtxOkP m φ d Δa tb :=
    hCb.of_subset (Lech.inferTypeIO_fvarLeaves m.wf fuel htb hwb)
  obtain ⟨hokTb, hmemB⟩ := ihis htb hwb hbb hLb hCb hdb htba hokB
  obtain ⟨wtba, hwtba⟩ := hwr hwtb htbW htbB htbL
    (LeafReadsP.of_ctxOkP hCtb) htba
  obtain ⟨hokW, heqW⟩ :=
    ihw hwtb htbW htbB htbL hCtb htba hwtba hokTb
  have hwrW : Expr.WScoped d (Expr.forallE ty₂ fb m₂) :=
    Lech.whnf_WScoped m.wf fuel hwtb htbW
  have hwrB : (Expr.forallE ty₂ fb m₂).looseBVarsBounded 0 = true :=
    Lech.whnf_looseBVars m.wf fuel hwtb htbB
  have hwrL : Expr.LeavesBounded (Expr.forallE ty₂ fb m₂) :=
    fun l hl => htbL l (Lech.whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCwr : CtxOkP m φ d Δa (Expr.forallE ty₂ fb m₂) :=
    hCtb.of_subset (Lech.whnf_fvarLeaves m.wf fuel hwtb)
  obtain ⟨ta₂, ba₂, hta₂, -, rfl⟩ := denoteP_forallE_inv hwtba
  simp only [Expr.WScoped] at hwrW
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwrB
  have hLty₂ : Expr.LeavesBounded ty₂ := fun l hl =>
    hwrL l (by simp [Expr.fvarLeaves, hl])
  have hCty₂ : CtxOkP m φ d Δa ty₂ :=
    hCwr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  have hokTa₂ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ ta₂ :=
    fun σ hσ =>
      ⟨((AnnotOk2_pi V σ 0 (pwBit φ m₂.pw) ta₂ ba₂) ▸ (hokW σ hσ).1).1,
        ((AnnotValidV_pi V σ 0 (pwBit φ m₂.pw) ta₂ ba₂)
          ▸ (hokW σ hσ).2).1⟩
  -- premise one: the two domains agree
  have hdom : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ ta₂ = interp2 V σ ta :=
    ihd hdty hwrW.1 hwrB.1 hLty₂ hwa.1 hba.1 hLty hCty₂ hCty hta₂ hta
      hokTa₂ hokTa
  -- premise two: `b` inhabits the product the ∀-type names
  have hmem : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ ba ∈ˢ piR (pwBit φ m₂.pw) (interp2 V σ ta₂)
        (fun x => interp2 V (cons x σ) ba₂) := by
    intro σ hσ
    have hm := hmemB σ hσ
    rw [heqW σ hσ, interp2_pi] at hm
    exact hm
  -- premise three (the P2 certificate): the two bits are equal
  have hbit : pwBit φ mb.pw = pwBit φ m₂.pw := by
    rw [hpw hμ]
  -- premise four: the λ's fibre is `app ⟦b⟧`
  have hdbUp : denoteP m.acval env φ (d + 1) b = some ba.lift := by
    rw [denoteP_weaken_top m.acval_closed hwb, hdb]; rfl
  have hdapp : denoteP m.acval env φ (d + 1) (.app b (.fvar d ty))
      = some (.app ba.lift (.bvar 0)) := by
    rw [denoteP, hdbUp, denoteP_fvar]
    simp
  have hCfvar : CtxOkP m φ (d + 1) (ta :: Δa) (.fvar d ty) := by
    have := CtxOkP.openS (n := n) (body := Expr.bvar 0) hCty
      (CtxOkP.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves])) hta
      hokTa
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOkP m φ (d + 1) (ta :: Δa) (.app b (.fvar d ty)) :=
    CtxOkP.app (CtxOkP.weakenTop hCb) hCfvar
  have hokApp : ∀ σ : Nat → V, Sat2 V (ta :: Δa) σ →
      AnnotOkP V σ (.app ba.lift (.bvar 0)) := by
    intro σ hσ
    have hσ' : Sat2 V Δa (fun j => σ (j + 1)) := Sat2_tail hσ
    have hx : σ 0 ∈ˢ interp2 V (fun j => σ (j + 1)) ta := hσ 0 ta rfl
    have hok0 := AnnotOkP.hoist_lift (X := ta) hokB σ hσ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨hok0.1, by simp, pwBit φ m₂.pw,
        interp2 V (fun j => σ (j + 1)) ta₂,
        (fun x => interp2 V (cons x (fun j => σ (j + 1))) ba₂), ?_, ?_,
        ?_⟩
      · rw [interp2_lift]; exact hmem _ hσ'
      · show σ 0 ∈ˢ _
        rw [hdom _ hσ']; exact hx
      · exact ((AnnotValidV_pi V _ 0 (pwBit φ m₂.pw) ta₂ ba₂)
          ▸ (hokW _ hσ').2).2.2
    · rw [AnnotValidV_app]
      exact ⟨hok0.2, by simp⟩
  have hbody : ∀ σ : Nat → V, Sat2 V (ta :: Δa) σ →
      interp2 V σ bda = interp2 V σ (.app ba.lift (.bvar 0)) :=
    ihd hdbody (Expr.WScoped.instantiate1 hwa.1 0 hwa.2)
      (Lech.looseBVarsBounded_instantiate1 bd 0 hba.2)
      (fun l hl => by
        rcases Lech.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
        · exact hLbd l h2
        · rw [Lech.Expr.fvarLeaves] at h2
          rcases List.mem_cons.mp h2 with rfl | h3
          · exact hba.1
          · exact hLty l h3)
      (by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (by omega) hwb, by omega,
          Expr.WScoped.mono (by omega) hwa.1⟩)
      (by simp [Expr.looseBVarsBounded, hbb])
      (fun l hl => by
        rw [Lech.Expr.fvarLeaves] at hl
        rcases List.mem_append.mp hl with h2 | h2
        · exact hLb l h2
        · rw [Lech.Expr.fvarLeaves] at h2
          rcases List.mem_cons.mp h2 with rfl | h3
          · exact hba.1
          · exact hLty l h3)
      (CtxOkP.open hCbd hCty hta hokTa) hCapp hbda hdapp hokBda hokApp
  -- η: `lamR_eta`, regime-uniform
  have hpt : ∀ x, x ∈ˢ interp2 V ρ ta →
      interp2 V (cons x ρ) bda = SetTheory.app (interp2 V ρ ba) x := by
    intro x hx
    rw [hbody _ (Sat2_cons V hρ hx), interp2_app, interp2_lift_cons,
      interp2_bvar]
    rfl
  rw [interp2_lam, lamR_congr hpt, hbit]
  exact lamR_eta (by rw [← hdom ρ hρ]; exact hmem ρ hρ)

end Lech.SetP
