import ConLeche.Model.Steps.Irrel
import ConLeche.Verify.Denote.StrLit

/-!
# The stuck fallbacks over `interp` (task #161, P4 — batch 7)

The defeq quarter (`Steps/DefEqP.lean`) routes seven residues out of
the stuck block.  This file discharges the four *semantic* ones that
do not belong to the basis tier:

| residue | discharge |
|---|---|
| `DefEqSpine` (5) | `defEqSpine_of_claims` — outright |
| `AppCongrStuck` (10) | `appCongrStuck_of_claims` — outright |
| `EtaCertStep` (11) | `etaCertStep_of_claims` — outright, `lamR_eta` |
| `StuckIrrelPQ` (6) | `stuckIrrelFueled_of_claims` — the proof-irrelevance arm outright, the three certificate arms routed |
| `DenotePStrLit` (7) | `denotePStrLit_of_guard` — outright, by computation |

`ReduceNatStepPQ` (residue 4) is **not** here: the `Nat` literal rows
are the basis tier's.

## What the P currency buys

Three of the five are *cleaner* than their v1 counterparts, for the
same reason `IrrelP.lean`'s proof irrelevance was:

* **T1/T2 (the spines).**  The v1 lane concludes a `DefEq` in the
  relational currency and needs `DefEqL` as a *second* inductive
  currency beside `DenoteSpine`.  Here the conclusion is a plain
  equation between two `interp` values, so the list recursion
  produces the single equation
  `asa.map (interp ρ) = bsa.map (interp ρ)` and
  `interp_mkAppN_congr` folds it — `DefEqL` has no counterpart and
  no relational rule is invoked at all.  `DefEqSpine` and
  `AppCongrStuck` differ **only** in where the head equality comes
  from (`acval_const_congr` on the nose vs. `ihd` at the head), so
  both are one call to the same `spine_congr`.

* **T3 (η).**  `lamR_eta` (`Interp/Ops.lean`) is *regime-uniform*: at
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
last arm is `proofIrrelPQ_of_claims` (`Steps/IrrelP.lean`); the first
three are **structure-capability tier** content — a stored structure's
η law and a stored unit-like family's collapse — and are routed as
`StructEtaIrrel` / `StructUnitIrrel`.  Their v1 counterparts (`PairEtaCertStepR`,
`StructEtaCertStepR` in `Bridge/StuckIrrel.lean`) are routed at exactly
the same three places, so the ledger is unchanged by the currency swap.

The two *totality* premises the P tier owes — a `denoteMeta` success this
file cannot produce — are the already-routed `InferReads` and
`WhnfReads` (`Steps/InferP.lean`); no new totality residue is
created here.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level inferTypeCore whnf
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
inductive DenoteMetaSpine (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (d : Nat) :
    List Expr → List AnnotTerm → Prop
  | nil : DenoteMetaSpine acval env φ d [] []
  | cons {a : Expr} {v : AnnotTerm} {as : List Expr} {vs : List AnnotTerm} :
      denoteMeta acval env φ d a = some v →
      DenoteMetaSpine acval env φ d as vs →
      DenoteMetaSpine acval env φ d (a :: as) (v :: vs)

/-- A member of a read spine reads (`DenoteMetaSpine`'s membership form —
the shape the projection clause's `getD` selection needs).  Relocated
from the retired `Steps/ProjPinsP.lean` (task #175 W6). -/
theorem DenoteMetaSpine.mem {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ x ∈ as, ∃ v, denoteMeta acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, ha⟩
    · exact ih x hx'

/-- A read spine has the length of its source. -/
theorem DenoteMetaSpine.length {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) : as.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- **The application spine, inverted at the validated reading**: the
head and every argument read, and the value is their `AnnotTerm`
application.  `denote_mkAppN_inv` without the fuel. -/
theorem denoteMeta_mkAppN_inv {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : AnnotTerm},
    denoteMeta acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denoteMeta acval env φ d f = some fa ∧
      DenoteMetaSpine acval env φ d as vs ∧ ea = ATerm.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denoteMeta_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

/-- **The spine congruence at `interp`**: equal heads and pointwise
equal arguments give equal applications.  One induction on the
argument list; the `.app` clause of `interp` is the whole content.
The pointwise hypothesis is carried as an equation between the two
*interpreted* spines — no relational currency is needed. -/
theorem interp_mkAppN_congr {ρ : Nat → V} :
    ∀ (asa bsa : List AnnotTerm) {fa fb : AnnotTerm},
      interp V ρ fa = interp V ρ fb →
      asa.map (interp V ρ) = bsa.map (interp V ρ) →
      interp V ρ (ATerm.mkAppN fa asa)
        = interp V ρ (ATerm.mkAppN fb bsa) := by
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
      exact ih bs (by simp only [interp_app, hf, hall.1]) hall.2

/-- Every argument of a truthful application spine is truthful, and so
is its head.  `WellDenoted.hoist_app`'s iterate, at `WellDenotedV`. -/
theorem hoist_spine {Δa : List AnnotTerm} :
    ∀ (asa : List AnnotTerm) {fa : AnnotTerm},
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (ATerm.mkAppN fa asa)) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ fa) ∧
        ∀ x ∈ asa, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · exact ((WellDenoted_app V ρ fa a) ▸ (happ ρ hρ).1).1
    · exact ((AnnotValid_app V ρ fa a) ▸ (happ ρ hρ).2).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fun ρ hρ =>
          ⟨((WellDenoted_app V ρ fa x) ▸ (happ ρ hρ).1).2.1,
            ((AnnotValid_app V ρ fa x) ▸ (happ ρ hρ).2).2⟩
      · exact hrest x hx'

/-- The frame conditions of every argument of a spine
(`frame_spineR`, P currency). -/
theorem frame_spine {m : EnvModel V env} {d : Nat} {Δa : List AnnotTerm}
    {a : Expr} (hws : Expr.WScoped d a)
    (hb : a.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded a)
    (hC : CtxOk m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOk m φ d Δa x := fun x hx =>
  ⟨hws.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hb x hx,
    fun l hl => hLb l (ConLeche.fvarLeaves_getAppArgs hx l hl),
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)⟩

/-- The frame conditions of a spine's head. -/
theorem frame_appFn {m : EnvModel V env} {d : Nat} {Δa : List AnnotTerm}
    {a : Expr} (hws : Expr.WScoped d a)
    (hb : a.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded a)
    (hC : CtxOk m φ d Δa a) :
    Expr.WScoped d a.getAppFn ∧
      a.getAppFn.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a.getAppFn ∧ CtxOk m φ d Δa a.getAppFn :=
  ⟨hws.getAppFn, ConLeche.looseBVarsBounded_getAppFn hb,
    fun l hl => hLb l (ConLeche.fvarLeaves_getAppFn l hl),
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppFn l hl)⟩

/-! ## T1 — `defEqList`'s soundness, and the shared spine congruence -/

/-- **A certified argument list is pointwise equal at `interp`.**
`defEqL_of_defEqListR`'s P transpose: the list recursion of
`defEqList` (`Kernel/Core.lean:755`), one `DefEqClaim` call per
certificate, in the checker's own order. -/
theorem map_interp_of_defEqListFueled {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) {d : Nat} {Δa : List AnnotTerm} :
    ∀ {as bs : List Expr} {asa bsa : List AnnotTerm},
      ConLeche.defEqListFueled μ env fuel d as bs = .ok true →
      (∀ x ∈ as, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
      (∀ x ∈ bs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
      DenoteMetaSpine m.acval env φ d as asa →
      DenoteMetaSpine m.acval env φ d bs bsa →
      (∀ x ∈ asa, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) →
      (∀ x ∈ bsa, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        asa.map (interp V ρ) = bsa.map (interp V ρ) := by
  intro as
  induction as with
  | nil =>
    intro bs asa bsa h _ _ hsa hsb _ _ ρ _
    cases hsa
    cases bs with
    | nil => cases hsb; rfl
    | cons _ _ =>
      simp [ConLeche.defEqListFueled, ConLeche.defEqList, pure, Except.pure] at h
  | cons x xs ih =>
    intro bs asa bsa h hfa hfb hsa hsb hoa hob ρ hρ
    cases bs with
    | nil =>
      simp [ConLeche.defEqListFueled, ConLeche.defEqList, pure, Except.pure] at h
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := ConLeche.defEqList_step_inv h
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

/-- **The shared spine congruence.**  Both `DefEqSpine` and
`AppCongrStuck` are this lemma; they differ only in the provenance of
`hhead` (a reading identity for the constant short-circuit, a
`DefEqClaim` verdict for the stuck congruence). -/
theorem spine_congr {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) {d : Nat} {a b : Expr}
    {Δa : List AnnotTerm} {aa ba : AnnotTerm}
    (hlist : ConLeche.defEqListFueled μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOk m φ d Δa a) (hCb : CtxOk m φ d Δa b)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hdb : denoteMeta m.acval env φ d b = some ba)
    (hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (hokB : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba)
    (hhead : ∀ {fa fb : AnnotTerm},
      denoteMeta m.acval env φ d a.getAppFn = some fa →
      denoteMeta m.acval env φ d b.getAppFn = some fb →
      (∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ fa) →
      (∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ fb) →
      ∀ σ : Nat → V, Sat V Δa σ → interp V σ fa = interp V σ fb)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ aa = interp V ρ ba := by
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp a).symm] at hda
  rw [show b = Expr.mkAppN b.getAppFn b.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp b).symm] at hdb
  obtain ⟨fa, asa, hfa, hspa, rfl⟩ := denoteMeta_mkAppN_inv hda
  obtain ⟨fb, bsa, hfb, hspb, rfl⟩ := denoteMeta_mkAppN_inv hdb
  obtain ⟨hoha, hoa⟩ := hoist_spine asa hokA
  obtain ⟨hohb, hob⟩ := hoist_spine bsa hokB
  exact interp_mkAppN_congr asa bsa (hhead hfa hfb hoha hohb ρ hρ)
    (map_interp_of_defEqListFueled ihd hlist (frame_spine hwa hba hLa hCa)
      (frame_spine hwb hbb hLb hCb) hspa hspb hoa hob ρ hρ)

/-- **Residue 5 discharged** — the lazy-delta same-head short-circuit.
The head equality is *on the nose*: `Level.isEquiv` is sound for
`eval`, and a constant's validated annotation reads nothing but its own
level parameters (`acval_const_congr`), so the two instantiations are
indistinguishable to the reading. -/
theorem defEqSpine_of_claims {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) (hap : AcvalParams m) :
    DefEqSpine μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨n, us, us', hfa, hfb, -, hlev, hlist⟩ := ConLeche.defeqSpine_inv h
  refine spine_congr ihd hlist hwa hba hLa hwb hbb hLb hCa hCb hda hdb
    hokA hokB (fun {ga gb} hga hgb _ _ σ _ => ?_) ρ hρ
  rw [hfa] at hga
  rw [hfb] at hgb
  rw [acval_const_congr hap hlev hga hgb]

/-! ## T2 — the stuck spine congruence -/

/-- **Residue 10 discharged** — head defeq plus argument-list defeq
gives equality of the applications.  `frame_spineR`'s argument at
`interp`: the head equality is `ihd`'s verdict, and `spine_congr`
does the rest. -/
theorem appCongrStuck_of_claims {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) :
    AppCongrStuck μ m φ fuel := by
  intro d a b Δa hhd hlist _hlen
    hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb hokA hokB ρ hρ
  obtain ⟨hwfa, hbfa, hLfa, hCfa⟩ := frame_appFn hwa hba hLa hCa
  obtain ⟨hwfb, hbfb, hLfb, hCfb⟩ := frame_appFn hwb hbb hLb hCb
  exact spine_congr ihd hlist hwa hba hLa hwb hbb hLb hCa hCb hda hdb
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
def StructEtaIrrel (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.structEtaCertFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **A stored unit-like family collapses its inhabitants**, routed.
Discharged at the **structure-capability tier**: the content is the
`unitlike` capability's own law, read off the install, exactly as
`structUnitCert_stepR` reads it off `DefEq.structUnit`.  (Note the
asymmetry with `UnitIrrelPQ` in `Steps/IrrelP.lean`: that one is
`isUnitLikeTy` on both *whnf'd inferred types*, this one is the
certificate's own telescope walk — two different obligations of the
same tier.) -/
def StructUnitIrrel (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.structUnitCertFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 6 discharged**, modulo the two structure-tier
certificates: the cascade's dispatch order, arm for arm, with the
proof-irrelevance arm closed outright by `proofIrrelPQ_of_claims`. -/
theorem stuckIrrelFueled_of_claims {m : EnvModel V env}
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hreads : InferReadsIOS m μ φ fuel)
    (hunit : UnitIrrelPQ μ m φ fuel)
    (hseta : StructEtaIrrel μ m φ fuel)
    (hsunit : StructUnitIrrel μ m φ fuel) :
    StuckIrrelPQ μ m φ fuel := by
  have hpi : ProofIrrelPQ μ m φ fuel :=
    proofIrrelPQ_of_claims ihis hsss hreads hunit
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, Bind.bind,
    Except.bind, ConLeche.structEtaCert_fold,
    ConLeche.structUnitCert_fold, ConLeche.proofIrrel_fold] at h
  cases h3 : ConLeche.structEtaCertFueled μ env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true =>
    exact hseta h3 hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  | false =>
  cases h4 : ConLeche.structEtaCertFueled μ env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true =>
    exact (hseta h4 hwb hbb hLb hwa hba hLa hCb hCa hdb hda hokB hokA
      ρ hρ).symm
  | false =>
  cases h5 : ConLeche.structUnitCertFueled μ env fuel d a b with
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
`denoteMeta`: `strLitToConstructor` (`Kernel/Core.lean:324`) builds
nothing but `.app`, `.const` and `.lit (.natVal _)` nodes, all three of
whose `denoteMeta` clauses are binder-free, and the `strVal` clause is
*defined* to be the corresponding `charListAV` spine.  So no `interp`
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
private theorem denoteMeta_const_nolevels
    {acval : Name → (Name → Nat) → AnnotTerm} {c : Name}
    {ci : ConLeche.ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denoteMeta acval env φ d (.const c [])
      = some (acval c (Level.substFn φ [] [])) := by
  rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- `List.nil.{0} Char`, read. -/
private theorem denoteMeta_nilTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listNilName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciN, p, mb, hfN, hlpN, -⟩ := listNil_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciN.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listNilName := by
    simp [levelParamsAt, hfN]
  rw [denoteMeta, denoteMeta_const hfN (by simp [hlpN]),
    denoteMeta_const_nolevels hfC hlpC d, hlpa]
  rfl

/-- `List.cons.{0} Char`, read. -/
private theorem denoteMeta_consTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listConsName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciC', p, -, -, -, hfC', hlpC', -⟩ := listCons_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciC'.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listConsName := by
    simp [levelParamsAt, hfC']
  rw [denoteMeta, denoteMeta_const hfC' (by simp [hlpC']),
    denoteMeta_const_nolevels hfC hlpC d, hlpa]
  rfl

/-- **The character-list expression reads as `charListAV`.** -/
private theorem denoteMeta_strLitList
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denoteMeta acval env φ d (ConLeche.strLitList cs)
        = some (charListAV
          (.app (acval ConLeche.listNilName
            (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (.app (acval ConLeche.listConsName
            (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (acval ConLeche.charOfNatName (Level.substFn φ [] []))
          (acval ConLeche.natZeroName (Level.substFn φ [] []))
          (acval ConLeche.natSuccName (Level.substFn φ [] []))
          cs) := by
  have hnat : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciF, mb, hfF, hlpF, -⟩ := charOfNat_shape hg
  intro cs
  induction cs with
  | nil =>
    rw [ConLeche.strLitList, charListAV]; exact denoteMeta_nilTerm hg d
  | cons c cs ih =>
    rw [ConLeche.strLitList, charListAV, denoteMeta, denoteMeta,
      denoteMeta_consTerm hg d, denoteMeta,
      denoteMeta_const_nolevels hfF hlpF d, denoteMeta_natLit hnat, ih]
    rfl

/-- **Residue 7 discharged** — a string literal's constructor form has
the literal's own validated reading, at every depth, together with the
four frame conditions (all free: the form is closed). -/
theorem denotePStrLit_of_guard {m : EnvModel V env} :
    DenotePStrLit m φ := by
  intro d st sa hg hsa
  obtain ⟨ciO, mb, hfO, hlpO, -⟩ := stringOfList_shape hg
  refine ⟨?_, ConLeche.strLitToConstructor_WScoped st d,
    ConLeche.strLitToConstructor_looseBVars st 0, fun l hl => ?_, ?_⟩
  · rw [ConLeche.strLitToConstructor_eq, denoteMeta,
      denoteMeta_const_nolevels hfO hlpO d, denoteMeta_strLitList hg d]
    rw [denoteMeta, if_pos hg] at hsa
    exact hsa
  · rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · exact ConLeche.strLitToConstructor_fvarLeaves st

/-! ## T3 — the η certificate

`etaCert` (`Kernel/Core.lean:1027`) infers the stuck side's type,
reduces it to a `∀`, defeqs the domains, defeqs the λ's opened body
against `app b x`, and — task #161 P2 — certifies `m₁.pw == m₂.pw`
at `μ.verifiedChecks`.  Read at `interp` those are exactly `lamR_eta`'s
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
`defeqStuck_claim` already carries — the bit certificate is only
written by a verified-mode run — and the two totality factors are the
routed `InferReads`/`WhnfReads`; no new residue. -/
theorem etaCertStep_of_claims {m : EnvModel V env}
    (hμ : μ.verifiedChecks = true)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hir : InferReadsIOS m μ φ fuel) (hwr : WhnfReads m μ φ fuel) :
    EtaCertStep μ m φ fuel := by
  intro d ty bd b mb Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨tb, ty₂, fb, m₂, htb, hwtb, hdty, hdbody, hpw⟩ :=
    ConLeche.etaCert_inv h
  simp only [Expr.WScoped] at hwa
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hLbd : Expr.LeavesBounded bd := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOk m φ d Δa ty :=
    hCa.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  have hCbd : CtxOk m φ d Δa bd :=
    hCa.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  -- the λ's own reading, and its two gradings
  obtain ⟨ta, bda, hta, hbda, rfl⟩ := denoteMeta_lam_inv hda
  have hokTa : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ ta := fun σ hσ =>
    ⟨((WellDenoted_lam V σ (pwBit φ mb.pw) ta bda) ▸ (hokA σ hσ).1).1,
      ((AnnotValid_lam V σ (pwBit φ mb.pw) ta bda) ▸ (hokA σ hσ).2).1⟩
  have hcons : ∀ σ : Nat → V, cons (σ 0) (fun j => σ (j + 1)) = σ := by
    intro σ; funext i; cases i with | zero => rfl | succ i => rfl
  have hokBda : ∀ σ : Nat → V, Sat V (ta :: Δa) σ →
      WellDenotedV V σ bda := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · have := ((WellDenoted_lam V _ (pwBit φ mb.pw) ta bda) ▸
        (hokA _ (Sat_tail hσ)).1).2.1 (σ 0) (hσ 0 ta rfl)
      rwa [hcons σ] at this
    · have := ((AnnotValid_lam V _ (pwBit φ mb.pw) ta bda) ▸
        (hokA _ (Sat_tail hσ)).2).2 (σ 0) (hσ 0 ta rfl)
      rwa [hcons σ] at this
  -- `b`'s inferred type, its reduct, and both readings
  obtain ⟨tba, htba⟩ :=
    hir htb hwb hbb hLb (LeafReads.of_ctxOk hCb) hdb
  have htbW : Expr.WScoped d tb :=
    ConLeche.inferTypeIO_WScoped m.wf fuel htb hwb
  have htbB : tb.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeIO_looseBVars m.wf fuel htb hwb hbb hLb
  have htbL : Expr.LeavesBounded tb := fun l hl =>
    hLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel htb hwb l hl)
  have hCtb : CtxOk m φ d Δa tb :=
    hCb.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel htb hwb)
  obtain ⟨hokTb, hmemB⟩ := ihis htb hwb hbb hLb hCb hdb htba hokB
  obtain ⟨wtba, hwtba⟩ := hwr hwtb htbW htbB htbL
    (LeafReads.of_ctxOk hCtb) htba
  obtain ⟨hokW, heqW⟩ :=
    ihw hwtb htbW htbB htbL hCtb htba hwtba hokTb
  have hwrW : Expr.WScoped d (Expr.forallE ty₂ fb m₂) :=
    ConLeche.whnf_WScoped m.wf fuel hwtb htbW
  have hwrB : (Expr.forallE ty₂ fb m₂).looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwtb htbB
  have hwrL : Expr.LeavesBounded (Expr.forallE ty₂ fb m₂) :=
    fun l hl => htbL l (ConLeche.whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCwr : CtxOk m φ d Δa (Expr.forallE ty₂ fb m₂) :=
    hCtb.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwtb)
  obtain ⟨ta₂, ba₂, hta₂, -, rfl⟩ := denoteMeta_forallE_inv hwtba
  simp only [Expr.WScoped] at hwrW
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwrB
  have hLty₂ : Expr.LeavesBounded ty₂ := fun l hl =>
    hwrL l (by simp [Expr.fvarLeaves, hl])
  have hCty₂ : CtxOk m φ d Δa ty₂ :=
    hCwr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  have hokTa₂ : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ ta₂ :=
    fun σ hσ =>
      ⟨((WellDenoted_pi V σ 0 (pwBit φ m₂.pw) ta₂ ba₂) ▸ (hokW σ hσ).1).1,
        ((AnnotValid_pi V σ 0 (pwBit φ m₂.pw) ta₂ ba₂)
          ▸ (hokW σ hσ).2).1⟩
  -- premise one: the two domains agree
  have hdom : ∀ σ : Nat → V, Sat V Δa σ →
      interp V σ ta₂ = interp V σ ta :=
    ihd hdty hwrW.1 hwrB.1 hLty₂ hwa.1 hba.1 hLty hCty₂ hCty hta₂ hta
      hokTa₂ hokTa
  -- premise two: `b` inhabits the product the ∀-type names
  have hmem : ∀ σ : Nat → V, Sat V Δa σ →
      interp V σ ba ∈ˢ piR (pwBit φ m₂.pw) (interp V σ ta₂)
        (fun x => interp V (cons x σ) ba₂) := by
    intro σ hσ
    have hm := hmemB σ hσ
    rw [heqW σ hσ, interp_pi] at hm
    exact hm
  -- premise three (the P2 certificate): the two bits are equal
  have hbit : pwBit φ mb.pw = pwBit φ m₂.pw := by
    rw [hpw hμ]
  -- premise four: the λ's fibre is `app ⟦b⟧`
  have hdbUp : denoteMeta m.acval env φ (d + 1) b = some ba.lift := by
    rw [denoteMeta_weaken_top m.acval_closed hwb, hdb]; rfl
  have hdapp : denoteMeta m.acval env φ (d + 1) (.app b (.fvar d ty))
      = some (.app ba.lift (.bvar 0)) := by
    rw [denoteMeta, hdbUp, denoteMeta_fvar]
    simp
  have hCfvar : CtxOk m φ (d + 1) (ta :: Δa) (.fvar d ty) := by
    have := CtxOk.openS (body := Expr.bvar 0) hCty
      (CtxOk.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves])) hta
      hokTa
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOk m φ (d + 1) (ta :: Δa) (.app b (.fvar d ty)) :=
    CtxOk.app (CtxOk.weakenTop hCb) hCfvar
  have hokApp : ∀ σ : Nat → V, Sat V (ta :: Δa) σ →
      WellDenotedV V σ (.app ba.lift (.bvar 0)) := by
    intro σ hσ
    have hσ' : Sat V Δa (fun j => σ (j + 1)) := Sat_tail hσ
    have hx : σ 0 ∈ˢ interp V (fun j => σ (j + 1)) ta := hσ 0 ta rfl
    have hok0 := WellDenotedV.hoist_lift (X := ta) hokB σ hσ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨hok0.1, by simp, pwBit φ m₂.pw,
        interp V (fun j => σ (j + 1)) ta₂,
        (fun x => interp V (cons x (fun j => σ (j + 1))) ba₂), ?_, ?_,
        ?_⟩
      · rw [interp_lift]; exact hmem _ hσ'
      · show σ 0 ∈ˢ _
        rw [hdom _ hσ']; exact hx
      · exact ((AnnotValid_pi V _ 0 (pwBit φ m₂.pw) ta₂ ba₂)
          ▸ (hokW _ hσ').2).2.2
    · rw [AnnotValid_app]
      exact ⟨hok0.2, by simp⟩
  have hbody : ∀ σ : Nat → V, Sat V (ta :: Δa) σ →
      interp V σ bda = interp V σ (.app ba.lift (.bvar 0)) :=
    ihd hdbody (Expr.WScoped.instantiate1 hwa.1 0 hwa.2)
      (ConLeche.looseBVarsBounded_instantiate1 bd 0 hba.2)
      (fun l hl => by
        rcases ConLeche.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
        · exact hLbd l h2
        · rw [ConLeche.Expr.fvarLeaves] at h2
          rcases List.mem_cons.mp h2 with rfl | h3
          · exact hba.1
          · exact hLty l h3)
      (by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (by omega) hwb, by omega,
          Expr.WScoped.mono (by omega) hwa.1⟩)
      (by simp [Expr.looseBVarsBounded, hbb])
      (fun l hl => by
        rw [ConLeche.Expr.fvarLeaves] at hl
        rcases List.mem_append.mp hl with h2 | h2
        · exact hLb l h2
        · rw [ConLeche.Expr.fvarLeaves] at h2
          rcases List.mem_cons.mp h2 with rfl | h3
          · exact hba.1
          · exact hLty l h3)
      (CtxOk.open hCbd hCty hta hokTa) hCapp hbda hdapp hokBda hokApp
  -- η: `lamR_eta`, regime-uniform
  have hpt : ∀ x, x ∈ˢ interp V ρ ta →
      interp V (cons x ρ) bda = SetTheory.app (interp V ρ ba) x := by
    intro x hx
    rw [hbody _ (Sat_cons V hρ hx), interp_app, interp_lift_cons,
      interp_bvar]
    rfl
  rw [interp_lam, lamR_congr hpt, hbit]
  exact lamR_eta (by rw [← hdom ρ hρ]; exact hmem ρ hρ)

end ConLeche.Model
