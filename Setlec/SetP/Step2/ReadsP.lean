import Setlec.SetP.Step2.InferP
import Setlec.SetP.Step2.InferIOP
import Setlec.SetP.Step2.WhnfP
import Setlec.SetP.Step2.DefEqP
import Setlec.SetP.Step2.ProjPinsP
import Setlec.SetP.Annot.EnvS2P
import Setlec.SetBase.LitParams

/-!
# The totality consolidation (task #161, P4 batch 6)

The three P quarters route six *totality* residues — statements of the
form "the checker's output annotates", which the dual-success claims
cannot produce because both readings sit in their premises:

| residue | home |
| --- | --- |
| `InferReadsP` | `Step2/InferP.lean` |
| `WhnfReadsP` | `Step2/InferP.lean` |
| `WhnfCoreExistsP` | `Step2/WhnfP.lean` |
| `InferExistsP` | `Step2/WhnfP.lean` |
| `WhnfCoreReductExistsP` | `Step2/DefEqP.lean` |
| `DenotePDeltaP` | `Step2/DefEqP.lean` |

This module consolidates them.  Two are *free conversions* (T1) —
`DenotePDeltaP` of an environment field, `WhnfCoreReductExistsP` of
its statement-identical sibling — and the other four are consequences
of one **readability walk** over the checker's own clause structure
(T2/T3): `denoteP` fails only on a loose `.bvar`, an
unfindable or mis-arity `.const`, an unsupported literal guard, or a
`.proj` index `≥ 2`, and the checker never *manufactures* any of those
— every output is a subterm, an instantiation, or a stored type of
something the subject already reads.

## FINDING (batch 6) — `InferReadsP` as stated was REFUTABLE; REPAIRED

`inferBody`'s `.fvar` clause returns the leaf's **stored annotation**
`ty`, which `denoteP`'s `fvar` clause never looks at — so the subject's
reading carries no information about it, and the residue was false on
`.fvar 0 n (.const c [])` at `d = 1` with `c ∉ env`.  Batch 8 applied
the sanctioned repair: `InferReadsP` (`Step2/InferP.lean`) now carries
the leaf premise `LeafReadsP m φ d e`, which its sibling
`InferExistsP` got for free from its `CtxOkP`.  Nothing is routed —
every consumer holds a `CtxOkP` at the same depth and discharges the
premise by `LeafReadsP.of_ctxOkP` — and `inferReadsP_of` below closes
the residue from `ReadsInputsP` alone.  See DESIGN.md.

`WhnfReadsP` never had the gap: `whnf`/`whnfCore` never return a stored
leaf annotation, so its walk needs no leaf premise.

## What is routed, and to which tier

| routed leaf | discharged by |
| --- | --- |
| `IotaReadsP` | the ι tier (rule-RHS readability) |
| `WhnfCoreProjReadsP` | the install tier (projection tables) |
| `InferProjReadsP` | the install tier (projection tables) |
| `ReduceNatReadsP` | the literal tier (`natOpResult` shapes) |
| `AcvalDefnInstP` | the install tier (already an `EnvS2PM` field) |

They are bundled as `ReadsInputsP`; the suppliers at the end of the
file take that bundle and produce five of the six residues.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! # T1 — the free conversions

Two of the six residues are *notational* variants of facts the
quarters already carry, and the conversions are eta-expansions. -/

/-- **`DenotePDeltaP` from the environment's own field.**
`DenotePDeltaP` (`Step2/DefEqP.lean`) is statement-identical to
`DeltaP` (`Step2/WhnfP.lean`) — same binders, same premises, same
conclusion — so `deltaP_of` discharges it verbatim.  Stated at the
`AcvalDefnInstP` field so the consumer can pass `m.defn_reads`. -/
theorem denotePDeltaP_of_fields (m : EnvS2Core V env)
    (hdi : AcvalDefnInstP m) : DenotePDeltaP m φ :=
  fun hud hea => deltaP_of m hdi hud hea

/-- `DenotePDeltaP`, read straight off the P environment invariant. -/
theorem EnvS2PM.denotePDeltaP (mp : EnvS2PM V μ env) :
    DenotePDeltaP mp.base2 φ :=
  denotePDeltaP_of_fields mp.base2 mp.defn_reads

/-- **`WhnfCoreExistsP` and `WhnfCoreReductExistsP` are the same
statement.**  Compared field by field: same implicit binders
(`d`, `e`, `e'`, `Δa`, then `ea`), same run, same scoping package,
same `CtxOkP`/reading/grading premises, same conclusion.  The only
difference is that `WhnfCoreExistsP` names `μ` explicitly where
`WhnfCoreReductExistsP` takes it from the section variable, so the
conversion is an eta-expansion — in **both** directions. -/
theorem whnfCoreReductExistsP_of {m : EnvS2Core V env}
    (h : WhnfCoreExistsP μ m φ fuel) :
    WhnfCoreReductExistsP μ m φ fuel := by
  intro _d _e _e' _Δa hrun hws hb hLb _ea hC hea hok
  exact h hrun hws hb hLb hC hea hok

/-- The converse of `whnfCoreReductExistsP_of` (same statement). -/
theorem whnfCoreExistsP_of_reduct {m : EnvS2Core V env}
    (h : WhnfCoreReductExistsP μ m φ fuel) :
    WhnfCoreExistsP μ m φ fuel := by
  intro _d _e _e' _Δa hrun hws hb hLb _ea hC hea hok
  exact h hrun hws hb hLb hC hea hok

/-- **`InferReadsP → InferExistsP`, one direction only.**  The two
differ in their premise sets: `InferExistsP` (`Step2/WhnfP.lean`)
carries the whole `CtxOkP m φ d Δa e`, `InferReadsP`
(`Step2/InferP.lean`) only its leaf weakening `LeafReadsP`.  So the
conversion holds *from the weaker-premised statement to the
stronger-premised one* — the context projects to the leaf package
(`LeafReadsP.of_ctxOkP`) — and the converse does **not** hold as a
conversion (there is no `Δa` to supply). -/
theorem inferExistsP_of_reads {m : EnvS2Core V env}
    (h : InferReadsP m μ φ fuel) : InferExistsP μ m φ fuel := by
  intro _d _e _t _Δa hrun hws hb hLb _ea hC hea
  exact h hrun hws hb hLb (LeafReadsP.of_ctxOkP hC) hea

/-! # T2/T3 — the readability walk

The leaf side condition `LeafReadsP` and its kit
(`of_ctxOkP`/`of_subset`/`weakenTop`/`openS`) now live in
`Step2/InferP.lean`, next to the residue that carries it (batch 8).

## The walk's three statements

`WhnfReadsP` and `InferReadsP` (`Step2/InferP.lean`) are used verbatim
— since batch 8's repair the residues' own statements are exactly what
the induction proves.  `whnfCore` has no residue of its own
(`WhnfCoreExistsP`/`WhnfCoreReductExistsP` carry a `CtxOkP` and a
grading the walk never reads), so its statement is made here. -/

/-- **The `whnfCore` reduct reads** — `WhnfCoreExistsP` with the
`CtxOkP` and grading premises dropped. -/
def WhnfCoreReadsP {env : Env} (m : EnvS2Core V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ea : AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReadsP m φ d e →
    denoteP m.acval env φ d e = some ea →
    ∃ ea', denoteP m.acval env φ d e' = some ea'

/-- **The joint statement.**  The checker's knot is mutual, so the three
walks are one induction on the shared fuel: `whnfCore` at `fuel + 1`
calls `whnfCore` and `whnf` at `fuel`; `whnf` at `fuel + 1` calls
`whnfCore` at `fuel`; `infer` at `fuel + 1` calls `infer` and `whnf` at
`fuel`.  `defeq` returns a `Bool` and so owes no reading — the two
clauses that call it (`whnfCore`'s β, `infer`'s application) read it
for the verdict only. -/
def ReadsAllP {env : Env} (m : EnvS2Core V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  WhnfCoreReadsP m μ φ fuel ∧ WhnfReadsP m μ φ fuel ∧
    InferReadsP m μ φ fuel

/-! ## The routed leaves

Four clauses of the checker produce a term that is **not** a subterm,
an instantiation, or a stored type of anything the subject reads, so
their readability is not the walk's to prove.  Each is stated as the
*whole clause's* obligation and named for the tier that owes it. -/

/-- **ι, routed to the iota tier.**  A recursor's fired right-hand side
reads.  Discharged where the rules are installed: `checkDecl`'s
recursor-installation path validates every rule's RHS through the
checker's own front door, which is exactly this. -/
def IotaReadsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e'' : Expr} {ea : AVExpr},
    Setlec.iotaRecP μ env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReadsP m φ d e →
    denoteP m.acval env φ d e = some ea →
    ∃ ea', denoteP m.acval env φ d e'' = some ea' ∧
      Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e'' ∧ LeafReadsP m φ d e''

/-- **`whnfCore`'s projection clause, routed to the install tier.**  The
reduct is a spine argument of a `whnf`'d scrutinee selected by the
projection table; reading it needs the table's own well-formedness, so
the whole clause is routed (`ProjStepP`'s shape, readings only). -/
def WhnfCoreProjReadsP (μ : CheckMode) {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i : Nat} {sn : Name} {pe e' : Expr} {ea : AVExpr},
    whnfCore μ env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    LeafReadsP m φ d (.proj sn i pe) →
    denoteP m.acval env φ d (.proj sn i pe) = some ea →
    ∃ ea', denoteP m.acval env φ d e' = some ea'

/-- **`infer`'s projection clause, routed to the install tier.**  The
inferred type is `piResidual` of the entry's stored level-parametric
type; its readability is the projection table's, not the walk's. -/
def InferProjReadsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i : Nat} {sn : Name} {pe t : Expr} {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    LeafReadsP m φ d (.proj sn i pe) →
    denoteP m.acval env φ d (.proj sn i pe) = some ea →
    ∃ ta, denoteP m.acval env φ d t = some ta

/-- **The literal acceleration, routed to the literal tier.**
`reduceNat`'s output is a `Nat`/`Bool` literal or constructor spine
built from the pinned heads; it reads under the same support guard the
subject read through, and the tier that pins the operations owes the
statement (`ReduceNatStepP`'s shape, readings and scoping only). -/
def ReduceNatReadsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    denoteP m.acval env φ d e = some ea →
    ∃ ea', denoteP m.acval env φ d e₂ = some ea' ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ LeafReadsP m φ d e₂

/-! ## The two projection leaves, discharged from the walk itself
(task #161, PROJ/STR tier)

**Neither is a routed leaf after all.**  `WhnfCoreProjReadsP` and
`InferProjReadsP` were stated as clause-granular obligations for the
install tier on the reading that "the reduct is a spine argument of a
`whnf`'d scrutinee selected by the projection table; reading it needs
the table's own well-formedness".  What the tier finds is that the
table's contribution is *arithmetic only* — `projPinsP`'s
`numParams`/`numFields`/level-arity, plus `projResidualP`'s computed
residual — and that every reading the two clauses need is the walk's
own induction hypothesis at `fuel`, which `readsAllP_of` has in hand at
exactly the point it uses them.

So the **statements stand unchanged** and the two fields leave
`ReadsInputsP`; what the install tier owes is the *semantic* projection
rows (`ProjStepP`, `InferProjStepP`), not these.
-/

/-- **`WhnfCoreProjReadsP`, discharged.**  Both branches of the clause
read: the stuck one is the projection of the reduced scrutinee (the
subject's own `i < 2` carries over), the firing one is a spine argument
of a constructor application, head-normalised — and a spine argument of
a reading reads (`DenoteSpineP.mem`). -/
theorem whnfCoreProjReadsP_of {m : EnvS2Core V env}
    (ihwc : WhnfCoreReadsP m μ φ fuel) (ihw : WhnfReadsP m μ φ fuel) :
    WhnfCoreProjReadsP μ m φ fuel := by
  intro d i sn pe e' ea h hws hb hLb hlrb hea
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := Setlec.whnf_proj_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hlrpe : LeafReadsP m φ d pe :=
    hlrb.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hi2, rfl⟩ := denoteP_proj_inv hea
  -- the reduced scrutinee
  obtain ⟨v₂, hv₂⟩ := ihw hwpe hws hb hLpe hlrpe hvp
  have hlr₂ : LeafReadsP m φ d e₂ :=
    hlrpe.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwpe)
  have hw₂ : Expr.WScoped d e₂ := Setlec.whnf_WScoped m.wf fuel hwpe hws
  have hb₂ : e₂.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwpe hb
  have hL₂ : Expr.LeavesBounded e₂ := fun l hl =>
    hLpe l (Setlec.whnf_fvarLeaves m.wf fuel hwpe l hl)
  -- the string-literal expansion, if it fired
  obtain ⟨v₃, hv₃, hw₃, hb₃, hL₃, hlr₃⟩ :
      ∃ v₃, denoteP m.acval env φ d e₃ = some v₃ ∧
        Expr.WScoped d e₃ ∧ e₃.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₃ ∧ LeafReadsP m φ d e₃ := by
    rcases Setlec.projLitToCtorP_inv hlit with rfl | ⟨st, rfl, hg, hred⟩
    · exact ⟨v₂, hv₂, hw₂, hb₂, hL₂, hlr₂⟩
    · obtain ⟨hSC, hwc, hbc, hLc, hnilc⟩ :=
        denotePStrLit_of_guard d st hg hv₂
      have hlrc : LeafReadsP m φ d (Setlec.strLitToConstructor st) := by
        intro l hl; rw [hnilc] at hl; exact nomatch hl
      obtain ⟨v₃, hv₃⟩ := ihw hred hwc hbc hLc hlrc hSC
      exact ⟨v₃, hv₃, Setlec.whnf_WScoped m.wf fuel hred hwc,
        Setlec.whnf_looseBVars m.wf fuel hred hbc,
        fun l hl => hLc l (Setlec.whnf_fvarLeaves m.wf fuel hred l hl),
        hlrc.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hred)⟩
  rcases hcase with rfl | ⟨us, entry, hfn, hfe, hnat, hilt, hlenA, hlenU,
    hwcf, -⟩
  · exact ⟨.proj i v₃, by rw [denoteP_proj, hv₃]; exact if_pos hi2⟩
  · -- the table fires: the reduct is a head-normalised spine argument
    have hmem : e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)
        ∈ e₃.getAppArgs := Setlec.getD_mem (by rw [hlenA]; omega)
    have hwF : Expr.WScoped d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) :=
      hw₃.getAppArgs _ hmem
    have hbF : (e₃.getAppArgs.getD (entry.numParams + i)
      (.bvar 0)).looseBVarsBounded 0 = true :=
      Setlec.looseBVarsBounded_getAppArgs hb₃ _ hmem
    have hLF : Expr.LeavesBounded
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) := fun l hl =>
      hL₃ l (Setlec.fvarLeaves_getAppArgs hmem l hl)
    rw [show e₃ = Expr.mkAppN e₃.getAppFn e₃.getAppArgs from
      (Setlec.Expr.mkAppN_getApp e₃).symm] at hv₃
    obtain ⟨-, vs, -, hspa, -⟩ := denoteP_mkAppN_inv hv₃
    obtain ⟨vf, hvf⟩ := hspa.mem _ hmem
    exact ihwc hwcf hwF hbF hLF
      (hlr₃.of_subset (Setlec.fvarLeaves_getAppArgs hmem)) hvf

/-- **`InferProjReadsP`, discharged.**  The returned type is
`projResidualP`'s computed residual: the first parameter of the reduced
subject type, or the second applied to `pe.1`.  Both read — the
parameters because the reduced type reads (`ihi` then `ihw`), the
projection node because the subject's own reading supplies `i < 2`. -/
theorem inferProjReadsP_of {m : EnvS2Core V env}
    (ihi : InferReadsP m μ φ fuel) (ihw : WhnfReadsP m μ φ fuel) :
    InferProjReadsP μ m φ fuel := by
  intro d i sn pe t ea h hws hb hLb hlr hea
  -- task #161 item B2 (harvest site 21 / P10): the returned type is
  -- the clause's own computed two-way residual, so the inversion hands
  -- it over directly — `projResidualP`'s derivation from a
  -- `piResidual` premise is retired with the walk.
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, hpair, -⟩ := Setlec.inferTypeCore_proj_inv h
  obtain ⟨A, B, hAB, hcase⟩ :=
    hpair (projEntry_not_tower m.proj_ok hfe hnat)
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hlrpe : LeafReadsP m φ d pe :=
    hlr.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hi2, rfl⟩ := denoteP_proj_inv hea
  -- the subject's type, and its head normal form
  obtain ⟨tpea, htpea⟩ := ihi htpe hws hb hLpe hlrpe hvp
  have hwtpe : Expr.WScoped d tpe :=
    inferTypeCore_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (inferTypeCore_fvarLeaves m.wf fuel htpe hws l hl)
  obtain ⟨tea, htea⟩ := ihw hwte hwtpe hbtpe hLtpe
    (hlrpe.of_subset (inferTypeCore_fvarLeaves m.wf fuel htpe hws))
    htpea
  have hbte : te.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwte hbtpe
  -- the reduced type's parameter spine reads
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Setlec.Expr.mkAppN_getApp te).symm] at htea
  obtain ⟨-, vs, -, hspt, -⟩ := denoteP_mkAppN_inv htea
  rw [hAB] at hspt
  rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hspt.mem t (by simp)
  · obtain ⟨Ba, hBa⟩ := hspt.mem B (by simp)
    exact ⟨.app Ba (.proj 0 vp), by
      rw [denoteP_app, hBa, denoteP_proj, hvp]
      simp⟩

/-! ## T3a — the `whnfCore` clauses -/

/-- The six shapes `whnfCoreBody` returns unchanged: the reduct *is*
the subject. -/
private theorem whnfCoreReads_leaf {m : EnvS2Core V env}
    {d : Nat} {e e' : Expr} {ea : AVExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx n ty, e = .fvar idx n ty) ∨
      (∃ n ty body bi, e = .forallE n ty body bi) ∨
      (∃ n ty body mb, e = .lam n ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore μ env (fuel + 1) d e = .ok e')
    (hea : denoteP m.acval env φ d e = some ea) :
    ∃ ea', denoteP m.acval env φ d e' = some ea' := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, n, ty, rfl⟩ |
      ⟨n, ty, body, bi, rfl⟩ | ⟨n, ty, body, mb, rfl⟩ |
      ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCoreR_sort, whnfCoreR_fvar, whnfCoreR_forallE,
        whnfCoreR_lam, whnfCoreR_const, whnfCoreR_lit,
        Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  exact ⟨ea, hea⟩

/-- **The ζ clause.**  `denoteP_beta` at the `letE` reading: the
reduct's annotation is the body's, instantiated at the value's. -/
private theorem whnfCoreReads_letE {m : EnvS2Core V env}
    (ihwc : WhnfCoreReadsP m μ φ fuel)
    {d : Nat} {nn : Name} {tt vv bb e' : Expr} {ea : AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.letE nn tt vv bb) = .ok e')
    (hws : Expr.WScoped d (.letE nn tt vv bb))
    (hb : (Expr.letE nn tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE nn tt vv bb))
    (hlr : LeafReadsP m φ d (.letE nn tt vv bb))
    (hea : denoteP m.acval env φ d (.letE nn tt vv bb) = some ea) :
    ∃ ea', denoteP m.acval env φ d e' = some ea' := by
  rw [Setlec.whnfCore_succ] at h
  simp only [Setlec.whnfCoreBody, Setlec.whnfCore_def] at h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denoteP] at hea
  rcases hta : denoteP m.acval env φ d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denoteP m.acval env φ d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denoteP m.acval env φ (d + 1)
      (bb.instantiate1 (.fvar d nn tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  have hsubred : ∀ l ∈ (bb.instantiate1 vv).fvarLeaves,
      l ∈ (Expr.letE nn tt vv bb).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hred : denoteP m.acval env φ d (bb.instantiate1 vv)
      = some (ba.inst va) := by
    rw [denoteP_beta m.acval_closed (acval_inst_self m)
      (n := nn) (ty := tt) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0,
      hba]
    rfl
  exact ihwc h (Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2)
    (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
    (fun l hl => hLb l (hsubred l hl)) (hlr.of_subset hsubred) hred

/-- **The `.app` clause.**  The head's reduct reads by the induction
hypothesis; the β branch is `denoteP_beta` again, the ι branch is the
routed `IotaReadsP`, and the stuck fallback re-assembles the two
readings the `denoteP` `app` clause wants. -/
private theorem whnfCoreReads_app {m : EnvS2Core V env}
    (hiota : IotaReadsP μ m φ fuel) (ihwc : WhnfCoreReadsP m μ φ fuel)
    {d : Nat} {f a e' : Expr} {ea : AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hlr : LeafReadsP m φ d (.app f a))
    (hea : denoteP m.acval env φ d (.app f a) = some ea) :
    ∃ ea', denoteP m.acval env φ d e' = some ea' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hlrf : LeafReadsP m φ d f :=
    hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  have hlra : LeafReadsP m φ d a :=
    hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv hea
  obtain ⟨f', hwf, hcase⟩ := Setlec.whnf_app_inv h
  obtain ⟨fa', hfa'⟩ := ihwc hwf hws.1 hb.1 hLf hlrf hfa
  have hwf' : Expr.WScoped d f' :=
    Setlec.whnfCore_WScoped m.wf fuel hwf hws.1
  have hbf' : f'.looseBVarsBounded 0 = true :=
    Setlec.whnfCore_looseBVars m.wf fuel hwf hb.1
  have hLf' : Expr.LeavesBounded f' := fun l hl =>
    hLf l (Setlec.whnfCore_fvarLeaves m.wf fuel hwf l hl)
  have hiapp : denoteP m.acval env φ d (.app f' a)
      = some (.app fa' aa) := by rw [denoteP, hfa', haa]; rfl
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
  have hlrapp : LeafReadsP m φ d (.app f' a) := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hlrf l (Setlec.whnfCore_fvarLeaves m.wf fuel hwf l hl)
    · exact hlra l hl
  rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, -⟩ |
    ⟨e'', hio, hwe''⟩ | rfl
  · -- β: the reduct is the λ's body opened at the argument
    obtain ⟨tya, ba, htya, hbb, rfl⟩ := denoteP_lam_inv hfa'
    simp only [Expr.WScoped] at hwf'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
    have hsubred : ∀ l ∈ (body.instantiate1 a).fvarLeaves,
        l ∈ (Expr.app (.lam n ty body mm) a).fvarLeaves := by
      intro l hl
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · simp [Expr.fvarLeaves, h2]
      · simp [Expr.fvarLeaves, h2]
    have hred : denoteP m.acval env φ d (body.instantiate1 a)
        = some (ba.inst aa) := by
      rw [denoteP_beta m.acval_closed (acval_inst_self m)
        (n := n) (ty := ty) hwf'.2.fvarsBelow hws.2 hb.2 haa 0, hbb]
      rfl
    exact ihwc hbeta (Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2)
      (Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2)
      (fun l hl => hLapp l (hsubred l hl))
      (hlrapp.of_subset hsubred) hred
  · -- ι: the routed rule-firing residue, then the recursion
    obtain ⟨ea₂, hea₂, hwe, hbe, hLe, hlre⟩ :=
      hiota hio hwapp hbapp hLapp hlrapp hiapp
    exact ihwc hwe'' hwe hbe hLe hlre hea₂
  · -- stuck: the head moved, the argument did not
    exact ⟨_, hiapp⟩

/-- **`WhnfCoreReadsP` at `fuel + 1`** — the ten shapes. -/
theorem whnfCoreReadsP_succ {m : EnvS2Core V env}
    (hiota : IotaReadsP μ m φ fuel)
    (ihwc : WhnfCoreReadsP m μ φ fuel) (ihw : WhnfReadsP m μ φ fuel) :
    WhnfCoreReadsP m μ φ (fuel + 1) := by
  intro d e e' ea h hws hb hLb hlr hea
  match e with
  | .sort u => exact whnfCoreReads_leaf (Or.inl ⟨u, rfl⟩) h hea
  | .fvar idx n ty =>
    exact whnfCoreReads_leaf (Or.inr (Or.inl ⟨idx, n, ty, rfl⟩)) h hea
  | .forallE n ty body bi =>
    exact whnfCoreReads_leaf
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hea
  | .lam n ty body mb =>
    exact whnfCoreReads_leaf
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩)))) h hea
  | .const n us =>
    exact whnfCoreReads_leaf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩))))) h hea
  | .lit l =>
    exact whnfCoreReads_leaf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))))) h hea
  | .bvar i => exact (whnfCore_bvar_claimP m hea).elim
  | .letE nn tt vv bb =>
    exact whnfCoreReads_letE ihwc h hws hb hLb hlr hea
  | .app f a => exact whnfCoreReads_app hiota ihwc h hws hb hLb hlr hea
  | .proj sn i pe =>
    exact whnfCoreProjReadsP_of ihwc ihw h hws hb hLb hlr hea

/-! ## T3b — the `whnf` reduction loop

`whnfLoop_claimP`'s shape with everything semantic deleted: three
branches, and each one hands the *next* subject's reading to the
budget induction hypothesis.  The δ branch is the sharpest — `DeltaP`
says the reduct reads at the **same** annotation, so nothing moves. -/

private theorem whnfLoopReads {m : EnvS2Core V env}
    (ihwc : WhnfCoreReadsP m μ φ fuel)
    (hnat : ReduceNatReadsP μ m φ fuel) (hdelta : DeltaP m φ) :
    ∀ (budget : Nat) {d : Nat} {e e' : Expr} {ea : AVExpr},
      Setlec.whnfLoop (Setlec.pureFns μ env fuel) env d budget e
        = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      LeafReadsP m φ d e →
      denoteP m.acval env φ d e = some ea →
      ∃ ea', denoteP m.acval env φ d e' = some ea' := by
  intro budget
  induction budget with
  | zero =>
    intro d e e' ea h
    rw [Setlec.whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d e e' ea h hws hb hLb hlr hea
    rw [Setlec.whnfLoop, Setlec.whnfStep] at h
    simp only [Bind.bind, Except.bind, Setlec.whnfCore_def] at h
    cases hwc : whnfCore μ env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨ea₁, hea₁⟩ := ihwc hwc hws hb hLb hlr hea
    have hlr₁ : LeafReadsP m φ d e₁ :=
      hlr.of_subset (Setlec.whnfCore_fvarLeaves m.wf fuel hwc)
    have hws₁ : Expr.WScoped d e₁ :=
      Setlec.whnfCore_WScoped m.wf fuel hwc hws
    have hb₁ : e₁.looseBVarsBounded 0 = true :=
      Setlec.whnfCore_looseBVars m.wf fuel hwc hb
    have hLb₁ : Expr.LeavesBounded e₁ := fun l hl =>
      hLb l (Setlec.whnfCore_fvarLeaves m.wf fuel hwc l hl)
    cases hrn : Setlec.reduceNatP μ env fuel d e₁ with
    | error err =>
      rw [Setlec.reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [Setlec.reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨ea₂, hea₂, hws₂, hb₂, hLb₂, hlr₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hea₁
      exact ih h hws₂ hb₂ hLb₂ hlr₂ hea₂
    | none, h =>
      dsimp only at h
      cases hud : Setlec.unfoldDefinition env e₁ with
      | none =>
        rw [hud] at h
        obtain rfl : e₁ = e' := Except.ok.inj h
        exact ⟨ea₁, hea₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        exact ih h (Setlec.unfoldDefinition_WScoped m.wf hud hws₁)
          (Setlec.unfoldDefinition_looseBVars m.wf hud hb₁)
          (fun l hl => hLb₁ l
            (Setlec.unfoldDefinition_fvarLeaves m.wf hud l hl))
          (hlr₁.of_subset
            (Setlec.unfoldDefinition_fvarLeaves m.wf hud))
          (hdelta hud hea₁)

/-- **`WhnfReadsP` at `fuel + 1`** — the residue's own statement, from
the loop induction. -/
theorem whnfReadsP_succ {m : EnvS2Core V env}
    (ihwc : WhnfCoreReadsP m μ φ fuel)
    (hnat : ReduceNatReadsP μ m φ fuel) (hdelta : DeltaP m φ) :
    WhnfReadsP m μ φ (fuel + 1) := by
  intro d e e' ea h hws hb hLb hlr hea
  rw [Setlec.whnf_succ, Setlec.whnfBody] at h
  exact whnfLoopReads ihwc hnat hdelta Setlec.whnfLoopFuel h hws hb
    hLb hlr hea

/-! ## T2 — the `infer` clauses

Per clause, what the inferred type's reading *is*:

* `.sort` → a sort node: `denoteP_sortQ`, free;
* `.fvar` → the **stored leaf annotation**: the `LeafReadsP` premise
  (see the FINDING — the only clause that needs it);
* `.const` → the instantiated stored type: `ConstTypeP`, which the
  `EnvS2PM` invariant derives (`EnvS2PM.constTypeP`);
* `.lit` → `Nat`/`String`'s own leaf, under the support guard the
  subject already read through — free;
* `.forallE` → a sort node again, free;
* `.lam` → the copied ∀-type: the domain from the subject, the
  codomain from the induction hypothesis across the `abstract1`/
  `instantiate1` round trip;
* `.app`, `.letE` → β/ζ shapes: `denoteP_beta`, whose two leaf
  premises are `m.acval_closed` and `acval_inst_self`;
* `.proj` → routed (`InferProjReadsP`). -/

/-- `.sort`: the inferred type is `.sort (.succ u)`. -/
theorem inferReads_sort {m : EnvS2Core V env}
    {d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
  subst h
  exact ⟨_, denoteP_sortQ⟩

/-- `.fvar`: the inferred type is the leaf's stored annotation, and its
reading is exactly what `LeafReadsP` provides. -/
theorem inferReads_fvar {m : EnvS2Core V env}
    {d idx : Nat} {n : Name} {ty t : Expr}
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hlr : LeafReadsP m φ d (.fvar idx n ty)) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hlr (idx, n, ty) (by simp [Expr.fvarLeaves])
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.const`: the subject's own reading pins `env.find?` and the arity,
and `ConstTypeP` answers with the instantiated type's row. -/
theorem inferReads_const {m : EnvS2Core V env}
    (hct : ConstTypeP m φ) {d : Nat} {n : Name} {us : List Level}
    {t : Expr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denoteP m.acval env φ d (.const n us) = some ea) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  obtain ⟨ci, hf, rfl⟩ := Setlec.inferTypeCore_const_inv h
  rw [denoteP, hf] at hea
  dsimp only at hea
  split at hea
  · next hlen =>
    obtain ⟨ta, hta, -, -⟩ := hct d n ci us hf hlen
    exact ⟨ta, hta⟩
  · exact nomatch hea

/-- `.lit (.natVal _)`: the inferred type is `.const natName []`, whose
reading the support guard pins to the `Nat` leaf itself. -/
theorem inferReads_natLit {m : EnvS2Core V env}
    {d k : Nat} {t : Expr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : Setlec.natLitSupported env = true := by simpa using hg
    cases hf : env.find? Setlec.natName with
    | none =>
      exfalso
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        natName_levelParams_nil hgt hf
      rcases hd : denoteP m.acval env φ d
          (Expr.const Setlec.natName []) with _ | ta
      · exfalso
        rw [denoteP, hf] at hd
        dsimp only at hd
        rw [if_pos (by simp [hlp])] at hd
        exact nomatch hd
      · exact ⟨ta, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.lit (.strVal _)`: the same move at `String`. -/
theorem inferReads_strLit {m : EnvS2Core V env}
    {d : Nat} {s : String} {t : Expr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : Setlec.strLitSupported env = true := by simpa using hg
    cases hf : env.find? Setlec.stringName with
    | none =>
      exfalso
      simp only [Setlec.strLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hgt
      rw [hf] at h2
      exact nomatch h2
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        stringName_levelParams_nil hgt hf
      rcases hd : denoteP m.acval env φ d
          (Expr.const Setlec.stringName []) with _ | ta
      · exfalso
        rw [denoteP, hf] at hd
        dsimp only at hd
        rw [if_pos (by simp [hlp])] at hd
        exact nomatch hd
      · exact ⟨ta, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.forallE`: the inferred type is `.sort (.imax u v)`. -/
private theorem inferReads_forallE {m : EnvS2Core V env}
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  exact ⟨_, denoteP_sortQ⟩

/-- `.lam`: the copied ∀-type.  Its domain reading is the subject's own;
its codomain reading is the induction hypothesis at the opened body,
transported across the `abstract1`/`instantiate1` round trip — which is
where the leaf premise has to be *opened* (`LeafReadsP.openS`). -/
private theorem inferReads_lam {m : EnvS2Core V env}
    (ihi : InferReadsP m μ φ fuel)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hlr : LeafReadsP m φ d (.lam n ty body mb))
    (hea : denoteP m.acval env φ d (.lam n ty body mb) = some ea) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  obtain ⟨-, -, bt, -, -, hbt, -, -, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨tyA, ba, htyA, hba, -⟩ := denoteP_lam_inv hea
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  -- the abstraction round trip (`infer_lam_claimP`'s move)
  have hleaf :
      Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact ⟨rfl, rfl⟩
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d n ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl =>
      hleaf l (inferTypeCore_fvarLeaves m.wf fuel hbt hwopen l hl))
  have hbtb : bt.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hbt hwopen hbopen hLopen
  have hround : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
    abstract1_instantiate1 bt 0 hcons hbtb
  obtain ⟨bta, hbta⟩ :=
    ihi hbt hwopen hbopen hLopen
      (LeafReadsP.openS (n := n) hws.1 hws.2
        (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]))
        (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]))
        htyA)
      hba
  refine ⟨AVExpr.pi 0 (pwBit φ mb.pw) tyA bta, ?_⟩
  rw [denoteP, htyA, hround, hbta]
  rfl

/-- `.app`: the inferred type is the whnf'd ∀-type's codomain, opened at
the argument — `denoteP_beta` backwards.  The function's type reads by
the inference hypothesis, its head normal form by the reduction
hypothesis. -/
private theorem inferReads_app {m : EnvS2Core V env}
    (ihi : InferReadsP m μ φ fuel) (ihw : WhnfReadsP m μ φ fuel)
    {d : Nat} {f a t : Expr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hlr : LeafReadsP m φ d (.app f a))
    (hea : denoteP m.acval env φ d (.app f a) = some ea) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  obtain ⟨tf, n', ty', body', mt', hif, hwf, rfl, -⟩ :=
    Setlec.inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, -⟩ := denoteP_app_inv hea
  -- the function's inferred type
  obtain ⟨tfa, htfa⟩ :=
    ihi hif hws.1 hb.1 hLf
      (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])) hfa
  have hwtf : Expr.WScoped d tf :=
    inferTypeCore_WScoped m.wf fuel hif hws.1
  have hbtf : tf.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hif hws.1 hb.1 hLf
  have hLtf : Expr.LeavesBounded tf := fun l hl =>
    hLf l (inferTypeCore_fvarLeaves m.wf fuel hif hws.1 l hl)
  -- its head normal form, a ∀
  obtain ⟨wa, hwa⟩ := ihw hwf hwtf hbtf hLtf
    ((hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])).of_subset
      (inferTypeCore_fvarLeaves m.wf fuel hif hws.1)) htfa
  obtain ⟨-, b'a, -, hb'a, -⟩ := denoteP_forallE_inv hwa
  have hwW : Expr.WScoped d (.forallE n' ty' body' mt') :=
    Setlec.whnf_WScoped m.wf fuel hwf hwtf
  simp only [Expr.WScoped] at hwW
  refine ⟨b'a.inst aa, ?_⟩
  rw [denoteP_beta m.acval_closed (acval_inst_self m)
    (n := n') (ty := ty') hwW.2.fvarsBelow hws.2 hb.2 haa 0, hb'a]
  rfl

/-- `.letE`: the ζ-shaped recursion — the checker infers the body
*opened at the value*, whose reading is `denoteP_beta` at the `letE`
node's own three readings. -/
private theorem inferReads_letE {m : EnvS2Core V env}
    (ihi : InferReadsP m μ φ fuel)
    {d : Nat} {nn : Name} {tt vv bb t : Expr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.letE nn tt vv bb) = .ok t)
    (hws : Expr.WScoped d (.letE nn tt vv bb))
    (hb : (Expr.letE nn tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE nn tt vv bb))
    (hlr : LeafReadsP m φ d (.letE nn tt vv bb))
    (hea : denoteP m.acval env φ d (.letE nn tt vv bb) = some ea) :
    ∃ ta, denoteP m.acval env φ d t = some ta := by
  obtain ⟨-, -, -, -, -, -, -, hbody⟩ :=
    Setlec.inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denoteP] at hea
  rcases hta : denoteP m.acval env φ d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denoteP m.acval env φ d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denoteP m.acval env φ (d + 1)
      (bb.instantiate1 (.fvar d nn tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  have hsubred : ∀ l ∈ (bb.instantiate1 vv).fvarLeaves,
      l ∈ (Expr.letE nn tt vv bb).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hred : denoteP m.acval env φ d (bb.instantiate1 vv)
      = some (ba.inst va) := by
    rw [denoteP_beta m.acval_closed (acval_inst_self m)
      (n := nn) (ty := tt) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0,
      hba]
    rfl
  exact ihi hbody (Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2)
    (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
    (fun l hl => hLb l (hsubred l hl)) (hlr.of_subset hsubred) hred

/-- **`InferReadsP` at `fuel + 1`** — the eleven shapes. -/
theorem inferReadsP_succ {m : EnvS2Core V env}
    (hct : ConstTypeP m φ)
    (ihi : InferReadsP m μ φ fuel) (ihw : WhnfReadsP m μ φ fuel) :
    InferReadsP m μ φ (fuel + 1) := by
  intro d e t ea h hws hb hLb hlr hea
  match e with
  | .sort u => exact inferReads_sort h
  | .bvar i => rw [denoteP_bvar] at hea; exact nomatch hea
  | .fvar idx n ty => exact inferReads_fvar h hlr
  | .const n us => exact inferReads_const hct h hea
  | .lit (.natVal k) => exact inferReads_natLit h
  | .lit (.strVal s) => exact inferReads_strLit h
  | .forallE n ty body mb => exact inferReads_forallE h
  | .lam n ty body mb =>
    exact inferReads_lam ihi h hws hb hLb hlr hea
  | .app f a => exact inferReads_app ihi ihw h hws hb hLb hlr hea
  | .letE nn tt vv bb =>
    exact inferReads_letE ihi h hws hb hLb hlr hea
  | .proj sn i pe =>
    exact inferProjReadsP_of ihi ihw h hws hb hLb hlr hea

/-! # The joint induction and the routed bundle -/

/-- Fuel zero: every entry point throws, so all three statements are
vacuous. -/
theorem readsAllP_zero (m : EnvS2Core V env) : ReadsAllP m μ φ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro d e e' ea h
    rw [Setlec.whnfCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · intro d e e' ea h
    rw [Setlec.whnf_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · intro d e t ea h
    rw [Setlec.inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The walk's routed inputs**, one field per named leaf, each with
the tier that owes it.  `const_ty` and `defn` are *already* derived
facts of the P environment invariant (`EnvS2PM.constTypeP`,
`EnvS2PM.defn_reads`); the other four are the clause-granular residues
this file introduces. -/
structure ReadsInputsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) : Prop where
  /-- the stored type's reading at a `const` node — **install tier**,
  and already an `EnvS2PM` consequence (`EnvS2PM.constTypeP`) -/
  const_ty : ConstTypeP m φ
  /-- a stored definition's value reads to the constant's own leaf —
  **install tier**, and already an `EnvS2PM` field (`defn_reads`) -/
  defn : AcvalDefnInstP m
  /-- a fired ι rule's right-hand side reads — **iota tier** (task
  #172 B4: conditional on the same-fuel reads walk, since the io-graded
  certificate no longer traverses the fabricated arguments) -/
  iota : ∀ fuel, WhnfReadsP m μ φ fuel → InferReadsIOP m μ φ fuel →
    IotaReadsP μ m φ fuel
  /-- the literal acceleration's output reads — **literal tier** -/
  nat : ∀ fuel, ReduceNatReadsP μ m φ fuel

/-- **The two install-tier fields, from the environment invariant.**
`EnvS2PM` already carries both, so a caller holding the P environment
structure owes only the four clause-granular leaves. -/
theorem ReadsInputsP.ofEnvS2PM (mp : EnvS2PM V μ env)
    (hiota : ∀ fuel, WhnfReadsP mp.base2 μ φ fuel →
      InferReadsIOP mp.base2 μ φ fuel → IotaReadsP μ mp.base2 φ fuel)
    (hnat : ∀ fuel, ReduceNatReadsP μ mp.base2 φ fuel) :
    ReadsInputsP μ mp.base2 φ where
  const_ty := mp.constTypeP
  defn := mp.defn_reads
  iota := hiota
  nat := hnat

end Setlec.SetR.Interp2
