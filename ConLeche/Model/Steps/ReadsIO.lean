module

public import ConLeche.Model.Steps.Reads
import ConLeche.Model.Steps.TowerKit
import ConLeche.Model.Steps.InferIO
public section

/-!
# The io reads walk — `InferReadsIO` DISCHARGED (task #172, batch B3)

`InferReadsIO` (`Model/Steps/InferIO.lean`) is the io lane's
**totality residue**: *if the io inference returns a type, that type
reads*.  The io-license batch routed it and named its discharge as
this batch's risk class:

> *"What B4/B3 still owe the assembly: `InferReadsIO` (the io reads
> walk — B3's named risk class) …"*

This module pays it, and the finding is that the risk class was
mispriced in the cheap direction, for a structural reason worth
recording.

## Why the walk is cheap, in one paragraph

`inferBodyIO` is `inferBody` with **one clause changed**, and the
change is behind the result: the io application clause skips the
per-argument certificate but returns `body.instantiate1 a`, the full
clause's own answer.  A *reads* statement only ever looks at the
returned type, so at the app clause the io walk consumes strictly
*less* than the full walk does — the certificate's `inferTypeCore …
a = .ok ta` conjunct, which the full lane's `inferReads_app` already
discards.  Every other clause is verbatim.  Concretely:

| shape | how the io walk gets it |
| --- | --- |
| `.sort`, `.fvar`, `.const`, `.lit` | the **full lane's own lemma**, transported across a lane equation (`inferTypeCoreIO_sort_eq` &c.) — no clause is re-proved |
| `.bvar` | the subject's reading is already `none` (`denoteMeta_bvar`); the run is not consulted |
| `.forallE` | one line: the inversion pins `t = .sort (.imax u v)` |
| `.lam`, `.app`, `.letE`, `.proj` | the four genuine mirrors — `inferReads_lam` / `_app` / `_letE` / `inferProjReads_of` with the io inversion, the io scoping trio, and `ihi : InferReadsIO` |

So the new mathematics is four clauses, and each is its full-lane
twin with three names changed (`inferTypeCore_*_inv` →
`inferTypeCoreIO_*_inv`, `inferTypeCore_{WScoped,looseBVars,
fvarLeaves}` → the io trio of `Verify/InferIOLeaves.lean`).  The
destructuring patterns are **arity-identical** — the io inversions
were stated to that shape by the io-license batch — so no `obtain`
pattern moved.

## The induction's shape, and why it is not the full walk's

The full walk is a *joint* induction over three statements
(`ReadsAll`), because the certified knot is mutual.  The io knot is a
**leaf lane**: its `whnfCore`/`whnf`/`defeq` fields are the full
knot's at the same fuel, and only `infer` is the io body.  So the io
walk is a *separate, single-statement* induction that **consumes** the
full walk's `whnf` residue at each level:

* `InferReadsIO m μ φ (fuel + 1)` from `InferReadsIO m μ φ fuel`
  (the io recursion) **and** `WhnfReads m μ φ fuel` (the full lane's,
  already total from `ReadsInputs`);
* nothing in this file supplies a full-lane residue, so the mode
  provenance the io knot enforces by construction is preserved in the
  proof tier too: no io conclusion is reachable from the full lane and
  no full-lane conclusion is produced here.

`inferReadsIO_of` therefore takes exactly `ReadsInputs` — the same
bundle the full walk takes, no io-graded input added — which is the
statement `InferInputsIO.infer_reads_io` wants.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level whnf whnfCore inferTypeCore
  inferTypeCoreIO)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The four genuine clauses

The lane-independent shapes are handled at the dispatcher, by
rewriting with the lane equations of `Verify/InferIOLemmas.lean`; the
four clauses below are the ones whose recursion is the io lane's. -/

/-- `.forallE`, io lane: the inferred type is `.sort (.imax u v)`,
which reads unconditionally.  The two recursive runs (the domain's
inference, the codomain's) are discarded — a sort node's reading needs
no induction hypothesis. -/
private theorem inferReadsIO_forallE {m : EnvModel V env}
    {d : Nat} {ty body t : Expr} {mb : ConLeche.BinderMeta}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.forallE ty body mb)
      = .ok t) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ :=
    ConLeche.inferTypeCoreIO_forall_inv h
  exact ⟨_, denoteMeta_sortQ⟩

/-- `.lam`, io lane: the copied ∀-type, exactly as in the full lane.
Its domain reading is the subject's own; its codomain reading is the
io induction hypothesis at the opened body, transported across the
`abstract1`/`instantiate1` round trip — whose two side conditions
(`fvarConsistent`, `looseBVarsBounded`) come from the io scoping trio
rather than the full lane's. -/
private theorem inferReadsIO_lam {m : EnvModel V env}
    (ihi : InferReadsIO m μ φ fuel)
    {d : Nat} {ty body t : Expr} {mb : ConLeche.BinderMeta}
    {ea : AnnotTerm}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.lam ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam ty body mb))
    (hb : (Expr.lam ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam ty body mb))
    (hlr : LeafReads m φ d (.lam ty body mb))
    (hea : denoteMeta m.acval env φ d (.lam ty body mb) = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta := by
  obtain ⟨bt, hbt, -, -, rfl⟩ :=
    ConLeche.inferTypeCoreIO_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨tyA, ba, htyA, hba, -⟩ := denoteMeta_lam_inv hea
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hleaf :
      Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl =>
      hleaf l (inferTypeCoreIO_fvarLeaves m.wf fuel hbt hwopen l hl))
  have hbtb : bt.looseBVarsBounded 0 = true :=
    inferTypeCoreIO_looseBVars m.wf fuel hbt hwopen hbopen hLopen
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    abstract1_instantiate1 bt 0 hcons hbtb
  obtain ⟨bta, hbta⟩ :=
    ihi hbt hwopen hbopen hLopen
      (LeafReads.openS hws.1 hws.2
        (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]))
        (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]))
        htyA)
      hba
  refine ⟨AnnotTerm.pi 0 (pwBit φ mb.pw) tyA bta, ?_⟩
  rw [denoteMeta, htyA, hround, hbta]
  rfl

/-- `.app`, io lane — **the clause the gate changes, and the one place
where the io reads statement is strictly cheaper than the full one.**
The inversion's fourth conjunct is a *disjunction* (the gate fired, or
the certificate ran); the walk discards it in both arms, because both
arms return `body'.instantiate1 a` and the reading of that is
`denoteMeta_beta` at the head's normalized ∀.  So the argument's own
inference is never consulted — which is exactly why the licensed skip
costs the totality metatheory nothing. -/
private theorem inferReadsIO_app {m : EnvModel V env}
    (ihi : InferReadsIO m μ φ fuel) (ihw : WhnfReads m μ φ fuel)
    {d : Nat} {f a t : Expr} {ea : AnnotTerm}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hlr : LeafReads m φ d (.app f a))
    (hea : denoteMeta m.acval env φ d (.app f a) = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta := by
  obtain ⟨tf, ty', body', mt', hif, hwf, rfl, -⟩ :=
    ConLeche.inferTypeCoreIO_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, -⟩ := denoteMeta_app_inv hea
  -- the function's inferred type, at the io lane
  obtain ⟨tfa, htfa⟩ :=
    ihi hif hws.1 hb.1 hLf
      (hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])) hfa
  have hwtf : Expr.WScoped d tf :=
    inferTypeCoreIO_WScoped m.wf fuel hif hws.1
  have hbtf : tf.looseBVarsBounded 0 = true :=
    inferTypeCoreIO_looseBVars m.wf fuel hif hws.1 hb.1 hLf
  have hLtf : Expr.LeavesBounded tf := fun l hl =>
    hLf l (inferTypeCoreIO_fvarLeaves m.wf fuel hif hws.1 l hl)
  -- its head normal form, a ∀ — at the FULL lane (the io knot's
  -- reduction fields are the certified knot's)
  obtain ⟨wa, hwa⟩ := ihw hwf hwtf hbtf hLtf
    ((hlr.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])).of_subset
      (inferTypeCoreIO_fvarLeaves m.wf fuel hif hws.1)) htfa
  obtain ⟨-, b'a, -, hb'a, -⟩ := denoteMeta_forallE_inv hwa
  have hwW : Expr.WScoped d (.forallE ty' body' mt') :=
    ConLeche.whnf_WScoped m.wf fuel hwf hwtf
  simp only [Expr.WScoped] at hwW
  refine ⟨b'a.inst aa, ?_⟩
  rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
    (ty := ty') hwW.2.fvarsBelow hws.2 hb.2 haa 0, hb'a]
  rfl

/-- `.letE`, io lane: the ζ-shaped recursion, whose three preceding
runs (the type's inference, its sort check, the value's conversion)
contribute nothing to the reading — the returned type is the *body
opened at the value*'s own inferred type, and its reading is
`denoteMeta_beta` at the `letE` node's three readings. -/
private theorem inferReadsIO_letE {m : EnvModel V env}
    (ihi : InferReadsIO m μ φ fuel)
    {d : Nat} {tt vv bb t : Expr} {ea : AnnotTerm}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.letE tt vv bb) = .ok t)
    (hws : Expr.WScoped d (.letE tt vv bb))
    (hb : (Expr.letE tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE tt vv bb))
    (hlr : LeafReads m φ d (.letE tt vv bb))
    (hea : denoteMeta m.acval env φ d (.letE tt vv bb) = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta := by
  obtain ⟨-, -, -, -, -, -, -, hbody⟩ :=
    ConLeche.inferTypeCoreIO_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denoteMeta] at hea
  rcases hta : denoteMeta m.acval env φ d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denoteMeta m.acval env φ d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denoteMeta m.acval env φ (d + 1)
      (bb.instantiate1 (.fvar d tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  have hsubred : ∀ l ∈ (bb.instantiate1 vv).fvarLeaves,
      l ∈ (Expr.letE tt vv bb).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hred : denoteMeta m.acval env φ d (bb.instantiate1 vv)
      = some (ba.inst va) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := tt) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0,
      hba]
    rfl
  exact ihi hbody (Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2)
    (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
    (fun l hl => hLb l (hsubred l hl)) (hlr.of_subset hsubred) hred

/-- `.proj`, io lane: the full row's mirror with the io inversion
(`inferProjReads_of`; task #175 wiring W5 for the tower branch). -/
private theorem inferReadsIO_proj {m : EnvModel V env}
    (htower : TowerOk m φ)
    (ihi : InferReadsIO m μ φ fuel) (ihw : WhnfReads m μ φ fuel)
    {d i : Nat} {sn : Name} {pe t : Expr} {ea : AnnotTerm}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.proj sn i pe) = .ok t)
    (hws : Expr.WScoped d (.proj sn i pe))
    (hb : (Expr.proj sn i pe).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.proj sn i pe))
    (hlr : LeafReads m φ d (.proj sn i pe))
    (hea : denoteMeta m.acval env φ d (.proj sn i pe) = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta := by
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hlenArgs,
    hlenUs, -, rfl, hsn⟩ := ConLeche.inferTypeCoreIO_proj_inv h
  subst hsn
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hlrpe : LeafReads m φ d pe :=
    hlr.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteMeta_proj_inv hea
  obtain ⟨tpea, htpea⟩ := ihi htpe hws hb hLpe hlrpe hvp
  have hwtpe : Expr.WScoped d tpe :=
    inferTypeCoreIO_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    inferTypeCoreIO_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws l hl)
  obtain ⟨tea, htea⟩ := ihw hwte hwtpe hbtpe hLtpe
    (hlrpe.of_subset
      (inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws)) htpea
  have hwte' : Expr.WScoped d te := ConLeche.whnf_WScoped m.wf fuel hwte hwtpe
  have hbte : te.looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwte hbtpe
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp te).symm] at htea
  obtain ⟨-, vs, -, hspt, -⟩ := denoteMeta_mkAppN_inv htea
  obtain ⟨-, -, -, -, -, _, -, -, hlaw, -⟩ := htower T i entry hfe
  obtain ⟨⟨Ta, hTa, -⟩, -⟩ := hlaw us hlenUs
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, -⟩ :=
    denoteMeta_typeAt_peel hfe hTa hlenArgs hframes (hspt.snoc hvp)
  exact ⟨restA, hrest⟩

/-! ## The walk -/

/-- **`InferReadsIO` at `fuel + 1`** — the eleven shapes.  Four
shapes are the full lane's lemmas across a lane equation, one is
closed by the subject's reading alone, one is a single line, and four
are the mirrors above. -/
theorem inferReadsIO_succ {m : EnvModel V env}
    (hct : ConstType m φ) (htower : TowerOk m φ)
    (ihi : InferReadsIO m μ φ fuel) (ihw : WhnfReads m μ φ fuel) :
    InferReadsIO m μ φ (fuel + 1) := by
  intro d e t ea h hws hb hLb hlr hea
  match e with
  | .sort u =>
    rw [ConLeche.inferTypeCoreIO_sort_eq] at h
    exact inferReads_sort h
  | .bvar i => rw [denoteMeta_bvar] at hea; exact nomatch hea
  | .fvar idx ty =>
    rw [ConLeche.inferTypeCoreIO_fvar_eq] at h
    exact inferReads_fvar h hlr
  | .const n us =>
    rw [ConLeche.inferTypeCoreIO_const_eq] at h
    exact inferReads_const hct h hea
  | .lit (.natVal k) =>
    rw [ConLeche.inferTypeCoreIO_lit_eq] at h
    exact inferReads_natLit h
  | .lit (.strVal s) =>
    rw [ConLeche.inferTypeCoreIO_lit_eq] at h
    exact inferReads_strLit h
  | .forallE ty body mb => exact inferReadsIO_forallE h
  | .lam ty body mb =>
    exact inferReadsIO_lam ihi h hws hb hLb hlr hea
  | .app f a => exact inferReadsIO_app ihi ihw h hws hb hLb hlr hea
  | .letE tt vv bb =>
    exact inferReadsIO_letE ihi h hws hb hLb hlr hea
  | .proj sn i pe =>
    exact inferReadsIO_proj htower ihi ihw h hws hb hLb hlr hea

/-- Fuel zero: the io entry point throws, so the statement is
vacuous. -/
theorem inferReadsIO_zero (m : EnvModel V env) :
    InferReadsIO m μ φ 0 := by
  intro d e t ea h
  rw [ConLeche.inferTypeCoreIO_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The joint walk, at every fuel (task #172 B4)

The io lane joins the induction: the ι row consumes the same-fuel
`whnf` and io-infer walks (the io-graded certificate does not traverse
its arguments, so the fabrication's readability is derived
semantically — `iotaReads_of`'s new premises), which is well-founded
because `whnfCore` at `fuel + 1` fires `iotaRec` at `fuel`. -/
def ReadsAll4 {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  WhnfCoreReads m μ φ fuel ∧ WhnfReads m μ φ fuel ∧
    InferReads m μ φ fuel ∧ InferReadsIO m μ φ fuel

theorem readsAll4_of {m : EnvModel V env} (hin : ReadsInputs μ m φ) :
    ∀ fuel, ReadsAll4 m μ φ fuel
  | 0 =>
    ⟨(readsAll_zero m).1, (readsAll_zero m).2.1,
      (readsAll_zero m).2.2, inferReadsIO_zero m⟩
  | fuel + 1 =>
    let ih := readsAll4_of hin fuel
    ⟨whnfCoreReads_succ (hin.iota fuel ih.2.1 ih.2.2.2) ih.1 ih.2.1,
      whnfReads_succ ih.1 (hin.nat fuel) (delta_of m hin.defn),
      inferReads_succ hin.const_ty hin.tower_ok ih.2.2.1 ih.2.1,
      inferReadsIO_succ hin.const_ty hin.tower_ok ih.2.2.2 ih.2.1⟩

/-- The `whnfCore` reduct reads, at every fuel. -/
theorem whnfCoreReads_of {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : WhnfCoreReads m μ φ fuel :=
  (readsAll4_of hin fuel).1

/-- **Residue 1/6 — `WhnfReads`, discharged outright.** -/
theorem whnfReads_of {m : EnvModel V env} (hin : ReadsInputs μ m φ) :
    WhnfReads m μ φ fuel :=
  (readsAll4_of hin fuel).2.1

/-- **Residue 6/6 — `InferReads`, discharged outright.** -/
theorem inferReads_of {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : InferReads m μ φ fuel :=
  (readsAll4_of hin fuel).2.2.1

/-- **The io reads residue, DISCHARGED** — a projection of the joint
walk. -/
theorem inferReadsIO_of {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : ∀ fuel, InferReadsIO m μ φ fuel :=
  fun fuel => (readsAll4_of hin fuel).2.2.2

/-- **Residue 2/6 — `WhnfCoreExists`, discharged outright.** -/
theorem whnfCoreExists_of {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : WhnfCoreExists μ m φ fuel := by
  intro _d _e _e' _Δa hrun hws hb hLb _ea hC hea _hok
  exact whnfCoreReads_of hin hrun hws hb hLb
    (LeafReads.of_ctxOk hC) hea

/-- **Residue 3/6 — `WhnfCoreReductExists`, discharged outright.** -/
theorem whnfCoreReductExists_of' {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : WhnfCoreReductExists μ m φ fuel :=
  whnfCoreExists_of_reduct (whnfCoreExists_of hin)

/-- **Residue 4/6 — `InferExists`, discharged outright.** -/
theorem inferExists_of {m : EnvModel V env} (hin : ReadsInputs μ m φ) :
    InferExists μ m φ fuel := by
  intro _d _e _t _Δa hrun hws hb hLb _ea hC hea
  exact inferReads_of hin hrun hws hb hLb (LeafReads.of_ctxOk hC)
    hea

/-- **Residue 5/6 — `DenoteMetaDelta`, discharged outright.** -/
theorem denoteMetaDelta_of {m : EnvModel V env}
    (hin : ReadsInputs μ m φ) : DenoteMetaDelta m φ :=
  denoteMetaDelta_of_fields m hin.defn

end ConLeche.Model
