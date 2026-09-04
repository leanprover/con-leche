import Setlec.SetP.Step2.InferP
import Setlec.SetP.Claims2PIO
import Setlec.Verify.InferIOLemmas

/-!
# The io infer quarter — the worked leaf and binder clauses (stage 2, B1)

The first worked example of the frozen `InferClaimsIO2P` species
(`Interp2/Claims2PIO.lean`).  Five clauses of the eleven-arm
dispatcher are proved here — the four leaves and one binder — and they
establish what the round-D study called "mechanical": at every clause
except `.app`, `inferBodyIO` is `inferBody` **verbatim**, so the io
twin of a clause proof is the clause proof with

* `inferTypeCoreIO_succ` / `inferBodyIO` in place of
  `inferTypeCore_succ` / `inferBody` (and, at the binder clauses, the
  io inversion — `inferTypeCoreIO_forall_inv`, `Verify/InferIOLemmas`),
* the recursive inference runs read at the io lane, the `whnf` /
  `ensureSort` runs read at the **full** lane (the io knot is a leaf
  lane: `pureFnsIO_whnf`, `ensureSortIO_def`),
* and the subject's `AnnotOkP` taken from the **premise** instead of
  established.

The premise costs nothing at these clauses — the leaves establish
their subject's grading outright, and the ∀ clause's parts come out of
the premise hereditarily (`AnnotOkP.hoist_pi`) rather than out of the
domain residue.  That is the point of the premise form: the
consumption direction is *cheaper*, everywhere except the one clause
where it is the whole content.

**THE APPLICATION CLAUSE IS NOT HERE.**  It is batch B2's, and it is
the only new mathematics of the campaign:

* at the gated branch (`μ.verified ∧ pw = .never`) it consumes the
  study's mechanized `io_domain_transfer` and `io_app_mem`
  (`_tmp/inferonly-study/ProbeIO.lean`, to be re-landed beside
  `Interp2/Ops.lean`'s `piR_dom_unique`), plus this batch's
  `pwBit_ne_zero_of_isNever` (`SetR/Annot/Bit.lean`) to move the
  kernel's `PropWhen.isNever` test to the claim's `pwBit φ pw ≠ 0`
  branch — soundly *and* exactly
  (`isNever_iff_forall_pwBit_ne_zero`);
* at the kept branch it reuses today's `ihd` route from
  `infer_app_claimP` (`Step2/InferP.lean:893`) unchanged, since the
  runs are there;
* and it may consume nothing else: `io_membership_fails_at_squash` is
  a model-class-wide wall, not a repair gap.

Its statement shape compiles as part of `InferClaimsIO2P`; nothing in
this file constrains it.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level whnf inferTypeCoreIO)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- The `AnnotOkP` ∀-splitter, public.  `Step2/DefEqP.lean` keeps a
private copy for its own plumbing and says in so many words that the
concurrently-written quarters may want the public name; the io quarter
is the quarter that wants it, because in premise form *every* binder
clause enters through this lemma. -/
theorem AnnotOkP.hoist_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOkP V ρ B) := by
  obtain ⟨h1, h2⟩ := AnnotOk2.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValidV_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValidV_pi V _ u v A B) ▸
      (h _ (Sat2_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- **The io lane's sort residue**: `SortSemAtP` at the io run, in
premise form.  It is the io quarter's single routed residue at this
batch; its discharge (`sortSemAtIOP_of_claims`, the mirror of
`sortSemAtP_of_claims`) needs the io *reads* walk, which is batch B3's
named risk class, so it is carried as a hypothesis here exactly as
`SortSemAtP` is carried by `infer_forallE_claimP`. -/
def SortSemAtIOP {env : Env} (m : EnvS2Core V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {u : Level} {Δa : List AVExpr}
    {ea : AVExpr},
    CtxOkP m φ d Δa e →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    inferTypeCoreIO μ env fuel d e = .ok t →
    whnf μ env fuel d t = .ok (.sort u) →
    denoteP m.acval env φ d e = some ea →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- **The io-inferred type reads** (the io lane's totality residue —
`InferReadsP` at the io run, with the same `LeafReadsP` repair).  Its
discharge is the io *reads* walk, batch B3's named risk class; until
then it routes exactly as the full lane's does. -/
def InferReadsIOP {env : Env} (m : EnvS2Core V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {ea : AVExpr},
    inferTypeCoreIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReadsP m φ d e →
    denoteP m.acval env φ d e = some ea →
    ∃ ta, denoteP m.acval env φ d t = some ta

/-- The projection clause, io lane, premise form (routed —
`InferProjStepP` transposed: the run is the io lane's because the
clause infers its scrutinee, and the subject's `AnnotOkP` moves to
the premises).  Its discharge is the structure-type walk, exactly as
the full lane's. -/
def InferProjStepIOP {env : Env} (m : EnvS2Core V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i : Nat} {sn : Name} {pe t : Expr} {Δa : List AVExpr}
    {ea ta : AVExpr},
    inferTypeCoreIO μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkP m φ d Δa (.proj sn i pe) →
    denoteP m.acval env φ d (.proj sn i pe) = some ea →
    denoteP m.acval env φ d t = some ta →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- **The io quarter's step shape** (`InferStepP`'s mirror): the five
claims at `fuel` give the io claim at `fuel + 1`, at a validating
mode.  This is the io slot of `CheckStep2P5`
(`Claims2PIO.lean`). -/
def InferStepIOP (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2Core V env) (φ : Name → Nat) (fuel : Nat),
    μ.verified = true →
    WhnfCoreClaims2P μ m φ fuel → WhnfClaims2P μ m φ fuel →
    DefEqClaims2P μ m φ fuel → InferClaims2P μ m φ fuel →
    InferClaimsIO2P μ m φ fuel →
    InferClaimsIO2P μ m φ (fuel + 1)

/-! ## The leaves -/

/-- `.sort`, io lane: both readings are sort nodes, the row is
`sound_sort`.  The premise is not used — a leaf establishes. -/
theorem infer_sort_claimIOP (m : EnvS2Core V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.sort u) = .ok t)
    (hea : denoteP m.acval env φ d (.sort u) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCoreIO_succ] at h
  simp only [Setlec.inferBodyIO, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
  subst h
  rw [denoteP_sortQ] at hea hta
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  obtain rfl : ta = .sort (Level.eval φ (.succ u)) :=
    (Option.some.inj hta).symm
  refine ⟨fun _ _ => ⟨by simp, by simp⟩, ?_⟩
  intro ρ _
  exact (sound_sort V ρ (u.eval φ)).2

/-- `.bvar`, io lane: outside the fragment, the checker throws — the
io grade narrows no rejection. -/
theorem infer_bvar_claimIOP (m : EnvS2Core V env) {d i : Nat} {t : Expr}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.bvar i) = .ok t)
    (_hea : denoteP m.acval env φ d (.bvar i) = some ea)
    (_hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCoreIO_succ] at h
  simp only [Setlec.inferBodyIO, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.fvar`, io lane: the leaf package of `CtxOkP` carries the type's
grading, so the clause takes no residue and no premise. -/
theorem infer_fvar_claimIOP (m : EnvS2Core V env)
    {d idx : Nat} {n : Name} {ty t : Expr} {Δa : List AVExpr}
    {ea ta : AVExpr}
    (hC : CtxOkP m φ d Δa (.fvar idx n ty))
    (h : inferTypeCoreIO μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hea : denoteP m.acval env φ d (.fvar idx n ty) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOkP.fvar_leaf hC
  rw [denoteP] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Setlec.inferTypeCoreIO_succ] at h
  simp only [Setlec.inferBodyIO, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rw [hden] at hta
    obtain rfl : ta = tya := (Option.some.inj hta).symm
    refine ⟨hokP, ?_⟩
    intro ρ hρ
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.const`, io lane: the stored type's row answers, exactly as in the
full lane — the constant clause performs no argument check in either
lane.  **One residue fewer than the full clause**: `infer_const_claimP`
needs `AcvalValidP` to establish the *subject's* bit validity, and in
premise form the subject's grading is given.  The premise form is
cheaper wherever it is not the whole content. -/
theorem infer_const_claimIOP (m : EnvS2Core V env)
    (hct : ConstTypeP m φ)
    {d : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denoteP m.acval env φ d (.const n us) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCoreIO_succ] at h
  simp only [Setlec.inferBodyIO, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  cases hf : env.find? n with
  | none =>
    rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      simp only [Except.ok.injEq] at h
      subst h
      rw [denoteP, hf] at hea
      dsimp only at hea
      rw [if_pos hlen] at hea
      obtain rfl : ea = m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us) :=
        (Option.some.inj hea).symm
      obtain ⟨ta', hta', hok, hmem⟩ := hct d n ci us hf hlen
      rw [hta'] at hta
      obtain rfl : ta = ta' := (Option.some.inj hta).symm
      exact ⟨fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The binder -/

/-- **`.forallE`, io lane — the binder species.**  The full lane's
clause (`infer_forallE_claimP`) runs four moves; the io twin runs the
same four, with move 1's inversion at the io lane and the *premise*
supplying hereditarily what the full clause establishes.  Nothing else
moves: the ∀ rule's own checks (domain sort, codomain sort, the
annotation validation) are kept by `inferBodyIO`, so move 3's
establishment step and move 4's numeral bridge are unchanged. -/
theorem infer_forallE_claimIOP (m : EnvS2Core V env)
    (hμ : μ.verified = true) (hss : SortSemAtIOP m μ φ fuel)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hb : (Expr.forallE n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE n ty body mb))
    (hC : CtxOkP m φ d Δa (.forallE n ty body mb))
    (hea : denoteP m.acval env φ d (.forallE n ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  -- move 1: the io run inversion, validation conjunct included
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, hpw, rfl⟩ :=
    Setlec.inferTypeCoreIO_forall_inv h
  have hz := hpw hμ
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteP_forallE_inv hea
  rw [denoteP_sortQ] at hta
  obtain rfl : ta = .sort (Level.eval φ (.imax u v)) :=
    (Option.some.inj hta).symm
  -- **the premise, spent**: the subject's grading splits hereditarily
  -- into the domain's and the opened codomain's — this is what the
  -- full lane had to establish from the residue instead
  obtain ⟨hokty, hokbody⟩ := AnnotOkP.hoist_pi (V := V) hok
  -- move 2: grade domain and opened codomain through the io sort
  -- residue, with the opened context built in place
  have hdomU := hss hC.forallE_ty hws.1 hb.1 hLty hty hwu htyA hokty
  have hCop : CtxOkP m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
    CtxOkP.openS (n := n) hC.forallE_ty hC.forallE_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  have hcodU := hss hCop hwopen hbopen hLopen hbt
    (Setlec.ensureSortCore_inv hens) hbaA hokbody
  refine ⟨?_, ?_⟩
  · -- the sort's own grading: leaves
    intro ρ hρ
    exact ⟨by simp, by simp⟩
  · -- the membership row, through the numeral bridge (move 4)
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ tyA →
        AnnotOk2 V (cons x ρ) baA ∧
          interp2 V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat2_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat2_cons V hρ hx)).2⟩
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 :=
      pwBit_of_equiv_zeronessOf hz φ
    have hbridge :
        interp2 V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp2 V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp2_pi, interp2_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2

end Setlec.SetR.Interp2
