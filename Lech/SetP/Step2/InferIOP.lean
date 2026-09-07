import Lech.SetP.Step2.InferP
import Lech.SetP.Claims2PIO
import Lech.SetP.IOLicenseP
import Lech.Verify.InferIOLemmas
import Lech.Verify.InferIOLeaves

/-!
# The io infer quarter — COMPLETE (stage 2 B1 + the io-license batch)

The worked quarter of the frozen `InferClaimsIO2P` species
(`SetP/Claims2PIO.lean`).  Ten of the eleven dispatcher arms are
proved here (`.proj` routes, as in the full lane), and the quarter is
assembled: `inferStepIOP_of` discharges `InferStepIOP` — the io slot
of `CheckStep2P5` — modulo the routed `InferInputsIOP`.  The recipe,
everywhere but `.app`: `inferBodyIO` is `inferBody` **verbatim**, so
the io twin of a clause proof is the clause proof with

* `inferTypeCoreIO_succ` / `inferBodyIO` in place of
  `inferTypeCore_succ` / `inferBody` (and the io inversions,
  `Verify/InferIOLemmas`),
* the recursive inference runs read at the io lane, the `whnf` /
  `ensureSort` / `defeq` runs read at the **full** lane (the io knot
  is a leaf lane: `pureFnsIO_whnf`, `ensureSortIO_def`),
* and the subject's `AnnotOkP` taken from the **premise** instead of
  established.

**Premise form is cheaper at every clause where it is not the whole
content** (the B1 finding, confirmed across the quarter): the `.const`
clause sheds `AcvalValidP`'s establishment use, the `.lam` clause
sheds the domain's sort run (`hoist_lam` supplies the grading the full
clause computes), and the `.letE` clause sheds *both* of the full
clause's residues (`SortSemAtP` and `InferReadsP`).  The two literal
clauses do not even need io proofs: neither recurses, so the io run
is the full run (`inferTypeCoreIO_lit_eq`) and the full-lane facts
apply across the transfer.

**THE APPLICATION CLAUSE** (`infer_app_claimIOP`) is the campaign's
only new mathematics — the io-license batch's centerpiece.  The
inversion's certificate disjunct (`inferTypeCoreIO_app_inv`) splits
it: the gated arm consumes the landed licenses
(`io_domain_transfer`, `SetP/IOLicenseP.lean`) against the premise's
hereditary app slot (`hoist_app`) at the bit `pwBit_ne_zero_of_isNever`
pins positive; the kept arm is `infer_app_claimP`'s `ihd` route with
the io lanes threaded.  The squash fence
(`io_membership_fails_at_squash`) is why the gate's `isNever` test is
exact, not conservative.

**Mode provenance (binding, unchanged).**  An io conclusion must
never feed a site that needs establishment form; the knot boundary
enforces it structurally — no full-lane body mentions `coreKnotIO`,
and `inferStepIOP_of` consumes the sealed four claims without ever
producing one.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level whnf inferTypeCoreIO)

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

/-- **The slot sort-sem** (task #172 B4): `SortSemAtIOSP` from the two
lanes' — the mode-bit case, one lane equation each way. -/
theorem sortSemAtIOSP_of {env : Env} {m : EnvS2Core V env}
    {φ : Name → Nat} {fuel : Nat}
    (hfull : SortSemAtP m μ φ fuel) (hio : SortSemAtIOP m μ φ fuel) :
    SortSemAtIOSP m μ φ fuel := by
  intro d e t u Δa ea hC hws hb hLb hrun hw hden hok ρ hρ
  cases hg : μ.betaGate with
  | false =>
    rw [Lech.inferTypeIO_off hg] at hrun
    exact hfull hC hws hb hLb hrun hw hden ρ hρ
  | true =>
    rw [Lech.inferTypeIO_on hg] at hrun
    exact hio hC hws hb hLb hrun hw hden hok ρ hρ

/-- The `AnnotOkP` λ-splitter (`hoist_pi`'s sibling): the premise
form's entry into the λ clause. -/
theorem AnnotOkP.hoist_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOkP V ρ b) := by
  obtain ⟨h1, h2⟩ := AnnotOk2.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValidV_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValidV_lam V _ v A b) ▸
      (h _ (Sat2_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- The `AnnotOkP` application splitter, slot included: the premise
form's entry into the app clause.  The third component is the
**hereditary app slot** — the existential product membership the
gated branch feeds to `io_domain_transfer`. -/
theorem AnnotOkP.hoist_app {Δa : List AVExpr} {f a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.app f a)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ f) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ a) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        ∃ (v : Nat) (A : V) (B : V → V),
          interp2 V ρ f ∈ˢ piR v A B ∧ interp2 V ρ a ∈ˢ A ∧
          (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :=
  ⟨fun ρ hρ => ⟨((AnnotOk2_app V ρ f a) ▸ (h ρ hρ).1).1,
      ((AnnotValidV_app V ρ f a) ▸ (h ρ hρ).2).1⟩,
    fun ρ hρ => ⟨((AnnotOk2_app V ρ f a) ▸ (h ρ hρ).1).2.1,
      ((AnnotValidV_app V ρ f a) ▸ (h ρ hρ).2).2⟩,
    fun ρ hρ => ((AnnotOk2_app V ρ f a) ▸ (h ρ hρ).1).2.2⟩

/-- The `AnnotOkP` `letE` splitter, in the raw value-indexed form
(`AnnotOk2`'s own clause shape — the hoist kit's note explains why no
opened form exists): the premise form's entry into the ζ crossing. -/
theorem AnnotOkP.hoist_letE {Δa : List AVExpr} {T v b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.letE T v b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ T) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ v) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOkP V (cons (interp2 V ρ v) ρ) b :=
  ⟨fun ρ hρ => ⟨((AnnotOk2_letE V ρ T v b) ▸ (h ρ hρ).1).1,
      ((AnnotValidV_letE V ρ T v b) ▸ (h ρ hρ).2).1⟩,
    fun ρ hρ => ⟨((AnnotOk2_letE V ρ T v b) ▸ (h ρ hρ).1).2.1,
      ((AnnotValidV_letE V ρ T v b) ▸ (h ρ hρ).2).2.1⟩,
    fun ρ hρ => ⟨((AnnotOk2_letE V ρ T v b) ▸ (h ρ hρ).1).2.2,
      ((AnnotValidV_letE V ρ T v b) ▸ (h ρ hρ).2).2.2⟩⟩

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

/-- **The slot reads** (task #172 B4): `InferReadsIOSP` from the two
lanes'. -/
theorem inferReadsIOSP_of {env : Env} {m : EnvS2Core V env}
    {φ : Name → Nat} {fuel : Nat}
    (hfull : InferReadsP m μ φ fuel) (hio : InferReadsIOP m μ φ fuel) :
    InferReadsIOSP m μ φ fuel := by
  intro d e t ea hrun hws hb hLb hlr hden
  cases hg : μ.betaGate with
  | false =>
    rw [Lech.inferTypeIO_off hg] at hrun
    exact hfull hrun hws hb hLb hlr hden
  | true =>
    rw [Lech.inferTypeIO_on hg] at hrun
    exact hio hrun hws hb hLb hlr hden

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
    μ.verifiedChecks = true →
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
  rw [Lech.inferTypeCoreIO_succ] at h
  simp only [Lech.inferBodyIO, pure,
    Except.pure, Except.ok.injEq] at h
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
  rw [Lech.inferTypeCoreIO_succ] at h
  simp only [Lech.inferBodyIO] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.fvar`, io lane: the leaf package of `CtxOkP` carries the type's
grading, so the clause takes no residue and no premise. -/
theorem infer_fvar_claimIOP (m : EnvS2Core V env)
    {d idx : Nat} {ty t : Expr} {Δa : List AVExpr}
    {ea ta : AVExpr}
    (hC : CtxOkP m φ d Δa (.fvar idx ty))
    (h : inferTypeCoreIO μ env (fuel + 1) d (.fvar idx ty) = .ok t)
    (hea : denoteP m.acval env φ d (.fvar idx ty) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOkP.fvar_leaf hC
  rw [denoteP] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Lech.inferTypeCoreIO_succ] at h
  simp only [Lech.inferBodyIO, pure,
    Except.pure] at h
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
  rw [Lech.inferTypeCoreIO_succ] at h
  simp only [Lech.inferBodyIO, pure,
    Except.pure, Bind.bind, Except.bind] at h
  cases hf : env.find? n with
  | none =>
    rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next htw =>
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
        obtain ⟨ta', hta', hok, hmem⟩ := hct d n ci us hf (by simpa using htw) hlen
        rw [hta'] at hta
        obtain rfl : ta = ta' := (Option.some.inj hta).symm
        exact ⟨fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
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
    (hμ : μ.verifiedChecks = true) (hss : SortSemAtIOP m μ φ fuel)
    {d : Nat} {ty body t : Expr} {mb : Lech.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.forallE ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE ty body mb))
    (hb : (Expr.forallE ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE ty body mb))
    (hC : CtxOkP m φ d Δa (.forallE ty body mb))
    (hea : denoteP m.acval env φ d (.forallE ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  -- move 1: the io run inversion, validation conjunct included
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, hpw, rfl⟩ :=
    Lech.inferTypeCoreIO_forall_inv h
  have hz := hpw hμ
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
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
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkP.openS hC.forallE_ty hC.forallE_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  have hcodU := hss hCop hwopen hbopen hLopen hbt
    (Lech.ensureSortCore_inv hens) hbaA hokbody
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
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 := by
      rw [← hz]; exact pwBit_zeronessOf φ v
    have hbridge :
        interp2 V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp2 V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp2_pi, interp2_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2

/-! ## The literal clauses — lane-independent

Neither literal clause recurses, so the io run *is* the full run
(`inferTypeCoreIO_lit_eq`) and the io twins are the full-lane facts
with the establishment conclusion dropped.  No new residue: the
`String` clause consumes the full lane's own routed
`InferStrLitStepP`. -/

/-- `.lit (.natVal k)`, io lane: the full clause across the run
transfer. -/
theorem infer_natLit_claimIOP (m : EnvS2Core V env) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m)
    {d k : Nat} {t : Expr} {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.lit (.natVal k)) = .ok t)
    (hea : denoteP m.acval env φ d (.lit (.natVal k)) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Lech.inferTypeCoreIO_lit_eq] at h
  obtain ⟨-, h2, h3⟩ := infer_natLit_claimP m hnh hval h hea hta
  exact ⟨h2, h3⟩

/-- `.lit (.strVal s)`, io lane: the full lane's routed residue across
the run transfer. -/
theorem infer_strLit_claimIOP (m : EnvS2Core V env)
    (hstr : InferStrLitStepP m μ φ fuel)
    {d : Nat} {s : String} {t : Expr} {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.lit (.strVal s)) = .ok t)
    (hea : denoteP m.acval env φ d (.lit (.strVal s)) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Lech.inferTypeCoreIO_lit_eq] at h
  obtain ⟨-, h2, h3⟩ := hstr (Δa := Δa) h hea hta
  exact ⟨h2, h3⟩

/-! ## The remaining binder and threading clauses -/

/-- **`.lam`, io lane — the chain-case species in premise form.**  The
full clause (`infer_lam_claimP`) establishes the domain's grading from
its own sort run; the premise supplies it here (`hoist_lam`), so the
clause consumes the io sort residue only inside the fibre regime
fact's *leaf* branch — the chain branch is the meta copy +
impredicativity, run-free, exactly as in the full lane. -/
theorem infer_lam_claimIOP (m : EnvS2Core V env)
    (hμ : μ.verifiedChecks = true) (hss : SortSemAtIOP m μ φ fuel)
    (ihio : InferClaimsIO2P μ m φ fuel)
    {d : Nat} {ty body t : Expr} {mb : Lech.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.lam ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam ty body mb))
    (hb : (Expr.lam ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam ty body mb))
    (hC : CtxOkP m φ d Δa (.lam ty body mb))
    (hea : denoteP m.acval env φ d (.lam ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨bt, hbt, hleafC, hchainC, rfl⟩ :=
    Lech.inferTypeCoreIO_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteP] at hea
  rcases htyA : denoteP m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denoteP m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam (pwBit φ mb.pw) tyA ba :=
    (Option.some.inj hea).symm
  -- the abstraction round trip, for the ∀-type's reading
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
  rw [denoteP, htyA, hround] at hta
  rcases hbtA : denoteP m.acval env φ (d + 1) bt with _ | btA
  · rw [hbtA] at hta; exact nomatch hta
  rw [hbtA] at hta
  obtain rfl : ta = .pi 0 (pwBit φ mb.pw) tyA btA :=
    (Option.some.inj hta).symm
  -- **the premise, spent**: the domain's and the opened body's grading
  obtain ⟨hokty, hokba⟩ := AnnotOkP.hoist_lam (V := V) hok
  -- the opened context, at the premise's own grading
  have hCop : CtxOkP m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkP.openS hC.lam_ty hC.lam_body htyA hokty
  obtain ⟨hrowT, hrowM⟩ :=
    ihio hbt hwopen hbopen hLopen hCop hba hbtA hokba
  -- the fibre regime fact, one `have`, both uses (the meta copy)
  have hCbt : CtxOkP m φ (d + 1) (tyA :: Δa) bt :=
    hCop.of_subset (inferTypeCoreIO_fvarLeaves m.wf fuel hbt hwopen)
  have hzfib : pwBit φ mb.pw = 0 →
      ∀ (ρ' : Nat → V), Sat2 V (tyA :: Δa) ρ' →
        interp2 V ρ' btA ∈ˢ (univZero : V) := by
    intro hb0 ρ' hρ'
    by_cases hbl : body.isLam
    · -- chain: no run — impredicativity at the copied meta
      obtain ⟨tyI, bI, mbI, rfl⟩ :
          ∃ tyI bI mbI, body = .lam tyI bI mbI := by
        cases body <;> simp [Expr.isLam] at hbl
        exact ⟨_, _, _, rfl⟩
      have hpwEq : mb.pw = mbI.pw :=
        hchainC hμ mbI.pw rfl
      obtain ⟨btI, rfl⟩ : ∃ btI,
          bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI := by
        cases fuel with
        | zero =>
          rw [Lech.inferTypeCoreIO_zero] at hbt
          simp [throw, throwThe, MonadExceptOf.throw] at hbt
        | succ f =>
          exact Lech.inferIO_lam_meta_copy hbt
      obtain ⟨tyIA, btIA, -, -, rfl⟩ := denoteP_forallE_inv hbtA
      rw [interp2_pi]
      have hinner : pwBit φ mbI.pw = 0 := by
        rw [← hpwEq]
        exact hb0
      rw [hinner]
      exact piR_zero_mem_univZero
    · -- leaf: the P2 leaf conjunct's run + the bit law, through the
      -- io sort residue at the premise the recursive call delivered
      obtain ⟨btt, vb, hbtt, hens, hzeq⟩ :=
        hleafC hμ (by simpa using hbl)
      exact pwBit_zero_mem_univZero hzeq hb0
        (hss hCbt (inferTypeCoreIO_WScoped m.wf fuel hbt hwopen)
          hbtb
          (fun l hl => hLopen l
            (inferTypeCoreIO_fvarLeaves m.wf fuel hbt hwopen l hl))
          hbtt (Lech.ensureSortCore_inv hens) hbtA hrowT ρ' hρ').2
  refine ⟨?_, ?_⟩
  · -- AnnotOkP of the copied ∀-type
    intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_pi]
      exact ⟨(hokty ρ hρ).1,
        fun x hx => (hrowT (cons x ρ) (Sat2_cons V hρ hx)).1⟩
    · rw [AnnotValidV_pi]
      exact ⟨(hokty ρ hρ).2,
        fun x hx => (hrowT (cons x ρ) (Sat2_cons V hρ hx)).2,
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat2_cons V hρ hx)⟩
  · -- the membership row
    intro ρ hρ
    exact (sound_lam V (hokty ρ hρ).1
      (fun x hx => (hokba (cons x ρ) (Sat2_cons V hρ hx)).1)
      (fun x hx => hrowM (cons x ρ) (Sat2_cons V hρ hx))
      (fun h0 x hx => hzfib h0 (cons x ρ) (Sat2_cons V hρ hx))).2

/-- **`.letE`, io lane.**  Premise form sheds *both* of the full
clause's residues: no `SortSemAtP` (the type's grading was only ever
needed to establish the subject's, which is now given) and no
`InferReadsP` (the value's grading likewise).  The ζ crossing is
`denoteP_beta` and the transport is `AnnotOkP_inst0`, unchanged. -/
theorem infer_letE_claimIOP (m : EnvS2Core V env)
    (ihio : InferClaimsIO2P μ m φ fuel)
    {d : Nat} {ty val b t : Expr} {Δa : List AVExpr}
    {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.letE ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE ty val b))
    (hb : (Expr.letE ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE ty val b))
    (hC : CtxOkP m φ d Δa (.letE ty val b))
    (hea : denoteP m.acval env φ d (.letE ty val b) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, sv, tvv, hty, hes, hvv, -, hbody⟩ :=
    Lech.inferTypeCoreIO_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hsubred : ∀ l ∈ (b.instantiate1 val).fvarLeaves,
      l ∈ (Expr.letE ty val b).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) :=
    fun l hl => hLb l (hsubred l hl)
  have hCred : CtxOkP m φ d Δa (b.instantiate1 val) :=
    hC.of_subset hsubred
  -- the subject's reading
  rw [denoteP] at hea
  rcases htyA : denoteP m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hvA : denoteP m.acval env φ d val with _ | vA
  · rw [hvA] at hea; exact nomatch hea
  rw [hvA] at hea
  rcases hbA : denoteP m.acval env φ (d + 1)
      (b.instantiate1 (.fvar d ty)) with _ | bA
  · rw [hbA] at hea; exact nomatch hea
  rw [hbA] at hea
  obtain rfl : ea = .letE tyA vA bA := (Option.some.inj hea).symm
  -- the ζ crossing: `denoteP_beta`, directly
  have hcross : denoteP m.acval env φ d (b.instantiate1 val)
      = some (bA.inst vA) := by
    rw [denoteP_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hvA 0, hbA]
    rfl
  -- **the premise, spent**: the value's and the body's grading
  obtain ⟨-, hokv, hokb⟩ := AnnotOkP.hoist_letE (V := V) hok
  have hokred : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ (bA.inst vA) := fun ρ hρ =>
    (AnnotOkP_inst0 (hokv ρ hρ)).mpr (hokb ρ hρ)
  obtain ⟨hrowBT, hrowBM⟩ :=
    ihio hbody hwred hbred hLred hCred hcross hta hokred
  refine ⟨hrowBT, ?_⟩
  intro ρ hρ
  rw [interp2_letE, ← interp2_inst0]
  exact hrowBM ρ hρ

/-- **`.app`, io lane — the campaign's only new mathematics** (the
frozen statement; DESIGN.md, "THE IO LICENSE BATCH").  The inversion's
certificate disjunct splits the proof:

* **gated arm** (`m'.pw.isNever` — the **datum alone** since the
  licence ruling of 2026-09-06; the clause never needed a mode
  hypothesis and now the disjunct does not carry one either): the
  skipped fact `⟦a⟧ ∈ ⟦Aa⟧` is recovered by `io_domain_transfer`
  from the premise's hereditary app slot (`hoist_app`), the io-run's
  computed product (`ihio` at `f` + the reduction claim) and
  `pwBit_ne_zero_of_isNever`.  No freshness, no nonemptiness, no
  `≠ pt` side condition;
* **kept arm**: the certificate ran, and the fact is
  `infer_app_claimP`'s `ihd` route with the io lanes threaded.

After `ha2` the two arms rejoin: the type's grading is the ∀'s own
fibre grading transported by `AnnotOkP_inst0`, and the membership is
the standard row (`sound_app`, whose kind-`0` premise the ∀'s
`AnnotValidV` component supplies — vacuously at the gated arm's
nonzero bit).  `io_membership_fails_at_squash`
(`SetP/IOLicenseP.lean`) is why the gated arm's `isNever` test cannot
be weakened: the same premise package at bit `0` has a mechanized
countermodel. -/
theorem infer_app_claimIOP (m : EnvS2Core V env)
    (hir : InferReadsIOP m μ φ fuel) (hwr : WhnfReadsP m μ φ fuel)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihio : InferClaimsIO2P μ m φ fuel)
    {d : Nat} {f a t : Expr} {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCoreIO μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkP m φ d Δa (.app f a))
    (hea : denoteP m.acval env φ d (.app f a) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tf, ty', body', mb', htf, hwf, rfl, hcert⟩ :=
    Lech.inferTypeCoreIO_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteP] at hea
  rcases hfa : denoteP m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteP m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- **the premise, spent**: the parts' grading and the hereditary slot
  obtain ⟨hokf, hoka, hslot⟩ := AnnotOkP.hoist_app (V := V) hok
  -- the head's io-inferred type: read (routed) and graded by `ihio`
  obtain ⟨tfa, htfa⟩ :=
    hir htf hws.1 hb.1 hLf (LeafReadsP.of_ctxOkP hC.app_fn) hfa
  obtain ⟨hrowfT, hrowfM⟩ :=
    ihio htf hws.1 hb.1 hLf hC.app_fn hfa htfa hokf
  have htfsub := inferTypeCoreIO_fvarLeaves m.wf fuel htf hws.1
  have htfw : Expr.WScoped d tf :=
    inferTypeCoreIO_WScoped m.wf fuel htf hws.1
  have htfb : tf.looseBVarsBounded 0 = true :=
    inferTypeCoreIO_looseBVars m.wf fuel htf hws.1 hb.1 hLf
  have htfL : Expr.LeavesBounded tf := fun l hl => hLf l (htfsub l hl)
  have htfC : CtxOkP m φ d Δa tf := hC.app_fn.of_subset htfsub
  -- the ∀-type: read (routed) and graded by the reduction claim
  obtain ⟨pa, hpa⟩ := hwr hwf htfw htfb htfL
    (LeafReadsP.of_ctxOkP htfC) htfa
  obtain ⟨hokpa, hredf⟩ :=
    ihw hwf htfw htfb htfL htfC htfa hpa hrowfT
  have hwfe : Expr.WScoped d (Expr.forallE ty' body' mb') :=
    whnf_WScoped m.wf fuel hwf htfw
  have hbfe : (Expr.forallE ty' body' mb').looseBVarsBounded 0
      = true := whnf_looseBVars m.wf fuel hwf htfb
  have hLfe : Expr.LeavesBounded (.forallE ty' body' mb') :=
    fun l hl => htfL l (whnf_fvarLeaves m.wf fuel hwf l hl)
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteP_forallE_inv hpa
  -- the ∀'s reading, split: domain, fibres, and the kind-`0` component
  have hokAa : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ Aa := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [AnnotOk2_pi] at h1
    rw [AnnotValidV_pi] at h2
    exact ⟨h1.1, h2.1⟩
  have hokBa : ∀ (ρ : Nat → V), Sat2 V Δa ρ →
      ∀ x, x ∈ˢ interp2 V ρ Aa → AnnotOkP V (cons x ρ) Ba := by
    intro ρ hρ x hx
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [AnnotOk2_pi] at h1
    rw [AnnotValidV_pi] at h2
    exact ⟨h1.2 x hx, h2.2.1 x hx⟩
  have hcod0 : ∀ (ρ : Nat → V), Sat2 V Δa ρ → pwBit φ mb'.pw = 0 →
      ∀ x, x ∈ˢ interp2 V ρ Aa →
        interp2 V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    obtain ⟨-, h2⟩ := hokpa ρ hρ
    rw [AnnotValidV_pi] at h2
    exact h2.2.2 h0 x hx
  -- the head's membership at the computed product
  have hf2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ fa
        ∈ˢ interp2 V ρ (.pi 0 (pwBit φ mb'.pw) Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  -- **the split fact**: the argument's membership in the computed
  -- domain — by cases on the certificate disjunct
  have ha2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ aa ∈ˢ interp2 V ρ Aa := by
    rcases hcert with hg | ⟨tya, hia, hde⟩
    · -- THE GATED ARM: the license fires
      have hw0 : pwBit φ mb'.pw ≠ 0 :=
        pwBit_ne_zero_of_isNever hg φ
      intro ρ hρ
      obtain ⟨v, A, B, hfslot, haslot, -⟩ := hslot ρ hρ
      have hf' := hf2 ρ hρ
      rw [interp2_pi] at hf'
      exact io_domain_transfer hw0 hfslot haslot hf'
    · -- THE KEPT ARM: the certificate ran — `infer_app_claimP`'s
      -- `ihd` route, io lanes threaded
      obtain ⟨tyaA, htyaA⟩ :=
        hir hia hws.2 hb.2 hLa (LeafReadsP.of_ctxOkP hC.app_arg) haa
      obtain ⟨hrowaT, hrowaM⟩ :=
        ihio hia hws.2 hb.2 hLa hC.app_arg haa htyaA hoka
      have htasub := inferTypeCoreIO_fvarLeaves m.wf fuel hia hws.2
      have htaw : Expr.WScoped d tya :=
        inferTypeCoreIO_WScoped m.wf fuel hia hws.2
      have htab : tya.looseBVarsBounded 0 = true :=
        inferTypeCoreIO_looseBVars m.wf fuel hia hws.2 hb.2 hLa
      have htaL : Expr.LeavesBounded tya := fun l hl =>
        hLa l (htasub l hl)
      have htaC : CtxOkP m φ d Δa tya := hC.app_arg.of_subset htasub
      have hLty' : Expr.LeavesBounded ty' := fun l hl =>
        hLfe l (by simp [Expr.fvarLeaves, hl])
      have hCpi : CtxOkP m φ d Δa (.forallE ty' body' mb') :=
        (hC.app_fn.of_subset htfsub).of_subset
          (whnf_fvarLeaves m.wf fuel hwf)
      have hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ tyaA = interp2 V ρ Aa :=
        ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC hCpi.forallE_ty
          htyaA hAa hrowaT hokAa
      intro ρ hρ
      rw [← hdom ρ hρ]
      exact hrowaM ρ hρ
  -- the returned type's reading, `denoteP_beta` backwards
  have hcross : denoteP m.acval env φ d (body'.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteP_beta (ty := ty') m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  rw [hcross] at hta
  obtain rfl : ta = Ba.inst aa := (Option.some.inj hta).symm
  -- the arms rejoin
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    exact (AnnotOkP_inst0 (hoka ρ hρ)).mpr (hokBa ρ hρ _ (ha2 ρ hρ))
  · intro ρ hρ
    exact (sound_app V (hokf ρ hρ).1 (hoka ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-! ## The io quarter, assembled

The routed inputs are the full quarter's (`InferInputsP` — the io
lane consumes `whnf_reads` and the two literal/const residues
unchanged) plus exactly two io-graded ones: the io reads residue and
the premise-form projection residue.  `SortSemAtIOP` is **derived**,
not routed: with the io scoping trio landed
(`Verify/InferIOLeaves.lean`), `sortSemAtIOP_of_claims` mirrors
`sortSemAtP_of_claims` — the batch-B1 residue dissolves. -/

/-- `SortSemAtIOP`'s discharge from the claims one fuel down — the
mirror of `sortSemAtP_of_claims`, with the type's grading coming out
of the io claim's *conclusion* (its premise is the subject's, which
`SortSemAtIOP` carries). -/
theorem sortSemAtIOP_of_claims {env : Env} {m : EnvS2Core V env}
    {fuel : Nat}
    (ihw : WhnfClaims2P μ m φ fuel) (ihio : InferClaimsIO2P μ m φ fuel)
    (hreads : InferReadsIOP m μ φ fuel) :
    SortSemAtIOP m μ φ fuel := by
  intro d e t u Δa ea hC hws hb hLb hi hw hea hok
  obtain ⟨ta, hta⟩ :=
    hreads hi hws hb hLb (LeafReadsP.of_ctxOkP hC) hea
  obtain ⟨hokT, hmem⟩ := ihio hi hws hb hLb hC hea hta hok
  have hwt : Expr.WScoped d t :=
    inferTypeCoreIO_WScoped m.wf fuel hi hws
  have hbt : t.looseBVarsBounded 0 = true :=
    inferTypeCoreIO_looseBVars m.wf fuel hi hws hb hLb
  have hLt : Expr.LeavesBounded t := fun l hl =>
    hLb l (inferTypeCoreIO_fvarLeaves m.wf fuel hi hws l hl)
  have hCt : CtxOkP m φ d Δa t :=
    hC.of_subset (inferTypeCoreIO_fvarLeaves m.wf fuel hi hws)
  obtain ⟨-, heq⟩ := ihw hw hwt hbt hLt hCt hta denoteP_sortQ hokT
  intro ρ hρ
  refine ⟨hok ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp2_sort] at hm
  exact hm

/-- **The io quarter's routed inputs**: the full quarter's bundle plus
the two io-graded residues. -/
structure InferInputsIOP (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- the full quarter's bundle (`const_ty`, `acval_valid`,
  `nat_heads`, `str_lit`, `proj`, `infer_reads`, `whnf_reads`) -/
  base : InferInputsP V μ
  /-- the io-inferred type reads (io totality residue; discharge =
  the io reads walk, B3) -/
  infer_reads_io : ∀ {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat), InferReadsIOP m μ φ fuel
  /-- the projection clause at the io grade, premise form -/
  proj_io : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStepIOP m μ φ fuel

/-- **`InferStepIOP`, modulo the routed inputs** — the eleven shapes
dispatched to the eleven clause lemmas, `inferStepP_of`'s mirror.
Ten are theorems of this file (the literal pair through the run
transfer); `.proj` routes through the input structure. -/
theorem inferStepIOP_of (h : InferInputsIOP V μ)
    (hμ : μ.verifiedChecks = true) : InferStepIOP μ V := by
  intro env m φ fuel _hv _ihwc ihw ihd _ihi ihio
  have hss : SortSemAtIOP m μ φ fuel :=
    sortSemAtIOP_of_claims ihw ihio (h.infer_reads_io m φ fuel)
  intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
  match e, hrun, hws, hb, hLb, hC, hea, hok with
  | .sort u, hrun, _, _, _, _, hea, _ =>
    exact infer_sort_claimIOP m hrun hea hta
  | .bvar i, hrun, _, _, _, _, hea, _ =>
    exact infer_bvar_claimIOP m hrun hea hta
  | .fvar idx ty, hrun, _, _, _, hC, hea, _ =>
    exact infer_fvar_claimIOP m hC hrun hea hta
  | .const nm us, hrun, _, _, _, _, hea, _ =>
    exact infer_const_claimIOP m (h.base.const_ty m φ) hrun hea hta
  | .lit (.natVal k), hrun, _, _, _, _, hea, _ =>
    exact infer_natLit_claimIOP m (h.base.nat_heads m φ)
      (h.base.acval_valid m) hrun hea hta
  | .lit (.strVal s), hrun, _, _, _, _, hea, _ =>
    exact infer_strLit_claimIOP m (h.base.str_lit m φ fuel) hrun hea hta
  | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
    exact infer_forallE_claimIOP m hμ hss hrun hws hb hLb hC hea hta hok
  | .lam ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
    exact infer_lam_claimIOP m hμ hss ihio hrun hws hb hLb hC hea hta
      hok
  | .app fe ae, hrun, hws, hb, hLb, hC, hea, hok =>
    exact infer_app_claimIOP m (h.infer_reads_io m φ fuel)
      (h.base.whnf_reads m φ fuel) ihw ihd ihio hrun hws hb hLb hC hea
      hta hok
  | .letE ty val bd, hrun, hws, hb, hLb, hC, hea, hok =>
    exact infer_letE_claimIOP m ihio hrun hws hb hLb hC hea hta hok
  | .proj sn i pe, hrun, hws, hb, hLb, hC, hea, hok =>
    exact h.proj_io m φ fuel hrun hws hb hLb hC hea hta hok

end Lech.SetP
