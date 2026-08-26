import Setlec.Model.DirectParams
import Setlec.Model.Extend.Model

/-!
# The direct install's per-field universe walk, semantically

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`) installs a
recognised simple structure as the type former, the constructor, the
recursor with its rule and the `nF` projection functions — and
**nothing else**.  It stores no `_model` companions: synthesising them
would be re-implementing the preprocessor inside the checker (user
ruling, DESIGN.md), and it is not needed — the environment invariant
carries no `_model` linkage at all (the identification is group-local
to a modeled block's install derivation, task #83), and the direct
capability record claims neither `eta` nor `unitlike`, so the
`CapsOk` obligations are vacuous.

What this module supplies is the step from the checker's per-field
universe walk to the semantic fact the dependent-pair tower consumes:

* `checkDirectFieldUniv_inv` — inversion of the walk: per field, the
  inferred sort, the `ensureSort` result and the `Level.leq` check;
* `FrameOk` — the five syntactic and two semantic conditions a
  per-binder soundness step needs at a frame, with the two steps
  (`FrameOk.dom`, `FrameOk.body`) that carry them across an opened `∀`;
* `FieldTele_of_walk` — the two combined: each opened field domain
  interprets, and its checked sort bound puts it in the structure's own
  universe by cumulativity.  This is the semantic content of the
  reference kernels' per-field universe bound
  (`Inductive/Add.lean:225-228`), and it is what discharges the guard
  on the type former's value at every later member of the block (see
  `Setlec/Model/DirectInstall.lean`).

The environment assembly itself is in `Setlec/Model/DirectDecl.lean`.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-! ### The per-field universe walk -/

/-- Inversion of the field-universe walk: every field's domain was
inferred, its sort ensured, and that sort checked `≤` the structure's
result sort. -/
theorem checkDirectFieldUniv_inv {env : Env} {F : Nat} {s : Level}
    {nP : Nat} {fvs : List Expr} :
    ∀ (k : Nat),
      checkDirectFieldUniv (fueledOps F) env s nP fvs k = .ok () →
      ∀ j, j < k → ∃ fv ty u, fvs[j]? = some fv ∧
        inferTypeCore env F (nP + j) (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore env F (nP + j) ty = .ok u ∧
        Level.leq u s = some true := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro h j hj
    rw [checkDirectFieldUniv] at h
    simp only [fueledOps_inferType, fueledOps_ensureSort, Bind.bind,
      Except.bind, unwrapOr] at h
    cases hfv : fvs[k]? with
    | none => rw [hfv] at h; exact nomatch h
    | some fv =>
      rw [hfv] at h
      simp only [pure, Except.pure] at h
      cases hty : inferTypeCore env F (nP + k) (Expr.fvarTypeD fv) with
      | error _ => rw [hty] at h; exact nomatch h
      | ok ty =>
        rw [hty] at h
        dsimp only [] at h
        cases hu : ensureSortCore env F (nP + k) ty with
        | error _ => rw [hu] at h; exact nomatch h
        | ok u =>
          rw [hu] at h
          simp only [liftFueled] at h
          cases hle : Level.leq u s with
          | none => rw [hle] at h; exact nomatch h
          | some b =>
            rw [hle] at h
            cases b with
            | false =>
              simp only [pure, Except.pure, Bool.false_eq_true, if_false,
                throw, throwThe, MonadExceptOf.throw] at h
              exact nomatch h
            | true =>
              simp only [pure, Except.pure, if_true] at h
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
              · exact ih h j hj'
              · exact ⟨fv, ty, u, hfv, hty, hu, hle⟩

/-! ### Frames

Everything a per-binder soundness step needs at a frame, bundled: the
`inferType`/`ensureSort` claims all take the same five syntactic and
semantic inputs, and the field walk has to re-establish them at each
opened binder. -/

/-- The frame conditions of one expression. -/
structure FrameOk (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) (d : Nat) (ρ : Nat → V) (e : Expr) : Prop where
  ws : Expr.WScoped d e
  bb : e.looseBVarsBounded 0 = true
  lb : Expr.LeavesBounded e
  fv : FvarsOk V cval env φ d ρ e
  an : AnnotOk V cval env φ d ρ e
  it : ∃ P, interpExpr V cval env φ d ρ e = some P

/-- A `∀`'s domain inherits the frame. -/
theorem FrameOk.dom {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {n : Name} {dom body : Expr} {mb : BinderMeta}
    (h : FrameOk V cval env φ d ρ (.forallE n dom body mb)) :
    FrameOk V cval env φ d ρ dom := by
  obtain ⟨hws, hbb, hlb, hfv, han, P, hit⟩ := h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
  simp only [AnnotOk] at han
  obtain ⟨handom, -⟩ := han
  rw [interpExpr] at hit
  cases hdom : interpExpr V cval env φ d ρ dom with
  | none => rw [hdom] at hit; exact nomatch hit
  | some A =>
    refine ⟨hws.1, hbb.1, ?_, ?_, handom, ⟨A, hdom⟩⟩
    · exact fun l hl => hlb l (by simp [Expr.fvarLeaves, hl])
    · exact FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv

/-- Opening a `∀` re-establishes the frame one binder up. -/
theorem FrameOk.body {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {n : Name} {dom body : Expr} {mb : BinderMeta}
    {A x : V}
    (h : FrameOk V cval env φ d ρ (.forallE n dom body mb))
    (hdom : interpExpr V cval env φ d ρ dom = some A) (hx : x ∈ˢ A) :
    FrameOk V cval env φ (d + 1) (updV V ρ d x)
      (body.instantiate1 (.fvar d n dom)) := by
  obtain ⟨hws, hbb, hlb, hfv, han, -⟩ := h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
  simp only [AnnotOk] at han
  obtain ⟨handom, hcond⟩ := han
  obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
  obtain ⟨w, hwi⟩ := hwfact
  have hlbdom : Expr.LeavesBounded dom :=
    fun l hl => hlb l (by simp [Expr.fvarLeaves, hl])
  have hbdom : dom.looseBVarsBounded 0 = true := hbb.1
  refine ⟨hws.1.instantiate1 0 hws.2,
    looseBVarsBounded_instantiate1 body 0 hbb.2, ?_, ?_, hAb, ⟨w, hwi⟩⟩
  · intro l hl
    rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hlb l (by simp [Expr.fvarLeaves, hl'])
    · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact hbdom
      · exact hlbdom l hl'
  · exact FvarsOk.instantiate1 hws.1
      (FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv)
      handom hdom hx body 0 hws.2
      (FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv)

/-- A value-spine fit carries the frame conditions to its residual:
each step is `FrameOk.body` at the domain interpretation and membership
the fit already supplies.  This is how the field telescope's frame is
obtained at the constructor's install — from the very walk whose
`FieldTele` is being established. -/
theorem FrameOk.ofTeleFit {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e vs d' ρ' rest →
      FrameOk V cval env φ d ρ e →
      FrameOk V cval env φ d' ρ' rest := by
  intro d ρ e vs d' ρ' rest hfit
  induction hfit with
  | nil => exact fun hfr => hfr
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx hfit ih =>
    intro hfr
    exact ih (hfr.body hity hx)

/-! ### Transferring a value-spine fit between two telescopes

The constructor's `mem_type` has to fold the **type former's** value at
the parameter values the **constructor's** own fit supplies, so a fit
of one telescope has to become a fit of the other across the checked
parameter-domain `isDefEq` (`Inductive/Add.lean:220-222`).

`Setlec/Model/IotaWalk.lean`'s `pi_walk` is that transfer at a *fixed*
frame along an expression spine (`TeleFitI`).  It does not apply here:
a `TeleFit` opens each binder at a **new** frame, and the two
telescopes open at their **own** binder names and domains, so the two
walks' subjects diverge syntactically after the first binder.

The split below keeps that difficulty in one place.  `DomsInterpEq` is
the whole semantic content — "at every stage the two head domains
interpret alike, and this continues on the bodies opened at the
respective variables" — and `TeleFit.transfer` consumes it in a
five-line induction.  Establishing `DomsInterpEq` from the kernel's
pins is the separate (and only hard) step. -/

/-- The two telescopes' domains interpret alike, stage by stage, each
side opened at its **own** binder variables. -/
def DomsAgree (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) :
    Nat → Nat → (Nat → V) → Expr → Nat → (Nat → V) → Expr → Prop
  | 0, _, _, _, _, _, _ => True
  | k + 1, d₁, ρ₁, .forallE n₁ dom₁ body₁ _, d₂, ρ₂,
      .forallE n₂ dom₂ body₂ _ =>
    (∀ A, interpExpr V cval env φ d₁ ρ₁ dom₁ = some A →
      interpExpr V cval env φ d₂ ρ₂ dom₂ = some A) ∧
    ∀ (x A : V), interpExpr V cval env φ d₁ ρ₁ dom₁ = some A → x ∈ˢ A →
      DomsAgree V cval env φ k (d₁ + 1) (updV V ρ₁ d₁ x)
        (body₁.instantiate1 (.fvar d₁ n₁ dom₁))
        (d₂ + 1) (updV V ρ₂ d₂ x)
        (body₂.instantiate1 (.fvar d₂ n₂ dom₂))
  | _ + 1, _, _, _, _, _, _ => False

/-- The one-frame case, which is what the install's per-frame pins
produce directly. -/
abbrev DomsInterpEq (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat) (k d : Nat) (ρ : Nat → V) (S R : Expr) :
    Prop :=
  DomsAgree V cval env φ k d ρ S d ρ R

/-- **The transfer.**  A value-spine fit of one telescope is a fit of
any telescope whose domains interpret alike stage by stage — at the
very same frames and valuation, which is what lets both towers fold at
one frame. -/
theorem TeleFit.transfer {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {tyS tyR : Expr}
      {vs : List V} {d' : Nat} {ρ' : Nat → V} {restS : Expr},
      TeleFit V cval env φ d₁ ρ₁ tyS vs d' ρ' restS → vs.length = k →
      DomsAgree V cval env φ k d₁ ρ₁ tyS d₂ ρ₂ tyR →
      ∃ d'' ρ'' restR, TeleFit V cval env φ d₂ ρ₂ tyR vs d'' ρ'' restR := by
  intro k
  induction k with
  | zero =>
    intro d₁ d₂ ρ₁ ρ₂ tyS tyR vs d' ρ' restS hfit hlen _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    exact ⟨d₂, ρ₂, tyR, TeleFit.nil⟩
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ tyS tyR vs d' ρ' restS hfit hlen hdoms
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ nS domS bodyS mS x xs dd ρρ rest A hdom hx hfit =>
      match tyR with
      | .forallE nR domR bodyR mR =>
        obtain ⟨hdomEq, hstep⟩ := hdoms
        obtain ⟨d'', ρ'', restR, hfitR⟩ := ih hfit (by simpa using hlen)
          (hstep x A hdom hx)
        exact ⟨d'', ρ'', restR, TeleFit.cons (hdomEq A hdom) hx hfitR⟩
      | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
      | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
        exact hdoms.elim

/-- A value-spine fit leaves the valuation below its starting frame
alone. -/
theorem TeleFit.rho_below {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e vs d' ρ' rest →
      ∀ i, i < d → ρ' i = ρ i := by
  intro d ρ e vs d' ρ' rest hfit
  induction hfit with
  | nil => intro _ _; rfl
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx hfit ih =>
    intro i hi
    rw [ih i (by omega)]
    simp only [updV]
    rw [if_neg (by omega)]

/-- A value-spine fit leaves the valuation above its own span alone. -/
theorem TeleFit.rho_above {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e vs d' ρ' rest →
      ∀ i, d + vs.length ≤ i → ρ' i = ρ i := by
  intro d ρ e vs d' ρ' rest hfit
  induction hfit with
  | nil => intro _ _; rfl
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx hfit ih =>
    intro i hi
    simp only [List.length_cons] at hi
    rw [ih i (by omega)]
    simp only [updV]
    rw [if_neg (by omega)]

/-- A value-spine fit puts its `i`-th value in slot `d + i`. -/
theorem TeleFit.slots {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e vs d' ρ' rest →
      ∀ i, i < vs.length → ρ' (d + i) = vs.getD i SetTheory.empty := by
  intro d ρ e vs d' ρ' rest hfit
  induction hfit with
  | nil => intro i hi; exact absurd hi (by simp)
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx hfit ih =>
    intro i hi
    cases i with
    | zero =>
      rw [Nat.add_zero, hfit.rho_below d (by omega)]
      simp [updV]
    | succ i =>
      have h := ih i (by simpa using hi)
      rw [show d + (i + 1) = d + 1 + i from by omega]
      rw [h]
      rfl

/-- Two fits of (possibly different) telescopes from the **same**
starting frame with the **same** values end at the same frame and
valuation: the valuation is determined by the values. -/
theorem TeleFit.rho_det {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {e₁ e₂ : Expr} {vs : List V}
    {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {r₁ r₂ : Expr}
    (h₁ : TeleFit V cval env φ d ρ e₁ vs d₁ ρ₁ r₁)
    (h₂ : TeleFit V cval env φ d ρ e₂ vs d₂ ρ₂ r₂) : ρ₁ = ρ₂ := by
  refine funext (fun i => ?_)
  by_cases hlo : i < d
  · rw [h₁.rho_below i hlo, h₂.rho_below i hlo]
  by_cases hhi : d + vs.length ≤ i
  · rw [h₁.rho_above i hhi, h₂.rho_above i hhi]
  · have hik : i - d < vs.length := by omega
    have he : d + (i - d) = i := by omega
    have e₁' := h₁.slots (i - d) hik
    have e₂' := h₂.slots (i - d) hik
    rw [he] at e₁' e₂'
    rw [e₁', e₂']

/-- **`DomsInterpEq` from the kernel's per-frame pins.**

`checkDirectParamDoms` compares parameter domain `j` at frame `j`, with
each telescope opened at its **own** variables, so at every stage both
sides carry their own frame conditions (`FrameOk.dom`) and
`isDefEqCore_sound` applies at exactly the frame the walk is at — no
lifting between frames, and no mixing of one telescope's annotations
into the other. -/
theorem DomsInterpEq.of_pins {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} :
    ∀ (k d : Nat) (ρ : Nat → V) (S R : Expr) (fvsS fvsR : List Expr)
      (rS rR : Expr),
      openPisAtFvars k S d = some (fvsS, rS) →
      openPisAtFvars k R d = some (fvsR, rR) →
      (∀ (j : Nat) (a b : Expr), fvsS[j]? = some a → fvsR[j]? = some b →
        isDefEqCore env F (d + j) (Expr.fvarTypeD a) (Expr.fvarTypeD b)
          = .ok true) →
      FrameOk V m.val env φ d ρ S →
      FrameOk V m.val env φ d ρ R →
      DomsInterpEq V m.val env φ k d ρ S R := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ S R fvsS fvsR rS rR hopS hopR hpins hfrS hfrR
    match S, R with
    | .forallE nS domS bodyS mS, .forallE nR domR bodyR mR =>
      simp only [openPisAtFvars] at hopS hopR
      cases hrecS : openPisAtFvars k
          (bodyS.instantiate1 (.fvar d nS domS)) (d + 1) with
      | none => rw [hrecS] at hopS; exact nomatch hopS
      | some qS =>
      cases hrecR : openPisAtFvars k
          (bodyR.instantiate1 (.fvar d nR domR)) (d + 1) with
      | none => rw [hrecR] at hopR; exact nomatch hopR
      | some qR =>
        rw [hrecS] at hopS
        rw [hrecR] at hopR
        simp only [Option.some.injEq, Prod.mk.injEq] at hopS hopR
        obtain ⟨rfl, rfl⟩ := hopS
        obtain ⟨rfl, rfl⟩ := hopR
        obtain ⟨hdWS, hdbS, hdlS, hdfS, hdaS, BS, hdiS⟩ := hfrS.dom
        obtain ⟨hdWR, hdbR, hdlR, hdfR, hdaR, BR, hdiR⟩ := hfrR.dom
        -- the pin at this binder, at exactly this frame
        have hpin : isDefEqCore env F d domS domR = .ok true := by
          have h0 := hpins 0 (.fvar d nS domS) (.fvar d nR domR) rfl rfl
          rwa [Nat.add_zero] at h0
        have hBeq : BS = BR :=
          isDefEqCore_sound m F hpin hdWS hdWR hdbS hdbR hdlS hdlR
            hdfS hdfR hdaS hdaR hdiS hdiR
        have hdiR' : ∀ A, interpExpr V m.val env φ d ρ domS = some A →
            interpExpr V m.val env φ d ρ domR = some A := by
          intro A hA
          have hAB : A = BS := (Option.some.inj (hdiS.symm.trans hA)).symm
          rw [hAB, hBeq]
          exact hdiR
        refine ⟨hdiR', ?_⟩
        · intro x A hA hx
          have hAB : A = BS := (Option.some.inj (hdiS.symm.trans hA)).symm
          subst hAB
          refine ih (d + 1) (updV V ρ d x) _ _ qS.1 qR.1 qS.2 qR.2
            hrecS hrecR ?_ (hfrS.body hdiS hx)
            (hfrR.body (hdiR' _ hdiS) hx)
          intro j a b ha hb
          have h1 := hpins (j + 1) a b (by simpa using ha) (by simpa using hb)
          rw [show d + 1 + j = d + (j + 1) from by omega]
          exact h1
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ =>
      simp only [openPisAtFvars] at hopR; exact nomatch hopR
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ =>
      simp only [openPisAtFvars] at hopS; exact nomatch hopS

/-! ### Relocating a telescope's tower across frames

`DomsAgree` relates two openings of one telescope at **unrelated
frames**, so it also relocates everything the openings determine: the
dependent-pair tower, the per-field universe bound, and (above) any
value-spine fit.  This is the `TeleFit.reframe0` family DESIGN records
as the endgame precondition for the direct class's `eta`/`unitlike` —
stated here for the towers generally rather than for one call site, so
those discharges can consume it unchanged.

Frames genuinely differ in the recursor's telescope: the type former's
value is a tower over the *constructor's* opening (field binders at
`nP …`), while the recursor puts the motive and minor in between (field
binders at `nP+2 …`). -/

/-- The dependent-pair tower depends on its telescope only through the
domains' interpretations, so it relocates across frames. -/
theorem sigmaTowerV_reframe {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {w : Nat} :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {t₁ t₂ : Expr},
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      FieldTele V cval env φ w k d₁ ρ₁ t₁ →
      sigmaTowerV V cval env φ w k d₁ ρ₁ t₁ =
        sigmaTowerV V cval env φ w k d₂ ρ₂ t₂ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ t₁ t₂ hag hfld
    match t₁, t₂ with
    | .forallE n₁ dom₁ body₁ m₁, .forallE n₂ dom₂ body₂ m₂ =>
      obtain ⟨hdomEq, hstep⟩ := hag
      obtain ⟨A, hA, hAu, hrest⟩ := hfld
      rw [sigmaTowerV_forallE, sigmaTowerV_forallE, hA, hdomEq A hA]
      -- `sigma_congr`: only the fibres *inside* the domain matter
      refine sigma_congr (fun x hx => ?_)
      exact ih (hstep x A hA hx) (hrest x hx)
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ => exact hag.elim
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ => exact hag.elim

/-- `ErasedEq` telescopes have equal towers: the tower reads the
domains' interpretations, which `ErasedEq` preserves
(`interp_erasedEq`), and nothing else. -/
theorem DomsAgree.of_erasedEq {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} :
    ∀ (k d : Nat) (ρ : Nat → V) {t₁ t₂ : Expr},
      Expr.ErasedEq t₁ t₂ →
      (Expr.stripPis k t₁).isSome = true →
      DomsAgree V cval env φ k d ρ t₁ d ρ t₂ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ t₁ t₂ hEE hstrip
    match t₁ with
    | .forallE n₁ dom₁ body₁ m₁ =>
      rw [Expr.stripPis] at hstrip
      have hb : (Expr.stripPis k body₁).isSome = true := by
        cases hs : Expr.stripPis k body₁ with
        | none => rw [hs] at hstrip; exact nomatch hstrip
        | some _ => rfl
      match t₂, hEE with
      | .forallE n₂ dom₂ body₂ m₂, hEE =>
        obtain ⟨-, hdomEE, hbodyEE⟩ := hEE
        refine ⟨fun A hA => by rw [← interp_erasedEq hdomEE d ρ]; exact hA,
          fun x A hA hx => ?_⟩
        exact ih (d + 1) (updV V ρ d x)
          (Expr.ErasedEq.instantiate1 hbodyEE (by exact rfl))
          (stripPis_instantiate1_isSome k body₁ _ 0 hb)
      | .bvar _, hEE | .fvar _ _ _, hEE | .sort _, hEE | .const _ _, hEE
      | .app _ _, hEE | .lam _ _ _ _, hEE | .letE _ _ _ _, hEE
      | .lit _, hEE | .proj _ _ _, hEE => exact hEE.elim
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hstrip

/-- `FrameOk.body` at a **foreign** opening variable: the binder is
opened at `.fvar d n' dom'` rather than at its own `.fvar d n dom`.
Everything the frame conditions read about the substituted variable
comes from `dom'`'s own frame; the two openings are `ErasedEq`, which
is all the interpretation (`interp_erasedEq`) and the annotation
truthfulness (`AnnotOk.erasedEq`) look at.

This is what an `Expr.instPisAt` walk needs: it instantiates one
telescope's bodies at *another* telescope's opening variables. -/
theorem FrameOk.body_at {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {n n' : Name} {dom dom' body : Expr}
    {mb : BinderMeta} {A x : V}
    (h : FrameOk V cval env φ d ρ (.forallE n dom body mb))
    (hfr' : FrameOk V cval env φ d ρ dom')
    (hdom : interpExpr V cval env φ d ρ dom = some A)
    (hdom' : interpExpr V cval env φ d ρ dom' = some A) (hx : x ∈ˢ A) :
    FrameOk V cval env φ (d + 1) (updV V ρ d x)
      (body.instantiate1 (.fvar d n' dom')) := by
  obtain ⟨hws, hbb, hlb, hfv, han, -⟩ := h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
  simp only [AnnotOk] at han
  obtain ⟨-, hcond⟩ := han
  obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
  obtain ⟨w, hwi⟩ := hwfact
  have hEE : Expr.ErasedEq (body.instantiate1 (.fvar d n dom))
      (body.instantiate1 (.fvar d n' dom')) :=
    Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl body) (by exact rfl)
  refine ⟨hfr'.ws.instantiate1 0 hws.2,
    looseBVarsBounded_instantiate1 body 0 hbb.2, ?_, ?_,
    AnnotOk.erasedEq _ hEE (d + 1) (updV V ρ d x) hAb,
    w, by rw [← interp_erasedEq hEE (d + 1) (updV V ρ d x)]; exact hwi⟩
  · intro l hl
    rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hlb l (by simp [Expr.fvarLeaves, hl'])
    · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact hfr'.bb
      · exact hfr'.lb l hl'
  · exact FvarsOk.instantiate1 hfr'.ws hfr'.fv hfr'.an hdom' hx body 0 hws.2
      (FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv)

/-- The frame conditions survive one more opened binder above them. -/
theorem FrameOk.weaken_top {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {x : V} {e : Expr}
    (h : FrameOk V cval env φ d ρ e) :
    FrameOk V cval env φ (d + 1) (updV V ρ d x) e := by
  obtain ⟨P, hP⟩ := h.it
  exact ⟨h.ws.mono (by omega), h.bb, h.lb, FvarsOk.weaken_top h.ws h.fv,
    AnnotOk.weaken_top h.ws h.an,
    P, by rw [interp_weaken_top h.ws]; exact hP⟩

/-- The frame conditions and the interpretation survive **any** number
of opened binders above them: a single padded valuation serves every
term that is frame-ok at the lower frame.  This is what lets a pin
checked at one *fixed* high frame — `checkProjRule`'s parameter-domain
`checkDefEqList` runs at `nP + nF`, not per binder — be consumed at the
telescope frames the walk is actually at. -/
theorem FrameOk.pad_exists {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (n d : Nat) (ρ : Nat → V),
      ∃ ρ' : Nat → V,
        (∀ {e : Expr}, FrameOk V cval env φ d ρ e →
          FrameOk V cval env φ (d + n) ρ' e) ∧
        (∀ {e : Expr}, Expr.WScoped d e →
          interpExpr V cval env φ (d + n) ρ' e =
            interpExpr V cval env φ d ρ e) := by
  intro n
  induction n with
  | zero => intro d ρ; exact ⟨ρ, fun h => h, fun _ => rfl⟩
  | succ n ih =>
    intro d ρ
    obtain ⟨ρ', hfr, hint⟩ := ih d ρ
    refine ⟨updV V ρ' (d + n) SetTheory.empty, fun h => ?_, fun hw => ?_⟩
    · rw [show d + (n + 1) = d + n + 1 from by omega]
      exact FrameOk.weaken_top (hfr h)
    · rw [show d + (n + 1) = d + n + 1 from by omega,
        interp_weaken_top (hw.mono (by omega)), hint hw]

/-- `isDefEqCore_sound` at a **higher** frame than the terms live at:
the pin's frame only has to dominate the frame the interpretations are
taken at. -/
theorem isDefEqCore_sound_at {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} {d D : Nat} {ρ : Nat → V} {a b : Expr} {A B : V}
    (hle : d ≤ D) (h : isDefEqCore env F D a b = .ok true)
    (hfa : FrameOk V m.val env φ d ρ a) (hfb : FrameOk V m.val env φ d ρ b)
    (hia : interpExpr V m.val env φ d ρ a = some A)
    (hib : interpExpr V m.val env φ d ρ b = some B) : A = B := by
  obtain ⟨ρ', hfr, hint⟩ := FrameOk.pad_exists (V := V) (cval := m.val)
    (env := env) (φ := φ) (D - d) d ρ
  rw [show d + (D - d) = D from by omega] at hfr hint
  exact isDefEqCore_sound m F h (hfr hfa).ws (hfr hfb).ws (hfr hfa).bb
    (hfr hfb).bb (hfr hfa).lb (hfr hfb).lb (hfr hfa).fv (hfr hfb).fv
    (hfr hfa).an (hfr hfb).an (by rw [hint hfa.ws]; exact hia)
    (by rw [hint hfb.ws]; exact hib)

/-- A term scoped below a fit's starting frame interprets the same at
the fit's end. -/
theorem interp_weaken_fit {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty vs d' ρ' rest →
      ∀ {e : Expr}, Expr.WScoped d e →
        interpExpr V cval env φ d' ρ' e = interpExpr V cval env φ d ρ e := by
  intro d ρ ty vs d' ρ' rest hfit
  induction hfit with
  | nil => intro e _; rfl
  | @cons d ρ n dom body mb x xs d' ρ' rest A hdom hx hfit ih =>
    intro e hw
    rw [ih (hw.mono (by omega)), interp_weaken_top hw]

/-- A value-spine fit's binder domains, read at the fit's **end**
frame, carry the corresponding values.  The domains are the opened
variables' annotations — which is exactly how the `instPisAt` walk of
the same telescope spells them (`openPisAtFvars_spec`). -/
theorem TeleFit.doms_at_end {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty vs d' ρ' rest →
      Expr.WScoped d ty →
      ∀ {fvs : List Expr}, openPisAtFvars vs.length ty d = some (fvs, rest) →
      ∀ (k : Nat) (a : Expr) (v : V), fvs[k]? = some a → vs[k]? = some v →
        ∃ A, interpExpr V cval env φ d' ρ' (Expr.fvarTypeD a) = some A ∧
          v ∈ˢ A := by
  intro d ρ ty vs d' ρ' rest hfit
  induction hfit with
  | nil => intro _ fvs _ k a v _ hv; simp at hv
  | @cons d ρ n dom body mb x xs d' ρ' rest A hdom hx hfit ih =>
    intro hwe fvs hop k a v ha hv
    have hwe' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwe
    simp only [List.length_cons, openPisAtFvars] at hop
    cases hrec : openPisAtFvars xs.length
        (body.instantiate1 (.fvar d n dom)) (d + 1) with
    | none => rw [hrec] at hop; exact nomatch hop
    | some q =>
      rw [hrec] at hop
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      cases k with
      | zero =>
        obtain rfl : Expr.fvar d n dom = a := Option.some.inj ha
        obtain rfl : x = v := Option.some.inj hv
        refine ⟨A, ?_, hx⟩
        show interpExpr V cval env φ d' ρ' dom = some A
        rw [interp_weaken_fit hfit (hwe'.1.mono (by omega)),
          interp_weaken_top hwe'.1]
        exact hdom
      | succ k =>
        refine ih ?_ hrec k a v (by simpa using ha) (by simpa using hv)
        refine Expr.WScoped.instantiate1_gen ?_ 0 (hwe'.2.mono (by omega))
        simp only [Expr.WScoped]
        exact ⟨by omega, hwe'.1⟩

/-- An `instPisAt` walk along a spine of **arbitrary** expressions with
known interpreted values is an expression-spine fit, provided the
walk's domains carry those values.  The free-variable case is
`pi_walk`; the direct path's projection stage walks the constructor
telescope at the earlier projections' *applications*, which are not
variables. -/
theorem TeleFitI.ofInstWalk {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {D : Nat} {ρ : Nat → V} :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rest : Expr}
      {vs : List V},
      Expr.instPisAt sp ty = some (ds, rest) →
      InstArgs cval env φ D ρ sp vs →
      (∀ a ∈ sp, AnnotOk V cval env φ D ρ a) →
      Expr.fvarsBelow D ty →
      (∀ (k : Nat) (a : Expr) (v : V), ds[k]? = some a → vs[k]? = some v →
        ∃ A, interpExpr V cval env φ D ρ a = some A ∧ v ∈ˢ A) →
      TeleFitI V cval env φ D ρ ty sp vs rest := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rest vs hinst hia _ _ _
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hinst
    obtain ⟨rfl, rfl⟩ := hinst
    match vs, hia with
    | [], _ => exact TeleFitI.nil
  | cons a sp ih =>
    intro ty ds rest vs hinst hia hAn hfb hmem
    obtain ⟨n, dom, body, mb, ds', rfl, rfl, hinst'⟩ := instPisAt_cons_inv hinst
    match vs, hia with
    | v :: vs', ⟨⟨hwa, hba, hiav⟩, hia'⟩ =>
      obtain ⟨A, hA, hvA⟩ := hmem 0 dom v rfl rfl
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      refine TeleFitI.cons hA hiav hvA hfb'.2 hwa hba
        (hAn a List.mem_cons_self) ?_
      exact ih hinst' hia' (fun b hb => hAn b (List.mem_cons_of_mem _ hb))
        (fvarsBelow_instantiate1_gen hwa.fvarsBelow 0 hfb'.2)
        (fun k b w hb hw => hmem (k + 1) b w (by simpa using hb)
          (by simpa using hw))

/-- The frame conditions survive a fit that starts above the term. -/
theorem FrameOk.weaken_fit {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty vs d' ρ' rest →
      ∀ {e : Expr}, FrameOk V cval env φ d ρ e →
        FrameOk V cval env φ d' ρ' e := by
  intro d ρ ty vs d' ρ' rest hfit
  induction hfit with
  | nil => intro e h; exact h
  | @cons d ρ n dom body mb x xs d' ρ' rest A hdom hx hfit ih =>
    intro e h; exact ih h.weaken_top

/-- An opening variable is frame-ok when its annotation is and the
valuation puts it in the annotation's interpretation. -/
theorem FrameOk.fvar {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d D : Nat} {ρ : Nat → V} {n : Name} {dom : Expr} {A : V}
    (hdom : FrameOk V cval env φ D ρ dom) (hlt : d < D)
    (hws : Expr.WScoped d dom)
    (hA : interpExpr V cval env φ D ρ dom = some A) (hmem : ρ d ∈ˢ A) :
    FrameOk V cval env φ D ρ (.fvar d n dom) := by
  refine ⟨by simp only [Expr.WScoped]; exact ⟨hlt, hws⟩, rfl, ?_, ?_,
    by simp only [AnnotOk], ρ d, by rw [interpExpr]⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hdom.bb
    · exact hdom.lb l hl
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨hlt, hdom.an, A, hA, hmem⟩
    · exact hdom.fv l hl

/-- Every variable an opening introduces is frame-ok at the fit's end
frame: its annotation is the binder domain the fit interpreted, and the
valuation carries the fitting value. -/
theorem FrameOk.openVars {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d : Nat} {ρ : Nat → V} {ty : Expr} {fvs : List Expr}
      {rest : Expr} {vs : List V} {d' : Nat} {ρ' : Nat → V},
      openPisAtFvars k ty d = some (fvs, rest) →
      TeleFit V cval env φ d ρ ty vs d' ρ' rest →
      vs.length = k →
      FrameOk V cval env φ d ρ ty →
      ∀ a ∈ fvs, FrameOk V cval env φ d' ρ' a := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty fvs rest vs d' ρ' hop _ _ _ a ha
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch ha
  | succ k ih =>
    intro d ρ ty fvs rest vs d' ρ' hop hfit hlen hfr a ha
    match ty with
    | .forallE n dom body mb =>
      cases hfit with
      | nil => exact absurd hlen (by simp)
      | @cons _ _ _ _ _ _ x xs _ _ _ A hdomI hx hfit' =>
        simp only [openPisAtFvars] at hop
        cases hrec : openPisAtFvars k
            (body.instantiate1 (.fvar d n dom)) (d + 1) with
        | none => rw [hrec] at hop; exact nomatch hop
        | some q =>
          rw [hrec] at hop
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          rcases List.mem_cons.mp ha with rfl | ha
          · refine FrameOk.weaken_fit hfit' ?_
            refine FrameOk.fvar (A := A) (FrameOk.weaken_top hfr.dom)
              (by omega) hfr.dom.ws ?_ ?_
            · rw [interp_weaken_top hfr.dom.ws]; exact hdomI
            · simpa only [updV, if_pos] using hx
          · exact ih hrec hfit' (by simpa using hlen) (hfr.body hdomI hx) a ha
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      simp only [openPisAtFvars] at hop; exact nomatch hop

/-- The frame conditions along an `Expr.instPisAt` walk at another
telescope's opening variables: each step is `FrameOk.body_at` at the
walked domain's interpretation, which the install's per-frame pins
identify with the substituted variable's, and the fit along the
*opened* telescope supplies the membership.

This is the residual counterpart of `DomsAgree.of_pins_inst` — the two
share their step, but a `DomsAgree` quantifies over all fitting values
while the residual's frame is at one spine. -/
theorem FrameOk.ofInstWalk {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} :
    ∀ (sp : List Expr) {R : Expr} {ds : List Expr} {rR : Expr} {d : Nat}
      {ρ : Nat → V} {S : Expr} {vs : List V} {d' : Nat} {ρ' : Nat → V}
      {rS : Expr},
      Expr.instPisAt sp R = some (ds, rR) →
      openPisAtFvars sp.length S d = some (sp, rS) →
      TeleFit V m.val env φ d ρ S vs d' ρ' rS →
      vs.length = sp.length →
      FrameOk V m.val env φ d ρ S →
      FrameOk V m.val env φ d ρ R →
      (∀ (j : Nat) (a b : Expr), sp[j]? = some a → ds[j]? = some b →
        isDefEqCore env F (d + j) (Expr.fvarTypeD a) b = .ok true) →
      FrameOk V m.val env φ d' ρ' rR := by
  intro sp
  induction sp with
  | nil =>
    intro R ds rR d ρ S vs d' ρ' rS hinst _ hfit hlen _ hfrR _
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hinst
    obtain ⟨rfl, rfl⟩ := hinst
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    exact hfrR
  | cons a sp ih =>
    intro R ds rR d ρ S vs d' ρ' rS hinst hop hfit hlen hfrS hfrR hpins
    match S with
    | .forallE nS domS bodyS mS =>
      cases hfit with
      | nil => exact absurd hlen (by simp)
      | @cons _ _ _ _ _ _ x vs' _ _ _ A hdomS hx hfit' =>
        simp only [List.length_cons, openPisAtFvars] at hop
        cases hrecS : openPisAtFvars sp.length
            (bodyS.instantiate1 (.fvar d nS domS)) (d + 1) with
        | none => rw [hrecS] at hop; exact nomatch hop
        | some qS =>
          rw [hrecS] at hop
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨ha, hrS⟩ := hop
          obtain ⟨rfl, rfl⟩ : Expr.fvar d nS domS = a ∧ qS.1 = sp := by
            cases ha; exact ⟨rfl, rfl⟩
          subst hrS
          obtain ⟨nR, domR, bodyR, mR, ds', rfl, rfl, hinst'⟩ :=
            instPisAt_cons_inv hinst
          obtain ⟨-, -, -, -, -, BR, hdiR⟩ := hfrR.dom
          have hpin : isDefEqCore env F d domS domR = .ok true := by
            have h0 := hpins 0 (.fvar d nS domS) domR rfl rfl
            rwa [Nat.add_zero] at h0
          obtain ⟨hdWS, hdbS, hdlS, hdfS, hdaS, -⟩ := hfrS.dom
          obtain ⟨hdWR, hdbR, hdlR, hdfR, hdaR, -⟩ := hfrR.dom
          have hBeq : A = BR :=
            isDefEqCore_sound m F hpin hdWS hdWR hdbS hdbR hdlS hdlR
              hdfS hdfR hdaS hdaR hdomS hdiR
          refine ih hinst' hrecS hfit' (by simpa using hlen)
            (hfrS.body hdomS hx)
            (FrameOk.body_at hfrR hfrS.dom (by rw [hBeq]; exact hdiR) hdomS hx)
            (fun j b c hb hc => by
              have h1 := hpins (j + 1) b c (by simpa using hb)
                (by simpa using hc)
              rw [show d + 1 + j = d + (j + 1) from by omega]
              exact h1)
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      simp only [List.length_cons, openPisAtFvars] at hop; exact nomatch hop

/-- **`DomsAgree` across a frame shift.**  One *closed* telescope,
walked along two free-variable spines that carry the **same values** at
otherwise unrelated frames, agrees stage by stage.

`ErasedEq` cannot reach this case: the two openings instantiate at
different `fvar` indices, so no per-stage syntactic relation survives.
What does survive is that every domain the walk meets is an `instSeq`
of a *closed*, position-bounded subterm of the telescope along the
consumed prefix, and for such a term `interp_instSeq_fvarFrames`
settles the two interpretations from the spines' values alone.

Stated on `instSeq` rather than on a telescope walk, because the two
shifted openings the recursor needs arise both ways: the constructor's
field telescope is the residual of an `instPisAt` walk
(`DomsAgree.of_shift` below), while the minor premise's is a *binder
domain* of the recursor's telescope, hence an `instSeq` of a closed
subterm and not a walk residual at all. -/
theorem DomsAgree.of_shiftSeq {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} :
    ∀ (k : Nat) {ty : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr} {sp₁ sp₂ : List Expr} {vs : List V} {D₁ D₂ : Nat}
      {ρ₁ ρ₂ : Nat → V},
      ty.hasFvar = false →
      ty.looseBVarsBounded sp₁.length = true →
      ty.stripPis k = some (bs, body) →
      FvarSpine D₁ ρ₁ sp₁ vs → FvarSpine D₂ ρ₂ sp₂ vs →
      DomsAgree V cval env φ k D₁ ρ₁ (instSeq sp₁ (sp₁.length - 1) ty)
        D₂ ρ₂ (instSeq sp₂ (sp₂.length - 1) ty) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro ty bs body sp₁ sp₂ vs D₁ D₂ ρ₁ ρ₂ hcl hbd hstrip hsp₁ hsp₂
    match ty with
    | .forallE n dom bodyE mb =>
      rw [Expr.stripPis] at hstrip
      cases hs : bodyE.stripPis k with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some q =>
        have hcl' : dom.hasFvar = false ∧ bodyE.hasFvar = false := by
          simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hcl
          exact hcl
        have hbd' : dom.looseBVarsBounded sp₁.length = true ∧
            bodyE.looseBVarsBounded (sp₁.length + 1) = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
          exact hbd
        have hdomEq := interp_instSeq_fvarFrames (V := V) (cval := cval)
          (env := env) (φ := φ) (e := dom) hcl'.1 hbd'.1 hsp₁ hsp₂
        -- the instantiation index of an opened body, spelled as the snoc
        -- spine's own
        have hidx : ∀ (sp : List Expr),
            instSeq sp (sp.length - 1 + 1) bodyE = instSeq sp sp.length bodyE := by
          intro sp
          cases sp with
          | nil => rfl
          | cons a as => simp
        have hsnoc : ∀ (sp : List Expr) (a : Expr),
            (instSeq sp sp.length bodyE).instantiate1 a =
              instSeq (sp ++ [a]) ((sp ++ [a]).length - 1) bodyE := by
          intro sp a
          rw [show (sp ++ [a]).length - 1 = sp.length from by simp,
            instSeq_append sp [a] sp.length bodyE, Nat.sub_self]
          rfl
        rw [instSeq_forallE sp₁ (sp₁.length - 1) n dom bodyE mb (by omega),
          instSeq_forallE sp₂ (sp₂.length - 1) n dom bodyE mb (by omega),
          hidx sp₁, hidx sp₂]
        refine ⟨fun A hA => by rw [← hdomEq]; exact hA, ?_⟩
        intro x A hA hx
        have hlift₁ : FvarSpine (D₁ + 1) (updV V ρ₁ D₁ x) sp₁ vs :=
          hsp₁.lift (by omega) (fun i hi => by
            simp only [updV]; rw [if_neg (by omega)])
        have hlift₂ : FvarSpine (D₂ + 1) (updV V ρ₂ D₂ x) sp₂ vs :=
          hsp₂.lift (by omega) (fun i hi => by
            simp only [updV]; rw [if_neg (by omega)])
        rw [hsnoc sp₁, hsnoc sp₂]
        refine ih (vs := vs ++ [x]) hcl'.2 (by simpa using hbd'.2)
          (by rw [hs]) ?_ ?_
        · exact hlift₁.snoc (v := x) ⟨D₁, n, _, rfl, by omega, by simp [updV]⟩
        · exact hlift₂.snoc (v := x) ⟨D₂, n, _, rfl, by omega, by simp [updV]⟩
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hstrip

/-- The walk-residual form of `DomsAgree.of_shiftSeq`: one closed
telescope, its parameter prefix consumed along two free-variable spines
with the same values, agrees on the remaining `k` binders at both
frames.

The recursor's minor premise is where this bites: its field binders
open at `nP+2 …` while the constructor's open at `nP …`. -/
theorem DomsAgree.of_shift {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {ty : Expr} (hcl : ty.hasFvar = false)
    (hty0 : ty.looseBVarsBounded 0 = true) (k : Nat)
    {bs : List (Name × Expr × BinderMeta)} {body : Expr}
    {sp₁ sp₂ : List Expr} {vs : List V} {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {ds₁ ds₂ : List Expr} {r₁ r₂ : Expr}
    (hstrip : ty.stripPis (sp₁.length + k) = some (bs, body))
    (h₁ : Expr.instPisAt sp₁ ty = some (ds₁, r₁))
    (h₂ : Expr.instPisAt sp₂ ty = some (ds₂, r₂))
    (hsp₁ : FvarSpine D₁ ρ₁ sp₁ vs) (hsp₂ : FvarSpine D₂ ρ₂ sp₂ vs) :
    DomsAgree V cval env φ k D₁ ρ₁ r₁ D₂ ρ₂ r₂ := by
  have hlen : sp₂.length = sp₁.length := by
    rw [FvarSpine.length hsp₂, ← FvarSpine.length hsp₁]
  obtain ⟨mid, hstripM, hstripK⟩ := Expr.stripPis_add sp₁.length k hstrip
  obtain ⟨rfl, -⟩ := instPisAt_stripPis sp₁ h₁ hstripM
  obtain ⟨rfl, -⟩ := instPisAt_stripPis sp₂ h₂ (by rw [hlen]; exact hstripM)
  exact DomsAgree.of_shiftSeq k (stripPis_body_hasFvar _ hstripM hcl)
    (by simpa using stripPis_body_bounded _ hstripM hty0) hstripK hsp₁ hsp₂

/-- `DomsAgree` composes: the middle telescope's domain interpretations
are what both halves quantify over. -/
theorem DomsAgree.trans {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d₁ d₂ d₃ : Nat} {ρ₁ ρ₂ ρ₃ : Nat → V} {t₁ t₂ t₃ : Expr},
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      DomsAgree V cval env φ k d₂ ρ₂ t₂ d₃ ρ₃ t₃ →
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₃ ρ₃ t₃ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d₁ d₂ d₃ ρ₁ ρ₂ ρ₃ t₁ t₂ t₃ h₁₂ h₂₃
    match t₁, t₂, t₃ with
    | .forallE _ _ _ _, .forallE _ _ _ _, .forallE _ _ _ _ =>
      exact ⟨fun A hA => h₂₃.1 A (h₁₂.1 A hA),
        fun x A hA hx => ih (h₁₂.2 x A hA hx) (h₂₃.2 x A (h₁₂.1 A hA) hx)⟩
    | .forallE _ _ _ _, .forallE _ _ _ _, .bvar _
    | .forallE _ _ _ _, .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .forallE _ _ _ _, .sort _
    | .forallE _ _ _ _, .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .forallE _ _ _ _, .app _ _
    | .forallE _ _ _ _, .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .forallE _ _ _ _, .letE _ _ _ _
    | .forallE _ _ _ _, .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .forallE _ _ _ _, .proj _ _ _ => exact h₂₃.elim
    | .forallE _ _ _ _, .bvar _, _ | .forallE _ _ _ _, .fvar _ _ _, _
    | .forallE _ _ _ _, .sort _, _ | .forallE _ _ _ _, .const _ _, _
    | .forallE _ _ _ _, .app _ _, _ | .forallE _ _ _ _, .lam _ _ _ _, _
    | .forallE _ _ _ _, .letE _ _ _ _, _ | .forallE _ _ _ _, .lit _, _
    | .forallE _ _ _ _, .proj _ _ _, _ => exact h₁₂.elim
    | .bvar _, _, _ | .fvar _ _ _, _, _ | .sort _, _, _ | .const _ _, _, _
    | .app _ _, _, _ | .lam _ _ _ _, _, _ | .letE _ _ _ _, _, _
    | .lit _, _, _ | .proj _ _ _, _, _ => exact h₁₂.elim

/-- The right-hand telescope may be replaced by an `ErasedEq` one: the
interpretation does not read binder names or `fvar` annotations
(`interp_erasedEq`), and the walk's shape comes from the left. -/
theorem DomsAgree.erasedEq_right {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {t₁ t₂ t₃ : Expr},
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      Expr.ErasedEq t₂ t₃ →
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₃ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ t₁ t₂ t₃ hag hEE
    match t₁, t₂ with
    | .forallE n₁ dom₁ body₁ m₁, .forallE n₂ dom₂ body₂ m₂ =>
      obtain ⟨hdomEq, hstep⟩ := hag
      match t₃, hEE with
      | .forallE n₃ dom₃ body₃ m₃, hEE =>
        obtain ⟨-, hdomEE, hbodyEE⟩ := hEE
        refine ⟨fun A hA => by
          rw [← interp_erasedEq hdomEE d₂ ρ₂]; exact hdomEq A hA, ?_⟩
        intro x A hA hx
        exact ih (hstep x A hA hx)
          (Expr.ErasedEq.instantiate1 hbodyEE (by exact rfl))
      | .bvar _, hEE | .fvar _ _ _, hEE | .sort _, hEE | .const _ _, hEE
      | .app _ _, hEE | .lam _ _ _ _, hEE | .letE _ _ _ _, hEE
      | .lit _, hEE | .proj _ _ _, hEE => exact hEE.elim
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ => exact hag.elim
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ => exact hag.elim

/-- **`DomsAgree` from pins against an instantiation walk.**  The
recursor's two pin sites (`checkDirectRecTy`) compare the *opened*
binder domains of one telescope against the domains an `Expr.instPisAt`
walk of the other produces **at those very variables** — not against a
second opening.  The walk's bodies are therefore instantiated at the
left telescope's variables, which `DomsAgree` (each side opened at its
own) meets only up to `ErasedEq`; `FrameOk.body_at` carries the frame
conditions onto the foreign opening and `erasedEq_right` closes the
gap at every stage. -/
theorem DomsAgree.of_pins_inst_gen {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} :
    ∀ (k d : Nat) (ρ : Nat → V) (S R : Expr) (fvsS : List Expr) (rS : Expr)
      (dsR : List Expr) (rR : Expr) (Df : Nat → Nat),
      (∀ j, j < k → d + j ≤ Df j) →
      openPisAtFvars k S d = some (fvsS, rS) →
      Expr.instPisAt fvsS R = some (dsR, rR) →
      (∀ (j : Nat) (a b : Expr), fvsS[j]? = some a → dsR[j]? = some b →
        isDefEqCore env F (Df j) (Expr.fvarTypeD a) b = .ok true) →
      FrameOk V m.val env φ d ρ S →
      FrameOk V m.val env φ d ρ R →
      DomsAgree V m.val env φ k d ρ S d ρ R := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ S R fvsS rS dsR rR Df hDf hopS hinstR hpins hfrS hfrR
    match S with
    | .forallE nS domS bodyS mS =>
      simp only [openPisAtFvars] at hopS
      cases hrecS : openPisAtFvars k
          (bodyS.instantiate1 (.fvar d nS domS)) (d + 1) with
      | none => rw [hrecS] at hopS; exact nomatch hopS
      | some qS =>
        rw [hrecS] at hopS
        simp only [Option.some.injEq, Prod.mk.injEq] at hopS
        obtain ⟨rfl, rfl⟩ := hopS
        obtain ⟨nR, domR, bodyR, mR, dsR', rfl, rfl, hinstR'⟩ :=
          instPisAt_cons_inv hinstR
        obtain ⟨hdWS, hdbS, hdlS, hdfS, hdaS, BS, hdiS⟩ := hfrS.dom
        obtain ⟨hdWR, hdbR, hdlR, hdfR, hdaR, BR, hdiR⟩ := hfrR.dom
        have hpin : isDefEqCore env F (Df 0) domS domR = .ok true :=
          hpins 0 (.fvar d nS domS) domR rfl rfl
        have hBeq : BS = BR :=
          isDefEqCore_sound_at m F (by have := hDf 0 (by omega); omega) hpin
            hfrS.dom hfrR.dom hdiS hdiR
        have hdiR' : ∀ A, interpExpr V m.val env φ d ρ domS = some A →
            interpExpr V m.val env φ d ρ domR = some A := by
          intro A hA
          have hAB : A = BS := (Option.some.inj (hdiS.symm.trans hA)).symm
          rw [hAB, hBeq]
          exact hdiR
        refine ⟨hdiR', ?_⟩
        intro x A hA hx
        have hAB : A = BS := (Option.some.inj (hdiS.symm.trans hA)).symm
        subst hAB
        refine DomsAgree.erasedEq_right k
          (ih (d + 1) (updV V ρ d x) _ _ qS.1 qS.2 dsR' rR (fun j => Df (j + 1))
            (fun j hj => by have := hDf (j + 1) (by omega); omega)
            hrecS hinstR'
            (fun j a b ha hb =>
              hpins (j + 1) a b (by simpa using ha) (by simpa using hb))
            (hfrS.body hdiS hx)
            (FrameOk.body_at hfrR hfrS.dom (hdiR' _ hdiS) hdiS hx))
          (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl bodyR) (by exact rfl))
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      simp only [openPisAtFvars] at hopS; exact nomatch hopS

/-- The per-frame instance: the pins were checked at exactly the frame
each binder sits at. -/
theorem DomsAgree.of_pins_inst {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} (k d : Nat) (ρ : Nat → V) (S R : Expr)
    (fvsS : List Expr) (rS : Expr) (dsR : List Expr) (rR : Expr)
    (hopS : openPisAtFvars k S d = some (fvsS, rS))
    (hinstR : Expr.instPisAt fvsS R = some (dsR, rR))
    (hpins : ∀ (j : Nat) (a b : Expr), fvsS[j]? = some a → dsR[j]? = some b →
      isDefEqCore env F (d + j) (Expr.fvarTypeD a) b = .ok true)
    (hfrS : FrameOk V m.val env φ d ρ S)
    (hfrR : FrameOk V m.val env φ d ρ R) :
    DomsAgree V m.val env φ k d ρ S d ρ R :=
  DomsAgree.of_pins_inst_gen m F k d ρ S R fvsS rS dsR rR (fun j => d + j)
    (fun _ _ => Nat.le_refl _) hopS hinstR hpins hfrS hfrR

/-- The fixed-frame instance: every pin was checked at one frame `D`
above the whole telescope (`checkProjRule`'s parameter-domain list). -/
theorem DomsAgree.of_pins_inst_at {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} (k d D : Nat) (ρ : Nat → V) (S R : Expr)
    (fvsS : List Expr) (rS : Expr) (dsR : List Expr) (rR : Expr)
    (hD : d + k ≤ D)
    (hopS : openPisAtFvars k S d = some (fvsS, rS))
    (hinstR : Expr.instPisAt fvsS R = some (dsR, rR))
    (hpins : ∀ (j : Nat) (a b : Expr), fvsS[j]? = some a → dsR[j]? = some b →
      isDefEqCore env F D (Expr.fvarTypeD a) b = .ok true)
    (hfrS : FrameOk V m.val env φ d ρ S)
    (hfrR : FrameOk V m.val env φ d ρ R) :
    DomsAgree V m.val env φ k d ρ S d ρ R :=
  DomsAgree.of_pins_inst_gen m F k d ρ S R fvsS rS dsR rR (fun _ => D)
    (fun _ hj => by omega) hopS hinstR hpins hfrS hfrR

/-- `DomsAgree` is symmetric once the left telescope is known to
interpret at every stage (`FrameOk`): the relation is an equality of
domain interpretations, stated one-directionally because the right side
need not be known to interpret. -/
theorem DomsAgree.symm {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {t₁ t₂ : Expr},
      FrameOk V cval env φ d₁ ρ₁ t₁ →
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      DomsAgree V cval env φ k d₂ ρ₂ t₂ d₁ ρ₁ t₁ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ t₁ t₂ hfr hag
    match t₁, t₂ with
    | .forallE n₁ dom₁ body₁ m₁, .forallE n₂ dom₂ body₂ m₂ =>
      obtain ⟨hdomEq, hstep⟩ := hag
      obtain ⟨A₁, hA₁⟩ := hfr.dom.it
      have hpin := hdomEq A₁ hA₁
      refine ⟨fun A hA => ?_, fun x A hA hx => ?_⟩
      · obtain rfl : A = A₁ := Option.some.inj (hA.symm.trans hpin)
        exact hA₁
      · obtain rfl : A = A₁ := Option.some.inj (hA.symm.trans hpin)
        exact ih (hfr.body hA₁ hx) (hstep x A hA₁ hx)
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ => exact hag.elim
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ => exact hag.elim

/-- `DomsAgree` moves across the block's own extensions, like the
towers it relocates: it reads the two telescopes only through their
binder domains' interpretations, and those domains resolve before the
extension. -/
theorem DomsAgree.congr {cval₁ cval₂ : ConstVal V} {env₁ env₂ : Env}
    {φ : Name → Nat} (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ) :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {t₁ t₂ : Expr}
      {fvs₁ fvs₂ : List Expr} {r₁ r₂ : Expr},
      openPisAtFvars k t₁ d₁ = some (fvs₁, r₁) →
      openPisAtFvars k t₂ d₂ = some (fvs₂, r₂) →
      (∀ x ∈ fvs₁, (Expr.fvarTypeD x).constsResolve env₁ = true) →
      (∀ x ∈ fvs₂, (Expr.fvarTypeD x).constsResolve env₁ = true) →
      DomsAgree V cval₁ env₁ φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      DomsAgree V cval₂ env₂ φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ t₁ t₂ fvs₁ fvs₂ r₁ r₂ hop₁ hop₂ hres₁ hres₂ hag
    match t₁, t₂ with
    | .forallE n₁ dom₁ body₁ m₁, .forallE n₂ dom₂ body₂ m₂ =>
      simp only [openPisAtFvars] at hop₁ hop₂
      cases hrec₁ : openPisAtFvars k
          (body₁.instantiate1 (.fvar d₁ n₁ dom₁)) (d₁ + 1) with
      | none => rw [hrec₁] at hop₁; exact nomatch hop₁
      | some q₁ =>
      cases hrec₂ : openPisAtFvars k
          (body₂.instantiate1 (.fvar d₂ n₂ dom₂)) (d₂ + 1) with
      | none => rw [hrec₂] at hop₂; exact nomatch hop₂
      | some q₂ =>
        rw [hrec₁] at hop₁
        rw [hrec₂] at hop₂
        simp only [Option.some.injEq, Prod.mk.injEq] at hop₁ hop₂
        obtain ⟨rfl, rfl⟩ := hop₁
        obtain ⟨rfl, rfl⟩ := hop₂
        obtain ⟨hdomEq, hstep⟩ := hag
        have hr₁ : dom₁.constsResolve env₁ = true := by
          simpa [Expr.fvarTypeD] using hres₁ _ List.mem_cons_self
        have hr₂ : dom₂.constsResolve env₁ = true := by
          simpa [Expr.fvarTypeD] using hres₂ _ List.mem_cons_self
        refine ⟨fun A hA => ?_, fun x A hA hx => ?_⟩
        · rw [← h dom₂ hr₂ d₂ ρ₂]
          exact hdomEq A (by rw [h dom₁ hr₁ d₁ ρ₁]; exact hA)
        · exact ih hrec₁ hrec₂
            (fun y hy => hres₁ y (List.mem_cons_of_mem _ hy))
            (fun y hy => hres₂ y (List.mem_cons_of_mem _ hy))
            (hstep x A (by rw [h dom₁ hr₁ d₁ ρ₁]; exact hA) hx)
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ =>
      simp only [openPisAtFvars] at hop₂; exact nomatch hop₂
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ =>
      simp only [openPisAtFvars] at hop₁; exact nomatch hop₁

/-- The per-field universe bound relocates across frames too. -/
theorem FieldTele_reframe {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {w : Nat} :
    ∀ (k : Nat) {d₁ d₂ : Nat} {ρ₁ ρ₂ : Nat → V} {t₁ t₂ : Expr},
      DomsAgree V cval env φ k d₁ ρ₁ t₁ d₂ ρ₂ t₂ →
      FieldTele V cval env φ w k d₁ ρ₁ t₁ →
      FieldTele V cval env φ w k d₂ ρ₂ t₂ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d₁ d₂ ρ₁ ρ₂ t₁ t₂ hag hfld
    match t₁, t₂ with
    | .forallE n₁ dom₁ body₁ m₁, .forallE n₂ dom₂ body₂ m₂ =>
      obtain ⟨hdomEq, hstep⟩ := hag
      obtain ⟨A, hA, hAu, hrest⟩ := hfld
      exact ⟨A, hdomEq A hA, hAu, fun x hx =>
        ih (hstep x A hA hx) (hrest x hx)⟩
    | .forallE _ _ _ _, .bvar _ | .forallE _ _ _ _, .fvar _ _ _
    | .forallE _ _ _ _, .sort _ | .forallE _ _ _ _, .const _ _
    | .forallE _ _ _ _, .app _ _ | .forallE _ _ _ _, .lam _ _ _ _
    | .forallE _ _ _ _, .letE _ _ _ _ | .forallE _ _ _ _, .lit _
    | .forallE _ _ _ _, .proj _ _ _ => exact hag.elim
    | .bvar _, _ | .fvar _ _ _, _ | .sort _, _ | .const _ _, _
    | .app _ _, _ | .lam _ _ _ _, _ | .letE _ _ _ _, _ | .lit _, _
    | .proj _ _ _, _ => exact hag.elim

/-- A value-spine fit moves along an `Expr.ErasedEq` telescope, at the
same frames and valuation: the fit reads the domains only through their
interpretations (`interp_erasedEq`), and each opening variable's index
is all `ErasedEq` records of it.  This is the fit-level counterpart of
`DomsAgree.of_erasedEq`, without its `stripPis` side condition. -/
theorem TeleFit.erasedEq {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ {d : Nat} {ρ : Nat → V} {t₁ : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {r₁ : Expr},
      TeleFit V cval env φ d ρ t₁ vs d' ρ' r₁ →
      ∀ {t₂ : Expr}, Expr.ErasedEq t₁ t₂ →
        ∃ r₂, TeleFit V cval env φ d ρ t₂ vs d' ρ' r₂ ∧
          Expr.ErasedEq r₁ r₂ := by
  intro d ρ t₁ vs d' ρ' r₁ hfit
  induction hfit with
  | nil => intro t₂ hEE; exact ⟨t₂, TeleFit.nil, hEE⟩
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx hfit ih =>
    intro t₂ hEE
    match t₂, hEE with
    | .forallE n₂ ty₂ body₂ m₂, hEE =>
      obtain ⟨-, htyEE, hbodyEE⟩ := hEE
      obtain ⟨r₂, hfit₂, hrEE⟩ := ih
        (t₂ := body₂.instantiate1 (.fvar d n₂ ty₂))
        (Expr.ErasedEq.instantiate1 hbodyEE
          (show Expr.ErasedEq (.fvar d n ty) (.fvar d n₂ ty₂) from rfl))
      exact ⟨r₂, TeleFit.cons (by rw [← interp_erasedEq htyEE d ρ]; exact hity)
        hx hfit₂, hrEE⟩
    | .bvar _, hEE | .fvar _ _ _, hEE | .sort _, hEE | .const _ _, hEE
    | .app _ _, hEE | .lam _ _ _ _, hEE | .letE _ _ _ _, hEE
    | .lit _, hEE | .proj _ _ _, hEE => exact hEE.elim

/-- The frame conditions move **up** the canonical list valuations: a
term frame-ok at `j` with the prefix's valuation is frame-ok at any
frame above `xs.length` with the whole list's.  The upward companion of
`interp_getD_canon`/`annotOk_getD_canon`, proved once for all six
components by iterating `FrameOk.weaken_top`. -/
theorem FrameOk.getD_up {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {e : Expr} {xs : List V} {j D : Nat}
    (hjx : j ≤ xs.length) (hxD : xs.length ≤ D)
    (h : FrameOk V cval env φ j
      (fun i => (xs.take j).getD i SetTheory.empty) e) :
    FrameOk V cval env φ D (fun i => xs.getD i SetTheory.empty) e := by
  have step1 : ∀ n, j + n ≤ xs.length →
      FrameOk V cval env φ (j + n)
        (fun i => (xs.take (j + n)).getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => intro _; exact h
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      obtain ⟨v, hv⟩ : ∃ v, xs[j + n]? = some v :=
        ⟨xs[j + n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hupd : (fun i => (xs.take (j + n + 1)).getD i SetTheory.empty) =
          updV V (fun i => (xs.take (j + n)).getD i SetTheory.empty)
            (j + n) v := by
        rw [List.take_add_one, hv]
        exact getD_snoc_eq_updV (by rw [List.length_take]; omega)
      rw [show j + (n + 1) = j + n + 1 from by omega, hupd]
      exact FrameOk.weaken_top hprev
  have h1 := step1 (xs.length - j) (by omega)
  rw [show j + (xs.length - j) = xs.length from by omega,
    List.take_of_length_le (Nat.le_refl _)] at h1
  have step2 : ∀ n, FrameOk V cval env φ (xs.length + n)
      (fun i => xs.getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      have hupd : (fun i => xs.getD i SetTheory.empty) =
          updV V (fun i => xs.getD i SetTheory.empty) (xs.length + n)
            (SetTheory.empty : V) := by
        funext i
        simp only [updV]
        split
        · next hi =>
          rw [hi, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega)]
          rfl
        · rfl
      have h3 := FrameOk.weaken_top (x := (SetTheory.empty : V)) ih
      rw [show xs.length + (n + 1) = xs.length + n + 1 from by omega]
      rwa [← hupd] at h3
  have h2 := step2 (D - xs.length)
  rw [show xs.length + (D - xs.length) = D from by omega] at h2
  exact h2

/-! ### From `FramePref` to a value-spine fit

The rule-tower machinery (`TowerOk.of_stages`) carries its stage
memberships as a `FramePref` over the *opening spine* — each value
inhabits its own frame variable's annotation, at the prefix
valuation — while every fold equation of the constructed values
consumes a `TeleFit` of the telescope itself.  The two valuation
conventions, `TeleFit`'s `updV` chain and `FramePref`'s
`fun i => (xs.take j).getD i ∅`, are equal *functions*, so the bridge
is the opening walk plus `funext` (`getD_snoc_eq_updV`). -/

/-- **`FramePref` is a fit.**  A prefix-membership invariant over an
opening spine is a value-spine fit of the opened telescope, at the
canonical list valuations and at the very frames the opening runs
at. -/
theorem TeleFit.of_framePref {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {spine : List Expr} {xs : List V}
    (hpref : FramePref cval env φ spine xs) :
    ∀ (n d : Nat) {e : Expr} {fvs : List Expr} {rest : Expr},
      openPisAtFvars n e d = some (fvs, rest) →
      (∀ k, k < n → spine[d + k]? = fvs[k]?) →
      d + n ≤ xs.length →
      TeleFit V cval env φ d (fun i => (xs.take d).getD i SetTheory.empty) e
        ((xs.drop d).take n) (d + n)
        (fun i => (xs.take (d + n)).getD i SetTheory.empty) rest := by
  intro n
  induction n with
  | zero =>
    intro d e fvs rest hop _ _
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    simpa using TeleFit.nil
  | succ n ih =>
    intro d e fvs rest hop halign hlen
    match e with
    | .forallE nm dom body mb =>
      simp only [openPisAtFvars] at hop
      cases hrec : openPisAtFvars n (body.instantiate1 (.fvar d nm dom))
          (d + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some q =>
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hd : d < xs.length := by omega
        have hxv : xs[d]? = some (xs.getD d SetTheory.empty) := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hd]
          rfl
        have hsp : spine[d]? = some (Expr.fvar d nm dom) := by
          have h0 := halign 0 (by omega)
          rw [Nat.add_zero] at h0
          rw [h0]
          rfl
        obtain ⟨B, hB, hvB⟩ := hpref d _ _ hxv hsp
        simp only [Expr.fvarTypeD] at hB
        -- the valuation after the head binder is the next prefix
        have hupd : (fun i => (xs.take (d + 1)).getD i SetTheory.empty) =
            updV V (fun i => (xs.take d).getD i SetTheory.empty) d
              (xs.getD d SetTheory.empty) := by
          rw [List.take_add_one, hxv]
          exact getD_snoc_eq_updV (by rw [List.length_take]; omega)
        have hrecfit := ih (d + 1) hrec
          (fun k hk => by
            have h := halign (k + 1) (by omega)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h
            simpa using h)
          (by omega)
        rw [hupd, show d + 1 + n = d + (n + 1) from by omega] at hrecfit
        have hhead : (xs.drop d).take (n + 1) =
            xs.getD d SetTheory.empty :: (xs.drop (d + 1)).take n := by
          rw [show xs.drop d = xs.getD d SetTheory.empty :: xs.drop (d + 1) from by
            rw [List.drop_eq_getElem_cons hd, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hd]
            rfl]
          rfl
        rw [hhead]
        exact TeleFit.cons hB hvB hrecfit
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hop

/-! ### `FieldTele` from the per-field universe walk -/

/-- The field telescope is small at the structure's own sort: each
opened field domain interprets, and its inferred sort — checked `≤` the
result sort — puts it in that universe by cumulativity.  This is the
semantic content of the reference kernels' per-field universe bound. -/
theorem FieldTele_of_walk {env : Env} (m : EnvModel V env) {F : Nat}
    {φ : Name → Nat} {s : Level} :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr) (xFvs : List Expr) (rest : Expr),
      openPisAtFvars k ty d = some (xFvs, rest) →
      FrameOk V m.val env φ d ρ ty →
      (∀ j, j < k → ∃ fv tyj u, xFvs[j]? = some fv ∧
        inferTypeCore env F (d + j) (Expr.fvarTypeD fv) = .ok tyj ∧
        ensureSortCore env F (d + j) tyj = .ok u ∧
        Level.leq u s = some true) →
      FieldTele V m.val env φ (s.eval φ) k d ρ ty := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ ty xFvs rest hop hfr hwalk
    match ty with
    | .forallE n dom body mb =>
      simp only [openPisAtFvars] at hop
      cases hrec : openPisAtFvars k (body.instantiate1 (.fvar d n dom)) (d + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some q =>
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        -- the head field: its domain is the frame's domain
        obtain ⟨fv0, ty0, u0, hfv0, hinf, hens, hle⟩ :=
          hwalk 0 (by omega)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hfv0
        obtain rfl := hfv0
        rw [Nat.add_zero] at hinf hens
        obtain ⟨hdws, hdbb, hdlb, hdfv, hdan, -⟩ := hfr.dom
        obtain ⟨-, ⟨v, tv, hvi, htvi, hmem⟩, htyW, htyA⟩ :=
          inferTypeCore_sound m F hinf hdws hdbb hdlb hdfv
        simp only [Expr.fvarTypeD] at hvi
        -- the inferred sort is a universe, and it is at most `s`
        have htyb : ty0.looseBVarsBounded 0 = true :=
          inferTypeCore_looseBVars m.wf F hinf hdws hdbb hdlb
        have htyLb : Expr.LeavesBounded ty0 := fun l hl =>
          hdlb l (inferTypeCore_fvarLeaves m.wf F hinf hdws l hl)
        have htyFv : FvarsOk V m.val env φ d ρ ty0 :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf F hinf hdws) hdfv
        have hens' := ensureSortCore_sound m F hens htyW htyb htyLb htyFv htyA
        rw [hens'] at htvi
        obtain rfl : tv = univ (u0.eval φ) := (Option.some.inj htvi).symm
        have hAu : v ∈ˢ (univ (s.eval φ) : V) :=
          univ_mono (Level.leq_sound hle φ) v hmem
        refine ⟨v, hvi, hAu, ?_⟩
        intro x hx
        refine ih (d + 1) (updV V ρ d x) _ q.1 q.2 hrec
          (hfr.body hvi hx) ?_
        intro j hj
        obtain ⟨fv, tyj, u, hfvj, hinfj, hensj, hlej⟩ := hwalk (j + 1) (by omega)
        simp only [List.getElem?_cons_succ] at hfvj
        refine ⟨fv, tyj, u, hfvj, ?_, ?_, hlej⟩
        · rw [show d + 1 + j = d + (j + 1) from by omega]; exact hinfj
        · rw [show d + 1 + j = d + (j + 1) from by omega]; exact hensj
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hop

end Setlec
