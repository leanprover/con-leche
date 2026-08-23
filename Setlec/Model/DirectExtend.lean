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
  obtain ⟨handom, ⟨cod, hcod⟩, -⟩ := han
  rw [interpExpr, hcod] at hit
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
  obtain ⟨handom, ⟨cod, hcod⟩, hcond⟩ := han
  obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
  obtain ⟨w, hwi, -⟩ := hwfact cod hcod
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

omit [SetTheory V] in
/-- Two instantiations of one telescope along **index-matched** free
variable spines agree up to `Expr.ErasedEq` — pointwise on the
instantiated domains and on the residual.

The recursor stage needs this because its `crest` instantiates the
constructor's telescope at the *recursor's* parameter variables, while
the type former's value is a tower over the constructor's *own*
opening: same indices, different binder names and annotations, which
`ErasedEq` — and hence the interpretation — does not read. -/
theorem instPisAt_erasedEq_spines :
    ∀ (sp₁ : List Expr) {sp₂ : List Expr} {e₁ e₂ : Expr}
      {ds₁ ds₂ : List Expr} {r₁ r₂ : Expr},
      Expr.ErasedEq e₁ e₂ →
      sp₁.length = sp₂.length →
      (∀ (j : Nat) (a b : Expr), sp₁[j]? = some a → sp₂[j]? = some b →
        Expr.ErasedEq a b) →
      Expr.instPisAt sp₁ e₁ = some (ds₁, r₁) →
      Expr.instPisAt sp₂ e₂ = some (ds₂, r₂) →
      (∀ (j : Nat) (a b : Expr), ds₁[j]? = some a → ds₂[j]? = some b →
        Expr.ErasedEq a b) ∧ Expr.ErasedEq r₁ r₂ := by
  intro sp₁
  induction sp₁ with
  | nil =>
    intro sp₂ e₁ e₂ ds₁ ds₂ r₁ r₂ hEE hlen _ h₁ h₂
    obtain rfl : sp₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun j a b ha _ => by simp at ha, hEE⟩
  | cons a₁ sp₁ ih =>
    intro sp₂ e₁ e₂ ds₁ ds₂ r₁ r₂ hEE hlen hsp h₁ h₂
    match sp₂ with
    | a₂ :: sp₂ =>
      obtain ⟨n₁, dom₁, body₁, m₁, ds₁', rfl, rfl, h₁'⟩ := instPisAt_cons_inv h₁
      match e₂, hEE with
      | .forallE n₂ dom₂ body₂ m₂, hEE =>
        obtain ⟨-, hdomEE, hbodyEE⟩ := hEE
        obtain ⟨n₂', dom₂', body₂', m₂', ds₂', heq₂, rfl, h₂'⟩ :=
          instPisAt_cons_inv h₂
        obtain ⟨rfl, rfl, rfl, rfl⟩ :
            n₂' = n₂ ∧ dom₂' = dom₂ ∧ body₂' = body₂ ∧ m₂' = m₂ := by
          cases heq₂; exact ⟨rfl, rfl, rfl, rfl⟩
        have ha : Expr.ErasedEq a₁ a₂ := hsp 0 a₁ a₂ rfl rfl
        obtain ⟨hds, hr⟩ := ih (Expr.ErasedEq.instantiate1 hbodyEE ha)
          (by simpa using hlen)
          (fun j x y hx hy => hsp (j + 1) x y (by simpa using hx)
            (by simpa using hy))
          h₁' h₂'
        refine ⟨fun j x y hx hy => ?_, hr⟩
        cases j with
        | zero =>
          obtain rfl := Option.some.inj hx
          obtain rfl := Option.some.inj hy
          exact hdomEE
        | succ j =>
          exact hds j x y (by simpa using hx) (by simpa using hy)

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

/-- **`DomsAgree` across a frame shift.**  One *closed* telescope,
walked along two free-variable spines that carry the **same values** at
otherwise unrelated frames, agrees stage by stage.

`ErasedEq` cannot reach this case: the two openings instantiate at
different `fvar` indices, so no per-stage syntactic relation survives.
What does survive is that each opened domain is an `instSeq` of the
telescope's *own* binder domain — closed (`stripPis_doms_hasFvar`) and
bounded by its position (`stripPis_doms_bounded`) — along the consumed
prefix (`instPisAt_head`), and for such a domain
`interp_instSeq_fvarFrames` settles the two interpretations from the
spines' values alone.

The recursor's minor premise is where this bites: its field binders
open at `nP+2 …` while the constructor's open at `nP …`. -/
theorem DomsAgree.of_shift {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {ty : Expr} (hcl : ty.hasFvar = false)
    (hty0 : ty.looseBVarsBounded 0 = true) :
    ∀ (k : Nat) {bs : List (Name × Expr × BinderMeta)} {body : Expr}
      {sp₁ sp₂ : List Expr} {vs : List V} {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
      {ds₁ ds₂ : List Expr} {r₁ r₂ : Expr},
      ty.stripPis (sp₁.length + k) = some (bs, body) →
      Expr.instPisAt sp₁ ty = some (ds₁, r₁) →
      Expr.instPisAt sp₂ ty = some (ds₂, r₂) →
      FvarSpine D₁ ρ₁ sp₁ vs → FvarSpine D₂ ρ₂ sp₂ vs →
      DomsAgree V cval env φ k D₁ ρ₁ r₁ D₂ ρ₂ r₂ := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro bs body sp₁ sp₂ vs D₁ D₂ ρ₁ ρ₂ ds₁ ds₂ r₁ r₂ hstrip h₁ h₂
      hsp₁ hsp₂
    have hlen : sp₂.length = sp₁.length := by
      rw [FvarSpine.length hsp₂, ← FvarSpine.length hsp₁]
    have hbslen : bs.length = sp₁.length + (k + 1) :=
      Expr.stripPis_length _ hstrip
    obtain ⟨b, hb⟩ : ∃ b, bs[sp₁.length]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bodyR₁, hr₁, hext₁⟩ := Expr.instPisAt_head sp₁ h₁ hstrip hb
    obtain ⟨bodyR₂, hr₂, hext₂⟩ := Expr.instPisAt_head sp₂ h₂
      (by rw [hlen]; exact hstrip) (by rw [hlen]; exact hb)
    -- the head domain is the telescope's own binder domain, instantiated
    -- along the consumed prefix on each side
    have hdomcl : b.2.1.hasFvar = false :=
      stripPis_doms_hasFvar _ hstrip hcl b (List.mem_of_getElem? hb)
    have hdombd : b.2.1.looseBVarsBounded sp₁.length = true := by
      simpa using stripPis_doms_bounded _ 0 hstrip hty0 sp₁.length b hb
    have hdomEq := interp_instSeq_fvarFrames (V := V) (cval := cval)
      (env := env) (φ := φ) (e := b.2.1) hdomcl hdombd hsp₁ hsp₂
    rw [hlen] at hr₂ hext₂ hdomEq
    subst hr₁; subst hr₂
    refine ⟨fun A hA => by rw [← hdomEq]; exact hA, ?_⟩
    intro x A hA hx
    have hlift₁ : FvarSpine (D₁ + 1) (updV V ρ₁ D₁ x) sp₁ vs :=
      hsp₁.lift (by omega) (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)])
    have hlift₂ : FvarSpine (D₂ + 1) (updV V ρ₂ D₂ x) sp₂ vs :=
      hsp₂.lift (by omega) (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)])
    have hstrip' : ∀ a : Expr,
        ty.stripPis ((sp₁ ++ [a]).length + k) = some (bs, body) := by
      intro a
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [show sp₁.length + (0 + 1) + k = sp₁.length + (k + 1) from by omega]
      exact hstrip
    exact ih (hstrip' _) (hext₁ _) (hext₂ _)
      (hlift₁.snoc (v := x) ⟨D₁, b.1, _, rfl, by omega, by simp [updV]⟩)
      (hlift₂.snoc (v := x) ⟨D₂, b.1, _, rfl, by omega, by simp [updV]⟩)

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
        obtain ⟨⟨v, tv, hvi, htvi, hmem⟩, htyW, htyA⟩ :=
          inferTypeCore_sound m F hinf hdws hdbb hdlb hdfv hdan
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
