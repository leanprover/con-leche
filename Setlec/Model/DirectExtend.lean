import Setlec.Model.DirectParams
import Setlec.Model.Extend.Model

/-!
# The direct install's per-field universe walk, semantically

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`) installs a
recognised simple structure as the type former, the constructor, the
recursor with its rule and the `nF` projection functions — and
**nothing else**.  It stores no `_model` companions: synthesising them
would be re-implementing the preprocessor inside the checker (user
ruling, DESIGN.md), and it is not needed, because every `ModeledOk`
linkage clause is premised on the companion being *stored* and so is
vacuous for a directly installed block (`directNoModel`).

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
def DomsInterpEq (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) : Nat → Nat → (Nat → V) → Expr → Expr → Prop
  | 0, _, _, _, _ => True
  | k + 1, d, ρ, .forallE nS domS bodyS _, .forallE nR domR bodyR _ =>
    (∀ A, interpExpr V cval env φ d ρ domS = some A →
      interpExpr V cval env φ d ρ domR = some A) ∧
    ∀ (x A : V), interpExpr V cval env φ d ρ domS = some A → x ∈ˢ A →
      DomsInterpEq V cval env φ k (d + 1) (updV V ρ d x)
        (bodyS.instantiate1 (.fvar d nS domS))
        (bodyR.instantiate1 (.fvar d nR domR))
  | _ + 1, _, _, _, _ => False

/-- **The transfer.**  A value-spine fit of one telescope is a fit of
any telescope whose domains interpret alike stage by stage — at the
very same frames and valuation, which is what lets both towers fold at
one frame. -/
theorem TeleFit.transfer {cval : ConstVal V} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d : Nat} {ρ : Nat → V} {tyS tyR : Expr} {vs : List V}
      {d' : Nat} {ρ' : Nat → V} {restS : Expr},
      TeleFit V cval env φ d ρ tyS vs d' ρ' restS → vs.length = k →
      DomsInterpEq V cval env φ k d ρ tyS tyR →
      ∃ restR, TeleFit V cval env φ d ρ tyR vs d' ρ' restR := by
  intro k
  induction k with
  | zero =>
    intro d ρ tyS tyR vs d' ρ' restS hfit hlen _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    exact ⟨tyR, TeleFit.nil⟩
  | succ k ih =>
    intro d ρ tyS tyR vs d' ρ' restS hfit hlen hdoms
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ nS domS bodyS mS x xs d₂ ρ₂ rest A hdom hx hfit =>
      match tyR with
      | .forallE nR domR bodyR mR =>
        obtain ⟨hdomEq, hstep⟩ := hdoms
        obtain ⟨restR, hfitR⟩ := ih hfit (by simpa using hlen)
          (hstep x A hdom hx)
        exact ⟨restR, TeleFit.cons (hdomEq A hdom) hx hfitR⟩
      | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
      | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
        exact hdoms.elim

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
